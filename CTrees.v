(** Copyright (c) 2015 Bill White **)
(** Distributed under the MIT/X11 software license **)
(** See http://www.opensource.org/licenses/mit-license.php **)

(** CTrees: Compact trees (ctrees) are representations of nonempty mtrees which
    store less information. There is no ctree corresponding to an empty mtree,
    so the type option (ctree n) is used when we want to allow for
    the possibility of an empty tree. 
    If there is only one leaf beneath a node that is nonempty, then the corresponding
    ctree node may be given by a leaf with the rest of the address and the
    nonempty hlist (nehlist) that at that leaf.
    As with mtrees, a ctree node may be a hash value summarizing the missing information
    that would be below the node.
    Suppose a ctree node has more than one nonempty leaf beneath it. In this case
    it is possible that only the left child has nonempty leaves, only the right child
    has nonempty leaves, or both children have nonempty leaves. There are three
    cases for each of these. The development is similar to the one in MTrees,
    falling back on results from MTrees when it is reasonable to do so.
    The ctree representation can be used to determine if a transaction is supported
    (see mtree_ctree_supports_tx and mtree_octree_supports_tx). A ctree
    can be transformed using tx_octree_trans and this preserves approximation
    of ledger functions (octree_approx_trans). The change in the sum of the asset values
    of transformed ctrees corresponds to the rewards/fees of the supported transaction.
 **)

Require Export MTrees.

(*** Compact representations of mtrees ***)
Fixpoint ctree (n:nat) : Type :=
  match n with
    | O => nehlist
    | S n => sum (prod (bitseq (S n)) nehlist)
                 (sum hashval
                      (sum (ctree n)
                           (sum (ctree n)
                                (prod (ctree n) (ctree n)))))
end.

Definition ctreeL (hl:nehlist) {n} : bitseq n -> ctree n :=
match n with
| O => fun alpha => hl
| S n => fun alpha => inl (alpha,hl)
end.

Definition ctreeH (n:nat) (h:hashval) : ctree n :=
match n with
| O => inl h
| S n => inr (inl h)
end.

Definition ctreeBL {n} (Tl : ctree n) : ctree (S n) :=
inr (inr (inl Tl)).

Definition ctreeBR {n} (Tr : ctree n) : ctree (S n) :=
inr (inr (inr (inl Tr))).

Definition ctreeB {n} (Tl Tr : ctree n) : ctree (S n) :=
inr (inr (inr (inr (Tl,Tr)))).

Fixpoint ctreeLinv {n} : ctree n -> option (bitseq n * nehlist) :=
match n with
| O => fun T:ctree 0 => Some(tt,T)
| S n => fun T => match T with
                    | inl (alpha,hl) => Some(alpha,hl)
                    | inr (inr (inl Tl)) =>
                      match ctreeLinv Tl with
                        | Some(alpha,hl) => Some((false,alpha),hl)
                        | None => None
                      end
                    | inr (inr (inr (inl Tr))) =>
                      match ctreeLinv Tr with
                        | Some(alpha,hl) => Some((true,alpha),hl)
                        | None => None
                      end
                    | _ => None
                  end
end.

Definition ctreeHinv {n} : ctree n -> option hashval :=
  match n with
    | O => fun hl => match hl with
                       | inl h => Some(h)
                       | _ => None
                     end
    | S n => fun T => match T with
                        | inr (inl h) => Some(h)
                        | _ => None
                      end
  end.

Fixpoint ctree_mtree {n} : ctree n -> mtree n :=
  match n as n' return ctree n' -> mtree n' with
    | O => fun hl:ctree 0 => singlebranch_mtree hl (tt:bitseq 0)
    | S n => fun T:ctree (S n) =>
               match T with
                   | inl (alpha,hl) => singlebranch_mtree hl alpha
                   | inr (inl h) => mtreeH n (Some h)
                   | inr (inr (inl Tl)) => mtreeB (ctree_mtree Tl) (empty_mtree n)
                   | inr (inr (inr (inl Tr))) =>  mtreeB (empty_mtree n) (ctree_mtree Tr)
                   | inr (inr (inr (inr (Tl,Tr)))) => mtreeB (ctree_mtree Tl) (ctree_mtree Tr)
           end
end.

Definition ctree_node {n} : option (ctree n) -> option (ctree n) -> option (ctree (S n)) :=
fun T1o T2o =>
  match T1o,T2o with
    | Some(T1),Some(T2) => Some (ctreeB T1 T2)
    | Some(T1),None =>
      match ctreeLinv T1 with
        | Some(alpha,hl) => Some (ctreeL hl ((false,alpha):bitseq (S n)))
        | None => Some (ctreeBL T1)
      end
    | None,Some(T2) =>
      match ctreeLinv T2 with
        | Some(alpha,hl) => Some (ctreeL hl ((true,alpha):bitseq (S n)))
        | None => Some (ctreeBR T2)
      end
    | None,None => None
  end.

Fixpoint mtree_octree {n} : mtree n -> option (ctree n) :=
match n with
| O => fun hl:mtree 0 =>
         match hl with
           | hlistN => None
           | hlistH h => Some (ctreeL (inl h) (tt:bitseq 0))
           | hlistC h hl => Some (ctreeL (inr (h,hl)) (tt:bitseq 0))
         end
| S n => fun T:mtree (S n) =>
           match T with
               | inl None => None
               | inl (Some h) => Some (ctreeH (S n) h)
               | inr (Tl,Tr) =>
                 ctree_node (mtree_octree Tl) (mtree_octree Tr)
           end
end.

Lemma ctreeLinv_singlebranch {n} :
  forall (T:ctree n) alpha hl, 
    ctreeLinv T = Some (alpha, hl) ->
    singlebranch_mtree hl alpha = ctree_mtree T.
induction n as [|n IH].
- simpl. intros hr [] hl. congruence.
- simpl. intros [[beta [h|[h hr]]]|[h|[Tl|[Tr|[Tl Tr]]]]] alpha hl H1.
  + inversion H1. reflexivity.
  + inversion H1. reflexivity.
  + discriminate H1.
  + destruct (ctreeLinv Tl) as [[gamma hl']|] eqn:E1.
    * { inversion H1. rewrite (IH Tl).
        - reflexivity.
        - congruence.
      }
    * discriminate H1.
  + destruct (ctreeLinv Tr) as [[gamma hl']|] eqn:E1.
    * { inversion H1. rewrite (IH Tr).
        - reflexivity.
        - congruence.
      }
    * discriminate H1.
  + discriminate H1.
Qed.

Definition octree_mtree {n} (T: option (ctree n)) : mtree n :=
match T with
| None => empty_mtree n
| Some T => ctree_mtree T
end.

Lemma octree_inv {n} (T:mtree n) :
  mtree_normal_p T ->
  octree_mtree (mtree_octree T) = T.
induction n as [|n IH].
- destruct T as [h| |h hl]; intros _. simpl.
  + reflexivity.
  + simpl. reflexivity.
  + simpl. reflexivity.
- destruct T as [[h|]|[Tl Tr]]; intros HTm.
  + simpl. reflexivity.
  + simpl. reflexivity.
  + simpl. generalize (IH Tr). generalize (IH Tl). unfold octree_mtree.
    destruct (mtree_octree Tl) as [Tlc|] eqn:Tle.
    * { destruct (mtree_octree Tr) as [Trc|] eqn:Tre.
        - intros IHl IHr. simpl. rewrite IHl.
          + rewrite IHr.
            * reflexivity.
            * revert HTm. apply mtree_normal_R.
          + revert HTm. apply mtree_normal_L.
        - intros IHl IHr. simpl.
          destruct (ctreeLinv Tlc) as [[alpha hl1]|] eqn:Tlce.
          + unfold mtreeB. rewrite <- IHl.
            * { rewrite <- IHr.
                - rewrite (ctreeLinv_singlebranch Tlc).
                  + reflexivity.
                  + assumption.
                - revert HTm. apply mtree_normal_R.
              } 
            * revert HTm. apply mtree_normal_L.
          + simpl. unfold mtreeB. rewrite <- IHl.
            * { rewrite <- IHr.
                - reflexivity.
                - revert HTm. apply mtree_normal_R.
              } 
            * revert HTm. apply mtree_normal_L.
      } 
    * { destruct (mtree_octree Tr) as [Trc|] eqn:Tre.
        - intros IHl IHr. simpl.
          destruct (ctreeLinv Trc) as [[alpha hr1]|] eqn:Trce.
          + unfold mtreeB. rewrite <- IHl.
            * { rewrite <- IHr.
                - rewrite (ctreeLinv_singlebranch Trc).
                  + reflexivity.
                  + assumption.
                - revert HTm. apply mtree_normal_R.
              } 
            * revert HTm. apply mtree_normal_L.
          + simpl. unfold mtreeB. rewrite <- IHl.
            * { rewrite <- IHr.
                - reflexivity.
                - revert HTm. apply mtree_normal_R.
              } 
            * revert HTm. apply mtree_normal_L.
        - intros IHl IHr. exfalso.
          generalize HTm. rewrite <- IHl.
          + rewrite <- IHr.
            * { simpl. intros [_ [_ [H1|H1]]].
                - apply H1. apply mtree_hashroot_empty.
                - apply H1. apply mtree_hashroot_empty.
              }
            * revert HTm. apply mtree_normal_R.
          + revert HTm. apply mtree_normal_L.
      } 
Qed.

Lemma ctree_mtree_hashroot_nonempty {n} :
  forall T:ctree n,
    mtree_hashroot (ctree_mtree T) <> None.
induction n as [|n IH].
- intros [h|[h hl]].
  + simpl. discriminate.
  + simpl. destruct (hlist_hashroot hl) as [k|]; discriminate.
- intros [[[[|] gamma] hl]|[h|[Tl|[Tr|[Tl Tr]]]]].
  + simpl. rewrite mtree_hashroot_empty. simpl.
    destruct (mtree_hashroot (singlebranch_mtree hl gamma)) as [k|] eqn:H1.
    * discriminate.
    * exfalso. revert H1. apply mtree_hashroot_singlebranch_nonempty.
  + simpl. rewrite mtree_hashroot_empty. simpl.
    destruct (mtree_hashroot (singlebranch_mtree hl gamma)) as [k|] eqn:H1.
    * discriminate.
    * exfalso. revert H1. apply mtree_hashroot_singlebranch_nonempty.
  + simpl. discriminate.
  + simpl.
    destruct (mtree_hashroot (ctree_mtree Tl)) as [k|] eqn:H1.
    * simpl. rewrite mtree_hashroot_empty. discriminate.
    * exfalso. revert H1. apply IH.
  + simpl.
    destruct (mtree_hashroot (ctree_mtree Tr)) as [k|] eqn:H1.
    * simpl. rewrite mtree_hashroot_empty. discriminate.
    * exfalso. revert H1. apply IH.
  + simpl.
    destruct (mtree_hashroot (ctree_mtree Tl)) as [k|] eqn:H1.
    * simpl. destruct (mtree_hashroot (ctree_mtree Tr)); discriminate.
    * exfalso. revert H1. apply IH.
Qed.

Lemma octree_mtree_normal {n} (T:option (ctree n)) :
  mtree_normal_p (octree_mtree T).
destruct T as [T|].
- induction n as [|n IH].
  + simpl. tauto.
  + simpl. destruct T as [[[[|] gamma] [h|[h hl]]]|[h|[Tl|[Tr|[Tl Tr]]]]].
    * { unfold mtreeB. repeat split.
        - apply empty_mtree_normal.
        - apply singlebranch_mtree_normal.
        - right. apply mtree_hashroot_singlebranch_nonempty.
      }
    * { unfold mtreeB. repeat split.
        - apply empty_mtree_normal.
        - apply singlebranch_mtree_normal.
        - right. apply mtree_hashroot_singlebranch_nonempty.
      }
    * { unfold mtreeB. repeat split.
        - simpl. apply singlebranch_mtree_normal.
        - apply empty_mtree_normal.
        - left. apply mtree_hashroot_singlebranch_nonempty.
      }
    * { unfold mtreeB. repeat split.
        - simpl. apply singlebranch_mtree_normal.
        - apply empty_mtree_normal.
        - left. apply mtree_hashroot_singlebranch_nonempty.
      }
    * unfold mtreeH. tauto.
    * { unfold mtreeB. repeat split.
        - apply IH.
        - apply empty_mtree_normal.
        - left. apply ctree_mtree_hashroot_nonempty.
      }
    * { unfold mtreeB. repeat split.
        - apply empty_mtree_normal.
        - apply IH.
        - right. apply ctree_mtree_hashroot_nonempty.
      }
    * { unfold mtreeB. repeat split.
        - apply IH.
        - apply IH.
        - left. apply ctree_mtree_hashroot_nonempty.
      }
- simpl. destruct n as [|n].
  + simpl. tauto.
  + simpl. tauto.
Qed.

Definition octree_approx_fun_p {n} (T:option (ctree n)) (f:bitseq n -> list asset) : Prop :=
mtree_approx_fun_p (octree_mtree T) f.

(*** This is used to deconstruct an octree at level n+1 into
 either a hash (structure unknown) or two subtrees at level n.
 The subtrees may be generated on the fly since we may need to modify them.
***)
Definition octree_S_inv {n} (T:option (ctree (S n))) :
  sum hashval (prod (option (ctree n)) (option (ctree n))) :=
match T with
| Some (inl ((false,gamma), hl)) => inr (Some (ctreeL hl gamma),None)
| Some (inl ((true,gamma), hl)) => inr (None,Some (ctreeL hl gamma))
| Some (inr (inl h)) => inl h
| Some (inr (inr (inl Tl))) => inr (Some Tl, None)
| Some (inr (inr (inr (inl Tr)))) => inr (None, Some Tr)
| Some (inr (inr (inr (inr (Tl, Tr))))) => inr (Some Tl, Some Tr)
| None => inr (None,None)
end.

Definition onehlist_hlist (hl:option nehlist) : hlist :=
match hl with
| Some (inl h) => hlistH h
| Some (inr (a,hl)) => hlistC a hl
| None => hlistN
end.

Fixpoint tx_octree_trans_ {n:nat} : forall (inpl:list (bitseq n * hashval)%type) (outpl:list (bitseq n * asset)%type) (T:option (ctree n)), option (ctree n) :=
match n with
  | O => fun inpl outpl =>
           match inpl,outpl with
             | nil,nil => fun (hl:option (ctree 0)) => hl
             | _,_ => fun (hl:option (ctree 0)) =>
                        match hlist_new_assets (map (@snd (bitseq 0) asset) outpl) (remove_assets_hlist (onehlist_hlist hl) (map (@snd (bitseq 0) hashval) inpl)) with
                          | hlistN => None
                          | hlistH h' => Some(inl h')
                          | hlistC h' hl' => Some(inr (h',hl'))
                        end
           end
  | S n => fun inpl outpl =>
             match inpl,outpl with
               | nil,nil => fun (T:option (ctree (S n))) => T
               | _,_ => (*** In this case since we're modifying subtrees, generate them on the fly and call recursively at level n ***)
                 fun (T:option (ctree (S n))) =>
                   match octree_S_inv T with
                     | inl h => T (*** structure unknown, error, but just return T ***)
                     | inr (Tl,Tr) =>
                       match tx_octree_trans_ (strip_bitseq_false inpl) (strip_bitseq_false outpl) Tl,tx_octree_trans_ (strip_bitseq_true inpl) (strip_bitseq_true outpl) Tr with
                         | None,None => None
                         | Some Tl',None => Some(inr (inr (inl Tl')))
                         | None,Some Tr' => Some(inr (inr (inr (inl Tr'))))
                         | Some Tl',Some Tr' => Some(inr (inr (inr (inr (Tl',Tr')))))
                       end
                   end
             end
end.

Definition tx_octree_trans m (tx:Tx) (T:option (ctree 162)) : option (ctree 162) :=
  tx_octree_trans_ (tx_inputs tx) (add_vout m (hashtx tx) (tx_outputs tx) 0) T.

Fixpoint ctree_full_approx_addr {n} : ctree n -> bitseq n -> Prop :=
match n with
| O => fun (T:ctree 0) (alpha:bitseq 0) => nehlist_full_approx T
| S n => fun (T:ctree (S n)) (alpha:bitseq (S n)) =>
           match T with
             | inl (beta,hl) =>
               if bitseq_eq_dec beta alpha then
                 nehlist_full_approx hl
               else
                 True
             | inr (inl _) => False
             | inr (inr (inl Tl)) =>
               match alpha with
                 | (false,alphar) => ctree_full_approx_addr Tl alphar
                 | (true,alphar) => True
               end
             | inr (inr (inr (inl Tr))) =>
               match alpha with
                 | (false,alphar) => True
                 | (true,alphar) => ctree_full_approx_addr Tr alphar
               end
             | inr (inr (inr (inr (Tl,Tr)))) =>
               match alpha with
                 | (false,alphar) => ctree_full_approx_addr Tl alphar
                 | (true,alphar) => ctree_full_approx_addr Tr alphar
               end
           end
end.

Fixpoint ctree_supports_addr {n} : ctree n -> bitseq n -> Prop :=
match n with
| O => fun (T:ctree 0) (alpha:bitseq 0) => True
| S n => fun (T:ctree (S n)) (alpha:bitseq (S n)) =>
           match T with
             | inl (beta,hl) => True (*** To fail to support an address, there would need to be a summarizing hash between here and the address leaf. Since from here everything is either the leaf beta or an empty leaf, there are no such summarizing hashes. ***)
             | inr (inl _) => False
             | inr (inr (inl Tl)) =>
               match alpha with
                 | (false,alphar) => ctree_supports_addr Tl alphar
                 | (true,alphar) => True (*** since empty ***)
               end
             | inr (inr (inr (inl Tr))) =>
               match alpha with
                 | (false,alphar) => True (*** since empty ***)
                 | (true,alphar) => ctree_supports_addr Tr alphar
               end
             | inr (inr (inr (inr (Tl,Tr)))) =>
               match alpha with
                 | (false,alphar) => ctree_supports_addr Tl alphar
                 | (true,alphar) => ctree_supports_addr Tr alphar
               end
           end
end.

Fixpoint ctree_supports_asset (a:asset) {n} : ctree n -> bitseq n -> Prop :=
match n with
| O => fun (hl:ctree 0) (alpha:bitseq 0) => In_hlist a (nehlist_hlist hl)
| S n => fun (T:ctree (S n)) (alpha:bitseq (S n)) =>
           match T with
             | inl (beta,hl) => if bitseq_eq_dec beta alpha then
                                  In_hlist a (nehlist_hlist hl)
                                else
                                  False
             | inr (inl _) => False
             | inr (inr (inl Tl)) =>
               match alpha with
                 | (false,alphar) => ctree_supports_asset a Tl alphar
                 | (true,alphar) => False
               end
             | inr (inr (inr (inl Tr))) =>
               match alpha with
                 | (false,alphar) => False
                 | (true,alphar) => ctree_supports_asset a Tr alphar
               end
             | inr (inr (inr (inr (Tl,Tr)))) =>
               match alpha with
                 | (false,alphar) => ctree_supports_asset a Tl alphar
                 | (true,alphar) => ctree_supports_asset a Tr alphar
               end
           end
end.
                   
Inductive ctree_asset_value_in T : list addr_assetid -> nat -> Prop :=
| ctree_asset_value_in_nil : ctree_asset_value_in T nil 0
| ctree_asset_value_in_cons h a u inpl alpha v :
    ctree_asset_value_in T inpl v ->
    ctree_supports_asset a T alpha ->
    asset_value a = Some u ->
    h = assetid a ->
    ctree_asset_value_in T ((alpha,h)::inpl) (u+v)
| ctree_asset_value_in_skip h a inpl alpha v :
    ctree_asset_value_in T inpl v ->
    ctree_supports_asset a T alpha ->
    asset_value a = None ->
    h = assetid a ->
    ctree_asset_value_in T ((alpha,h)::inpl) v
.

Lemma ctree_asset_value_in_app T inpl1 inpl2 utot1 utot2 :
  ctree_asset_value_in T inpl1 utot1 ->
  ctree_asset_value_in T inpl2 utot2 ->
  ctree_asset_value_in T (inpl1 ++ inpl2) (utot1 + utot2).
intros H. induction H as [|h a u inpr1 alpha v H1 IH H2 H3 H4|h a inpr1 alpha v H1 IH H2 H3 H4].
- intros H1. exact H1.
- intros H5.
  assert (L1: u + v + utot2 = u + (v + utot2)) by omega.
  rewrite L1.
  change (ctree_asset_value_in T ((alpha, h) :: (inpr1 ++ inpl2))
                                  (u + (v + utot2))).
  apply ctree_asset_value_in_cons with (a := a).
  + now apply IH.
  + assumption.
  + assumption.
  + assumption.
- intros H5.
  change (ctree_asset_value_in T ((alpha, h) :: (inpr1 ++ inpl2))
                                  (v + utot2)).
  apply ctree_asset_value_in_skip with (a := a).
  + now apply IH.
  + assumption.
  + assumption.
  + assumption.
Qed.

(*** Precondition for checking if tx is a valid tx. ***)
Definition ctree_can_support_tx (tx:Tx) (T : ctree 162) : Prop :=
(forall alpha h, In (alpha,h) (tx_inputs tx) -> exists u, ctree_supports_asset (h,u) T alpha)
/\
(forall alpha u, In (alpha,u) (tx_outputs tx) -> ctree_supports_addr T alpha)
/\
(forall alpha obl b n beta, In (alpha,(obl,rights b n beta)) (tx_outputs tx) -> ctree_full_approx_addr T (termaddr_addr beta))
/\
(forall alpha b, In alpha (output_uses b (tx_outputs tx)) -> ctree_full_approx_addr T (termaddr_addr alpha))
/\
(forall k1 k2 b, In (k1,k2) (output_creates b (tx_outputs tx)) -> ctree_full_approx_addr T (hashval_term_addr k1))
/\
(forall alpha obl b beta r, In (termaddr_addr alpha,(obl,owns b beta r)) (tx_outputs tx) -> ctree_full_approx_addr T (termaddr_addr alpha))
/\
(forall obl gamma nonce th d alpha h,
   In (alpha,(obl,signapublication gamma nonce th d)) (tx_outputs tx) ->
   In h (signaspec_stp_markers d) \/ In h (signaspec_known_markers th d) ->
   exists k bday obl', ctree_supports_asset (k,(bday,(obl',marker))) T (hashval_term_addr h))
/\
(forall obl gamma nonce th d alpha h,
   In (alpha,(obl,docpublication gamma nonce th d)) (tx_outputs tx) ->
   In h (doc_stp_markers d) \/ In h (doc_known_markers th d) ->
   exists k bday obl', ctree_supports_asset (k,(bday,(obl',marker))) T (hashval_term_addr h))
.

Inductive ctree_rights_consumed (b:bool) (alpha:termaddr) (T:ctree 162) : list addr_assetid -> nat -> Prop :=
| ctree_rights_consumed_nil : ctree_rights_consumed b alpha T nil 0
| ctree_rights_consumed_cons beta h inpr r1 bday obl r2:
    ctree_rights_consumed b alpha T inpr r1 ->
    ctree_supports_asset (h,(bday,(obl,rights b r2 alpha))) T beta ->
    ctree_rights_consumed b alpha T ((beta,h)::inpr) (r1 + r2)
| ctree_rights_consumed_skip beta h inpr r1 bday obl u:
    ctree_rights_consumed b alpha T inpr r1 ->
    ctree_supports_asset (h,(bday,(obl,u))) T beta ->
    (~exists r2, u = rights b r2 alpha) ->
    ctree_rights_consumed b alpha T ((beta,h)::inpr) r1
.

Lemma ctree_rights_consumed_app b alpha T inpl1 inpl2 r1 r2 :
  ctree_rights_consumed b alpha T inpl1 r1 ->
  ctree_rights_consumed b alpha T inpl2 r2 ->
  ctree_rights_consumed b alpha T (inpl1 ++ inpl2) (r1 + r2).
intros H1 H2. induction H1 as [|beta h inpr r11 bday obl r12 H11 IH H12|beta h inpr r11 bday obl u H11 IH H12 H13].
- exact H2.
- revert IH H12.
  assert (L1: r11 + r12 + r2 = (r11 + r2) + r12) by omega.
  rewrite L1. apply ctree_rights_consumed_cons.
- revert IH H12 H13. apply ctree_rights_consumed_skip.
Qed.

Definition ctree_rights_balanced (T:ctree 162) (alpha:termaddr) (b:bool) (inpl:list addr_assetid) (outpl:list addr_preasset) : Prop :=
   (forall (rtot1 rtot2 : nat) (h : hashval) (bday:nat) (obl : obligation) 
      (beta : payaddr) (u : nat),
    count_rights_used (output_uses b outpl) alpha = rtot1 ->
    ctree_supports_asset (h, (bday,(obl, owns b beta (Some u)))) T (termaddr_addr alpha) ->
    rights_out b outpl alpha = rtot2 ->
    exists rtot3 rtot4 : nat,
      ctree_rights_consumed b alpha T inpl rtot3 /\
      rtot4 * u <= units_sent_to_addr (payaddr_addr beta) outpl /\
      rtot1 + rtot2 = rtot3 + rtot4).

(*** A marker at the term address for #(#_{th}trm,#a) means trm has type a in theory with hash th. ***)
Definition ctree_lookup_stp (T:ctree 162) (h:hashval) (a:stp) : Prop :=
  exists k bday obl,
    ctree_supports_asset (k,(bday,(obl,marker))) T (hashval_term_addr (hashpair h (hashstp a))).

(*** A marker at the term address for #_{th}trm means trm has been proven in theory with hash th. ***)
Definition ctree_lookup_known (T:ctree 162) (h:hashval) : Prop :=
  exists k bday obl,
    ctree_supports_asset (k,(bday,(obl,marker))) T (hashval_term_addr h).

Definition ctree_supports_tx (tht:option (ttree 160)) (sigt:option (stree 160)) (blkheight:nat) (tx:Tx) (T : ctree 162) fee rew : Prop :=
(forall alpha u, In (alpha,u) (tx_outputs tx) -> ctree_supports_addr T alpha)
/\
(exists utot:nat,
ctree_asset_value_in T (tx_inputs tx) utot
/\
asset_value_out (tx_outputs tx) + fee + out_burncost (tx_outputs tx) = utot + rew)
/\
(*** if rights are mentioned (i.e., being output and/or used), then they must be transfered or purchased from the owner (who creates them) ***)
((forall alpha b,
   (*** these are the rights being used up to publish documents that use alpha in this transaction ***)
    rights_mentioned alpha b (tx_outputs tx) ->
    (ctree_full_approx_addr T (termaddr_addr alpha)) (*** need all assets to be visible here ***)
    /\
    (*** it's not owned by someone blocking its use and... ***)
    ((~exists h' bday' obl' beta', ctree_supports_asset (h',(bday',(obl',owns b beta' None))) T (termaddr_addr alpha))
     /\
     ctree_rights_balanced T alpha b (tx_inputs tx) (tx_outputs tx)))
 /\
 (*** and if some rights are in the input, then the rights must be mentioned in the output ***)
 (forall alpha b beta h bday obl n,
    In (beta,h) (tx_inputs tx) ->
    ctree_supports_asset (h,(bday,(obl,rights b n alpha))) T beta ->
    rights_mentioned alpha b (tx_outputs tx)))
/\
(*** publications were declared in advance by a currently usable intention ***)
((forall obl gamma nonce d alpha,
    In (alpha,(obl,theorypublication gamma nonce d)) (tx_outputs tx) ->
    check_theoryspec_p d
    /\
    exists beta h bday obl,
      beta = hashval_publication_addr (hashpair (hashaddr (payaddr_addr gamma)) (hashpair (hashnat nonce) (hashtheoryspec d)))
      /\
      In (beta,h) (tx_inputs tx)
      /\
      bday + intention_minage <= blkheight
      /\
      ctree_supports_asset (h,(bday,(obl,marker))) T beta)
 /\
 (forall obl gamma nonce th d alpha,
    In (alpha,(obl,signapublication gamma nonce th d)) (tx_outputs tx) ->
    check_signaspec_p (ctree_lookup_stp T) (ctree_lookup_known T) tht sigt th d
    /\
    exists beta h bday obl,
      beta = hashval_publication_addr (hashpair (hashaddr (payaddr_addr gamma)) (hashpair (hashnat nonce) (hashopair2 th (hashsignaspec d))))
      /\
      In (beta,h) (tx_inputs tx)
      /\
      bday + intention_minage <= blkheight
      /\
      ctree_supports_asset (h,(bday,(obl,marker))) T beta)
 /\
 (forall obl gamma nonce th d alpha,
    In (alpha,(obl,docpublication gamma nonce th d)) (tx_outputs tx) ->
    check_doc_p (ctree_lookup_stp T) (ctree_lookup_known T) tht sigt th d
    /\
    exists beta h bday obl,
      beta = hashval_publication_addr (hashpair (hashaddr (payaddr_addr gamma)) (hashpair (hashnat nonce) (hashopair2 th (hashdoc d))))
      /\
      In (beta,h) (tx_inputs tx)
      /\
      bday + intention_minage <= blkheight
      /\
      ctree_supports_asset (h,(bday,(obl,marker))) T beta))
/\
(*** newly claimed ownership must be new and must be supported by a document in the tx ***)
(forall alpha b obl beta r,
    In (termaddr_addr alpha,(obl,owns b beta r)) (tx_outputs tx) ->
    ctree_full_approx_addr T (termaddr_addr alpha) (*** need to view the whole asset list to ensure no current owner of obj ***)
    /\
    ((exists h beta' bday' obl' r', ctree_supports_asset (h,(bday',(obl',owns b beta' r'))) T (termaddr_addr alpha)
                              /\ In (termaddr_addr alpha,h) (tx_inputs tx))
     \/
     ((~exists h beta' bday' obl' r', ctree_supports_asset (h,(bday',(obl',owns b beta' r'))) T (termaddr_addr alpha))
      /\
      exists k1 k2,
        In (k1,k2) (output_creates b (tx_outputs tx))
        /\
        alpha = hashval_termaddr k1)))
/\
(*** new objects and props must be given ownership by the tx publishing the document ***)
(forall k1 k2 b,
   In (k1,k2) (output_creates b (tx_outputs tx)) ->
   ctree_full_approx_addr T (hashval_term_addr k1) (*** need to view the whole asset list to ensure no current owner of prop ***)
   /\
   (~(exists h' beta' bday' obl' r', ctree_supports_asset (h',(bday',(obl',owns b beta' r'))) T (hashval_term_addr k1)) ->
    (exists beta obl r, In (hashval_term_addr k1,(obl,owns b beta r)) (tx_outputs tx))
    /\
    (if b then
     (exists obl2 obl3,
        In (hashval_term_addr (hashpair k1 k2),(obl2,marker)) (tx_outputs tx) (*** record the prop with this proof ***)
        /\
        In (hashval_term_addr k1,(obl3,marker)) (tx_outputs tx)) (*** record that the prop is provable ***)
     else
       exists obl2,
         In (hashval_term_addr (hashpair k1 k2),(obl2,marker)) (tx_outputs tx)))) (*** record that the trm has the tp ***)
/\
(*** 
 Bounties can be collected by the owners of props.
 The idea is that the input and output must include
 the ownership of alpha as a prop. So (assuming the obl' is reasonable)
 the owner of alpha as a prop must sign the tx.
 I don't allow ownership to change in such transactions for
 simplicity, but ownership can change in transactions that don't
 collect bounties.
***)
(forall alpha h bday obl u,
   In (alpha,h) (tx_inputs tx) ->
   ctree_supports_asset (h,(bday,(obl,bounty u))) T alpha ->
   ctree_full_approx_addr T alpha
   /\
   exists h' bday' obl' beta r,
     In (alpha,h') (tx_inputs tx)
     /\
     ctree_supports_asset (h',(bday',(obl',owns true beta r))) T alpha
     /\
     In (alpha,(obl',owns true beta r)) (tx_outputs tx))
.

Definition octree_supports_tx tht sigt m (tx:Tx) (T : option (ctree 162)) fee rew : Prop :=
  match T with
    | None => False (*** We could say the empty tree supports an empty tx, but there seems to be no good reason for this. ***)
    | Some T => ctree_supports_tx tht sigt m tx T fee rew
  end.

Lemma ctree_supports_asset_S_inv_L (a:asset) {n} :
  forall T:ctree (S n),
  forall Tl:ctree n, forall Tr:option (ctree n),
    forall alpha,
    octree_S_inv (Some T) = inr (Some Tl, Tr) ->
    ctree_supports_asset a T (false, alpha) ->
    ctree_supports_asset a Tl alpha.
intros [[[[|] alpha] h]|[h|[Tl'|[Tr'|[Tl' Tr']]]]]; try (simpl; discriminate).
- intros Tl [Tr|] beta H1 H2; simpl in H1.
  + inversion H1.
  + inversion H1. unfold ctree_supports_asset in H2.
    change (if @bitseq_eq_dec (S n) (false,alpha) (false,beta) then In_hlist a (nehlist_hlist h) else False)
      in H2.
    destruct (@bitseq_eq_dec (S n) (false,alpha) (false,beta)) as [D1|D1].
    * { destruct n as [|n].
        - simpl. tauto.
        - change (if bitseq_eq_dec alpha beta then In_hlist a (nehlist_hlist h) else False).
          destruct (bitseq_eq_dec alpha beta) as [D2|D2].
          + tauto.
          + inversion D1. contradiction.
      }
    * contradiction H2.
- intros Tl [Tr|] beta H1 H2; simpl in H1.
  + inversion H1.
  + inversion H1. simpl in H2. congruence.
- intros Tl [Tr|] beta H1 H2; simpl in H1.
  + inversion H1. simpl in H2. congruence.
  + inversion H1.
Qed.

Lemma ctree_supports_asset_S_inv_R (a:asset) {n} :
  forall T:ctree (S n),
  forall Tl:option (ctree n), forall Tr:ctree n,
    forall alpha,
    octree_S_inv (Some T) = inr (Tl, Some Tr) ->
    ctree_supports_asset a T (true, alpha) ->
    ctree_supports_asset a Tr alpha.
intros [[[[|] alpha] h]|[h|[Tl'|[Tr'|[Tl' Tr']]]]]; try (simpl; discriminate).
- intros [Tl|] Tr beta H1 H2; simpl in H1.
  + inversion H1.
  + inversion H1. unfold ctree_supports_asset in H2.
    change (if @bitseq_eq_dec (S n) (true,alpha) (true,beta) then In_hlist a (nehlist_hlist h) else False)
      in H2.
    destruct (@bitseq_eq_dec (S n) (true,alpha) (true,beta)) as [D1|D1].
    * { destruct n as [|n].
        - simpl. tauto.
        - change (if bitseq_eq_dec alpha beta then In_hlist a (nehlist_hlist h) else False).
          destruct (bitseq_eq_dec alpha beta) as [D2|D2].
          + tauto.
          + inversion D1. contradiction.
      }
    * contradiction H2.
- intros [Tl|] Tr beta H1 H2; simpl in H1.
  + inversion H1.
  + inversion H1. simpl in H2. congruence.
- intros [Tl|] Tr beta H1 H2; simpl in H1.
  + inversion H1. simpl in H2. congruence.
  + inversion H1.
Qed.

Definition ctree_valid (T:ctree 162) : Prop := mtree_valid (ctree_mtree T).

Opaque ctree_supports_asset.

Lemma ctree_check_signaspec_r_marker sigt T th thy d h :
  In h (signaspec_stp_markers d) \/ In h (signaspec_known_markers th d) ->
  check_signaspec_r (ctree_lookup_stp T) (ctree_lookup_known T) sigt th thy d ->
  exists (k : hashval) (bday : nat) (obl : obligation),
    ctree_supports_asset (k, (bday, (obl, marker))) T (hashval_term_addr h).
intros H1 H2. induction d as [|[h'|h' a|m a|p] dr IH].
- destruct H1 as [[]|[]].
- simpl in H1. simpl in H2. destruct sigt as [sigt|].
  + destruct (signa_lookup (hashval_bit160 h') sigt) as [sth [y z]] eqn:E1.
    apply IH.
    * exact H1.
    * destruct H2 as [H2 _]. exact H2.
  + contradiction H2.
- destruct H2 as [H3 [k [bday [obl H4]]]].
  simpl in H1. destruct H1 as [[H1|H1]|H1].
  + exists k. exists bday. exists obl. subst h. exact H4.
  + apply IH.
    * left. exact H1.
    * exact H3.
  + apply IH.
    * right. exact H1.
    * exact H3.
- destruct H2 as [H3 H4]. apply IH.
  + exact H1.
  + exact H3.
- destruct H2 as [H3 [k [bday [obl H4]]]].
  simpl in H1. destruct H1 as [H1|[H1|H1]].
  + apply IH.
    * left. exact H1.
    * exact H3.
  + exists k. exists bday. exists obl. subst h. exact H4.
  + apply IH.
    * right. exact H1.
    * exact H3.
Qed.

Lemma ctree_check_signaspec_p_marker tht sigt T th d h :
  In h (signaspec_stp_markers d) \/ In h (signaspec_known_markers th d) ->
  check_signaspec_p (ctree_lookup_stp T) (ctree_lookup_known T) tht sigt th d ->
  exists (k : hashval) (bday : nat) (obl' : obligation),
    ctree_supports_asset (k, (bday, (obl', marker))) T (hashval_term_addr h).
unfold check_signaspec_p. destruct th as [th|].
- destruct tht as [tht|].
  + apply ctree_check_signaspec_r_marker.
  + tauto.
- apply ctree_check_signaspec_r_marker.
Qed.

Lemma ctree_check_doc_r_marker sigt T th thy d h :
  In h (doc_stp_markers d) \/ In h (doc_known_markers th d) ->
  check_doc_r (ctree_lookup_stp T) (ctree_lookup_known T) sigt th thy d ->
  exists (k : hashval) (bday : nat) (obl : obligation),
    ctree_supports_asset (k, (bday, (obl, marker))) T (hashval_term_addr h).
intros H1 H2. induction d as [|[h'|h' a|m a|p|p d] dr IH].
- destruct H1 as [[]|[]].
- simpl in H1. simpl in H2. destruct sigt as [sigt|].
  + destruct (signa_lookup (hashval_bit160 h') sigt) as [sth [y z]] eqn:E1.
    apply IH.
    * exact H1.
    * destruct H2 as [H2 _]. exact H2.
  + contradiction H2.
- destruct H2 as [H3 [k [bday [obl H4]]]].
  simpl in H1. destruct H1 as [[H1|H1]|H1].
  + exists k. exists bday. exists obl. subst h. exact H4.
  + apply IH.
    * left. exact H1.
    * exact H3.
  + apply IH.
    * right. exact H1.
    * exact H3.
- destruct H2 as [H3 H4]. apply IH.
  + exact H1.
  + exact H3.
- destruct H2 as [H3 [k [bday [obl H4]]]].
  simpl in H1. destruct H1 as [H1|[H1|H1]].
  + apply IH.
    * left. exact H1.
    * exact H3.
  + exists k. exists bday. exists obl. subst h. exact H4.
  + apply IH.
    * right. exact H1.
    * exact H3.
- destruct H2 as [H3 H4]. apply IH.
  + exact H1.
  + exact H3.
Qed.

Lemma ctree_check_doc_p_marker tht sigt T th d h :
  In h (doc_stp_markers d) \/ In h (doc_known_markers th d) ->
  check_doc_p (ctree_lookup_stp T) (ctree_lookup_known T) tht sigt th d ->
  exists (k : hashval) (bday : nat) (obl' : obligation),
    ctree_supports_asset (k, (bday, (obl', marker))) T (hashval_term_addr h).
unfold check_doc_p. destruct th as [th|].
- destruct tht as [tht|].
  + apply ctree_check_doc_r_marker.
  + tauto.
- apply ctree_check_doc_r_marker.
Qed.

Theorem ctree_supports_tx_can_support tht sigt m tx (T:ctree 162) fee rew :
  ctree_supports_tx tht sigt m tx T fee rew ->
  ctree_can_support_tx tx T.
intros [Hs1 [[utot [Hs2 Hs3]] [[Hs4a Hs4b] [[Hs5a [Hs5b Hs5c]] [Hs6 [Hs7 Hs8]]]]]]. repeat split.
- destruct tx as [inpl outpl]. 
  clear Hs1 rew Hs3 Hs4a Hs4b Hs5a Hs5b Hs5c Hs6 Hs7 Hs8.
  change (ctree_asset_value_in T inpl utot) in Hs2.
  change (forall (alpha : addr) (h : hashval),
            In (alpha, h) inpl ->
            exists oblu, ctree_supports_asset (h, oblu) T alpha).
  induction Hs2 as [|h a u inpl alpha v H1 IH H2 H3 H4|h a inpl alpha v H1 IH H2 H3 H4].
  + intros alpha h [].
  + intros beta k [H5|H5].
    * inversion H5. subst beta. subst k. subst h. exists (assetbday a,(assetobl a,assetpre a)).
      destruct a as [h [bday [obl w]]]. exact H2.
    * apply IH. exact H5.
  + intros beta k [H5|H5].
    * inversion H5. subst beta. subst k. subst h. exists (assetbday a,(assetobl a,assetpre a)).
      destruct a as [h [bday [obl w]]]; exact H2.
    * apply IH. exact H5.
- exact Hs1.
- intros alpha obl b n beta H1.
  assert (L1: In beta (output_uses b (tx_outputs tx)) \/
              (exists (alpha : addr) (obl : obligation) (n : nat),
                 In (alpha, (obl, rights b n beta)) (tx_outputs tx))).
  { right. exists alpha. exists obl. exists n. exact H1. }
  destruct (Hs4a beta b L1) as [H2 _].
  exact H2.
- intros alpha b H1.
  assert (L1: rights_mentioned alpha b (tx_outputs tx)).
  { left. exact H1. }
  destruct (Hs4a alpha b L1) as [H2 _].
  exact H2.
- intros k1 k2 b H1. destruct (Hs7 k1 k2 b H1) as [H2 _]. exact H2.
- intros alpha obl b beta r H1. destruct (Hs6 alpha b obl beta r H1) as [H2 _]. exact H2.
- intros obl gamma nonce th d alpha h H1 H2.
  destruct (Hs5b obl gamma nonce th d alpha H1) as [H3 _].
  revert H2 H3. apply ctree_check_signaspec_p_marker.
- intros obl gamma nonce th d alpha h H1 H2.
  destruct (Hs5c obl gamma nonce th d alpha H1) as [H3 _].
  revert H2 H3. apply ctree_check_doc_p_marker.
Qed.

Lemma empty_mtree_trans {n:nat} :
  empty_mtree n = tx_mtree_trans_ nil nil (empty_mtree n).
destruct n as [|n].
- simpl. reflexivity.
- simpl. reflexivity.
Qed.

Lemma tx_octree_trans_outpl_nonempty {n} (gamma:bitseq n) (v:asset) outpl :
  tx_octree_trans_ nil ((gamma,v)::outpl) None <> None.
induction n as [|n IH].
- simpl. discriminate.
- destruct gamma as [[|] gamma].
  + simpl. destruct (tx_octree_trans_ nil (strip_bitseq_false outpl) None) as [Tl'|].
    * { (*** Coq needs some serious help via change here, or the next destruct has no effect. ***)
        change ((fun x : option (ctree n) =>
                  match x return option (ctree (S n)) with
                    | Some Tr'0 => Some (inr (inr (inr (inr (Tl', Tr'0)))))
                    | None => Some (inr (inr (inl Tl')))
                  end <> None)
               (tx_octree_trans_ nil ((gamma, v) :: strip_bitseq_true outpl) None)).
        destruct (tx_octree_trans_ nil ((gamma, v) :: strip_bitseq_true outpl) None) as [Tr'|].
        - discriminate.
        - discriminate.
      }
    * { (*** Again, Coq needs this change before the destruct to work properly. ***)
        change ((fun x : option (ctree n) =>
                  match x return option (ctree (S n)) with
                    | Some Tr' => Some (inr (inr (inr (inl Tr'))))
                    | None => None
                  end <> None)
                  (tx_octree_trans_ nil ((gamma, v) :: strip_bitseq_true outpl) None)).
        destruct (tx_octree_trans_ nil ((gamma, v) :: strip_bitseq_true outpl) None) as [Tr'|] eqn: H1.
        - discriminate.
        - exfalso. revert H1. apply IH.
      }
  + simpl. (*** In this case, Coq needs the change before this destruct. ***)
    change ((fun x : option (ctree n) =>
               match x return option (ctree (S n)) with
                 | Some Tl' =>
                   match tx_octree_trans_ nil (strip_bitseq_true outpl) None with
                     | Some Tr' => Some (inr (inr (inr (inr (Tl', Tr')))))
                     | None => Some (inr (inr (inl Tl')))
                   end
                 | None =>
                   match tx_octree_trans_ nil (strip_bitseq_true outpl) None with
                     | Some Tr' => Some (inr (inr (inr (inl Tr'))))
                     | None => None
                   end
               end <> None)
              (tx_octree_trans_ nil ((gamma, v) :: strip_bitseq_false outpl) None)).
    destruct (tx_octree_trans_ nil ((gamma,v) ::(strip_bitseq_false outpl)) None) as [Tl'|] eqn: H1.
    * { destruct (tx_octree_trans_ nil (strip_bitseq_true outpl) None) as [Tr'|].
        - discriminate.
        - discriminate.
      }
    * { destruct (tx_octree_trans_ nil (strip_bitseq_true outpl) None) as [Tr'|].
        - discriminate.
        - exfalso. revert H1. apply IH.
      }
Qed.

Lemma tx_trans_mtree_emptyctree_eq {n:nat} :
  forall outpl,
    octree_mtree
      (tx_octree_trans_ nil outpl None) =
    tx_mtree_trans_ nil outpl (empty_mtree n).
induction n as [|n IH].
- intros [|[k v] outpr].
  + simpl. reflexivity.
  + simpl. reflexivity.
- intros [|[gamma v] outpr].
  + simpl. reflexivity.
  + set (outpl := ((gamma, v) :: outpr)).
    change (@octree_mtree (S n) (match tx_octree_trans_ nil (strip_bitseq_false outpl) None,tx_octree_trans_ nil (strip_bitseq_true outpl) None with
                         | None,None => None
                         | Some Tl',None => Some(inr (inr (inl Tl')))
                         | None,Some Tr' => Some(inr (inr (inr (inl Tr'))))
                         | Some Tl',Some Tr' => Some(inr (inr (inr (inr (Tl',Tr')))))
                       end) =
            mtreeB (tx_mtree_trans_ nil (strip_bitseq_false outpl) (empty_mtree n))
                   (tx_mtree_trans_ nil (strip_bitseq_true outpl) (empty_mtree n))).
    generalize (IH (strip_bitseq_false outpl)).
    generalize (IH (strip_bitseq_true outpl)).
    destruct (tx_octree_trans_ nil (strip_bitseq_false outpl) None) as [Tl'|] eqn: ETl'.
    * { destruct (tx_octree_trans_ nil (strip_bitseq_true outpl) None) as [Tr'|] eqn: ETr'.
        - intros H1 H2.
          change (mtreeB (ctree_mtree Tl') (ctree_mtree Tr') =
                  mtreeB (tx_mtree_trans_ nil (strip_bitseq_false outpl) (empty_mtree n))
                                          (tx_mtree_trans_ nil (strip_bitseq_true outpl) (empty_mtree n))).
          f_equal.
          + exact H2.
          + exact H1.
        - intros H1 H2.
          change (mtreeB (ctree_mtree Tl') (empty_mtree n) =
                  mtreeB (tx_mtree_trans_ nil (strip_bitseq_false outpl) (empty_mtree n))
                         (tx_mtree_trans_ nil (strip_bitseq_true outpl) (empty_mtree n))).
          f_equal.
          + exact H2.
          + exact H1.
      }
    * { destruct (tx_octree_trans_ nil (strip_bitseq_true outpl) None) as [Tr'|] eqn: ETr'.
        - intros H1 H2.
          change (mtreeB (empty_mtree n) (ctree_mtree Tr') =
                  mtreeB (tx_mtree_trans_ nil (strip_bitseq_false outpl) (empty_mtree n))
                                          (tx_mtree_trans_ nil (strip_bitseq_true outpl) (empty_mtree n))).
          f_equal.
          + exact H2.
          + exact H1.
        - intros H1 H2. exfalso. (*** This case is impossible since outpl is nonempty and so it must have been put into either the left or right. ***)
          destruct gamma as [[|] gamma].
          + unfold outpl in ETr'. revert ETr'. apply tx_octree_trans_outpl_nonempty.
          + unfold outpl in ETl'. revert ETl'. apply tx_octree_trans_outpl_nonempty.
      }
Qed.

Lemma tx_octree_trans_S_inv_lemNN {n} :
  forall inpl outpl,
  forall T:option (ctree (S n)),
  forall Tl Tr:option (ctree n),
    inpl <> nil \/ outpl <> nil ->
    octree_S_inv T = inr (Tl, Tr) ->
    tx_octree_trans_ (strip_bitseq_false inpl) (strip_bitseq_false outpl) Tl = None ->
    tx_octree_trans_ (strip_bitseq_true inpl) (strip_bitseq_true outpl) Tr = None ->
    tx_octree_trans_ inpl outpl T = None.
intros [|a inpl] [|b outpl] T Tl Tr H1 H2 H3 H4.
- exfalso. tauto.
- simpl. rewrite H2.
  change (match
             tx_octree_trans_ (strip_bitseq_false nil) (strip_bitseq_false (b :: outpl)) Tl
           with
             | Some Tl' =>
               match tx_octree_trans_ (strip_bitseq_true nil) (strip_bitseq_true (b :: outpl)) Tr
               with
                 | Some Tr' => Some (ctreeB Tl' Tr')
                 | None => Some (ctreeBL Tl')
               end
             | None =>
               match tx_octree_trans_ (strip_bitseq_true nil) (strip_bitseq_true (b :: outpl)) Tr
               with
                 | Some Tr' => Some (ctreeBR Tr')
                 | None => None
               end
           end
          = None).
  rewrite H3. rewrite H4.
  reflexivity.
- simpl. rewrite H2.
  change (match
             tx_octree_trans_ (strip_bitseq_false (a::inpl)) (strip_bitseq_false nil) Tl
           with
             | Some Tl' =>
               match tx_octree_trans_ (strip_bitseq_true (a::inpl)) (strip_bitseq_true nil) Tr
               with
                 | Some Tr' => Some (ctreeB Tl' Tr')
                 | None => Some (ctreeBL Tl')
               end
             | None =>
               match tx_octree_trans_ (strip_bitseq_true (a::inpl)) (strip_bitseq_true nil) Tr
               with
                 | Some Tr' => Some (ctreeBR Tr')
                 | None => None
               end
           end
          = None).
  rewrite H3. rewrite H4.
  reflexivity.
- simpl. rewrite H2.
  change (match
             tx_octree_trans_ (strip_bitseq_false (a::inpl)) (strip_bitseq_false (b :: outpl)) Tl
           with
             | Some Tl' =>
               match tx_octree_trans_ (strip_bitseq_true (a::inpl)) (strip_bitseq_true (b :: outpl)) Tr
               with
                 | Some Tr' => Some (ctreeB Tl' Tr')
                 | None => Some (ctreeBL Tl')
               end
             | None =>
               match tx_octree_trans_ (strip_bitseq_true (a::inpl)) (strip_bitseq_true (b :: outpl)) Tr
               with
                 | Some Tr' => Some (ctreeBR Tr')
                 | None => None
               end
           end
          = None).
  rewrite H3. rewrite H4.
  reflexivity.
Qed.

Lemma tx_octree_trans_S_inv_lemSN {n} :
  forall inpl outpl,
  forall T:option (ctree (S n)),
  forall Tl Tr:option (ctree n), forall Tl':ctree n,
    inpl <> nil \/ outpl <> nil ->
    octree_S_inv T = inr (Tl, Tr) ->
    tx_octree_trans_ (strip_bitseq_false inpl) (strip_bitseq_false outpl) Tl = Some Tl' ->
    tx_octree_trans_ (strip_bitseq_true inpl) (strip_bitseq_true outpl) Tr = None ->
    tx_octree_trans_ inpl outpl T = Some(ctreeBL Tl').
intros [|a inpl] [|b outpl] T Tl Tr Tl' H1 H2 H3 H4.
- exfalso. tauto.
- simpl. rewrite H2.
  change (match
             tx_octree_trans_ (strip_bitseq_false nil) (strip_bitseq_false (b :: outpl)) Tl
           with
             | Some Tl' =>
               match tx_octree_trans_ (strip_bitseq_true nil) (strip_bitseq_true (b :: outpl)) Tr
               with
                 | Some Tr' => Some (ctreeB Tl' Tr')
                 | None => Some (ctreeBL Tl')
               end
             | None =>
               match tx_octree_trans_ (strip_bitseq_true nil) (strip_bitseq_true (b :: outpl)) Tr
               with
                 | Some Tr' => Some (ctreeBR Tr')
                 | None => None
               end
           end
          = Some (ctreeBL Tl')).
  rewrite H3. rewrite H4.
  reflexivity.
- simpl. rewrite H2.
  change (match
             tx_octree_trans_ (strip_bitseq_false (a::inpl)) (strip_bitseq_false nil) Tl
           with
             | Some Tl' =>
               match tx_octree_trans_ (strip_bitseq_true (a::inpl)) (strip_bitseq_true nil) Tr
               with
                 | Some Tr' => Some (ctreeB Tl' Tr')
                 | None => Some (ctreeBL Tl')
               end
             | None =>
               match tx_octree_trans_ (strip_bitseq_true (a::inpl)) (strip_bitseq_true nil) Tr
               with
                 | Some Tr' => Some (ctreeBR Tr')
                 | None => None
               end
           end
          = Some (ctreeBL Tl')).
  rewrite H3. rewrite H4.
  reflexivity.
- simpl. rewrite H2.
  change (match
             tx_octree_trans_ (strip_bitseq_false (a::inpl)) (strip_bitseq_false (b :: outpl)) Tl
           with
             | Some Tl' =>
               match tx_octree_trans_ (strip_bitseq_true (a::inpl)) (strip_bitseq_true (b :: outpl)) Tr
               with
                 | Some Tr' => Some (ctreeB Tl' Tr')
                 | None => Some (ctreeBL Tl')
               end
             | None =>
               match tx_octree_trans_ (strip_bitseq_true (a::inpl)) (strip_bitseq_true (b :: outpl)) Tr
               with
                 | Some Tr' => Some (ctreeBR Tr')
                 | None => None
               end
           end
          = Some (ctreeBL Tl')).
  rewrite H3. rewrite H4.
  reflexivity.
Qed.

Lemma tx_octree_trans_S_inv_lemNS {n} :
  forall inpl outpl,
  forall T:option (ctree (S n)),
  forall Tl Tr:option (ctree n), forall Tr': ctree n,
    inpl <> nil \/ outpl <> nil ->
    octree_S_inv T = inr (Tl, Tr) ->
    tx_octree_trans_ (strip_bitseq_false inpl) (strip_bitseq_false outpl) Tl = None ->
    tx_octree_trans_ (strip_bitseq_true inpl) (strip_bitseq_true outpl) Tr = Some Tr' ->
    tx_octree_trans_ inpl outpl T = Some (ctreeBR Tr').
intros [|a inpl] [|b outpl] T Tl Tr Tr' H1 H2 H3 H4.
- exfalso. tauto.
- simpl. rewrite H2.
  change (match
             tx_octree_trans_ (strip_bitseq_false nil) (strip_bitseq_false (b :: outpl)) Tl
           with
             | Some Tl' =>
               match tx_octree_trans_ (strip_bitseq_true nil) (strip_bitseq_true (b :: outpl)) Tr
               with
                 | Some Tr' => Some (ctreeB Tl' Tr')
                 | None => Some (ctreeBL Tl')
               end
             | None =>
               match tx_octree_trans_ (strip_bitseq_true nil) (strip_bitseq_true (b :: outpl)) Tr
               with
                 | Some Tr' => Some (ctreeBR Tr')
                 | None => None
               end
           end
          = Some (ctreeBR Tr')).
  rewrite H3. rewrite H4.
  reflexivity.
- simpl. rewrite H2.
  change (match
             tx_octree_trans_ (strip_bitseq_false (a::inpl)) (strip_bitseq_false nil) Tl
           with
             | Some Tl' =>
               match tx_octree_trans_ (strip_bitseq_true (a::inpl)) (strip_bitseq_true nil) Tr
               with
                 | Some Tr' => Some (ctreeB Tl' Tr')
                 | None => Some (ctreeBL Tl')
               end
             | None =>
               match tx_octree_trans_ (strip_bitseq_true (a::inpl)) (strip_bitseq_true nil) Tr
               with
                 | Some Tr' => Some (ctreeBR Tr')
                 | None => None
               end
           end
          = Some (ctreeBR Tr')).
  rewrite H3. rewrite H4.
  reflexivity.
- simpl. rewrite H2.
  change (match
             tx_octree_trans_ (strip_bitseq_false (a::inpl)) (strip_bitseq_false (b :: outpl)) Tl
           with
             | Some Tl' =>
               match tx_octree_trans_ (strip_bitseq_true (a::inpl)) (strip_bitseq_true (b :: outpl)) Tr
               with
                 | Some Tr' => Some (ctreeB Tl' Tr')
                 | None => Some (ctreeBL Tl')
               end
             | None =>
               match tx_octree_trans_ (strip_bitseq_true (a::inpl)) (strip_bitseq_true (b :: outpl)) Tr
               with
                 | Some Tr' => Some (ctreeBR Tr')
                 | None => None
               end
           end
          = Some (ctreeBR Tr')).
  rewrite H3. rewrite H4.
  reflexivity.
Qed.

Lemma tx_octree_trans_S_inv_lemSS {n} :
  forall inpl outpl,
  forall T:option (ctree (S n)),
  forall Tl Tr:option (ctree n), forall Tl' Tr':ctree n,
    inpl <> nil \/ outpl <> nil ->
    octree_S_inv T = inr (Tl, Tr) ->
    tx_octree_trans_ (strip_bitseq_false inpl) (strip_bitseq_false outpl) Tl = Some Tl' ->
    tx_octree_trans_ (strip_bitseq_true inpl) (strip_bitseq_true outpl) Tr = Some Tr' ->
    tx_octree_trans_ inpl outpl T = Some(ctreeB Tl' Tr').
intros [|a inpl] [|b outpl] T Tl Tr Tl' Tr' H1 H2 H3 H4.
- exfalso. tauto.
- simpl. rewrite H2.
  change (match
             tx_octree_trans_ (strip_bitseq_false nil) (strip_bitseq_false (b :: outpl)) Tl
           with
             | Some Tl' =>
               match tx_octree_trans_ (strip_bitseq_true nil) (strip_bitseq_true (b :: outpl)) Tr
               with
                 | Some Tr' => Some (ctreeB Tl' Tr')
                 | None => Some (ctreeBL Tl')
               end
             | None =>
               match tx_octree_trans_ (strip_bitseq_true nil) (strip_bitseq_true (b :: outpl)) Tr
               with
                 | Some Tr' => Some (ctreeBR Tr')
                 | None => None
               end
           end
          = Some (ctreeB Tl' Tr')).
  rewrite H3. rewrite H4.
  reflexivity.
- simpl. rewrite H2.
  change (match
             tx_octree_trans_ (strip_bitseq_false (a::inpl)) (strip_bitseq_false nil) Tl
           with
             | Some Tl' =>
               match tx_octree_trans_ (strip_bitseq_true (a::inpl)) (strip_bitseq_true nil) Tr
               with
                 | Some Tr' => Some (ctreeB Tl' Tr')
                 | None => Some (ctreeBL Tl')
               end
             | None =>
               match tx_octree_trans_ (strip_bitseq_true (a::inpl)) (strip_bitseq_true nil) Tr
               with
                 | Some Tr' => Some (ctreeBR Tr')
                 | None => None
               end
           end
          = Some (ctreeB Tl' Tr')).
  rewrite H3. rewrite H4.
  reflexivity.
- simpl. rewrite H2.
  change (match
             tx_octree_trans_ (strip_bitseq_false (a::inpl)) (strip_bitseq_false (b :: outpl)) Tl
           with
             | Some Tl' =>
               match tx_octree_trans_ (strip_bitseq_true (a::inpl)) (strip_bitseq_true (b :: outpl)) Tr
               with
                 | Some Tr' => Some (ctreeB Tl' Tr')
                 | None => Some (ctreeBL Tl')
               end
             | None =>
               match tx_octree_trans_ (strip_bitseq_true (a::inpl)) (strip_bitseq_true (b :: outpl)) Tr
               with
                 | Some Tr' => Some (ctreeBR Tr')
                 | None => None
               end
           end
          = Some (ctreeB Tl' Tr')).
  rewrite H3. rewrite H4.
  reflexivity.
Qed.

Lemma tx_octree_trans_nochange_lem {n} :
  forall T:option (ctree n),
    tx_octree_trans_ nil nil T = T.
destruct n as [|n].
- intros T. simpl. reflexivity.
- intros T. simpl. reflexivity.
Qed.

Lemma octree_mtree_S_inv_SS {n} :
  forall T:option (ctree (S n)),
  forall Tl Tr:ctree n,
    octree_S_inv T = inr (Some(Tl), Some(Tr)) ->
    octree_mtree T = mtreeB (octree_mtree (Some Tl)) (octree_mtree (Some Tr)).
intros [[[[[|] alpha] h]|[h|[Tl'|[Tr'|[Tl' Tr']]]]]|] Tl Tr; try (simpl; discriminate).
simpl. intros H1. inversion H1. reflexivity.
Qed.

Lemma octree_mtree_S_inv_SN {n} :
  forall T:option (ctree (S n)),
  forall Tl:ctree n,
    octree_S_inv T = inr (Some(Tl),None) ->
    octree_mtree T = mtreeB (octree_mtree (Some Tl)) (empty_mtree n).
intros [[[[[|] alpha] h]|[h|[Tl'|[Tr'|[Tl' Tr']]]]]|] Tl; try (simpl; discriminate).
- simpl. intros H1. inversion H1. destruct n; simpl; reflexivity.
- simpl. intros H1. inversion H1. reflexivity.
Qed.

Lemma octree_mtree_S_inv_NS {n} :
  forall T:option (ctree (S n)),
  forall Tr:ctree n,
    octree_S_inv T = inr (None, Some(Tr)) ->
    octree_mtree T = mtreeB (empty_mtree n) (octree_mtree (Some Tr)).
intros [[[[[|] alpha] h]|[h|[Tl'|[Tr'|[Tl' Tr']]]]]|] Tr; try (simpl; discriminate).
- simpl. intros H1. inversion H1. destruct n; simpl; reflexivity.
- simpl. intros H1. inversion H1. reflexivity.
Qed.

Lemma octree_mtree_S_inv_NN {n} :
  forall T:option (ctree (S n)),
    octree_S_inv T = inr (None,None) ->
    octree_mtree T = empty_mtree (S n).
intros [[[[[|] alpha] h]|[h|[Tl'|[Tr'|[Tl' Tr']]]]]|]; try (simpl; discriminate).
simpl. intros _. reflexivity.
Qed.

Lemma ctree_supports_addr_S_inv_L {n} :
  forall T:ctree (S n),
  forall Tl:ctree n, forall Tr:option (ctree n),
    forall alpha,
    octree_S_inv (Some T) = inr (Some Tl, Tr) ->
    ctree_supports_addr T (false, alpha) ->
    ctree_supports_addr Tl alpha.
intros [[[[|] alpha] h]|[h|[Tl'|[Tr'|[Tl' Tr']]]]]; try (simpl; discriminate).
- intros Tl [Tr|] beta H1 H2; simpl in H1.
  + inversion H1.
  + inversion H1. destruct n; simpl; tauto.
- intros Tl [Tr|] beta H1 H2; simpl in H1.
  + inversion H1.
  + inversion H1. simpl in H2. congruence.
- intros Tl [Tr|] beta H1 H2; simpl in H1.
  + inversion H1. simpl in H2. congruence.
  + inversion H1.
Qed.

Lemma ctree_supports_addr_S_inv_R {n} :
  forall T:ctree (S n),
  forall Tl:option (ctree n), forall Tr:ctree n,
    forall alpha,
    octree_S_inv (Some T) = inr (Tl, Some Tr) ->
    ctree_supports_addr T (true, alpha) ->
    ctree_supports_addr Tr alpha.
intros [[[[|] alpha] h]|[h|[Tl'|[Tr'|[Tl' Tr']]]]]; try (simpl; discriminate).
- intros [Tl|] Tr beta H1 H2; simpl in H1.
  + inversion H1.
  + inversion H1. destruct n; simpl; tauto.
- intros [Tl|] Tr beta H1 H2; simpl in H1.
  + inversion H1.
  + inversion H1. simpl in H2. congruence.
- intros [Tl|] Tr beta H1 H2; simpl in H1.
  + inversion H1. simpl in H2. congruence.
  + inversion H1.
Qed.

Opaque equi.

Lemma tx_trans_mtree_ctree_eq_0 :
  forall inpl outpl,
  forall (alphapre:bitseq 0 -> addr),
    forall (T: ctree 0),
      (forall gamma delta, alphapre gamma = alphapre delta -> gamma = delta)
      ->
      equi (octree_mtree
              (tx_octree_trans_ inpl outpl (Some T)))
           (tx_mtree_trans_ inpl outpl
                            (octree_mtree (Some T))).
intros [|a inpl] [|b outpl] alphapre T Hapi.
- simpl. apply equi_ref.
- simpl. apply equi_ref.
- simpl. change (match T with
                     | inl h => hlistH h
                     | inr (a, hl) => hlistC a hl
                   end) with (nehlist_hlist T).
    destruct (remove_assets_hlist (nehlist_hlist T)
                                  (@cons hashval (@snd unit hashval a)
                                         (@map (prod unit hashval) hashval (@snd unit hashval) inpl)))
              as [h'| |h' hl'] eqn:He.
  + simpl. reflexivity.
  + simpl. reflexivity.
  + simpl. reflexivity.
- simpl. reflexivity.
Qed.

Opaque tx_octree_trans_.

(*** The interesting induction cases where either inpl or outpl is nonempty. ***)
Lemma tx_trans_mtree_ctree_eq_S {n:nat} m (fullinpl:list addr_assetid) (fulloutpl:list addr_preasset) (txh:hashval) :
  (forall (inpl : list (bitseq n * hashval))
         (outpl : list (bitseq n * asset)) (alphapre : bitseq n -> addr)
         (T : ctree n),
       (forall gamma delta : bitseq n,
        alphapre gamma = alphapre delta -> gamma = delta) ->
       inpl_reln alphapre fullinpl inpl ->
       outpl_reln m txh alphapre 0 fulloutpl outpl ->
       (forall (alpha : bitseq n) h,
        In (alpha, h) inpl -> exists u, ctree_supports_asset (h,u) T alpha) ->
       (forall (alpha : bitseq n) (u : asset),
        In (alpha, u) outpl -> ctree_supports_addr T alpha) ->
       equi
         (octree_mtree (tx_octree_trans_ inpl outpl (Some T)))
         (tx_mtree_trans_ inpl outpl (octree_mtree (Some T)))) ->
  forall (inpl : list (bitseq (S n) * hashval)) (outpl : list (bitseq (S n) * asset))
         (alphapre : bitseq (S n) -> addr)
         (T : ctree (S n)),
  (forall gamma delta : bitseq (S n),
     alphapre gamma = alphapre delta -> gamma = delta) ->
  inpl <> nil \/ outpl <> nil ->
  inpl_reln alphapre fullinpl inpl ->
  outpl_reln m txh alphapre 0 fulloutpl outpl ->
  (forall (alpha : bitseq (S n)) h,
     In (alpha, h) inpl -> exists u, ctree_supports_asset (h,u) T alpha) ->
  (forall (alpha : bitseq (S n)) (u : asset),
     In (alpha, u) outpl ->
     ctree_supports_addr T alpha) ->
  equi
    (octree_mtree
       (tx_octree_trans_ inpl outpl (Some T)))
    (tx_mtree_trans_ inpl outpl
                     (octree_mtree (Some T))).
intros IH inpl outpl alphapre T Hapi H0 H1 H2 H3 H4.
assert (L0: equi (octree_mtree (tx_octree_trans_ inpl outpl (Some T)))
                   (tx_mtree_trans_ inpl outpl (octree_mtree (Some T)))
              =
                   (equi (octree_mtree
                            (match octree_S_inv (Some T) with
                               | inl h => (Some T)
                               | inr (Tl,Tr) =>
                                 match tx_octree_trans_ (strip_bitseq_false inpl) (strip_bitseq_false outpl) Tl,tx_octree_trans_ (strip_bitseq_true inpl) (strip_bitseq_true outpl) Tr with
                                   | None,None => None
                                   | Some Tl',None => Some(inr (inr (inl Tl')))
                                   | None,Some Tr' => Some(inr (inr (inr (inl Tr'))))
                                   | Some Tl',Some Tr' => Some(inr (inr (inr (inr (Tl',Tr')))))
                                 end
                             end)
                         )
                         (tx_mtree_trans_ inpl outpl (octree_mtree (Some T))))).
{ destruct inpl as [|[gamma u] inpl]; destruct outpl as [|[delta v] outpl];
  try reflexivity.
  exfalso.
  destruct H0 as [H0|H0].
  - apply H0. reflexivity.
  - apply H0. reflexivity.
}
rewrite L0. clear L0.
destruct (octree_S_inv (Some T)) as [h|[[Tl|] [Tr|]]] eqn:H5.
- exfalso. destruct T as [[[[|] gamma] hl]|[h'|[Tl|[Tr|[Tl Tr]]]]]; try discriminate H5.
  destruct inpl as [|[gamma u] inpl].
  + destruct outpl as [|[delta v] outpl].
    * exfalso. destruct H0 as [H0|H0]; apply H0; reflexivity.
    * assert (L1: In (delta, v) ((delta, v) :: outpl)) by now left.
      apply H4 in L1. simpl in L1. contradiction L1.
  + assert (L1: In (gamma, u) ((gamma, u) :: inpl)) by now left.
    apply H3 in L1. simpl in L1. destruct L1 as [_ []].
- assert (L2: octree_mtree (Some T) = mtreeB (octree_mtree (Some Tl)) (octree_mtree (Some Tr))).
  { apply octree_mtree_S_inv_SS. exact H5. }
  rewrite L2.
  assert (L3: equi (octree_mtree
                      (tx_octree_trans_ (strip_bitseq_false inpl) (strip_bitseq_false outpl)
                                               (Some Tl)))
                   (tx_mtree_trans_ (strip_bitseq_false inpl) (strip_bitseq_false outpl)
                                    (ctree_mtree Tl))).
  { apply (IH (strip_bitseq_false inpl) (strip_bitseq_false outpl) (fun gamma => alphapre(false,gamma)) Tl).
    - intros gamma' delta' H8. apply Hapi in H8. injection H8. tauto.
    - now apply (inpl_reln_strip_bitseq_false alphapre fullinpl inpl Hapi).
    - now apply (outpl_reln_strip_bitseq_false m txh alphapre fulloutpl outpl Hapi 0).
    - intros alpha h H8.
      apply strip_bitseq_false_iff in H8.
      generalize (H3 (false,alpha) h H8).
      intros [u H9].
      exists u.
      now apply (ctree_supports_asset_S_inv_L (h,u) T Tl (Some Tr) alpha).
    - intros alpha a H8.
      apply strip_bitseq_false_iff in H8.
      generalize (H4 (false,alpha) a H8).
      now apply (ctree_supports_addr_S_inv_L T Tl (Some Tr) alpha).
  }
  assert (L4: equi (octree_mtree
                      (tx_octree_trans_ (strip_bitseq_true inpl) (strip_bitseq_true outpl)
                                               (Some Tr)))
                   (tx_mtree_trans_ (strip_bitseq_true inpl) (strip_bitseq_true outpl)
                                    (ctree_mtree Tr))).
  { apply (IH (strip_bitseq_true inpl) (strip_bitseq_true outpl) (fun gamma => alphapre(true,gamma)) Tr).
    - intros gamma' delta' H8. apply Hapi in H8. injection H8. tauto.
    - now apply (inpl_reln_strip_bitseq_true alphapre fullinpl inpl Hapi).
    - now apply (outpl_reln_strip_bitseq_true m txh alphapre fulloutpl outpl Hapi 0).
    - intros alpha h H8.
      apply strip_bitseq_true_iff in H8.
      generalize (H3 (true,alpha) h H8).
      intros [u H9]. exists u.
      now apply (ctree_supports_asset_S_inv_R (h,u) T (Some Tl) Tr alpha).
    - intros alpha a H8.
      apply strip_bitseq_true_iff in H8.
      generalize (H4 (true,alpha) a H8).
      now apply (ctree_supports_addr_S_inv_R T (Some Tl) Tr alpha).
  }
  assert (L5: (tx_mtree_trans_ inpl outpl
                               (mtreeB (octree_mtree (Some Tl)) (octree_mtree (Some Tr))))
              = (mtreeB (tx_mtree_trans_ (strip_bitseq_false inpl) (strip_bitseq_false outpl) (ctree_mtree Tl))
                        (tx_mtree_trans_ (strip_bitseq_true inpl) (strip_bitseq_true outpl) (ctree_mtree Tr)))).
  { destruct inpl as [|[gamma u] inpl].
    - destruct outpl as [|[delta v] outpl].
      + exfalso. destruct H0 as [H0|H0]; apply H0; reflexivity.
      + reflexivity.
    - reflexivity.
  }
  rewrite L5.
  apply (equi_rew_lem1 L3 L4).
  destruct (tx_octree_trans_ (strip_bitseq_false inpl) (strip_bitseq_false outpl) (Some Tl)) as [Tl'|] eqn:H6.
  + destruct (tx_octree_trans_ (strip_bitseq_true inpl) (strip_bitseq_true outpl) (Some Tr)) as [Tr'|] eqn:H7.
    * apply equi_ref.
    * apply equi_ref.
  + destruct (tx_octree_trans_ (strip_bitseq_true inpl) (strip_bitseq_true outpl) (Some Tr)) as [Tr'|] eqn:H7.
    * apply equi_ref.
    * apply equi_empty_lem. (*** this kind of case is why I need equi instead of = ***)
- assert (L2: octree_mtree (Some T) = mtreeB (octree_mtree (Some Tl)) (empty_mtree n)).
  { apply octree_mtree_S_inv_SN. exact H5. }
  rewrite L2.
  assert (L3: equi (octree_mtree
                      (tx_octree_trans_ (strip_bitseq_false inpl) (strip_bitseq_false outpl)
                                               (Some Tl)))
                   (tx_mtree_trans_ (strip_bitseq_false inpl) (strip_bitseq_false outpl)
                                    (ctree_mtree Tl))).
  { apply (IH (strip_bitseq_false inpl) (strip_bitseq_false outpl) (fun gamma => alphapre(false,gamma)) Tl).
    - intros gamma' delta' H8. apply Hapi in H8. injection H8. tauto.
    - now apply (inpl_reln_strip_bitseq_false alphapre fullinpl inpl Hapi).
    - now apply (outpl_reln_strip_bitseq_false m txh alphapre fulloutpl outpl Hapi 0).
    - intros alpha h H8.
      apply strip_bitseq_false_iff in H8.
      generalize (H3 (false,alpha) h H8).
      intros [u H9]. exists u.
      now apply (ctree_supports_asset_S_inv_L (h,u) T Tl None alpha).
    - intros alpha a H8.
      apply strip_bitseq_false_iff in H8.
      generalize (H4 (false,alpha) a H8).
      now apply (ctree_supports_addr_S_inv_L T Tl None alpha).
  }
  assert (L4: equi (octree_mtree
                      (tx_octree_trans_ (strip_bitseq_true inpl) (strip_bitseq_true outpl)
                                               None))
                   (tx_mtree_trans_ (strip_bitseq_true inpl) (strip_bitseq_true outpl)
                                    (empty_mtree n))).
  { assert (L4a: strip_bitseq_true inpl = nil).
    { destruct (strip_bitseq_true inpl) as [|[delta k] inpr'] eqn:H6; try reflexivity.
      exfalso.
      assert (L4aa: In ((true,delta),k) inpl).
      { apply strip_bitseq_true_iff. rewrite H6. now left. }
      apply H3 in L4aa. destruct L4aa as [u L4ab].
      destruct T as [[[[|] gamma] hl]|[h'|[Tl0|[Tr0|[Tl0 Tr0]]]]]; try contradiction L4ab; inversion H5.
    }
    rewrite L4a.
    rewrite tx_trans_mtree_emptyctree_eq. apply equi_ref.
  }
  assert (L5: (tx_mtree_trans_ inpl outpl
                               (mtreeB (octree_mtree (Some Tl)) (empty_mtree n)))
              = (mtreeB (tx_mtree_trans_ (strip_bitseq_false inpl) (strip_bitseq_false outpl) (ctree_mtree Tl))
                        (tx_mtree_trans_ (strip_bitseq_true inpl) (strip_bitseq_true outpl) (empty_mtree n)))).
  { destruct inpl as [|[gamma u] inpl].
    - destruct outpl as [|[delta v] outpl].
      + exfalso. destruct H0 as [H0|H0]; apply H0; reflexivity.
      + reflexivity.
    - reflexivity.
  }
  rewrite L5.
  apply (equi_rew_lem1 L3 L4).
  destruct (tx_octree_trans_ (strip_bitseq_false inpl) (strip_bitseq_false outpl) (Some Tl)) as [Tl'|] eqn:H6.
  + destruct (tx_octree_trans_ (strip_bitseq_true inpl) (strip_bitseq_true outpl) None) as [Tr'|] eqn:H7.
    * apply equi_ref.
    * apply equi_ref.
  + destruct (tx_octree_trans_ (strip_bitseq_true inpl) (strip_bitseq_true outpl) None) as [Tr'|] eqn:H7.
    * apply equi_ref.
    * apply equi_empty_lem.
- assert (L2: octree_mtree (Some T) = mtreeB (empty_mtree n) (octree_mtree (Some Tr))).
  { apply octree_mtree_S_inv_NS. exact H5. }
  rewrite L2.
  assert (L3: equi (octree_mtree
                      (tx_octree_trans_ (strip_bitseq_false inpl) (strip_bitseq_false outpl)
                                               None))
                   (tx_mtree_trans_ (strip_bitseq_false inpl) (strip_bitseq_false outpl)
                                    (empty_mtree n))).
  { assert (L3a: strip_bitseq_false inpl = nil).
    { destruct (strip_bitseq_false inpl) as [|[delta k] inpr'] eqn:H6; try reflexivity.
      exfalso.
      assert (L3aa: In ((false,delta),k) inpl).
      { apply strip_bitseq_false_iff. rewrite H6. now left. }
      apply H3 in L3aa. destruct L3aa as [u L3ab].
      destruct T as [[[[|] gamma] hl]|[h'|[Tl0|[Tr0|[Tl0 Tr0]]]]]; try contradiction L3ab; inversion H5.
    }
    rewrite L3a.
    rewrite tx_trans_mtree_emptyctree_eq. apply equi_ref.
  }
  assert (L4: equi (octree_mtree
                      (tx_octree_trans_ (strip_bitseq_true inpl) (strip_bitseq_true outpl)
                                               (Some Tr)))
                   (tx_mtree_trans_ (strip_bitseq_true inpl) (strip_bitseq_true outpl)
                                    (ctree_mtree Tr))).
  { apply (IH (strip_bitseq_true inpl) (strip_bitseq_true outpl) (fun gamma => alphapre(true,gamma)) Tr).
    - intros gamma' delta' H8. apply Hapi in H8. injection H8. tauto.
    - now apply (inpl_reln_strip_bitseq_true alphapre fullinpl inpl Hapi).
    - now apply (outpl_reln_strip_bitseq_true m txh alphapre fulloutpl outpl Hapi 0).
    - intros alpha h H8.
      apply strip_bitseq_true_iff in H8.
      generalize (H3 (true,alpha) h H8).
      intros [u H9]. exists u.
      now apply (ctree_supports_asset_S_inv_R (h,u) T None Tr alpha).
    - intros alpha a H8.
      apply strip_bitseq_true_iff in H8.
      generalize (H4 (true,alpha) a H8).
      now apply (ctree_supports_addr_S_inv_R T None Tr alpha).
  }
  assert (L5: (tx_mtree_trans_ inpl outpl
                               (mtreeB (empty_mtree n) (octree_mtree (Some Tr))))
              = (mtreeB (tx_mtree_trans_ (strip_bitseq_false inpl) (strip_bitseq_false outpl) (empty_mtree n))
                        (tx_mtree_trans_ (strip_bitseq_true inpl) (strip_bitseq_true outpl) (ctree_mtree Tr)))).
  { destruct inpl as [|[gamma u] inpl].
    - destruct outpl as [|[delta v] outpl].
      + exfalso. destruct H0 as [H0|H0]; apply H0; reflexivity.
      + reflexivity.
    - reflexivity.
  }
  rewrite L5.
  apply (equi_rew_lem1 L3 L4).
  destruct (tx_octree_trans_ (strip_bitseq_false inpl) (strip_bitseq_false outpl) None) as [Tl'|] eqn:H6.
  + destruct (tx_octree_trans_ (strip_bitseq_true inpl) (strip_bitseq_true outpl) (Some Tr)) as [Tr'|] eqn:H7.
    * apply equi_ref.
    * apply equi_ref.
  + destruct (tx_octree_trans_ (strip_bitseq_true inpl) (strip_bitseq_true outpl) (Some Tr)) as [Tr'|] eqn:H7.
    * apply equi_ref.
    * apply equi_empty_lem.
- assert (L2: octree_mtree (Some T) = (empty_mtree (S n))).
  { apply octree_mtree_S_inv_NN. exact H5. }
  rewrite L2.
  assert (Li: inpl = nil).
  { destruct inpl as [|[delta k] inpr] eqn:H6; try reflexivity.
    exfalso.
    assert (Lia: In (delta,k) ((delta,k)::inpr)) by now left.
    apply H3 in Lia.
    destruct T as [[[[|] gamma] hl]|[h'|[Tl0|[Tr0|[Tl0 Tr0]]]]]; try contradiction Lia; inversion H5.
  }
  subst inpl.
  assert (L3: equi (octree_mtree
                      (tx_octree_trans_ nil (strip_bitseq_false outpl)
                                               None))
                   (tx_mtree_trans_ nil (strip_bitseq_false outpl)
                                    (empty_mtree n))).
  { rewrite tx_trans_mtree_emptyctree_eq. apply equi_ref. }
  assert (L4: equi (octree_mtree
                      (tx_octree_trans_ nil (strip_bitseq_true outpl)
                                               None))
                   (tx_mtree_trans_ nil (strip_bitseq_true outpl)
                                    (empty_mtree n))).
  { rewrite tx_trans_mtree_emptyctree_eq. apply equi_ref. }
  assert (L5: (tx_mtree_trans_ nil outpl (empty_mtree (S n))
              = (mtreeB (tx_mtree_trans_ nil (strip_bitseq_false outpl) (empty_mtree n))
                        (tx_mtree_trans_ nil (strip_bitseq_true outpl) (empty_mtree n))))).
  { destruct outpl as [|[delta v] outpl].
    - exfalso. destruct H0 as [H0|H0]; apply H0; reflexivity.
    - reflexivity.
  }
  rewrite L5.
  apply (equi_rew_lem1 L3 L4).
  simpl.
  destruct (tx_octree_trans_ nil (strip_bitseq_false outpl) None) as [Tl'|] eqn:H6.
  + destruct (tx_octree_trans_ nil (strip_bitseq_true outpl) None) as [Tr'|] eqn:H7.
    * apply equi_ref.
    * apply equi_ref.
  + destruct (tx_octree_trans_ nil (strip_bitseq_true outpl) None) as [Tr'|] eqn:H7.
    * apply equi_ref.
    * apply equi_empty_lem.
Qed.

Lemma tx_trans_mtree_ctree_eq {n:nat} m (fullinpl:list addr_assetid) (fulloutpl:list addr_preasset) (txh:hashval) :
  forall inpl outpl,
  forall (alphapre:bitseq n -> addr),
    forall (T: ctree n),
      (forall gamma delta, alphapre gamma = alphapre delta -> gamma = delta)
      ->
      inpl_reln alphapre fullinpl inpl ->
      outpl_reln m txh alphapre 0 fulloutpl outpl ->
      (forall alpha h, In (alpha,h) inpl -> exists u, ctree_supports_asset (h,u) T alpha) ->
      (forall alpha u, In (alpha,u) outpl -> ctree_supports_addr T alpha) ->
      equi (octree_mtree
              (tx_octree_trans_ inpl outpl (Some T)))
           (tx_mtree_trans_ inpl outpl
                            (octree_mtree (Some T))).
induction n as [|n IH].
- intros inpl outpl alphapre T Hapi _ _ _ _.
  revert inpl outpl alphapre T Hapi.
  apply tx_trans_mtree_ctree_eq_0.
- intros inpl outpl alphapre T Hapi H1 H2 H3 H4.
  assert (L1: inpl = nil /\ outpl = nil \/ (inpl <> nil \/ outpl <> nil)).
  { destruct inpl as [|[gamma u] inpl].
    - destruct outpl as [|[delta v] outpl].
      + tauto.
      + right. right. discriminate.
    - right. left. discriminate.
  }
  destruct L1 as [[L1a L1b]|L1].
  + subst inpl. subst outpl. simpl. apply equi_ref.
  + exact (tx_trans_mtree_ctree_eq_S m fullinpl fulloutpl txh IH inpl outpl alphapre T Hapi L1 H1 H2 H3 H4).
Qed.

Opaque ctree_supports_addr.

Lemma tx_trans_mtree_octree_eq tht sigt m (tx:Tx) (T:option (ctree 162)) fee rew :
  octree_supports_tx tht sigt m tx T fee rew ->
  octree_mtree (tx_octree_trans m tx T) = normalize_mtree (tx_mtree_trans m tx (octree_mtree T)).
intros H1.
destruct T as [T|].
- assert (L1: normalize_mtree (octree_mtree (tx_octree_trans m tx (Some T))) = octree_mtree (tx_octree_trans m tx (Some T))).
  { apply normalize_mtree_normal_p_id. apply octree_mtree_normal. }
  rewrite <- L1.
  apply equi_normalize_mtree_2.
  destruct tx as [inpl outpl]. unfold tx_mtree_trans. unfold tx_octree_trans.
  apply ctree_supports_tx_can_support in H1.
  destruct H1 as [H2a [H2b [H2c [H2d H2e]]]].
  apply (tx_trans_mtree_ctree_eq m inpl outpl (hashtx(inpl,outpl)) inpl (add_vout m (hashtx (inpl, outpl)) (tx_outputs (inpl, outpl)) 0) (fun alpha => alpha) T).
  + tauto.
  + apply inpl_reln_start.
  + apply outpl_reln_start.
  + exact H2a.
  + intros alpha [k [bday [obl v]]] H5. apply add_vout_lem in H5. destruct H5 as [Hb [j [H6 H7]]].
    apply (H2b alpha (obl,v)). apply (nth_error_In _ j).
    exact H6.
- contradiction H1.
Qed.

Transparent mtree_supports_addr.

Transparent ctree_supports_addr.

Lemma ctree_mtree_supports_addr {n} (T:ctree n) (alpha:bitseq n) :
  ctree_supports_addr T alpha ->
  mtree_supports_addr (ctree_mtree T) alpha.
induction n as [|n IH].
- simpl. tauto.
- destruct T as [[gamma hl]|[h|[Tl|[Tr|[Tl Tr]]]]].
  + unfold ctree_supports_addr.
    destruct (bitseq_eq_dec gamma alpha) as [D1|D1].
    * intros _. unfold ctree_mtree. subst gamma. apply singlebranch_mtree_supports_addr.
    * { destruct gamma as [[|] gamma]; destruct alpha as [[|] alpha]; intros _.
        - apply singlebranch_mtree_supports_addr.
        - apply empty_mtree_supports_addr.
        - apply empty_mtree_supports_addr.
        - apply singlebranch_mtree_supports_addr.
      }
  + simpl. tauto.
  + destruct alpha as [[|] alphar].
    * intros _. simpl. apply empty_mtree_supports_addr.
    * simpl. apply IH.
  + destruct alpha as [[|] alphar].
    * simpl. apply IH.
    * intros _. simpl. apply empty_mtree_supports_addr.
  + destruct alpha as [[|] alphar].
    * simpl. apply IH.
    * simpl. apply IH.
Qed.

Lemma mtree_ctree_supports_addr {n} (T:ctree n) (alpha:bitseq n) :
  mtree_supports_addr (ctree_mtree T) alpha ->
  ctree_supports_addr T alpha.
induction n as [|n IH].
- simpl. tauto.
- destruct T as [[gamma hl]|[h|[Tl|[Tr|[Tl Tr]]]]].
  + unfold ctree_supports_addr. tauto.
  + simpl. tauto.
  + destruct alpha as [[|] alphar].
    * simpl. tauto.
    * simpl. apply IH.
  + destruct alpha as [[|] alphar].
    * simpl. apply IH.
    * simpl. tauto.
  + destruct alpha as [[|] alphar].
    * simpl. apply IH.
    * simpl. apply IH.
Qed.

Opaque mtree_supports_addr.

Lemma ctree_mtree_full_approx_addr {n} (T:ctree n) (alpha:bitseq n) :
  ctree_full_approx_addr T alpha ->
  mtree_full_approx_addr (ctree_mtree T) alpha.
induction n as [|n IH].
- simpl. destruct T as [h|[h hl]].
  + simpl. tauto.
  + simpl. tauto.
- destruct T as [[gamma hl]|[h|[Tl|[Tr|[Tl Tr]]]]].
  + unfold ctree_full_approx_addr.
    destruct (bitseq_eq_dec gamma alpha) as [D1|D1].
    * intros H1. unfold ctree_mtree. subst gamma.
      apply singlebranch_mtree_full_approx_addr.
      now right.
    * { destruct gamma as [[|] gamma]; destruct alpha as [[|] alpha]; intros H1.
        - apply singlebranch_mtree_full_approx_addr. now left.
        - apply empty_mtree_full_approx_addr.
        - apply empty_mtree_full_approx_addr.
        - apply singlebranch_mtree_full_approx_addr. now left.
      }
  + simpl. tauto.
  + destruct alpha as [[|] alphar].
    * intros _. simpl. apply empty_mtree_full_approx_addr.
    * simpl. apply IH.
  + destruct alpha as [[|] alphar].
    * simpl. apply IH.
    * intros _. simpl. apply empty_mtree_full_approx_addr.
  + destruct alpha as [[|] alphar].
    * simpl. apply IH.
    * simpl. apply IH.
Qed.

Lemma mtree_ctree_full_approx_addr {n} (T:ctree n) (alpha:bitseq n) :
  mtree_full_approx_addr (ctree_mtree T) alpha ->
  ctree_full_approx_addr T alpha.
induction n as [|n IH].
- simpl. destruct T as [h|[h hl]].
  + simpl. tauto.
  + simpl. tauto.
- destruct T as [[gamma hl]|[h|[Tl|[Tr|[Tl Tr]]]]].
  + unfold ctree_full_approx_addr.
    destruct (bitseq_eq_dec gamma alpha) as [H1|H1].
    * intros H2. unfold ctree_mtree in H2.
      apply singlebranch_mtree_full_approx_addr_conv in H2.
      tauto.
    * tauto.
  + simpl. tauto.
  + destruct alpha as [[|] alphar].
    * simpl. tauto.
    * simpl. apply IH.
  + destruct alpha as [[|] alphar].
    * simpl. apply IH.
    * simpl. tauto.
  + destruct alpha as [[|] alphar].
    * simpl. apply IH.
    * simpl. apply IH.
Qed.

Transparent mtree_supports_asset.

Lemma singlebranch_mtree_supports_asset (a:asset) {n} (hl:nehlist) (alpha:bitseq n) :
   In_hlist a (nehlist_hlist hl) ->
   mtree_supports_asset a (singlebranch_mtree hl alpha) alpha.
intros H1. induction n as [|n IH].
- simpl. exact H1.
- destruct alpha as [[|] alpha].
  + simpl. apply IH.
  + simpl. apply IH.
Qed.

Transparent ctree_supports_asset.

Lemma ctree_mtree_supports_asset (a:asset) {n} (T:ctree n) (alpha:bitseq n) :
  ctree_supports_asset a T alpha ->
  mtree_supports_asset a (ctree_mtree T) alpha.
induction n as [|n IH].
- simpl. intros H1. exact H1.
- destruct T as [[gamma hl]|[h|[Tl|[Tr|[Tl Tr]]]]].
  + unfold ctree_supports_asset.
    destruct (bitseq_eq_dec gamma alpha) as [D1|D1].
    * unfold ctree_mtree. subst gamma. apply singlebranch_mtree_supports_asset.
    * tauto.
  + simpl. tauto.
  + destruct alpha as [[|] alpha].
    * simpl. tauto.
    * simpl. apply IH.
  + destruct alpha as [[|] alpha].
    * simpl. apply IH.
    * simpl. tauto.
  + destruct alpha as [[|] alpha].
    * simpl. apply IH.
    * simpl. apply IH.
Qed.

Transparent mtree_supports_asset.

Lemma mtree_ctree_supports_asset (a:asset) {n} (T:ctree n) (alpha:bitseq n) :
  mtree_supports_asset a (ctree_mtree T) alpha ->
  ctree_supports_asset a T alpha.
induction n as [|n IH].
- simpl. intros H1. exact H1.
- destruct T as [[gamma hl]|[h|[Tl|[Tr|[Tl Tr]]]]].
  + unfold ctree_supports_asset.
    destruct (bitseq_eq_dec gamma alpha) as [D1|D1].
    * unfold ctree_mtree. subst gamma.
      intros H1. apply singlebranch_mtree_supports_asset_conv in H1.
      tauto.
    * intros H1. apply singlebranch_mtree_supports_asset_conv in H1.
      tauto.
  + simpl. tauto.
  + destruct alpha as [[|] alpha].
    * simpl. apply empty_mtree_p_not_supports_asset. apply empty_mtree_p_empty_mtree.
    * simpl. apply IH.
  + destruct alpha as [[|] alpha].
    * simpl. apply IH.
    * simpl. apply empty_mtree_p_not_supports_asset. apply empty_mtree_p_empty_mtree.
  + destruct alpha as [[|] alpha].
    * simpl. apply IH.
    * simpl. apply IH.
Qed.

Opaque ctree_supports_asset.
Opaque mtree_supports_asset.

Lemma ctree_mtree_asset_value_in (T:ctree 162) inpl utot :
  ctree_asset_value_in T inpl utot ->
  mtree_asset_value_in (ctree_mtree T) inpl utot.
intros H. induction H as [|h a u inpl alpha v H1 IH H2 H3 H4|h a inpl alpha v H1 IH H2 H3 H4].
- apply mtree_asset_value_in_nil.
- apply mtree_asset_value_in_cons with (a := a).
  + exact IH.
  + apply ctree_mtree_supports_asset. exact H2.
  + exact H3.
  + exact H4.
- apply mtree_asset_value_in_skip with (a := a).
  + exact IH.
  + apply ctree_mtree_supports_asset. exact H2.
  + exact H3.
  + exact H4.
Qed.

Lemma mtree_ctree_asset_value_in (T:ctree 162) inpl utot :
  mtree_asset_value_in (ctree_mtree T) inpl utot ->
  ctree_asset_value_in T inpl utot.
intros H. induction H as [|h a u inpl alpha v H1 IH H2 H3 H4|h a inpl alpha v H1 IH H2 H3 H4].
- apply ctree_asset_value_in_nil.
- apply ctree_asset_value_in_cons with (a := a).
  + exact IH.
  + apply mtree_ctree_supports_asset. exact H2.
  + exact H3.
  + exact H4.
- apply ctree_asset_value_in_skip with (a := a).
  + exact IH.
  + apply mtree_ctree_supports_asset. exact H2.
  + exact H3.
  + exact H4.
Qed.

Lemma mtree_ctree_rights_consumed (T:ctree 162) (b:bool) (alpha:termaddr) (inpl:list addr_assetid) (utot:nat) :
  mtree_rights_consumed b alpha (ctree_mtree T) inpl utot
  -> ctree_rights_consumed b alpha T inpl utot.
intros H. induction H as [|beta h inpr r1 bday obl r2 H2 IH H3|beta h inpr r1 bday obl u H2 IH H3 H4].
- apply ctree_rights_consumed_nil.
- apply ctree_rights_consumed_cons with (bday := bday) (obl := obl).
  + exact IH.
  + revert H3. apply mtree_ctree_supports_asset.
- apply ctree_rights_consumed_skip with (bday := bday) (obl := obl) (u := u).
  + exact IH.
  + revert H3. apply mtree_ctree_supports_asset.
  + exact H4.
Qed.

Lemma ctree_mtree_rights_consumed (T:ctree 162) (b:bool) (alpha:termaddr) (inpl:list addr_assetid) (utot:nat) :
  ctree_rights_consumed b alpha T inpl utot
  -> mtree_rights_consumed b alpha (ctree_mtree T) inpl utot.
intros H. induction H as [|beta h inpr r1 bday obl r2 H2 IH H3|beta h inpr r1 bday obl u H2 IH H3 H4].
- apply mtree_rights_consumed_nil.
- apply mtree_rights_consumed_cons with (bday := bday) (obl := obl).
  + exact IH.
  + revert H3. apply ctree_mtree_supports_asset.
- apply mtree_rights_consumed_skip with (bday := bday) (obl := obl) (u := u).
  + exact IH.
  + revert H3. apply ctree_mtree_supports_asset.
  + exact H4.
Qed.

Theorem octree_mtree_supports_tx tht sigt m (tx:Tx) (T:option (ctree 162)) fee rew :
  octree_supports_tx tht sigt m tx T fee rew ->
  mtree_supports_tx tht sigt m tx (octree_mtree T) fee rew.
destruct T as [T|].
- intros [Hs1 [[utot [Hs2 Hs3]] [[Hs4a Hs4b] [[Hs5a [Hs5b Hs5c]] [Hs6 [Hs7 Hs8]]]]]].
  unfold octree_mtree. split.
  + intros alpha a H1. apply Hs1 in H1.
    apply ctree_mtree_supports_addr.
    exact H1.
  + split.
    * { exists utot. split.
        - apply ctree_mtree_asset_value_in. exact Hs2.
        - exact Hs3.
      }
    * { split.
        - split.
          + intros alpha b H1.
            destruct (Hs4a alpha b H1) as [H2 [H3 H4]].
            split.
            * revert H2. apply ctree_mtree_full_approx_addr.
            * { split.
                - intros [h' [bday' [obl' [beta' H5]]]].
                  apply H3. exists h'. exists bday'. exists obl'. exists beta'.
                  revert H5. apply mtree_ctree_supports_asset.
                - intros rtot1 rtot2 h bday obl beta u H5 H6 H7.
                  apply mtree_ctree_supports_asset in H6.
                  destruct (H4 rtot1 rtot2 h bday obl beta u H5 H6 H7) as [rtot3 [rtot4 [H8 [H9 H10]]]].
                  exists rtot3. exists rtot4.
                  repeat split.
                  + revert H8. apply ctree_mtree_rights_consumed.
                  + exact H9.
                  + exact H10.
              }
          + intros alpha b beta h bday obl n H1 H2.
            assert (L1: ctree_supports_asset (h, (bday, (obl, rights b n alpha))) T beta).
            { apply mtree_ctree_supports_asset. exact H2. }
            revert H1 L1. apply Hs4b.
        - split; [split; [|split]| ].
          + intros obl gamma nonce d alpha H1.
            destruct (Hs5a obl gamma nonce d alpha H1) as [Hch [beta [h [bday' [obl' [H2 [H3 [H4 H5]]]]]]]].
            split.
            * exact Hch.
            * { exists beta. exists h. exists bday'. exists obl'. repeat split.
                - exact H2.
                - exact H3.
                - exact H4.
                - revert H5. apply ctree_mtree_supports_asset.
              }
          + intros obl gamma nonce th d alpha H1.
            destruct (Hs5b obl gamma nonce th d alpha H1) as [Hch [beta [h [bday' [obl' [H2 [H3 [H4 H5]]]]]]]].
            split.
            * { revert Hch. apply check_signaspec_p_subq.
                - intros k b [k' [bday'' [obl'' H7]]].
                  exists k'. exists bday''. exists obl''.
                  revert H7. apply ctree_mtree_supports_asset.
                - intros k [k' [bday'' [obl'' H7]]].
                  exists k'. exists bday''. exists obl''.
                  revert H7. apply ctree_mtree_supports_asset.
              }
            * { exists beta. exists h. exists bday'. exists obl'. repeat split.
                - exact H2.
                - exact H3.
                - exact H4.
                - revert H5. apply ctree_mtree_supports_asset.
              }
          + intros obl gamma nonce th d alpha H1.
            destruct (Hs5c obl gamma nonce th d alpha H1) as [Hch [beta [h [bday' [obl' [H2 [H3 [H4 H5]]]]]]]].
            split.
            * { revert Hch. apply check_doc_p_subq.
                - intros k b [k' [bday'' [obl'' H7]]].
                  exists k'. exists bday''. exists obl''.
                  revert H7. apply ctree_mtree_supports_asset.
                - intros k [k' [bday'' [obl'' H7]]].
                  exists k'. exists bday''. exists obl''.
                  revert H7. apply ctree_mtree_supports_asset.
              }
            * { exists beta. exists h. exists bday'. exists obl'. repeat split.
                - exact H2.
                - exact H3.
                - exact H4.
                - revert H5. apply ctree_mtree_supports_asset.
              }
          + split.
            * { intros alpha b obl beta r H1.
                destruct (Hs6 alpha b obl beta r H1) as [H2 H3].
                split.
                - revert H2. apply ctree_mtree_full_approx_addr.
                - destruct H3 as [[h [beta' [bday' [obl' [r' [H4 H5]]]]]]|[H4 H5]].
                  + left. exists h. exists beta'. exists bday'. exists obl'. exists r'.
                    split.
                    * revert H4. apply ctree_mtree_supports_asset.
                    * exact H5.
                  + right. split.
                    * intros [h [beta' [bday' [obl' [r' H6]]]]].
                      apply H4. exists h. exists beta'. exists bday'. exists obl'. exists r'.
                      revert H6. apply mtree_ctree_supports_asset.
                    * exact H5.
              }
            * { split.
                - intros k1 k2 b H1. destruct (Hs7 k1 k2 b H1) as [H2 H3]. split.
                  + revert H2. apply ctree_mtree_full_approx_addr.
                  + intros H4. apply H3. intros [h' [beta' [bday' [obl' [r' H5]]]]].
                    apply H4. exists h'. exists beta'. exists bday'. exists obl'. exists r'.
                    revert H5. apply ctree_mtree_supports_asset.
                - intros alpha h bday obl u H1 H2.
                  apply mtree_ctree_supports_asset in H2.
                  destruct (Hs8 alpha h bday obl u H1 H2) as [H3 [h' [bday' [obl' [beta [r [H4 [H5 H6]]]]]]]].
                  split.
                  + revert H3. apply ctree_mtree_full_approx_addr.
                  + exists h'. exists bday'. exists obl'. exists beta. exists r. repeat split.
                    * exact H4.
                    * revert H5. apply ctree_mtree_supports_asset.
                    * exact H6.
              }
      }
- intros H1. contradiction H1.
Qed.

Theorem mtree_ctree_supports_tx tht sigt m (tx:Tx) (T:ctree 162) fee rew :
  mtree_supports_tx tht sigt m tx (ctree_mtree T) fee rew ->
  ctree_supports_tx tht sigt m tx T fee rew.
intros [Hs1 [[utot [Hs2 Hs3]] [[Hs4a Hs4b] [[Hs5a [Hs5b Hs5c]] [Hs6 [Hs7 Hs8]]]]]].
  split.
  + intros alpha a H1. apply Hs1 in H1.
    apply mtree_ctree_supports_addr.
    exact H1.
  + split.
    * { exists utot. split.
        - apply mtree_ctree_asset_value_in. exact Hs2.
        - exact Hs3.
      }
    * { split.
        - split.
          + intros alpha b H1.
            destruct (Hs4a alpha b H1) as [H2 [H3 H4]].
            split.
            * revert H2. apply mtree_ctree_full_approx_addr.
            * { split.
                - intros [h' [bday' [obl' [beta' H5]]]].
                  apply H3. exists h'. exists bday'. exists obl'. exists beta'.
                  revert H5. apply ctree_mtree_supports_asset.
                - intros rtot1 rtot2 h bday obl beta u H5 H6 H7.
                  apply ctree_mtree_supports_asset in H6.
                  destruct (H4 rtot1 rtot2 h bday obl beta u H5 H6 H7) as [rtot3 [rtot4 [H8 [H9 H10]]]].
                  exists rtot3. exists rtot4.
                  repeat split.
                  + revert H8. apply mtree_ctree_rights_consumed.
                  + exact H9.
                  + exact H10.
              }
          + intros alpha b beta h bday obl n H1 H2.
            assert (L1: mtree_supports_asset (h, (bday, (obl, rights b n alpha))) (ctree_mtree T) beta).
            { apply ctree_mtree_supports_asset. exact H2. }
            revert H1 L1. apply Hs4b.
        - split; [split; [|split]|].
          + intros obl gamma nonce d alpha H1.
            destruct (Hs5a obl gamma nonce d alpha H1) as [Hch [beta [h [bday' [obl' [H2 [H3 [H4 H5]]]]]]]].
            split.
            * exact Hch.
            * { exists beta. exists h. exists bday'. exists obl'. repeat split.
                - exact H2.
                - exact H3.
                - exact H4.
                - revert H5. apply mtree_ctree_supports_asset.
              }
          + intros obl gamma nonce th d alpha H1.
            destruct (Hs5b obl gamma nonce th d alpha H1) as [Hch [beta [h [bday' [obl' [H2 [H3 [H4 H5]]]]]]]].
            split.
            * { revert Hch. apply check_signaspec_p_subq.
                - intros k b [k' [bday'' [obl'' H7]]].
                  exists k'. exists bday''. exists obl''.
                  revert H7. apply mtree_ctree_supports_asset.
                - intros k [k' [bday'' [obl'' H7]]].
                  exists k'. exists bday''. exists obl''.
                  revert H7. apply mtree_ctree_supports_asset.
              }
            * { exists beta. exists h. exists bday'. exists obl'. repeat split.
                - exact H2.
                - exact H3.
                - exact H4.
                - revert H5. apply mtree_ctree_supports_asset.
              }
          + intros obl gamma nonce th d alpha H1.
            destruct (Hs5c obl gamma nonce th d alpha H1) as [Hch [beta [h [bday' [obl' [H2 [H3 [H4 H5]]]]]]]].
            split.
            * { revert Hch. apply check_doc_p_subq.
                - intros k b [k' [bday'' [obl'' H7]]].
                  exists k'. exists bday''. exists obl''.
                  revert H7. apply mtree_ctree_supports_asset.
                - intros k [k' [bday'' [obl'' H7]]].
                  exists k'. exists bday''. exists obl''.
                  revert H7. apply mtree_ctree_supports_asset.
              }
            * { exists beta. exists h. exists bday'. exists obl'. repeat split.
                - exact H2.
                - exact H3.
                - exact H4.
                - revert H5. apply mtree_ctree_supports_asset.
              }
          + split.
            * { intros alpha b obl beta r H1.
                destruct (Hs6 alpha b obl beta r H1) as [H2 H3].
                split.
                - revert H2. apply mtree_ctree_full_approx_addr.
                - destruct H3 as [[h [beta' [bday' [obl' [r' [H4 H5]]]]]]|[H4 H5]].
                  + left. exists h. exists beta'. exists bday'. exists obl'. exists r'.
                    split.
                    * revert H4. apply mtree_ctree_supports_asset.
                    * exact H5.
                  + right. split.
                    * intros [h [beta' [bday' [obl' [r' H6]]]]].
                      apply H4. exists h. exists beta'. exists bday'. exists obl'. exists r'.
                      revert H6. apply ctree_mtree_supports_asset.
                    * exact H5.
              }
            * { split.
                - intros k1 k2 b H1. destruct (Hs7 k1 k2 b H1) as [H2 H3]. split.
                  + revert H2. apply mtree_ctree_full_approx_addr.
                  + intros H4. apply H3. intros [h' [beta' [bday' [obl' [r' H5]]]]].
                    apply H4. exists h'. exists beta'. exists bday'. exists obl'. exists r'.
                    revert H5. apply mtree_ctree_supports_asset.
                - intros alpha h bday obl u H1 H2.
                  apply ctree_mtree_supports_asset in H2.
                  destruct (Hs8 alpha h bday obl u H1 H2) as [H3 [h' [bday' [obl' [beta [r [H4 [H5 H6]]]]]]]].
                  split.
                  + revert H3. apply mtree_ctree_full_approx_addr.
                  + exists h'. exists bday'. exists obl'. exists beta. exists r. repeat split.
                    * exact H4.
                    * revert H5. apply mtree_ctree_supports_asset.
                    * exact H6.
              }
      }
Qed.

Opaque mtree_approx_fun_p.
Opaque empty_mtree.

Theorem mtree_octree_supports_tx tht sigt m (tx:Tx) (T:option (ctree 162)) fee rew :
  tx_inputs tx <> nil ->
  mtree_supports_tx tht sigt m tx (octree_mtree T) fee rew ->
  octree_supports_tx tht sigt m tx T fee rew.
intros H1. destruct T as [T|].
- apply mtree_ctree_supports_tx.
- (*** Corner case. The empty MTree would support an empty tx, but such txs are not valid anyway. ***)
  intros H2. exfalso. apply mtree_supports_tx_can_support in H2.
  destruct H2 as [H3 _].
  destruct (tx_inputs tx) as [|[alpha h] txr].
  + apply H1. reflexivity.
  + assert (L1: In (alpha, h) ((alpha, h) :: txr)) by now left.
    destruct (H3 alpha h L1) as [[obl u] H4].
    change (mtree_supports_asset (h, (obl, u)) (empty_mtree 162) alpha) in H4.
    assert (L2: mtree_approx_fun_p (empty_mtree 162) (fun beta:addr => nil)).
    { apply (empty_approx_empty_fun (fun alpha => nil)). intros _. reflexivity. }
    generalize (mtree_supports_asset_In_statefun _ _ _ _ L2 H4).
    simpl. tauto.
Qed.

Lemma ctree_mtree_can_support_tx (tx:Tx) (T:ctree 162) :
  ctree_can_support_tx tx T ->
  mtree_can_support_tx tx (ctree_mtree T).
intros [Hcs1 [Hcs2 [Hcs3 [Hcs4 [Hcs5 [Hcs6 [Hcs7 Hcs8]]]]]]]. split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
- intros alpha h H1. destruct (Hcs1 alpha h H1) as [oblu H2].
  exists oblu. revert H2. apply ctree_mtree_supports_asset.
- intros alpha oblu H1. apply ctree_mtree_supports_addr.
  revert H1. apply Hcs2.
- intros alpha obl b n beta H1. apply ctree_mtree_full_approx_addr.
  revert H1. apply Hcs3.
- intros alpha b H1. apply ctree_mtree_full_approx_addr.
  revert H1. apply Hcs4.
- intros k1 k2 b H1. apply ctree_mtree_full_approx_addr.
  revert H1. apply Hcs5.
- intros alpha obl b beta r H1. apply ctree_mtree_full_approx_addr.
  revert H1. apply Hcs6.
- intros obl gamma nonce th d alpha h H1 H2.
  destruct (Hcs7 obl gamma nonce th d alpha h H1 H2) as [k [bday [obl' H3]]].
  exists k. exists bday. exists obl'. revert H3. apply ctree_mtree_supports_asset.
- intros obl gamma nonce th d alpha h H1 H2.
  destruct (Hcs8 obl gamma nonce th d alpha h H1 H2) as [k [bday [obl' H3]]].
  exists k. exists bday. exists obl'. revert H3. apply ctree_mtree_supports_asset.
Qed.

Theorem ctree_supports_tx_statefun_conv tht sigt m tx (T:ctree 162) f fee rew :
  (forall h alpha u alpha' u', In (h,u) (f alpha) -> In (h,u') (f alpha') -> alpha = alpha' /\ u = u') ->
  mtree_approx_fun_p (ctree_mtree T) f ->  
  tx_valid tx ->
  ctree_can_support_tx tx T ->
  statefun_supports_tx tht sigt m f tx fee rew ->
  ctree_supports_tx tht sigt m tx T fee rew.
intros Hf2 H1 Ht Hcs Hxf.
apply mtree_ctree_supports_tx.
revert Hxf. apply (mtree_supports_tx_statefun_conv _ _ _ _ _ _ _ _ Hf2 H1 Ht).
revert Hcs. apply ctree_mtree_can_support_tx.
Qed.
    
Theorem octree_approx_trans tht sigt m (tx:Tx) (T:option (ctree 162)) f fee rew :
  sf_valid f ->
  octree_supports_tx tht sigt m tx T fee rew ->
  octree_approx_fun_p T f ->
  octree_approx_fun_p (tx_octree_trans m tx T) (tx_statefun_trans m tx f).
unfold octree_approx_fun_p.
intros H1 H2 H3.
rewrite (tx_trans_mtree_octree_eq _ _ _ _ _ _ _ H2).
apply normalize_mtree_approx_fun_p.
apply (mtree_approx_trans tht sigt m tx (octree_mtree T) f fee rew H1).
- now apply octree_mtree_supports_tx.
- exact H3.
Qed.

Fixpoint hlist_reduce_to_min_support (aidl : list hashval) (hl:hlist) : hlist :=
  match aidl with
    | nil => (*** no more info is needed, so just remember the hash of the rest of the asset list ***)
      match hlist_hashroot hl with
        | Some(h) => hlistH h
        | None => hlistN
      end
    | _ =>
      match hl with
        | hlistC (h,u) hr =>
          hlistC (h,u) (hlist_reduce_to_min_support (remove hashval_eq_dec h aidl) hr)
        | _ => hl
      end
  end.

Definition preasset_marker_dec (u:preasset) : {u = marker} + {u <> marker}.
destruct u; try (right; discriminate). left. reflexivity.
Defined.

(*** Go until find marker and all of aidl have been included. ***)
Fixpoint hlist_reduce_to_min_support_marker (aidl : list hashval) (hl:hlist) : hlist :=
  match hl with
    | hlistC (h,(bday,(obl,u))) hr =>  
      if preasset_marker_dec u then
        hlistC (h,(bday,(obl,u))) (hlist_reduce_to_min_support (remove hashval_eq_dec h aidl) hr)
      else
        hlistC (h,(bday,(obl,u))) (hlist_reduce_to_min_support_marker (remove hashval_eq_dec h aidl) hr)
    | _ => hl (*** in practice, this shouldn't happen ***)
  end.

Definition nehlist_hashroot (hl:nehlist) : hashval :=
  match hl with
    | inl h => h
    | inr (a,hr) =>
      match hlist_hashroot hr with
        | None => hashpair (hashnat 3) (hashasset a)
        | Some k => hashpair (hashnat 4) (hashpair (hashasset a) k)
      end
  end.

Fixpoint ctree_hashroot {n} : ctree n -> hashval :=
match n with
| O => fun hl : ctree 0 => nehlist_hashroot hl
| S n => fun T : ctree (S n) =>
           match T with
             | inl ((false,gamma),hl) =>
               hashopair1 (ctree_hashroot (ctreeL hl gamma)) None
             | inl ((true,gamma),hl) =>
               hashopair2 None (ctree_hashroot (ctreeL hl gamma))
             | inr (inl h) => h
             | inr (inr (inl Tl)) =>
               hashopair1 (ctree_hashroot Tl) None
             | inr (inr (inr (inl Tr))) =>
               hashopair2 None (ctree_hashroot Tr)
             | inr (inr (inr (inr (Tl,Tr)))) =>
               hashopair1 (ctree_hashroot Tl) (Some (ctree_hashroot Tr))
           end
end.

Definition strip_bitseq_false0 {n} (l:list (bitseq (S n))) : list (bitseq n) :=
map (@fst (bitseq n) unit)
    (strip_bitseq_false
       (map (fun alpha => (alpha,tt)) l)).

Definition strip_bitseq_true0 {n} (l:list (bitseq (S n))) : list (bitseq n) :=
map (@fst (bitseq n) unit)
    (strip_bitseq_true
       (map (fun alpha => (alpha,tt)) l)).

Lemma strip_bitseq_false0_iff {n} (l:list (bitseq (S n))) :
  forall alpha, In alpha (strip_bitseq_false0 l) <-> In (false,alpha) l.
intros alpha. unfold strip_bitseq_false0. split.
- intros H1. apply in_map_iff in H1. destruct H1 as [[beta []] [H2 H3]].
  simpl in H2. subst beta. apply strip_bitseq_false_iff in H3.
  apply in_map_iff in H3. destruct H3 as [beta [H4 H5]].
  inversion H4. subst beta. assumption.
- intros H1. apply in_map_iff. exists (alpha,tt). split.
  + reflexivity.
  + apply strip_bitseq_false_iff. apply in_map_iff.
    exists (false,alpha). split.
    * reflexivity.
    * assumption.
Qed.

Lemma strip_bitseq_true0_iff {n} (l:list (bitseq (S n))) :
  forall alpha, In alpha (strip_bitseq_true0 l) <-> In (true,alpha) l.
intros alpha. unfold strip_bitseq_true0. split.
- intros H1. apply in_map_iff in H1. destruct H1 as [[beta []] [H2 H3]].
  simpl in H2. subst beta. apply strip_bitseq_true_iff in H3.
  apply in_map_iff in H3. destruct H3 as [beta [H4 H5]].
  inversion H4. subst beta. assumption.
- intros H1. apply in_map_iff. exists (alpha,tt). split.
  + reflexivity.
  + apply strip_bitseq_true_iff. apply in_map_iff.
    exists (true,alpha). split.
    * reflexivity.
    * assumption.
Qed.

Fixpoint ctree_reduce_to_min_support {n} :
  forall (inpl : list (bitseq n * hashval))
         (outpl : list (bitseq n))
         (full : list (bitseq n))
         (markers : list (bitseq n))
         (T:ctree n), ctree n :=
match n with
| O => fun inpl outpl full markers (hl:ctree 0) =>
         match full with
           | (_::_) => hl (*** need a full approx for this address, so delete nothing ***)
           | nil =>
             match hl return ctree 0 with
               | inl h => inl h
               | inr ((h,(bday,(obl,u))),hr) =>
                 match markers with
                   | nil =>
                     match inpl with
                       | nil => inl (match hlist_hashroot hr with
                                       | None => hashpair (hashnat 3) (hashasset (h,(bday,(obl,u))))
                                       | Some k => hashpair (hashnat 4) (hashpair (hashasset (h,(bday,(obl,u)))) k)
                                     end)
                       | _ =>
                         inr ((h,(bday,(obl,u))),hlist_reduce_to_min_support (remove hashval_eq_dec h (map (@snd (bitseq 0) hashval) inpl)) hr)
                     end
                   | (_::_) =>
                     if preasset_marker_dec u then
                       inr ((h,(bday,(obl,u))),hlist_reduce_to_min_support (remove hashval_eq_dec h (map (@snd (bitseq 0) hashval) inpl)) hr)
                     else
                       inr ((h,(bday,(obl,u))),hlist_reduce_to_min_support_marker (remove hashval_eq_dec h (map (@snd (bitseq 0) hashval) inpl)) hr)
                     end
                 end
             end
| S n => fun inpl outpl full markers (T:ctree (S n)) =>
           match inpl,outpl,full,markers return ctree (S n) with
             | nil,nil,nil,nil => inr (inl (ctree_hashroot T))
             | _,_,_,_ =>
               match T with
                 | inr (inr (inl Tl)) =>
                   ctreeBL (ctree_reduce_to_min_support (strip_bitseq_false inpl)
                                                        (strip_bitseq_false0 outpl)
                                                        (strip_bitseq_false0 full)
                                                        (strip_bitseq_false0 markers)
                                                        Tl)
                 | inr (inr (inr (inl Tr))) =>
                   ctreeBR (ctree_reduce_to_min_support (strip_bitseq_true inpl)
                                                        (strip_bitseq_true0 outpl)
                                                        (strip_bitseq_true0 full)
                                                        (strip_bitseq_true0 markers)
                                                        Tr)

                 | inr (inr (inr (inr (Tl,Tr)))) =>
                   ctreeB (ctree_reduce_to_min_support (strip_bitseq_false inpl)
                                                       (strip_bitseq_false0 outpl)
                                                       (strip_bitseq_false0 full)
                                                       (strip_bitseq_false0 markers)
                                                       Tl)
                          (ctree_reduce_to_min_support (strip_bitseq_true inpl)
                                                       (strip_bitseq_true0 outpl)
                                                       (strip_bitseq_true0 full)
                                                       (strip_bitseq_true0 markers)
                                                       Tr)
                 | _ => T
               end
           end
end.

Definition octree_reduce_to_min_support {n} 
           (inpl : list (bitseq n * hashval))
           (outpl : list (bitseq n))
           (full : list (bitseq n))
           (markers : list (bitseq n))
           (T:option (ctree n)): option (ctree n) :=
match T with
| None => None
| Some T => Some (ctree_reduce_to_min_support inpl outpl full markers T)
end.

Fixpoint full_needed_1 (outpl : list addr_preasset) : list addr :=
match outpl with
| nil => nil
| (alpha,(obl,rights b n beta))::outpr => termaddr_addr beta::full_needed_1 outpr
| (alpha,(obl,owns b beta r))::outpr => alpha::full_needed_1 outpr
| _::outpr => full_needed_1 outpr
end.

Definition full_needed (outpl : list addr_preasset) : list addr :=
  map termaddr_addr (output_uses false outpl)
      ++ map termaddr_addr (output_uses true outpl)
      ++ map (fun k:prod hashval hashval => let (k1,k2) := k in hashval_term_addr k1) (output_creates false outpl)
      ++ map (fun k:prod hashval hashval => let (k1,k2) := k in hashval_term_addr k1) (output_creates true outpl)
      ++ full_needed_1 outpl.

Lemma In_full_needed_uses outpl b alpha :
  In alpha (output_uses b outpl) -> In (termaddr_addr alpha) (full_needed outpl).
unfold full_needed. intros H1. destruct b.
- apply in_or_app. right. apply in_or_app. left. apply in_map. exact H1.
- apply in_or_app. left. apply in_map. exact H1.
Qed.

Lemma In_full_needed_creates outpl b k1 k2 :
  In (k1,k2) (output_creates b outpl) -> In (hashval_term_addr k1) (full_needed outpl).
unfold full_needed. intros H1. destruct b.
- apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
  apply in_map_iff. exists (k1,k2). split.
  + reflexivity.
  + exact H1.
- apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
  apply in_map_iff. exists (k1,k2). split.
  + reflexivity.
  + exact H1.
Qed.

Lemma In_full_needed_rights outpl alpha obl b n beta :
  In (alpha,(obl,rights b n beta)) outpl -> In (termaddr_addr beta) (full_needed outpl).
intros H1.
unfold full_needed. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right.
induction outpl as [|x outpr IH].
- contradiction H1.
- destruct H1 as [H1|H1].
  + subst x. simpl. now left.
  + destruct x as [gamma [obl' v']]; destruct v'; simpl; tauto.
Qed.

Lemma In_full_needed_owns outpl alpha obl b beta r :
  In (alpha,(obl,owns b beta r)) outpl -> In alpha (full_needed outpl).
intros H1.
unfold full_needed. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right.
induction outpl as [|x outpr IH].
- contradiction H1.
- destruct H1 as [H1|H1].
  + subst x. simpl. now left.
  + destruct x as [gamma [obl' v']]; destruct v'; try exact (IH H1); right; exact (IH H1).
Qed.

Definition octree_reduce_to_min_support_tx (tx:Tx) (T:option (ctree 162)) : option (ctree 162) :=
  let (inpl,outpl) := tx in
  octree_reduce_to_min_support
    inpl (map (@fst addr (prod obligation preasset)) outpl) (full_needed outpl) (map hashval_term_addr (output_markers outpl)) T.

Lemma remove_hashval_iff (x y:hashval) (l:list hashval) :
  In x (remove hashval_eq_dec y l) <-> In x l /\ x <> y.
induction l as [|z r IH].
- simpl. tauto.
- simpl. destruct (hashval_eq_dec y z) as [H1|H1].
  + split.
    * tauto.
    * { intros [[H2|H2] H3].
        - exfalso. congruence.
        - tauto.
      }
  + split.
    * { intros [H2|H2].
        - split.
          + tauto.
          + congruence.
        - tauto.
      }
    * { intros [[H2|H2] H3].
        - now left.
        - right. tauto.
      }
Qed.

Definition fnlh (hl : hlist) : Prop :=
forall h oblu oblv, In_hlist (h,oblu) hl -> In_hlist (h,oblv) hl -> oblu = oblv.

Lemma hlist_reduce_to_min_support_assets (hl:hlist) (inpr : list hashval) :
  fnlh hl ->
  (forall (h : hashval), In h inpr -> exists u, In_hlist (h,u) hl) ->
  (forall h u, In h inpr ->
               In_hlist (h,u) hl ->
               In_hlist (h, u) (hlist_reduce_to_min_support inpr hl)).
revert inpr. induction hl as [k| |[k v] hr IH].
- intros inpr Hf H1 h u H2 H3. inversion H3.
- intros inpr Hf H1 h u H2 H3. inversion H3.
- intros inpr Hf H1 h u H2 H3. destruct inpr as [|k' inpr'].
  + contradiction H2.
  + simpl. revert H1 H2 H3. set (inpr := (k' :: inpr')).
    intros H1 H2 H3.
    destruct (hashval_eq_dec h k) as [D1|D1].
    * { inversion H3.
        - apply In_hlist_H.
        - subst k.
          assert (L1: u = v).
          { apply (Hf h u v).
            - now right.
            - now left.
          } 
          subst v. apply In_hlist_H.
      }
    * { inversion H3.
        - contradiction.
        - change (In_hlist (h, u)
                           (hlistC (k, v)
                                   (hlist_reduce_to_min_support
                                      (remove hashval_eq_dec k inpr) hr))).
          assert (Lf: fnlh hr).
          { intros h' u' v' H5 H6. apply (Hf h' u' v'); now right. }
          assert (L1: forall h : hashval,
                        In h (remove hashval_eq_dec k inpr) ->
                        exists oblu, In_hlist (h, oblu) hr).
          { intros h' H6. apply remove_hashval_iff in H6.
            destruct H6 as [H7 H8].
            apply H1 in H7.
            destruct H7 as [obl'w H9]. inversion H9.
            - exfalso. contradiction (H8 H6).
            - exists obl'w. assumption.
          }
          assert (L2: In h (remove hashval_eq_dec k inpr)).
          { apply remove_hashval_iff. tauto. }
          right. 
          exact (IH (remove hashval_eq_dec k inpr) Lf L1 h u L2 H0).
      }
Qed.

Lemma hlist_reduce_to_min_support_marker_assets (hl:hlist) (inpr : list hashval) :
  fnlh hl ->
  (forall (h : hashval), In h inpr -> exists u, In_hlist (h,u) hl) ->
  (forall h u, In h inpr ->
               In_hlist (h,u) hl ->
               In_hlist (h, u) (hlist_reduce_to_min_support_marker inpr hl)).
revert inpr. induction hl as [k| |[k v] hr IH].
- intros inpr Hf H1 h u H2 H3. inversion H3.
- intros inpr Hf H1 h u H2 H3. inversion H3.
- intros inpr Hf H1 h u H2 H3. destruct inpr as [|k' inpr'].
  + contradiction H2.
  + simpl. revert H1 H2 H3. set (inpr := (k' :: inpr')).
    intros H1 H2 H3.
    destruct v as [bday [obl v]].
    destruct (preasset_marker_dec v) as [Hvm|Hvm].
    * { destruct (hashval_eq_dec h k) as [D1|D1].
        - inversion H3.
          + apply In_hlist_H.
          + subst k.
            assert (L1: u = (bday,(obl,v))).
            { apply (Hf h u (bday,(obl,v))).
              - now right.
              - now left.
            } 
            subst u. apply In_hlist_H.
        - inversion H3.
          + contradiction.
          + change (In_hlist (h, u)
                             (hlistC (k, (bday,(obl,v)))
                                     (hlist_reduce_to_min_support
                                        (remove hashval_eq_dec k inpr) hr))).
            assert (Lf: fnlh hr).
            { intros h' u' v' H5 H6. apply (Hf h' u' v'); now right. }
            assert (L1: forall h : hashval,
                          In h (remove hashval_eq_dec k inpr) ->
                          exists oblu, In_hlist (h, oblu) hr).
            { intros h' H6. apply remove_hashval_iff in H6.
              destruct H6 as [H7 H8].
              apply H1 in H7.
              destruct H7 as [obl'w H9]. inversion H9.
              - exfalso. contradiction (H8 H6).
              - exists obl'w. assumption.
            }
            assert (L2: In h (remove hashval_eq_dec k inpr)).
            { apply remove_hashval_iff. tauto. }
            right.
            exact (hlist_reduce_to_min_support_assets hr (remove hashval_eq_dec k inpr) Lf L1 h u L2 H0).
      }
    * { destruct (hashval_eq_dec h k) as [D1|D1].
        - inversion H3.
          + apply In_hlist_H.
          + subst k.
            assert (L1: u = (bday,(obl,v))).
            { apply (Hf h u (bday,(obl,v))).
              - now right.
              - now left.
            } 
            subst u. apply In_hlist_H.
        - inversion H3.
          + contradiction.
          + change (In_hlist (h, u)
                             (hlistC (k, (bday,(obl,v)))
                                     (hlist_reduce_to_min_support_marker
                                        (remove hashval_eq_dec k inpr) hr))).
            assert (Lf: fnlh hr).
            { intros h' u' v' H5 H6. apply (Hf h' u' v'); now right. }
            assert (L1: forall h : hashval,
                          In h (remove hashval_eq_dec k inpr) ->
                          exists oblu, In_hlist (h, oblu) hr).
            { intros h' H6. apply remove_hashval_iff in H6.
              destruct H6 as [H7 H8].
              apply H1 in H7.
              destruct H7 as [obl'w H9]. inversion H9.
              - exfalso. contradiction (H8 H6).
              - exists obl'w. assumption.
            }
            assert (L2: In h (remove hashval_eq_dec k inpr)).
            { apply remove_hashval_iff. tauto. }
            right.
            exact (IH (remove hashval_eq_dec k inpr) Lf L1 h u L2 H0).
      }
Qed.

Transparent octree_approx_fun_p.
Transparent ctree_supports_asset.

Lemma ctree_supports_assets_min {n} :
  forall (inpl : list (bitseq n * hashval))
         (outpl : list (bitseq n))
         (full :list (bitseq n))
         (markers :list (bitseq n))
         (T : ctree n)
         (f : bitseq n -> list asset),
    (forall h alpha u alpha' u', In (h,u) (f alpha) -> In (h,u') (f alpha') -> alpha = alpha' /\ u = u') ->
    octree_approx_fun_p (Some T) f ->
    (forall (alpha : bitseq n) (h : hashval),
       In (alpha, h) inpl ->
       exists u, ctree_supports_asset (h,u) T alpha) ->
    forall (alpha : bitseq n) (h : hashval),
      In (alpha, h) inpl ->
      exists u, ctree_supports_asset (h,u)
                                     (ctree_reduce_to_min_support inpl outpl full markers T) alpha.
induction n as [|n IH].
- intros inpl outpl full markers [h|[[h [bday [obl u]]] hl]] f Hf2 HTf H1 [] k H2.
  + simpl. exfalso. apply H1 in H2. simpl in H2. destruct H2 as [u H2]. inversion H2.
  + simpl. destruct (hashval_eq_dec k h) as [D1|D1].
    * { destruct inpl as [|[[] k'] inpr].
        - contradiction H2.
        - subst k. exists (bday,(obl,u)). simpl. unfold ctree_supports_asset.
          destruct full; destruct markers; try apply In_hlist_H.
          destruct u; apply In_hlist_H.
      }
    * { destruct inpl as [|[[] k'] inpr].
        - contradiction H2.
        - generalize H2. intros H2a. apply H1 in H2. simpl. simpl in H2. destruct H2 as [v H2]. inversion H2.
          + exists (bday,(obl,u)). destruct full; destruct markers; try apply In_hlist_H.
            destruct u; apply In_hlist_H.
          + simpl. set (inpl := ((tt,k') :: inpr)).
            change (forall (alpha : bitseq 0) k,
                      In (alpha, k) inpl ->
                      exists v, @ctree_supports_asset (k,v) 0 (inr ((h, (bday,(obl,u))), hl)) alpha) in H1.
            destruct full; destruct markers.
            * { change (exists v, In_hlist (k, v)
                                           (hlistC (h, (bday, (obl, u)))
                                                   (hlist_reduce_to_min_support
                                                      (remove hashval_eq_dec h (map (snd (B:=hashval)) inpl))
                                                      hl))).
                assert (Lf: forall h oblu oblv, In_hlist (h,oblu) hl -> In_hlist (h,oblv) hl -> oblu = oblv).
                { intros h' [obl1 u'] [obl2 v'] H4 H5.
                  assert (Lfa:In (h', (obl1, u')) (f tt)).
                  { change (hashassetlist (f tt) = hlist_hashroot (hlistC (h,(bday,(obl,u))) hl)) in HTf.
                    apply (In_hlist_In_assetlist _ _ _ HTf).
                    now right.
                  }
                  assert (Lfb:In (h', (obl2, v')) (f tt)).
                  { change (hashassetlist (f tt) = hlist_hashroot (hlistC (h,(bday,(obl,u))) hl)) in HTf.
                    apply (In_hlist_In_assetlist _ _ _ HTf).
                    now right.
                  }
                  generalize (Hf2 h' tt (obl1,u') tt (obl2,v') Lfa Lfb). tauto.
                }
                assert (L1:forall k : hashval,
                             In k (remove hashval_eq_dec h (map (snd (B:=hashval)) inpl)) ->
                             exists bdayoblv : prod nat (prod obligation preasset), In_hlist (k, bdayoblv) hl).
                { intros h' H4. apply remove_hashval_iff in H4. destruct H4 as [H5 H6].
                  apply in_map_iff in H5. destruct H5 as [[[] h''] [H7 H8]].
                  simpl in H7. subst h''. apply H1 in H8. destruct H8 as [bdayoblv' H9].
                  simpl in H9. inversion H9.
                  - contradiction.
                  - now exists bdayoblv'.
                }
                assert (L2:In k (remove hashval_eq_dec h (map (snd (B:=hashval)) inpl))).
                { apply remove_hashval_iff. split.
                  - apply in_map_iff. exists (tt,k). split.
                    + reflexivity.
                    + exact H2a.
                  - exact D1.
                }
                exists v. right.
                exact (hlist_reduce_to_min_support_assets hl (remove hashval_eq_dec h (map (snd (B:=hashval)) inpl)) Lf L1 k v L2 H0).
              }
            * { destruct (preasset_marker_dec u) as [Hum|Hum].
                - change (exists v, In_hlist (k, v)
                                           (hlistC (h, (bday, (obl, u)))
                                                   (hlist_reduce_to_min_support
                                                      (remove hashval_eq_dec h (map (snd (B:=hashval)) inpl))
                                                      hl))).
                  assert (Lf: forall h oblu oblv, In_hlist (h,oblu) hl -> In_hlist (h,oblv) hl -> oblu = oblv).
                  { intros h' [obl1 u'] [obl2 v'] H4 H5.
                    assert (Lfa:In (h', (obl1, u')) (f tt)).
                    { change (hashassetlist (f tt) = hlist_hashroot (hlistC (h,(bday,(obl,u))) hl)) in HTf.
                      apply (In_hlist_In_assetlist _ _ _ HTf).
                      now right.
                    }
                    assert (Lfb:In (h', (obl2, v')) (f tt)).
                    { change (hashassetlist (f tt) = hlist_hashroot (hlistC (h,(bday,(obl,u))) hl)) in HTf.
                      apply (In_hlist_In_assetlist _ _ _ HTf).
                      now right.
                    }
                    generalize (Hf2 h' tt (obl1,u') tt (obl2,v') Lfa Lfb). tauto.
                  }
                  assert (L1:forall k : hashval,
                               In k (remove hashval_eq_dec h (map (snd (B:=hashval)) inpl)) ->
                               exists bdayoblv : prod nat (prod obligation preasset), In_hlist (k, bdayoblv) hl).
                  { intros h' H4. apply remove_hashval_iff in H4. destruct H4 as [H5 H6].
                    apply in_map_iff in H5. destruct H5 as [[[] h''] [H7 H8]].
                    simpl in H7. subst h''. apply H1 in H8. destruct H8 as [bdayoblv' H9].
                    simpl in H9. inversion H9.
                    - contradiction.
                    - now exists bdayoblv'.
                  }
                  assert (L2:In k (remove hashval_eq_dec h (map (snd (B:=hashval)) inpl))).
                  { apply remove_hashval_iff. split.
                    - apply in_map_iff. exists (tt,k). split.
                      + reflexivity.
                      + exact H2a.
                    - exact D1.
                  }
                  exists v. right.
                  exact (hlist_reduce_to_min_support_assets hl (remove hashval_eq_dec h (map (snd (B:=hashval)) inpl)) Lf L1 k v L2 H0).
                - change (exists v, In_hlist (k, v)
                                           (hlistC (h, (bday, (obl, u)))
                                                   (hlist_reduce_to_min_support_marker
                                                      (remove hashval_eq_dec h (map (snd (B:=hashval)) inpl))
                                                      hl))).
                  assert (Lf: forall h oblu oblv, In_hlist (h,oblu) hl -> In_hlist (h,oblv) hl -> oblu = oblv).
                  { intros h' [obl1 u'] [obl2 v'] H4 H5.
                    assert (Lfa:In (h', (obl1, u')) (f tt)).
                    { change (hashassetlist (f tt) = hlist_hashroot (hlistC (h,(bday,(obl,u))) hl)) in HTf.
                      apply (In_hlist_In_assetlist _ _ _ HTf).
                      now right.
                    }
                    assert (Lfb:In (h', (obl2, v')) (f tt)).
                    { change (hashassetlist (f tt) = hlist_hashroot (hlistC (h,(bday,(obl,u))) hl)) in HTf.
                      apply (In_hlist_In_assetlist _ _ _ HTf).
                      now right.
                    }
                    generalize (Hf2 h' tt (obl1,u') tt (obl2,v') Lfa Lfb). tauto.
                  }
                  assert (L1:forall k : hashval,
                               In k (remove hashval_eq_dec h (map (snd (B:=hashval)) inpl)) ->
                               exists bdayoblv : prod nat (prod obligation preasset), In_hlist (k, bdayoblv) hl).
                  { intros h' H4. apply remove_hashval_iff in H4. destruct H4 as [H5 H6].
                    apply in_map_iff in H5. destruct H5 as [[[] h''] [H7 H8]].
                    simpl in H7. subst h''. apply H1 in H8. destruct H8 as [bdayoblv' H9].
                    simpl in H9. inversion H9.
                    - contradiction.
                    - now exists bdayoblv'.
                  }
                  assert (L2:In k (remove hashval_eq_dec h (map (snd (B:=hashval)) inpl))).
                  { apply remove_hashval_iff. split.
                    - apply in_map_iff. exists (tt,k). split.
                      + reflexivity.
                      + exact H2a.
                    - exact D1.
                  }
                  exists v. right.
                  exact (hlist_reduce_to_min_support_marker_assets hl (remove hashval_eq_dec h (map (snd (B:=hashval)) inpl)) Lf L1 k v L2 H0).
              }
            * exists v. simpl. now apply In_hlist_C.
            * exists v. simpl. now apply In_hlist_C.
      }
- intros inpl outpl full markers [[gamma hl]|[h|[Tl|[Tr|[Tl Tr]]]]] f Hf2 HTf H1 alpha k H2.
  + generalize H2. intros H2a. apply H1 in H2. destruct H2 as [v H2].
    change (if bitseq_eq_dec gamma alpha then
              In_hlist (k,v) (nehlist_hlist hl)
            else
              False) in H2.
    destruct (bitseq_eq_dec gamma alpha) as [D1|D1].
    * { destruct inpl as [|[delta k'] inpr].
        - contradiction H2a.
        - subst gamma. exists v.
          set (inpl := ((delta,k') :: inpr)).
          change (forall (beta : bitseq (S n)) (h : hashval),
                    In (beta, h) inpl ->
                    exists oblu,
                      ctree_supports_asset (h, oblu) (ctreeL hl alpha) beta) in H1.
          destruct hl as [h|[[h u] hl]].
          + inversion H2.
          + change (if bitseq_eq_dec alpha alpha then
                      In_hlist (k,v) (hlistC (h,u) hl)
                    else
                      False).
            destruct (bitseq_eq_dec alpha alpha) as [D1|D1].
            * exact H2.
            * exfalso. apply D1. reflexivity.
      }
    * contradiction H2.
  + exfalso. apply H1 in H2. destruct H2 as [v H2]. simpl in H2.
    contradiction H2.
  + destruct alpha as [[|] alpha].
    * exfalso. apply H1 in H2. destruct H2 as [v H2]. simpl in H2.
      contradiction H2.
    * { generalize H2. intros H2a. apply H1 in H2. destruct H2 as [v H2]. simpl in H2.
        destruct inpl as [|[delta k'] inpr].
        - contradiction H2a.
        - simpl.
          apply (IH (strip_bitseq_false ((delta,k')::inpr)) (strip_bitseq_false0 outpl) (strip_bitseq_false0 full) (strip_bitseq_false0 markers) Tl (fun beta => f(false,beta))).
          + intros h beta u beta' u' H3 H4.
            generalize (Hf2 h (false,beta) u (false,beta') u' H3 H4).
            intros [H5 H6]. inversion H5. tauto.
          + destruct HTf as [HTfL _]. exact HTfL.
          + intros beta h H3.
            apply strip_bitseq_false_iff in H3.
            apply H1 in H3.
            exact H3.
          + apply strip_bitseq_false_iff. exact H2a.
      }
  + destruct alpha as [[|] alpha].
    * { generalize H2. intros H2a. apply H1 in H2. destruct H2 as [v H2]. simpl in H2.
        destruct inpl as [|[delta k'] inpr].
        - contradiction H2a.
        - simpl.
          apply (IH (strip_bitseq_true ((delta,k')::inpr)) (strip_bitseq_true0 outpl) (strip_bitseq_true0 full) (strip_bitseq_true0 markers) Tr (fun beta => f(true,beta))).
          + intros h beta u beta' u' H3 H4.
            generalize (Hf2 h (true,beta) u (true,beta') u' H3 H4).
            intros [H5 H6]. inversion H5. tauto.
          + destruct HTf as [_ HTfR]. exact HTfR.
          + intros beta h H3.
            apply strip_bitseq_true_iff in H3.
            apply H1 in H3.
            exact H3.
          + apply strip_bitseq_true_iff. exact H2a.
      }
    * exfalso. apply H1 in H2. destruct H2 as [v H2]. simpl in H2.
      contradiction H2.
  + destruct alpha as [[|] alpha].
    * { destruct inpl as [|[delta k'] inpr].
        - contradiction H2.
        - (** This case could be a copy of the one above for the ctreeBR case. It's slightly reorganized because I had to track down a bug. ***)
          assert (L1: forall (beta : bitseq n) (h : hashval),
                        In (beta, h) (strip_bitseq_true ((delta, k') :: inpr)) ->
                        exists oblu,
                          ctree_supports_asset (h, oblu)
                                               (ctree_reduce_to_min_support
                                                  (strip_bitseq_true ((delta, k') :: inpr))
                                                  (strip_bitseq_true0 outpl)
                                                  (strip_bitseq_true0 full)
                                                  (strip_bitseq_true0 markers)
                                                  Tr) beta).
          { apply (IH (strip_bitseq_true ((delta,k')::inpr)) (strip_bitseq_true0 outpl) (strip_bitseq_true0 full) (strip_bitseq_true0 markers) Tr (fun beta => f(true,beta))).
            - intros h beta oblu beta' oblu' H3 H4.
              generalize (Hf2 h (true,beta) oblu (true,beta') oblu' H3 H4).
              intros [H5 H6]. inversion H5. tauto.
            - destruct HTf as [_ HTfR]. exact HTfR.
            - intros beta h H3.
              apply strip_bitseq_true_iff in H3.
              apply H1 in H3.
              exact H3.
          }
          assert (L2: In (alpha, k) (strip_bitseq_true ((delta, k') :: inpr))).
          { apply strip_bitseq_true_iff. exact H2. }
          exact (L1 alpha k L2).
      }
    * { generalize H2. intros H2a. apply H1 in H2. destruct H2 as [v H2]. simpl in H2.
        destruct inpl as [|[delta k'] inpr].
        - contradiction H2a.
        - simpl.
          apply (IH (strip_bitseq_false ((delta,k')::inpr)) (strip_bitseq_false0 outpl) (strip_bitseq_false0 full) (strip_bitseq_false0 markers) Tl (fun beta => f(false,beta))).
          + intros h beta u beta' u' H3 H4.
            generalize (Hf2 h (false,beta) u (false,beta') u' H3 H4).
            intros [H5 H6]. inversion H5. tauto.
          + destruct HTf as [HTfL _]. exact HTfL.
          + intros beta h H3.
            apply strip_bitseq_false_iff in H3.
            apply H1 in H3.
            exact H3.
          + apply strip_bitseq_false_iff. exact H2a.
      }
Qed.

Lemma ctree_supports_addrs_min {n} :
  forall (inpl : list (bitseq n * hashval))
         (outpl : list (bitseq n))
         (full : list (bitseq n))
         (markers : list (bitseq n))
         (T : ctree n),
  (forall (alpha : bitseq n),
     In alpha outpl ->
     ctree_supports_addr T alpha) ->
   forall (alpha : bitseq n),
   In alpha outpl ->
   ctree_supports_addr (ctree_reduce_to_min_support inpl outpl full markers T) alpha.
induction n as [|n IH].
- intros inpl outpl full markers hl H1 [] H2. simpl. tauto.
- intros inpl outpl full markers [[gamma hl]|[h|[Tl|[Tr|[Tl Tr]]]]] H1 alpha H2.
  + simpl. generalize H2. intros H2a. apply H1 in H2.
    destruct outpl as [|z outpr].
    * contradiction H2a.
    * assert (L1: ctree_reduce_to_min_support inpl (z :: outpr) full markers (inl (gamma, hl))
                  = ctreeL hl gamma).
      { destruct inpl; reflexivity. }
      change ((fun x => ctree_supports_addr x alpha)
                (ctree_reduce_to_min_support inpl (z :: outpr) full markers (inl (gamma, hl)))).
      rewrite L1. simpl. tauto.
  + exfalso. apply H1 in H2. simpl in H2. contradiction H2.
  + destruct alpha as [[|] alpha].
    * { simpl. destruct outpl as [|z outpr].
        - contradiction H2.
        - destruct inpl as [|y inpr].
          + simpl. tauto.
          + simpl. tauto.
      }
    * { generalize H2. intros H2a. apply H1 in H2.
        simpl in H2.
        destruct outpl as [|z outpr].
        - contradiction H2a.
        - destruct inpl as [|[delta k'] inpr].
          + simpl.
            apply (IH nil (strip_bitseq_false0 (z::outpr)) (strip_bitseq_false0 full) (strip_bitseq_false0 markers) Tl).
            * intros beta H3. apply strip_bitseq_false0_iff in H3.
              exact (H1 (false,beta) H3).
            * apply strip_bitseq_false0_iff. exact H2a.
          + simpl.
            apply (IH (strip_bitseq_false ((delta,k')::inpr)) (strip_bitseq_false0 (z::outpr)) (strip_bitseq_false0 full) (strip_bitseq_false0 markers) Tl).
            * intros beta H3. apply strip_bitseq_false0_iff in H3.
              exact (H1 (false,beta) H3).
            * apply strip_bitseq_false0_iff. exact H2a.
      }
  + destruct alpha as [[|] alpha].
    * { generalize H2. intros H2a. apply H1 in H2.
        simpl in H2.
        destruct outpl as [|z outpr].
        - contradiction H2a.
        - destruct inpl as [|[delta k'] inpr].
          + simpl.
            apply (IH nil (strip_bitseq_true0 (z::outpr)) (strip_bitseq_true0 full) (strip_bitseq_true0 markers) Tr).
            * intros beta H3. apply strip_bitseq_true0_iff in H3.
              exact (H1 (true,beta) H3).
            * apply strip_bitseq_true0_iff. exact H2a.
          + simpl.
            apply (IH (strip_bitseq_true ((delta,k')::inpr)) (strip_bitseq_true0 (z::outpr)) (strip_bitseq_true0 full) (strip_bitseq_true0 markers) Tr).
            * intros beta H3. apply strip_bitseq_true0_iff in H3.
              exact (H1 (true,beta) H3).
            * apply strip_bitseq_true0_iff. exact H2a.
      }
    * { simpl. destruct outpl as [|z outpr].
        - contradiction H2.
        - destruct inpl as [|y inpr].
          + simpl. tauto.
          + simpl. tauto.
      }
  + destruct alpha as [[|] alpha].
    * { generalize H2. intros H2a. apply H1 in H2.
        simpl in H2.
        destruct outpl as [|z outpr].
        - contradiction H2a.
        - destruct inpl as [|[delta k'] inpr].
          + simpl.
            apply (IH nil (strip_bitseq_true0 (z::outpr)) (strip_bitseq_true0 full) (strip_bitseq_true0 markers) Tr).
            * intros beta H3. apply strip_bitseq_true0_iff in H3.
              exact (H1 (true,beta) H3).
            * apply strip_bitseq_true0_iff. exact H2a.
          + simpl.
            apply (IH (strip_bitseq_true ((delta,k')::inpr)) (strip_bitseq_true0 (z::outpr)) (strip_bitseq_true0 full) (strip_bitseq_true0 markers) Tr).
            * intros beta H3. apply strip_bitseq_true0_iff in H3.
              exact (H1 (true,beta) H3).
            * apply strip_bitseq_true0_iff. exact H2a.
      }
    * { generalize H2. intros H2a. apply H1 in H2.
        simpl in H2.
        destruct outpl as [|z outpr].
        - contradiction H2a.
        - destruct inpl as [|[delta k'] inpr].
          + simpl.
            apply (IH nil (strip_bitseq_false0 (z::outpr)) (strip_bitseq_false0 full) (strip_bitseq_false0 markers) Tl).
            * intros beta H3. apply strip_bitseq_false0_iff in H3.
              exact (H1 (false,beta) H3).
            * apply strip_bitseq_false0_iff. exact H2a.
          + simpl.
            apply (IH (strip_bitseq_false ((delta,k')::inpr)) (strip_bitseq_false0 (z::outpr)) (strip_bitseq_false0 full) (strip_bitseq_false0 markers) Tl).
            * intros beta H3. apply strip_bitseq_false0_iff in H3.
              exact (H1 (false,beta) H3).
            * apply strip_bitseq_false0_iff. exact H2a.
      }
Qed.

Lemma ctree_supports_asset_In_statefun (a:asset) {n} :
  forall (T:ctree n) (f:bitseq n -> list asset),
    forall (alpha:bitseq n),
      octree_approx_fun_p (Some T) f ->
      ctree_supports_asset a T alpha -> In a (f alpha).
intros T f alpha H1 H2.
apply ctree_mtree_supports_asset in H2.
revert H2. apply mtree_supports_asset_In_statefun.
exact H1.
Qed.

Lemma ctree_valid_supports_asset_uniq (a1 a2:asset) (T:ctree 162) (alpha:addr) :
  ctree_valid T ->
  ctree_supports_asset a1 T alpha ->
  ctree_supports_asset a2 T alpha ->
  assetid a1 = assetid a2 -> a1 = a2.
intros [f [[_ [Hf2 _]] HTf]] H1 H2 H3.
assert (L1: In a1 (f alpha)).
{ revert H1. apply ctree_supports_asset_In_statefun. exact HTf. }
assert (L2: In a2 (f alpha)).
{ revert H2. apply ctree_supports_asset_In_statefun. exact HTf. }
destruct a1 as [h oblu1].
destruct a2 as [h2 oblu2].
simpl in H3. subst h2.
destruct (Hf2 h alpha oblu1 alpha oblu2 L1 L2) as [_ H4].
congruence.
Qed.

Definition subqneh (hl1 hl2 : nehlist) : Prop :=
match hl1 with
  | inl h1 => h1 = nehlist_hashroot hl2
  | inr (a1,hr1) =>
    match hl2 with
      | inr (a2,hr2) => a1 = a2 /\ subqh hr1 hr2
      | _ => False
    end
end.

Definition subqc {n:nat} (T1 T2 : ctree n) : Prop :=
subqm (ctree_mtree T1) (ctree_mtree T2).

Lemma subqm_singlebranch_mtree_eq {n} (hl1 hl2:nehlist) (gamma1 gamma2:bitseq n) :
  subqm (singlebranch_mtree hl1 gamma1) (singlebranch_mtree hl2 gamma2) ->
  gamma1 = gamma2 /\ subqneh hl1 hl2.
induction n as [|n IH].
- destruct gamma1 as []. destruct gamma2 as [].
  intros H1. split.
  + reflexivity.
  + destruct hl1 as [h1|[a1 hr1]]; destruct hl2 as [h2|[a2 hr2]].
    * simpl in H1. simpl. inversion H1. simpl in H0. inversion H0.
      reflexivity.
    * { simpl in H1. simpl. inversion H1. simpl in H0.
        destruct (hlist_hashroot hr2) as [k|] eqn:H3.
        - inversion H0. simpl. reflexivity.
        - inversion H0. simpl. reflexivity.
      }
    * simpl in H1. inversion H1.
    * { simpl in H1. inversion H1. split.
        - reflexivity.
        - exact H0.
      }
- destruct gamma1 as [[|] gamma1]; destruct gamma2 as [[|] gamma2].
  + simpl. intros [H1 H2].
    destruct (IH gamma1 gamma2 H2) as [IH1 IH2].
    split.
    * congruence.
    * assumption.
  + simpl. intros [H1 H2]. exfalso.
    apply subqm_hashroot_eq in H2.
    rewrite mtree_hashroot_empty in H2.
    destruct (mtree_hashroot (singlebranch_mtree hl1 gamma1)) as [k|] eqn:H3.
    * discriminate H2.
    * revert H3. apply mtree_hashroot_singlebranch_nonempty.
  + simpl. intros [H1 H2]. exfalso.
    apply subqm_hashroot_eq in H1.
    rewrite mtree_hashroot_empty in H1.
    destruct (mtree_hashroot (singlebranch_mtree hl1 gamma1)) as [k|] eqn:H3.
    * discriminate H1.
    * revert H3. apply mtree_hashroot_singlebranch_nonempty.
  + simpl. intros [H1 H2].
    destruct (IH gamma1 gamma2 H1) as [IH1 IH2].
    split.
    * congruence.
    * assumption.
Qed.

Lemma subqc_supports_addr {n} (T1 T2:ctree n) (alpha:bitseq n) :
  subqc T1 T2
  -> ctree_supports_addr T1 alpha
  -> ctree_supports_addr T2 alpha.
intros H1 H2.
apply ctree_mtree_supports_addr in H2.
apply mtree_ctree_supports_addr.
revert H1 H2. apply subqm_supports_addr.
Qed.

Lemma subqc_supports_asset (a:asset) {n} (T1 T2:ctree n) (alpha:bitseq n) :
  subqc T1 T2
  -> ctree_supports_asset a T1 alpha
  -> ctree_supports_asset a T2 alpha.
intros H1 H2.
apply mtree_ctree_supports_asset.
apply (subqm_supports_asset _ _ _ _ H1).
apply ctree_mtree_supports_asset.
exact H2.
Qed.

Lemma subqc_full_approx_addr {n} (T1 T2:ctree n) (alpha:bitseq n) :
  subqc T1 T2
  -> ctree_full_approx_addr T1 alpha
  -> ctree_full_approx_addr T2 alpha.
intros H1 H2.
apply mtree_ctree_full_approx_addr.
apply (subqm_full_approx_addr _ _ _ H1).
apply ctree_mtree_full_approx_addr.
exact H2.
Qed.

Lemma subqc_asset_value_in T1 T2 inpl utot :
  subqc T1 T2 ->
  ctree_asset_value_in T1 inpl utot ->
  ctree_asset_value_in T2 inpl utot.
intros H1 H2. induction H2 as [|h a u inpl alpha v H2 IH H3|h a inpl alpha v H2 IH H3 H3'].
- apply ctree_asset_value_in_nil.
- apply ctree_asset_value_in_cons with (a := a).
  + exact IH.
  + revert H3. apply subqc_supports_asset. exact H1.
  + assumption.
  + assumption.
- apply ctree_asset_value_in_skip with (a := a).
  + exact IH.
  + revert H3. apply subqc_supports_asset. exact H1.
  + exact H3'.
  + assumption.
Qed.

Lemma subqc_rights_consumed (T1 T2:ctree 162) (b:bool) (alpha:termaddr) (inpl:list addr_assetid) (utot:nat) :
  subqc T1 T2
  -> ctree_rights_consumed b alpha T1 inpl utot
  -> ctree_rights_consumed b alpha T2 inpl utot.
intros H1 H2. induction H2 as [|beta h inpr r1 bday obl r2 H2 IH H3|beta h inpr r1 bday obl u H2 IH H3].
- apply ctree_rights_consumed_nil.
- apply ctree_rights_consumed_cons with (bday := bday) (obl := obl).
  + exact IH.
  + revert H3. apply subqc_supports_asset. exact H1.
- apply ctree_rights_consumed_skip with (bday := bday) (obl := obl) (u := u).
  + exact IH.
  + revert H3. apply subqc_supports_asset. exact H1.
  + assumption.
Qed.

Lemma mtree_hashroot_ctree_hashroot_L {n:nat} (gamma : bitseq n) (hl:nehlist) k :
  mtree_hashroot (singlebranch_mtree hl gamma) = Some k ->
  ctree_hashroot (ctreeL hl gamma) = k.
revert k. induction n as [|n IH]; intros k.
- simpl. destruct hl as [h|[h hr]].
  + simpl. intros H1. inversion H1. reflexivity.
  + simpl. destruct (hlist_hashroot hr) as [k'|] eqn: E1.
    * intros H1. inversion H1. reflexivity.
    * intros H1. inversion H1. reflexivity.
- destruct gamma as [[|] gamma].
  + simpl. rewrite mtree_hashroot_empty. simpl.
    destruct (mtree_hashroot (singlebranch_mtree hl gamma)) as [k''|] eqn: E2.
    * intros H1. inversion H1. f_equal.
      apply (IH gamma k'').
      exact E2.
    * discriminate.
  + simpl. rewrite mtree_hashroot_empty. simpl.
    destruct (mtree_hashroot (singlebranch_mtree hl gamma)) as [k''|] eqn: E2.
    * intros H1. inversion H1. f_equal.
      apply (IH gamma k'').
      exact E2.
    * discriminate.
Qed.

Lemma mtree_hashroot_ctree_hashroot {n} (T:ctree n) :
  mtree_hashroot (ctree_mtree T) = Some (ctree_hashroot T).
induction n as [|n IH].
- destruct T as [h|[[h u] hl]].
  + simpl. reflexivity.
  + simpl. destruct (hlist_hashroot hl) as [k|].
    * simpl. reflexivity.
    * simpl. reflexivity.
- destruct T as [[[[|] gamma] hl]|[h|[Tl|[Tr|[Tl Tr]]]]].
  + simpl. rewrite mtree_hashroot_empty. simpl.
    destruct (mtree_hashroot (singlebranch_mtree hl gamma)) as [k|] eqn: E1.
    * f_equal. f_equal. symmetry. apply mtree_hashroot_ctree_hashroot_L. exact E1.
    * exfalso. revert E1. apply mtree_hashroot_singlebranch_nonempty.
  + simpl. rewrite mtree_hashroot_empty. simpl.
    destruct (mtree_hashroot (singlebranch_mtree hl gamma)) as [k|] eqn: E1.
    * unfold hashopair. f_equal. f_equal.
      symmetry. apply mtree_hashroot_ctree_hashroot_L. exact E1.
    * exfalso. revert E1. apply mtree_hashroot_singlebranch_nonempty.
  + simpl. reflexivity.
  + simpl. rewrite mtree_hashroot_empty. unfold hashopair.
    rewrite IH. reflexivity.
  + simpl. rewrite mtree_hashroot_empty. simpl.
    rewrite IH. reflexivity.
  + simpl. rewrite IH. rewrite IH. reflexivity.
Qed.

Lemma subqm_ctree_mtree_nonempty_1 {n} (T:ctree n) :
  ~ subqm (ctree_mtree T) (empty_mtree n).
intros H1. apply subqm_hashroot_eq in H1.
rewrite mtree_hashroot_ctree_hashroot in H1.
rewrite mtree_hashroot_empty in H1.
discriminate H1.
Qed.

Lemma subqm_ctree_mtree_nonempty_2 {n} (T:ctree n) :
  ~ subqm (empty_mtree n) (ctree_mtree T).
intros H1. apply subqm_hashroot_eq in H1.
rewrite mtree_hashroot_ctree_hashroot in H1.
rewrite mtree_hashroot_empty in H1.
discriminate H1.
Qed.

Lemma ctreeL_supports_asset (a:asset) {n} (hl:nehlist) (alpha:bitseq n) :
  In_hlist a (nehlist_hlist hl) ->
  ctree_supports_asset a (ctreeL hl alpha) alpha.
intros H1. destruct n as [|n].
- exact H1.
- change (if bitseq_eq_dec alpha alpha then
            In_hlist a (nehlist_hlist hl)
          else
            False).
  destruct (bitseq_eq_dec alpha alpha) as [D|D].
  + exact H1.
  + apply D. reflexivity.
Qed.

Lemma ctreeL_supports_asset_conv (a:asset) {n} (hl:nehlist) (gamma alpha:bitseq n) :
   ctree_supports_asset a (ctreeL hl gamma) alpha ->
   gamma = alpha /\ In_hlist a (nehlist_hlist hl).
intros H1. induction n as [|n IH].
- simpl in H1. destruct gamma as []. destruct alpha as [].
  tauto.
- destruct gamma as [[|] gamma]; destruct alpha as [[|] alpha].
  + simpl.
    assert (L1: ctree_supports_asset a (ctreeL hl gamma) alpha).
    { change (if @bitseq_eq_dec (S n) (true,gamma) (true,alpha) then
                In_hlist a (nehlist_hlist hl)
              else
                False) in H1.
      destruct (@bitseq_eq_dec (S n) (true,gamma) (true,alpha)) as [D1|D1].
      - destruct n as [|n].
        + change (In_hlist a (nehlist_hlist hl)).
          exact H1.
        + change (if bitseq_eq_dec gamma alpha then
                    In_hlist a (nehlist_hlist hl)
                  else
                    False).
          destruct (bitseq_eq_dec gamma alpha) as [D2|D2].
          * exact H1.
          * congruence.
      - contradiction H1.
    }
    destruct (IH gamma alpha L1) as [IH1 IH2]. subst gamma. tauto.
  + exfalso. revert H1. simpl. tauto.
  + exfalso. revert H1. simpl. tauto.
  + simpl.
    assert (L1: ctree_supports_asset a (ctreeL hl gamma) alpha).
    { change (if @bitseq_eq_dec (S n) (false,gamma) (false,alpha) then
                In_hlist a (nehlist_hlist hl)
              else
                False) in H1.
      destruct (@bitseq_eq_dec (S n) (false,gamma) (false,alpha)) as [D1|D1].
      - destruct n as [|n].
        + change (In_hlist a (nehlist_hlist hl)).
          exact H1.
        + change (if bitseq_eq_dec gamma alpha then
                    In_hlist a (nehlist_hlist hl)
                  else
                    False).
          destruct (bitseq_eq_dec gamma alpha) as [D2|D2].
          * exact H1.
          * congruence.
      - contradiction H1.
    }
    destruct (IH gamma alpha L1) as [IH1 IH2]. subst gamma. tauto.
Qed.

Lemma subqm_singlebranch_ctreeL_1 (hl hl':nehlist) {n} (beta gamma:bitseq n) :
  subqm (singlebranch_mtree hl gamma) (ctree_mtree (ctreeL hl' beta))
  ->
  beta = gamma /\ subqneh hl hl'.
destruct n as [|n].
- intros H1. destruct beta as []. destruct gamma as []. split.
  + reflexivity.
  + destruct hl as [h|[h hl]]; destruct hl' as [h'|[h' hl']]; simpl; simpl in H1.
    * inversion H1. simpl in H0. inversion H0. reflexivity.
    * { inversion H1. simpl in H0. destruct (hlist_hashroot hl') as [k'|].
        - inversion H0. reflexivity.
        - inversion H0. reflexivity.
      }
    * inversion H1.
    * inversion H1. tauto.
- destruct beta as [[|] beta]; destruct gamma as [[|] gamma].
  + intros [H1 H2]. apply subqm_singlebranch_mtree_eq in H2.
    destruct H2 as [H3 H4]. split.
    * congruence.
    * exact H4.
  + intros [H1 H2]. exfalso.
    apply subqm_hashroot_eq in H1.
    rewrite mtree_hashroot_empty in H1. revert H1.
    apply mtree_hashroot_singlebranch_nonempty.
  + intros [H1 H2]. exfalso.
    apply subqm_hashroot_eq in H2.
    rewrite mtree_hashroot_empty in H2. revert H2.
    apply mtree_hashroot_singlebranch_nonempty.
  + intros [H1 H2]. apply subqm_singlebranch_mtree_eq in H1.
    destruct H1 as [H3 H4]. split.
    * congruence.
    * exact H4.
Qed.

Lemma subqm_singlebranch_ctreeL_2 (hl hl':nehlist) {n} (beta gamma:bitseq n) :
  subqm (ctree_mtree (ctreeL hl' beta)) (singlebranch_mtree hl gamma)
  ->
  beta = gamma /\ subqneh hl' hl.
destruct n as [|n].
- intros H1. destruct beta as []. destruct gamma as []. split.
  + reflexivity.
  + destruct hl as [h|[h hl]]; destruct hl' as [h'|[h' hl']]; simpl; simpl in H1.
    * inversion H1. simpl in H0. inversion H0. reflexivity.
    * inversion H1.
    * { inversion H1. simpl in H0. destruct (hlist_hashroot hl) as [k|].
        - inversion H0. reflexivity.
        - inversion H0. reflexivity.
      }
    * inversion H1. tauto.
- destruct beta as [[|] beta]; destruct gamma as [[|] gamma].
  + intros [H1 H2]. apply subqm_singlebranch_mtree_eq in H2.
    destruct H2 as [H3 H4]. split.
    * congruence.
    * exact H4.
  + intros [H1 H2]. exfalso.
    apply subqm_hashroot_eq in H2.
    rewrite mtree_hashroot_empty in H2. revert H2.
    apply mtree_hashroot_singlebranch_nonempty.
  + intros [H1 H2]. exfalso.
    apply subqm_hashroot_eq in H1.
    rewrite mtree_hashroot_empty in H1. revert H1.
    apply mtree_hashroot_singlebranch_nonempty.
  + intros [H1 H2]. apply subqm_singlebranch_mtree_eq in H1.
    destruct H1 as [H3 H4]. split.
    * congruence.
    * exact H4.
Qed.

Lemma subqneh_full_approx_In_conv (a:asset) (hl1 hl2:nehlist) :
  subqneh hl1 hl2 ->
  nehlist_full_approx hl1 ->
  In_hlist a (nehlist_hlist hl2) ->
  In_hlist a (nehlist_hlist hl1).
destruct hl1 as [h1|[h1 hl1]]; destruct hl2 as [h2|[h2 hl2]].
- simpl. tauto.
- simpl. tauto.
- simpl. tauto.
- simpl. intros [H1 H2] H3.
  apply subqh_full_approx_In_conv.
  + subst h2. apply subqhC. exact H2.
  + exact H3.
Qed.

Lemma subqc_full_approx_supports_asset_conv_single_1 (a:asset) (hl:nehlist) {n} (T:ctree n) (gamma alpha:bitseq n) :
  subqm (singlebranch_mtree hl gamma) (ctree_mtree T) ->
  ctree_supports_asset a T alpha ->
  alpha = gamma.
induction n as [|n IH].
- destruct gamma as []. destruct alpha as []. tauto.
- destruct T as [[beta hr]|[h|[Tl|[Tr|[Tl Tr]]]]].
  + intros H1 H2.
    destruct (ctreeL_supports_asset_conv _ _ _ _ H2) as [H3 H4].
    change (subqm (singlebranch_mtree hl gamma) (ctree_mtree (ctreeL hr beta))) in H1.
    apply subqm_singlebranch_ctreeL_1 in H1.
    destruct H1 as [H1a H1b].
    congruence.
  + intros H1 H2. simpl in H1. destruct gamma as [[|] gamma]; contradiction H1.
  + destruct gamma as [[|] gamma]; destruct alpha as [[|] alpha]; try (simpl; tauto).
    * intros [H1 _]. exfalso. revert H1. apply subqm_ctree_mtree_nonempty_2.
    * intros [H1 _] H2.
      change (ctree_supports_asset a Tl alpha) in H2.
      generalize (IH Tl gamma alpha H1 H2). congruence.
  + destruct gamma as [[|] gamma]; destruct alpha as [[|] alpha]; try (simpl; tauto).
    * intros [_ H1] H2.
      change (ctree_supports_asset a Tr alpha) in H2.
      generalize (IH Tr gamma alpha H1 H2). congruence.
    * intros [_ H1]. exfalso. revert H1. apply subqm_ctree_mtree_nonempty_2.
  + destruct gamma as [[|] gamma]; destruct alpha as [[|] alpha].
    * intros [_ H1] H2.
      change (ctree_supports_asset a Tr alpha) in H2.
      generalize (IH Tr gamma alpha H1 H2). congruence.
    * intros [H1 _]. exfalso. revert H1. apply subqm_ctree_mtree_nonempty_2.
    * intros [_ H1]. exfalso. revert H1. apply subqm_ctree_mtree_nonempty_2.
    * intros [H1 _] H2.
      change (ctree_supports_asset a Tl alpha) in H2.
      generalize (IH Tl gamma alpha H1 H2). congruence.
Qed.

Lemma subqc_full_approx_supports_asset_conv_single_2 (a:asset) (hl:nehlist) {n} (T:ctree n) (alpha:bitseq n) :
  subqm (singlebranch_mtree hl alpha) (ctree_mtree T) ->
  nehlist_full_approx hl ->
  ctree_supports_asset a T alpha ->
  In_hlist a (nehlist_hlist hl).
induction n as [|n IH].
- destruct alpha as []. destruct hl as [h|[h hl]].
  + simpl. tauto.
  + simpl. intros H1 H2 H3.
    apply subqh_full_approx_In_conv with (hl2 := nehlist_hlist T).
    * exact H1.
    * exact H2.
    * exact H3.
- destruct T as [[beta hr]|[h|[Tl|[Tr|[Tl Tr]]]]].
  + intros H1 H2 H3.
    destruct (ctreeL_supports_asset_conv _ _ _ _ H3) as [H4 H5].
    change (subqm (singlebranch_mtree hl alpha) (ctree_mtree (ctreeL hr beta))) in H1.
    apply subqm_singlebranch_ctreeL_1 in H1.
    destruct H1 as [H1a H1b].
    revert H1b H2 H5. apply subqneh_full_approx_In_conv.
  + intros H1 H2 H3. simpl in H1. destruct alpha as [[|] alpha]; contradiction H1.
  + destruct alpha as [[|] alpha]; try (simpl; tauto).
    intros [H1 _] H2 H3.
    change (ctree_supports_asset a Tl alpha) in H3.
    exact (IH Tl alpha H1 H2 H3).
  + destruct alpha as [[|] alpha]; try (simpl; tauto).
    intros [_ H1] H2 H3.
    change (ctree_supports_asset a Tr alpha) in H3.
    exact (IH Tr alpha H1 H2 H3).
  + destruct alpha as [[|] alpha].
    * intros [_ H1] H2 H3.
      change (ctree_supports_asset a Tr alpha) in H3.
      exact (IH Tr alpha H1 H2 H3).
    * intros [H1 _] H2 H3.
      change (ctree_supports_asset a Tl alpha) in H3.
      exact (IH Tl alpha H1 H2 H3).
Qed.

Lemma subqc_full_approx_supports_asset_conv (a:asset) {n} (T1 T2:ctree n) (alpha:bitseq n) :
  subqc T1 T2 ->
  ctree_full_approx_addr T1 alpha ->
  ctree_supports_asset a T2 alpha ->
  ctree_supports_asset a T1 alpha.
induction n as [|n IH].
- destruct T1 as [h1|[h1 hl1]].
  + simpl. tauto.
  + destruct T2 as [h2|[h2 hl2]].
    * simpl. intros H1 H2 H3. inversion H3.
    * { simpl. intros H1 H2 H3. inversion H3.
        - inversion H1. apply In_hlist_H.
        - apply In_hlist_C. revert H2 H0. apply subqh_full_approx_In_conv.
          inversion H1. assumption.
      }
- destruct T1 as [[gamma1 hl1]|[h1|[T1l|[T1r|[T1l T1r]]]]].
  + intros H1 H2 H3.
    change (subqm (singlebranch_mtree hl1 gamma1) (ctree_mtree T2)) in H1.
    change (if bitseq_eq_dec gamma1 alpha then
              nehlist_full_approx hl1
            else
              True) in H2.
    change (if bitseq_eq_dec gamma1 alpha then
              In_hlist a (nehlist_hlist hl1)
            else
              False).
    destruct (bitseq_eq_dec gamma1 alpha) as [D1|D1].
    * subst gamma1.
      exact (subqc_full_approx_supports_asset_conv_single_2 _ _ _ _ H1 H2 H3).
    * generalize (subqc_full_approx_supports_asset_conv_single_1 _ _ _ _ _ H1 H3).
      congruence.
  + simpl. tauto.
  + destruct T2 as [[gamma2 hl2]|[h2|[T2l|[T2r|[T2l T2r]]]]].
    * { intros H1 H2 H3.
        change (if bitseq_eq_dec gamma2 alpha then
                  In_hlist a (nehlist_hlist hl2)
                else
                  False) in H3.
        destruct (bitseq_eq_dec gamma2 alpha) as [D1|D1]; try contradiction H3.
        subst gamma2.
        destruct alpha as [[|] alpha].
        - destruct H1 as [H1a H1b]. exfalso. revert H1a. apply subqm_ctree_mtree_nonempty_1.
        - destruct H1 as [H1a H1b].
          change (ctree_supports_asset a T1l alpha).
          apply (IH T1l (ctreeL hl2 alpha) alpha).
          + destruct n; exact H1a.
          + exact H2.
          + apply ctreeL_supports_asset. exact H3.
      }
    * simpl. tauto.
    * { intros [H1a H1b]. destruct alpha as [[|] alpha].
        - simpl. tauto.
        - simpl. apply IH. exact H1a.
      }
    * intros [H1a H1b]. exfalso. revert H1a. apply subqm_ctree_mtree_nonempty_1.
    * intros [H1a H1b]. exfalso. revert H1b. apply subqm_ctree_mtree_nonempty_2.
  + destruct T2 as [[gamma2 hl2]|[h2|[T2l|[T2r|[T2l T2r]]]]].
    * { intros H1 H2 H3.
        change (if bitseq_eq_dec gamma2 alpha then
                  In_hlist a (nehlist_hlist hl2)
                else
                  False) in H3.
        destruct (bitseq_eq_dec gamma2 alpha) as [D1|D1]; try contradiction H3.
        subst gamma2.
        destruct alpha as [[|] alpha].
        - destruct H1 as [H1a H1b].
          change (ctree_supports_asset a T1r alpha).
          apply (IH T1r (ctreeL hl2 alpha) alpha).
          + destruct n; exact H1b.
          + exact H2.
          + apply ctreeL_supports_asset. exact H3.
        - destruct H1 as [H1a H1b]. exfalso. revert H1b. apply subqm_ctree_mtree_nonempty_1.
      }
    * simpl. tauto.
    * intros [H1a H1b]. exfalso. revert H1b. apply subqm_ctree_mtree_nonempty_1.
    * { intros [H1a H1b]. destruct alpha as [[|] alpha].
        - simpl. apply IH. exact H1b.
        - simpl. tauto.
      }
    * intros [H1a H1b]. exfalso. revert H1a. apply subqm_ctree_mtree_nonempty_2.
  + destruct T2 as [[gamma2 hl2]|[h2|[T2l|[T2r|[T2l T2r]]]]].
    * { intros H1 H2 H3.
        change (if bitseq_eq_dec gamma2 alpha then
                  In_hlist a (nehlist_hlist hl2)
                else
                  False) in H3.
        destruct (bitseq_eq_dec gamma2 alpha) as [D1|D1]; try contradiction H3.
        subst gamma2.
        destruct alpha as [[|] alpha].
        - destruct H1 as [H1a H1b]. exfalso. revert H1a. apply subqm_ctree_mtree_nonempty_1.
        - destruct H1 as [H1a H1b]. exfalso. revert H1b. apply subqm_ctree_mtree_nonempty_1.
      }
    * simpl. tauto.
    * intros [H1a H1b]. exfalso. revert H1b. apply subqm_ctree_mtree_nonempty_1.
    * intros [H1a H1b]. exfalso. revert H1a. apply subqm_ctree_mtree_nonempty_1.
    * { intros [H1a H1b]. destruct alpha as [[|] alpha].
        - simpl. apply IH. exact H1b.
        - simpl. apply IH. exact H1a.
      }
Qed.

Opaque ctree_supports_asset.

Lemma subqc_lookup_stp (T1 T2:ctree 162) h a :
  subqc T1 T2 ->
  ctree_lookup_stp T1 h a ->
  ctree_lookup_stp T2 h a.
unfold ctree_lookup_stp. intros H1 [k [bday [obl H2]]].
exists k. exists bday. exists obl. revert H2.
apply subqc_supports_asset. exact H1.
Qed.

Lemma subqc_lookup_known (T1 T2:ctree 162) h :
  subqc T1 T2 ->
  ctree_lookup_known T1 h ->
  ctree_lookup_known T2 h.
unfold ctree_lookup_stp. intros H1 [k [bday [obl H2]]].
exists k. exists bday. exists obl. revert H2.
apply subqc_supports_asset. exact H1.
Qed.

Lemma subqc_check_signaspec_p (T1 T2:ctree 162) tht sigt th d :
  subqc T1 T2 ->
  check_signaspec_p (ctree_lookup_stp T1) (ctree_lookup_known T1) tht sigt th d ->
  check_signaspec_p (ctree_lookup_stp T2) (ctree_lookup_known T2) tht sigt th d.
intros H1. apply check_signaspec_p_subq.
- intros h a. revert H1. apply subqc_lookup_stp.
- intros h. revert H1. apply subqc_lookup_known.
Qed.

Lemma subqc_check_doc_p (T1 T2:ctree 162) tht sigt th d :
  subqc T1 T2 ->
  check_doc_p (ctree_lookup_stp T1) (ctree_lookup_known T1) tht sigt th d ->
  check_doc_p (ctree_lookup_stp T2) (ctree_lookup_known T2) tht sigt th d.
intros H1. apply check_doc_p_subq.
- intros h a. revert H1. apply subqc_lookup_stp.
- intros h. revert H1. apply subqc_lookup_known.
Qed.

Theorem subqc_supports_tx tht sigt m tx (T1 T2:ctree 162) fee rew :
  ctree_valid T2 ->
  subqc T1 T2 ->
  ctree_supports_tx tht sigt m tx T1 fee rew ->
  ctree_supports_tx tht sigt m tx T2 fee rew.
intros HTvalid. generalize HTvalid. intros [f [Hf HTf]] H0 Hs.
generalize Hs. intros [Hs1 [[utot [Hs2 Hs3]] [[Hs4a Hs4b] [[Hs5a [Hs5b Hs5c]] [Hs6 [Hs7 Hs8]]]]]].
apply ctree_supports_tx_can_support in Hs.
destruct Hs as [Hc1 [Hc2 [Hc3 [Hc4 Hc5]]]].
split.
- intros alpha u H5. generalize (Hs1 alpha u H5).
  apply subqc_supports_addr. exact H0.
- split.
  + exists utot. split.
    * revert H0 Hs2. apply subqc_asset_value_in.
    * exact Hs3.
  + split.
    * { split.
        - intros alpha b H1.
          destruct (Hs4a alpha b H1) as [H2 [H3 H4]].
          split.
          + revert H0 H2. apply subqc_full_approx_addr.
          + split.
            * intros [h' [bday' [obl' [beta' H5]]]].
              apply H3. exists h'. exists bday'. exists obl'. exists beta'.
              revert H0 H2 H5. apply subqc_full_approx_supports_asset_conv.
            * { intros rtot1 rtot2 h bday obl beta u H5 H6 H7.
                assert (L1: ctree_supports_asset (h, (bday,(obl, owns b beta (Some u)))) T1 (termaddr_addr alpha)).
                { revert H0 H2 H6. apply subqc_full_approx_supports_asset_conv. }
                destruct (H4 rtot1 rtot2 h bday obl beta u H5 L1 H7) as [rtot3 [rtot4 [H8 [H9 H10]]]].
                exists rtot3. exists rtot4.
                repeat split.
                - revert H0 H8. apply subqc_rights_consumed.
                - exact H9.
                - exact H10.
              }
        - intros alpha b beta h bday obl n H1 H2.
          assert (L1: ctree_supports_asset (h, (bday,(obl, rights b n alpha))) T1 beta).
          { destruct (Hc1 _ _ H1) as [[bday' [obl' v]] H3].
            generalize (subqc_supports_asset _ T1 T2 beta H0 H3).
            intros H4.
            assert (L1a: (h, (bday', (obl', v))) = (h, (bday, (obl, rights b n alpha)))).
            { apply (ctree_valid_supports_asset_uniq _ _ T2 beta HTvalid H4 H2).
              reflexivity.
            }
            inversion L1a. subst bday'. subst obl'. subst v. exact H3.
          }
          revert H1 L1. apply Hs4b.
      }
    * { split; [split; [|split]|].
        - intros obl gamma nonce d alpha H1.
          destruct (Hs5a obl gamma nonce d alpha H1) as [Hch [beta [h [bday' [obl' [H2 [H3 [H4 H5]]]]]]]].
          split.
          + exact Hch.
          + exists beta. exists h. exists bday'. exists obl'. repeat split.
            * exact H2.
            * exact H3.
            * exact H4.
            * revert H0 H5. apply subqc_supports_asset.
        - intros obl gamma nonce th d alpha H1.
          destruct (Hs5b obl gamma nonce th d alpha H1) as [Hch [beta [h [bday' [obl' [H2 [H3 [H4 H5]]]]]]]].
          split.
          + revert Hch. apply subqc_check_signaspec_p. exact H0.
          + exists beta. exists h. exists bday'. exists obl'. repeat split.
            * exact H2.
            * exact H3.
            * exact H4.
            * revert H0 H5. apply subqc_supports_asset.
        - intros obl gamma nonce th d alpha H1.
          destruct (Hs5c obl gamma nonce th d alpha H1) as [Hch [beta [h [bday' [obl' [H2 [H3 [H4 H5]]]]]]]].
          split.
          + revert Hch. apply subqc_check_doc_p. exact H0.
          + exists beta. exists h. exists bday'. exists obl'. repeat split.
            * exact H2.
            * exact H3.
            * exact H4.
            * revert H0 H5. apply subqc_supports_asset.
        - split.
          + intros alpha b obl beta r H1.
            destruct (Hs6 alpha b obl beta r H1) as [H2 H3].
            split.
            * revert H0 H2. apply subqc_full_approx_addr.
            * { destruct H3 as [[h [beta' [bday' [obl' [r' [H4 H5]]]]]]|[H4 H5]].
                - left. exists h. exists beta'. exists bday'. exists obl'. exists r'.
                  split.
                  + revert H0 H4. apply subqc_supports_asset.
                  + exact H5.
                - right. split.
                  + intros [h [beta' [bday' [obl' [r' H6]]]]].
                    apply H4. exists h. exists beta'. exists bday'. exists obl'. exists r'.
                    revert H0 H2 H6. apply subqc_full_approx_supports_asset_conv.
                  + exact H5.
              }
          + split.
            * { intros k1 k2 b H1. destruct (Hs7 k1 k2 b H1) as [H2 H3]. split.
                - revert H0 H2. apply subqc_full_approx_addr.
                - intros H4. apply H3. intros [h' [beta' [bday' [obl' [r' H5]]]]].
                  apply H4. exists h'. exists beta'. exists bday'. exists obl'. exists r'.
                  revert H0 H5. apply subqc_supports_asset.
              }
            * { intros alpha h bday obl u H1 H2.
                generalize H1. intros H1a.
                apply Hc1 in H1a.
                destruct H1a as [[bday' [obl' v]] H3].
                generalize (subqc_supports_asset _ T1 T2 alpha H0 H3).
                intros H4.
                assert (L1: (h, (bday',(obl', v))) = (h, (bday,(obl, bounty u)))).
                { apply (ctree_valid_supports_asset_uniq _ _ T2 alpha HTvalid H4 H2).
                  reflexivity.
                }
                inversion L1.
                subst bday'. subst obl'. subst v.
                destruct (Hs8 alpha h bday obl u H1 H3) as [H6 [h' [bday' [obl' [beta [r [H7 [H8 H9]]]]]]]].
                split.
                - revert H0 H6. apply subqc_full_approx_addr.
                - exists h'. exists bday'. exists obl'. exists beta. exists r. repeat split.
                  + exact H7.
                  + revert H0 H8. apply subqc_supports_asset.
                  + exact H9.
              }
      }
Qed.

Lemma subqh_hlist_reduce_to_min_support aidl hl :
   subqh (hlist_reduce_to_min_support aidl hl) hl.
revert aidl. induction hl as [h| |[h u] hr IH]; intros aidl.
- simpl. destruct aidl; apply subqh_ref.
- simpl. destruct aidl; apply subqh_ref.
- simpl. destruct aidl as [|k aidr].
  + destruct (hlist_hashroot hr) as [k'|] eqn: H1.
    * apply subqhH. simpl. rewrite H1. reflexivity.
    * apply subqhH. simpl. rewrite H1. reflexivity.
  + simpl. apply subqhC. apply IH.
Qed.

Lemma subqh_hlist_reduce_to_min_support_marker aidl hl :
   subqh (hlist_reduce_to_min_support_marker aidl hl) hl.
revert aidl. induction hl as [h| |[h [bday [obl u]]] hr IH]; intros aidl.
- simpl. destruct aidl; apply subqh_ref.
- simpl. destruct aidl; apply subqh_ref.
- simpl. destruct (preasset_marker_dec u) as [Hum|Hum].
  + apply subqhC. apply subqh_hlist_reduce_to_min_support.
  + apply subqhC. apply IH.
Qed.

Lemma subqneh_hashroot_eq hl1 hl2 : subqneh hl1 hl2 -> nehlist_hashroot hl1 = nehlist_hashroot hl2.
destruct hl1 as [h1|[a1 hr1]]; simpl.
- tauto.
- destruct hl2 as [h2|[a2 hr2]]; simpl.
  + tauto.
  + intros [H1 H2].
    change ((fun hr a => match hr with
               | Some k => hashpair (hashnat 4) (hashpair (hashasset a) k)
               | None => hashpair (hashnat 3) (hashasset a)
             end) (hlist_hashroot hr1) a1 =
            (fun hr a => match hr with
               | Some k => hashpair (hashnat 4) (hashpair (hashasset a) k)
               | None => hashpair (hashnat 3) (hashasset a)
             end) (hlist_hashroot hr2) a2).
    set (f := (fun hr a => match hr with
               | Some k => hashpair (hashnat 4) (hashpair (hashasset a) k)
               | None => hashpair (hashnat 3) (hashasset a)
             end)).
    f_equal.
    * revert H2. apply subqh_hashroot_eq.
    * assumption.
Qed.

Lemma subqc_hashroot_eq {n} (T1 T2:ctree n) : subqc T1 T2 -> ctree_hashroot T1 = ctree_hashroot T2.
intros H1.
generalize (mtree_hashroot_ctree_hashroot T1). intros H2.
generalize (mtree_hashroot_ctree_hashroot T2). intros H3.
unfold subqc in H1.
apply subqm_hashroot_eq in H1.
congruence.
Qed.

Lemma subqc_ctree_reduce_to_min_support {n} inpl outpl full markers (T:ctree n) :
   subqc (ctree_reduce_to_min_support inpl outpl full markers T) T.
induction n as [|n IH].
- destruct T as [h|[[h [bday [obl u]]] hl]].
  + simpl. destruct full; apply subqm_ref.
  + simpl. destruct inpl as [|z inpr].
    * { unfold subqc. simpl. destruct full; destruct markers.
        - apply subqhH.
          simpl. destruct (hlist_hashroot hl) as [k|].
          + simpl. reflexivity.
          + simpl. reflexivity.
        - destruct (preasset_marker_dec u) as [Hum|Hum].
          + simpl. apply subqhC. apply subqh_hlist_reduce_to_min_support.
          + simpl. apply subqhC. apply subqh_hlist_reduce_to_min_support_marker.
        - simpl. apply subqh_ref.
        - simpl. apply subqh_ref.
      }
    * { destruct full; destruct markers.
        - apply subqhC. apply subqh_hlist_reduce_to_min_support.
        - destruct (preasset_marker_dec u) as [Hum|Hum].
          + simpl. apply subqhC. apply subqh_hlist_reduce_to_min_support.
          + simpl. apply subqhC. apply subqh_hlist_reduce_to_min_support_marker.
        - apply subqh_ref.
        - apply subqh_ref.
      }
- assert (L1: inpl = nil /\ outpl = nil /\ full = nil /\ markers = nil \/ (inpl <> nil \/ outpl <> nil \/ full <> nil \/ markers <> nil)).
  { destruct inpl as [|z inpl].
    - destruct outpl as [|y outpl].
      + destruct full as [|x full].
        * { destruct markers as [|w markers].
            - tauto.
            - right. right. right. right. discriminate.
          }
        * right. right. right. left. discriminate.
      + right. right. left. discriminate.
    - right. left. discriminate.
  }
  destruct L1 as [[L1a [L1b [L1c L1d]]]|L1].
  + subst inpl. subst outpl. subst full. subst markers.
    change (subqc (ctreeH (S n) (ctree_hashroot T)) T).
    change (subqm (ctree_mtree (ctreeH (S n) (ctree_hashroot T))) (ctree_mtree T)).
    change (mtree_hashroot (ctree_mtree T) = Some (ctree_hashroot T)).
    apply mtree_hashroot_ctree_hashroot.
  + destruct T as [[[[|] gamma] hl]|[h|[Tl|[Tr|[Tl Tr]]]]].
    * { unfold subqc.
        change (subqm
                  (ctree_mtree
                     (ctree_reduce_to_min_support inpl outpl full markers (@ctreeL hl (S n) (true, gamma))))
                  (ctree_mtree (@ctreeL hl (S n) (true, gamma)))).
        assert (L2: ctree_reduce_to_min_support inpl outpl full markers (@ctreeL hl (S n) (true, gamma))
                    = (@ctreeL hl (S n) (true, gamma))).
        { destruct inpl as [|y inpr]; try reflexivity.
          destruct outpl as [|z outpr]; try reflexivity.
          destruct full as [|x fullr]; try reflexivity.
          destruct markers as [|w markerr]; try reflexivity.
          exfalso. tauto.
        }
        rewrite L2. apply subqm_ref.
      }
    * { unfold subqc.
        change (subqm
                  (ctree_mtree
                     (ctree_reduce_to_min_support inpl outpl full markers (@ctreeL hl (S n) (false, gamma))))
                  (ctree_mtree (@ctreeL hl (S n) (false, gamma)))).
        assert (L2: ctree_reduce_to_min_support inpl outpl full markers (@ctreeL hl (S n) (false, gamma))
                    = (@ctreeL hl (S n) (false, gamma))).
        { destruct inpl as [|y inpr]; try reflexivity.
          destruct outpl as [|z outpr]; try reflexivity.
          destruct full as [|x fulr]; try reflexivity.
          destruct markers as [|w markerr]; try reflexivity.
          exfalso. tauto.
        }
        rewrite L2. apply subqm_ref.
      }
    * change (subqc (ctree_reduce_to_min_support inpl outpl full markers (ctreeH (S n) h)) (ctreeH (S n) h)).
      assert (L2: ctree_reduce_to_min_support inpl outpl full markers (ctreeH (S n) h) = (ctreeH (S n) h)).
      { destruct inpl as [|y inpr]; try reflexivity.
        destruct outpl as [|z outpr]; try reflexivity.
        destruct full as [|x fulr]; try reflexivity.
        destruct markers as [|w markerr]; try reflexivity.
      }
      rewrite L2. apply subqm_ref.
    * { change (subqc (ctree_reduce_to_min_support inpl outpl full markers (ctreeBL Tl))
                      (ctreeBL Tl)).
        assert (L2: ctree_reduce_to_min_support inpl outpl full markers (ctreeBL Tl)
                    = ctreeBL (ctree_reduce_to_min_support (strip_bitseq_false inpl)
                                                           (strip_bitseq_false0 outpl)
                                                           (strip_bitseq_false0 full)
                                                           (strip_bitseq_false0 markers)
                                                           Tl)).
        { destruct inpl as [|y inpr]; try reflexivity.
          destruct outpl as [|z outpr]; try reflexivity.
          destruct full as [|x fulr]; try reflexivity.
          destruct markers as [|w markerr]; try reflexivity.
          exfalso. tauto.
        }
        rewrite L2.
        unfold subqc.
        change (subqm (mtreeB (ctree_mtree
                                 (ctree_reduce_to_min_support (strip_bitseq_false inpl)
                                                              (strip_bitseq_false0 outpl)
                                                              (strip_bitseq_false0 full)
                                                              (strip_bitseq_false0 markers)
                                                              Tl))
                              (empty_mtree n))
                      (mtreeB (ctree_mtree Tl) (empty_mtree n))).
        split.
        - apply IH.
        - apply subqm_ref.
      }
    * { change (subqc (ctree_reduce_to_min_support inpl outpl full markers (ctreeBR Tr))
                      (ctreeBR Tr)).
        assert (L2: ctree_reduce_to_min_support inpl outpl full markers (ctreeBR Tr)
                    = ctreeBR (ctree_reduce_to_min_support (strip_bitseq_true inpl)
                                                           (strip_bitseq_true0 outpl)
                                                           (strip_bitseq_true0 full)
                                                           (strip_bitseq_true0 markers)
                                                           Tr)).
        { destruct inpl as [|y inpr]; try reflexivity.
          destruct outpl as [|z outpr]; try reflexivity.
          destruct full as [|x fulr]; try reflexivity.
          destruct markers as [|w markerr]; try reflexivity.
          exfalso. tauto.
        }
        rewrite L2.
        unfold subqc.
        change (subqm (mtreeB (empty_mtree n)
                              (ctree_mtree
                                 (ctree_reduce_to_min_support (strip_bitseq_true inpl)
                                                              (strip_bitseq_true0 outpl)
                                                              (strip_bitseq_true0 full)
                                                              (strip_bitseq_true0 markers)
                                                              Tr)))
                              
                      (mtreeB (empty_mtree n) (ctree_mtree Tr))).
        split.
        - apply subqm_ref.
        - apply IH.
      }
    * { change (subqc (ctree_reduce_to_min_support inpl outpl full markers (ctreeB Tl Tr))
                      (ctreeB Tl Tr)).
        assert (L2: ctree_reduce_to_min_support inpl outpl full markers (ctreeB Tl Tr)
                    = ctreeB
                        (ctree_reduce_to_min_support (strip_bitseq_false inpl)
                                                     (strip_bitseq_false0 outpl)
                                                     (strip_bitseq_false0 full)
                                                     (strip_bitseq_false0 markers)
                                                     Tl)
                        (ctree_reduce_to_min_support (strip_bitseq_true inpl)
                                                     (strip_bitseq_true0 outpl)
                                                     (strip_bitseq_true0 full)
                                                     (strip_bitseq_true0 markers)
                                                     Tr)).
        { destruct inpl as [|y inpr]; try reflexivity.
          destruct outpl as [|z outpr]; try reflexivity.
          destruct full as [|x fulr]; try reflexivity.
          destruct markers as [|w markerr]; try reflexivity.
          exfalso. tauto.
        }
        rewrite L2.
        unfold subqc.
        change (subqm (mtreeB (ctree_mtree
                                 (ctree_reduce_to_min_support (strip_bitseq_false inpl)
                                                              (strip_bitseq_false0 outpl)
                                                              (strip_bitseq_false0 full)
                                                              (strip_bitseq_false0 markers)
                                                              Tl))
                              (ctree_mtree
                                 (ctree_reduce_to_min_support (strip_bitseq_true inpl)
                                                              (strip_bitseq_true0 outpl)
                                                              (strip_bitseq_true0 full)
                                                              (strip_bitseq_true0 markers)
                                                              Tr)))
                      (mtreeB (ctree_mtree Tl) (ctree_mtree Tr))).
        split.
        - apply IH.
        - apply IH.
      }
Qed.

Opaque ctree_supports_asset.
Opaque ctree_reduce_to_min_support.
Opaque mtree_approx_fun_p.
Opaque ctree_mtree.

Lemma ctree_asset_value_in_min inpl outpl full markers T utot f :
    (forall h alpha u alpha' u', In (h,u) (f alpha) -> In (h,u') (f alpha') -> alpha = alpha' /\ u = u') ->
    octree_approx_fun_p (Some T) f ->
  ctree_asset_value_in T inpl utot ->
  forall inpr,
    (forall (alpha : bitseq 162) (h : hashval),
       In (alpha, h) inpr ->
       exists u, ctree_supports_asset (h,u) T alpha) ->
    (forall a, In a inpl -> In a inpr) ->
  ctree_asset_value_in (ctree_reduce_to_min_support inpr outpl full markers T) inpl utot.
intros Hf2 HTf H. induction H as [|h a u inpl alpha v H1 IH H2 H2b H2c|h a inpl alpha v H1 IH H2 H2b H2c].
- intros inpr _ _. apply ctree_asset_value_in_nil.
- intros inpr H3 H4.
  apply (ctree_asset_value_in_cons (ctree_reduce_to_min_support inpr outpl full markers T)
                                      h a u inpl alpha).
  + apply IH.
    * exact H3.
    * intros a' H5. apply H4. now right.
  + assert (L1: In (alpha, h) inpr).
    { apply H4. now left. }
    destruct (ctree_supports_assets_min inpr outpl full markers T f Hf2 HTf H3 alpha h L1) as [[bday [obl w]] H5].
    assert (L2: ctree_supports_asset (h, (bday,(obl, w))) T alpha).
    { revert H5. apply subqc_supports_asset.
      apply subqc_ctree_reduce_to_min_support.
    }
    assert (L3: In (h, (bday,(obl, w))) (f alpha)).
    { unfold octree_approx_fun_p in HTf. unfold octree_mtree in HTf.
      apply (mtree_supports_asset_In_statefun (h, (bday,(obl, w))) (ctree_mtree T)).
      - exact HTf.
      - apply ctree_mtree_supports_asset. exact L2.
    }
    assert (L4: In (h,(assetbday a,(assetobl a,assetpre a))) (f alpha)).
    { unfold octree_approx_fun_p in HTf. unfold octree_mtree in HTf.
      apply (mtree_supports_asset_In_statefun (h,(assetbday a,(assetobl a,assetpre a))) (ctree_mtree T)).
      - exact HTf.
      - apply ctree_mtree_supports_asset.
        destruct a as [h' [bday' [obl' u']]].
        simpl in H2c. subst h'.
        exact H2.
    }
    assert (L5: bday = assetbday a /\ obl = assetobl a /\ w = assetpre a).
    { destruct (Hf2 h alpha (bday,(obl,w)) alpha (assetbday a,(assetobl a,assetpre a)) L3 L4) as [_ H6].
      inversion H6. tauto.
    }
    destruct L5 as [L5a [L5b L5c]].
    rewrite L5a in H5. rewrite L5b in H5. rewrite L5c in H5.
    destruct a as [h' [bday' [obl' u']]].
    simpl in H2c. subst h'.
    exact H5.
  + exact H2b.
  + exact H2c.
- intros inpr H3 H4.
  apply (ctree_asset_value_in_skip (ctree_reduce_to_min_support inpr outpl full markers T)
                                      h a inpl alpha).
  + apply IH.
    * exact H3.
    * intros a' H5. apply H4. now right.
  + assert (L1: In (alpha, h) inpr).
    { apply H4. now left. }
    destruct (ctree_supports_assets_min inpr outpl full markers T f Hf2 HTf H3 alpha h L1) as [[bday [obl w]] H5].
    assert (L2: ctree_supports_asset (h, (bday,(obl, w))) T alpha).
    { revert H5. apply subqc_supports_asset.
      apply subqc_ctree_reduce_to_min_support.
    }
    assert (L3: In (h, (bday,(obl, w))) (f alpha)).
    { unfold octree_approx_fun_p in HTf. unfold octree_mtree in HTf.
      apply (mtree_supports_asset_In_statefun (h, (bday,(obl, w))) (ctree_mtree T)).
      - exact HTf.
      - apply ctree_mtree_supports_asset. exact L2.
    }
    assert (L4: In (h, (assetbday a,(assetobl a,assetpre a))) (f alpha)).
    { unfold octree_approx_fun_p in HTf. unfold octree_mtree in HTf.
      apply (mtree_supports_asset_In_statefun (h, (assetbday a,(assetobl a,assetpre a))) (ctree_mtree T)).
      - exact HTf.
      - apply ctree_mtree_supports_asset.
        destruct a as [h' [bday' [obl' u']]].
        simpl in H2c. subst h'.
        exact H2.
    }
    assert (L5: bday = assetbday a /\ obl = assetobl a /\ w = assetpre a).
    { destruct (Hf2 h alpha (bday,(obl,w)) alpha (assetbday a,(assetobl a,assetpre a)) L3 L4) as [_ H6].
      inversion H6. tauto.
    }
    destruct L5 as [L5a [L5b L5c]].
    rewrite L5a in H5. rewrite L5b in H5. rewrite L5c in H5.
    destruct a as [h' [bday' [obl' u']]].
    simpl in H2c. subst h'.
    exact H5.
  + exact H2b.
  + exact H2c.
Qed.

Transparent ctree_reduce_to_min_support.

Lemma ctree_full_approx_min {n} :
  forall (inpl : list (bitseq n * hashval))
         (outpl : list (bitseq n))
         (full : list (bitseq n))
         (markers : list (bitseq n))
         (T : ctree n)
         (alpha:bitseq n),
    ctree_full_approx_addr T alpha ->
    In alpha full ->
    ctree_full_approx_addr (ctree_reduce_to_min_support inpl outpl full markers T) alpha.
induction n as [|n IH].
- intros inpl outpl full markers T alpha H1 H2. simpl.
  destruct full as [|x full].
  + contradiction H2.
  + simpl in H1. exact H1.
- intros inpl outpl full markers T alpha H1 H2. simpl.
 assert (L1: inpl = nil /\ outpl = nil /\ full = nil /\ markers = nil \/ (inpl <> nil \/ outpl <> nil \/ full <> nil \/ markers <> nil)).
  { destruct inpl as [|z inpl].
    - destruct outpl as [|y outpl].
      + destruct full as [|x full].
        * { destruct markers as [|w markers].
            - tauto.
            - right. right. right. right. discriminate.
          }
        * right. right. right. left. discriminate.
      + right. right. left. discriminate.
    - right. left. discriminate.
  }
  destruct L1 as [[L1a [L1b [L1c L1d]]]|L1].
  + subst full. contradiction H2.
  + change (ctree_full_approx_addr (ctree_reduce_to_min_support inpl outpl full markers T) alpha).
    assert (L2: ctree_reduce_to_min_support inpl outpl full markers T
                = match T with
                    | inl _ => T
                    | inr (inl _) => T
                    | inr (inr (inl Tl)) =>
                      ctreeBL
                        (ctree_reduce_to_min_support 
                           (strip_bitseq_false inpl)
                           (strip_bitseq_false0 outpl)
                           (strip_bitseq_false0 full)
                           (strip_bitseq_false0 markers)
                           Tl)
                    | inr (inr (inr (inl Tr))) =>
                      ctreeBR
                        (ctree_reduce_to_min_support 
                           (strip_bitseq_true inpl) 
                           (strip_bitseq_true0 outpl)
                           (strip_bitseq_true0 full)
                           (strip_bitseq_true0 markers)
                           Tr)
                    | inr (inr (inr (inr (Tl, Tr)))) =>
                      ctreeB
                        (ctree_reduce_to_min_support 
                           (strip_bitseq_false inpl)
                           (strip_bitseq_false0 outpl)
                           (strip_bitseq_false0 full)
                           (strip_bitseq_false0 markers)
                           Tl)
                        (ctree_reduce_to_min_support 
                           (strip_bitseq_true inpl) 
                           (strip_bitseq_true0 outpl)
                           (strip_bitseq_true0 full)
                           (strip_bitseq_true0 markers)
                           Tr)
                  end).
    { simpl.
      destruct inpl as [|y inpr]; try reflexivity.
      destruct outpl as [|z outpr]; try reflexivity.
      destruct full as [|x fulr]; try reflexivity.
      exfalso. tauto.
    }
    rewrite L2.
    destruct T as [[gamma hl]|[h|[Tl|[Tr|[Tl Tr]]]]].
    * exact H1.
    * exact H1.
    * { destruct alpha as [[|] alpha].
        - simpl. tauto.
        - simpl in H1. simpl.
          apply (IH (strip_bitseq_false inpl)
                    (strip_bitseq_false0 outpl)
                    (strip_bitseq_false0 full)
                    (strip_bitseq_false0 markers)
                    Tl alpha).
          + exact H1.
          + now apply strip_bitseq_false0_iff.
      }
    * { destruct alpha as [[|] alpha].
        - simpl in H1. simpl.
          apply (IH (strip_bitseq_true inpl)
                    (strip_bitseq_true0 outpl)
                    (strip_bitseq_true0 full)
                    (strip_bitseq_true0 markers)
                    Tr alpha).
          + exact H1.
          + now apply strip_bitseq_true0_iff.
        - simpl. tauto.
      }
    * { destruct alpha as [[|] alpha].
        - simpl in H1. simpl.
          apply (IH (strip_bitseq_true inpl)
                    (strip_bitseq_true0 outpl)
                    (strip_bitseq_true0 full)
                    (strip_bitseq_true0 markers)
                    Tr alpha).
          + exact H1.
          + now apply strip_bitseq_true0_iff.
        - simpl in H1. simpl.
          apply (IH (strip_bitseq_false inpl)
                    (strip_bitseq_false0 outpl)
                    (strip_bitseq_false0 full)
                    (strip_bitseq_false0 markers)
                    Tl alpha).
          + exact H1.
          + now apply strip_bitseq_false0_iff.
      }
Qed.

Lemma ctree_rights_consumed_min b alpha rtot inpl outpl full markers (T:ctree 162) :
  In (termaddr_addr alpha) full ->
  (forall gamma k oblu, In (gamma,k) inpl ->
                       ctree_supports_asset (k,oblu) T gamma
                       ->
                       ctree_supports_asset (k,oblu)
                                            (ctree_reduce_to_min_support inpl outpl full markers T)
                                            gamma) ->                       
  ctree_rights_consumed b alpha T inpl rtot ->
  ctree_rights_consumed b alpha (ctree_reduce_to_min_support inpl outpl full markers T) inpl rtot.
intros H1 Ha H.
assert (L1: forall inpl', (forall z, In z inpl -> In z inpl') ->
                          (forall gamma k oblu, In (gamma,k) inpl' ->
                                               ctree_supports_asset (k,oblu) T gamma
                                               ->
                                               ctree_supports_asset (k,oblu)
                                                                    (ctree_reduce_to_min_support inpl' outpl full markers T)
                                                                    gamma) ->
                          ctree_rights_consumed b alpha (ctree_reduce_to_min_support inpl' outpl full markers T) inpl rtot).
{ clear Ha. induction H as [|beta h inpr r1 bday obl r2 H2 IH H3|beta h inpr r1 bday obl u H2 IH H3 H4]; intros inpl' H0 H0'.
  - apply ctree_rights_consumed_nil.
  - apply (ctree_rights_consumed_cons b alpha _ beta h inpr r1 bday obl r2).
    + apply IH.
      * intros z H4. apply H0. now right.
      * exact H0'.
    + apply H0'.
      * apply H0. now left.
      * exact H3.
  - apply (ctree_rights_consumed_skip b alpha _ beta h inpr r1 bday obl u).
    + apply IH.
      * intros z H5. apply H0. now right.
      * exact H0'.
    + apply H0'.
      * apply H0. now left.
      * exact H3.
    + exact H4.
}
apply L1.
- intros z. tauto.
- exact Ha.
Qed.

Lemma hlist_reduce_to_min_support_marker_marker k bday obl aidl hl :
  In_hlist (k, (bday, (obl, marker))) hl ->
  exists (k : hashval) (bday : nat) (obl : obligation),
    In_hlist (k, (bday, (obl, marker)))
             (hlist_reduce_to_min_support_marker aidl hl).
revert aidl. induction hl as [h| |[h [bday' [obl' u]]] hl IH]; intros aidl.
- intros H1. inversion H1.
- intros H1. inversion H1.
- intros H1. inversion H1.
  + exists h. exists bday'. exists obl'. apply In_hlist_H.
  + simpl. destruct (preasset_marker_dec u) as [Hum|Hum].
    * exists h. exists bday'. exists obl'. subst u. apply In_hlist_H.
    * destruct (IH (remove hashval_eq_dec h aidl) H0) as [k' [bday'' [obl'' H3]]].
      exists k'. exists bday''. exists obl''.
      apply In_hlist_C.
      exact H3.
Qed.

Transparent ctree_supports_asset.

Lemma ctree_markers_min {n} :
  forall (inpl : list (bitseq n * hashval))
         (outpl : list (bitseq n))
         (full : list (bitseq n))
         (markers : list (bitseq n))
         (T : ctree n)
         (alpha:bitseq n),
    (exists k bday obl, ctree_supports_asset (k,(bday,(obl,marker))) T alpha) ->
    In alpha markers ->
    (exists k bday obl, ctree_supports_asset (k,(bday,(obl,marker)))
                                             (ctree_reduce_to_min_support inpl outpl full markers T)
                                             alpha).
induction n as [|n IH].
- simpl. intros inpl _ full markers hl [] [k [bday [obl H1]]] H2.
  destruct markers as [|[] markers].
  + contradiction H2.
  + destruct full as [|z full].
    * { destruct hl as [h|[[h [bday' [obl' u]]] hl]].
        - inversion H1.
        - inversion H1.
          + exists h. exists bday'. exists obl'. simpl. apply In_hlist_H.
          + destruct (preasset_marker_dec u) as [Hum|Hum].
            * exists h. exists bday'. exists obl'. simpl. subst u. apply In_hlist_H.
            * simpl. 
              destruct (hlist_reduce_to_min_support_marker_marker k bday obl (remove hashval_eq_dec h (map (snd (B:=hashval)) inpl)) hl H0) as [k' [bday'' [obl'' H4]]].
              exists k'. exists bday''. exists obl''.
              apply In_hlist_C. exact H4.
      }
    * exists k. exists bday. exists obl. exact H1.
- intros inpl outpl full markers [[gamma hl]|[h|[Tl|[Tr|[Tl Tr]]]]] alpha.
  + unfold ctree_supports_asset at 1. destruct (bitseq_eq_dec gamma alpha) as [E|E].
    * { subst gamma. intros [k [bday [obl H1]]] H2.
        destruct alpha as [[|] alpha].
        - unfold ctree_reduce_to_min_support.
          exists k. exists bday. exists obl.
          destruct inpl.
          + destruct outpl.
            * { destruct full.
                - destruct markers.
                  + contradiction H2.
                  + unfold ctree_supports_asset.
                    destruct (@bitseq_eq_dec (S n) (true, alpha) (true, alpha)) as [E1|E1].
                    * exact H1.
                    * congruence.
                - unfold ctree_supports_asset.
                  destruct (@bitseq_eq_dec (S n) (true, alpha) (true, alpha)) as [E1|E1].
                  + exact H1.
                  + congruence.
              }
            * { unfold ctree_supports_asset.
                destruct (@bitseq_eq_dec (S n) (true, alpha) (true, alpha)) as [E1|E1].
                - exact H1.
                - congruence.
              }
          + unfold ctree_supports_asset.
            destruct (@bitseq_eq_dec (S n) (true, alpha) (true, alpha)) as [E1|E1].
            * exact H1.
            * congruence.
        - unfold ctree_reduce_to_min_support.
          exists k. exists bday. exists obl.
          destruct inpl.
          + destruct outpl.
            * { destruct full.
                - destruct markers.
                  + contradiction H2.
                  + unfold ctree_supports_asset.
                    destruct (@bitseq_eq_dec (S n) (false, alpha) (false, alpha)) as [E1|E1].
                    * exact H1.
                    * congruence.
                - unfold ctree_supports_asset.
                  destruct (@bitseq_eq_dec (S n) (false, alpha) (false, alpha)) as [E1|E1].
                  + exact H1.
                  + congruence.
              }
            * { unfold ctree_supports_asset.
                destruct (@bitseq_eq_dec (S n) (false, alpha) (false, alpha)) as [E1|E1].
                - exact H1.
                - congruence.
              }
          + unfold ctree_supports_asset.
            destruct (@bitseq_eq_dec (S n) (false, alpha) (false, alpha)) as [E1|E1].
            * exact H1.
            * congruence.
      }
    * intros [_ [_ [_ []]]].
  + intros [k [bday [obl []]]].
  + intros H1 H2. destruct alpha as [[|] alpha].
    * destruct H1 as [k [bday [obl []]]].
    * assert (L1: In alpha (strip_bitseq_false0 markers)).
      { apply strip_bitseq_false0_iff. exact H2. }
      destruct (IH (strip_bitseq_false inpl) (strip_bitseq_false0 outpl) (strip_bitseq_false0 full) (strip_bitseq_false0 markers) Tl alpha H1 L1) as [k [bday [obl H3]]].
      exists k. exists bday. exists obl.
      assert (L2: ctree_reduce_to_min_support inpl outpl full markers (inr (inr (inl Tl)))
                  = ctreeBL (ctree_reduce_to_min_support (strip_bitseq_false inpl)
                                                         (strip_bitseq_false0 outpl)
                                                         (strip_bitseq_false0 full)
                                                         (strip_bitseq_false0 markers)
                                                         Tl)).
      { destruct inpl; try reflexivity.
        destruct outpl; try reflexivity.
        destruct full; try reflexivity.
        destruct markers; try reflexivity.
        contradiction H2.
      }
      change ((fun z => @ctree_supports_asset (k, (bday, (obl, marker))) (S n) z (false,alpha)) (ctree_reduce_to_min_support inpl outpl full markers (inr (inr (inl Tl))))).
      rewrite L2.
      simpl. exact H3.
  + intros H1 H2. destruct alpha as [[|] alpha].
    * assert (L1: In alpha (strip_bitseq_true0 markers)).
      { apply strip_bitseq_true0_iff. exact H2. }
      destruct (IH (strip_bitseq_true inpl) (strip_bitseq_true0 outpl) (strip_bitseq_true0 full) (strip_bitseq_true0 markers) Tr alpha H1 L1) as [k [bday [obl H3]]].
      exists k. exists bday. exists obl.
      assert (L2: ctree_reduce_to_min_support inpl outpl full markers (inr (inr (inr (inl Tr))))
                  = ctreeBR (ctree_reduce_to_min_support (strip_bitseq_true inpl)
                                                         (strip_bitseq_true0 outpl)
                                                         (strip_bitseq_true0 full)
                                                         (strip_bitseq_true0 markers)
                                                         Tr)).
      { destruct inpl; try reflexivity.
        destruct outpl; try reflexivity.
        destruct full; try reflexivity.
        destruct markers; try reflexivity.
        contradiction H2.
      }
      change ((fun z => @ctree_supports_asset (k, (bday, (obl, marker))) (S n) z (true,alpha)) (ctree_reduce_to_min_support inpl outpl full markers (inr (inr (inr (inl Tr)))))).
      rewrite L2.
      simpl. exact H3.
    * destruct H1 as [k [bday [obl []]]].
  + intros H1 H2. destruct alpha as [[|] alpha].
    * assert (L1: In alpha (strip_bitseq_true0 markers)).
      { apply strip_bitseq_true0_iff. exact H2. }
      destruct (IH (strip_bitseq_true inpl) (strip_bitseq_true0 outpl) (strip_bitseq_true0 full) (strip_bitseq_true0 markers) Tr alpha H1 L1) as [k [bday [obl H3]]].
      exists k. exists bday. exists obl.
      assert (L2: ctree_reduce_to_min_support inpl outpl full markers (inr (inr (inr (inr (Tl,Tr)))))
                  = ctreeB (ctree_reduce_to_min_support (strip_bitseq_false inpl)
                                                        (strip_bitseq_false0 outpl)
                                                        (strip_bitseq_false0 full)
                                                        (strip_bitseq_false0 markers)
                                                        Tl)
                           (ctree_reduce_to_min_support (strip_bitseq_true inpl)
                                                        (strip_bitseq_true0 outpl)
                                                        (strip_bitseq_true0 full)
                                                        (strip_bitseq_true0 markers)
                                                        Tr)).
      { destruct inpl; try reflexivity.
        destruct outpl; try reflexivity.
        destruct full; try reflexivity.
        destruct markers; try reflexivity.
        contradiction H2.
      }
      change ((fun z => @ctree_supports_asset (k, (bday, (obl, marker))) (S n) z (true,alpha)) (ctree_reduce_to_min_support inpl outpl full markers (inr (inr (inr (inr (Tl,Tr))))))).
      rewrite L2.
      simpl. exact H3.
    * assert (L1: In alpha (strip_bitseq_false0 markers)).
      { apply strip_bitseq_false0_iff. exact H2. }
      destruct (IH (strip_bitseq_false inpl) (strip_bitseq_false0 outpl) (strip_bitseq_false0 full) (strip_bitseq_false0 markers) Tl alpha H1 L1) as [k [bday [obl H3]]].
      exists k. exists bday. exists obl.
      assert (L2: ctree_reduce_to_min_support inpl outpl full markers (inr (inr (inr (inr (Tl,Tr)))))
                  = ctreeB (ctree_reduce_to_min_support (strip_bitseq_false inpl)
                                                        (strip_bitseq_false0 outpl)
                                                        (strip_bitseq_false0 full)
                                                        (strip_bitseq_false0 markers)
                                                        Tl)
                           (ctree_reduce_to_min_support (strip_bitseq_true inpl)
                                                        (strip_bitseq_true0 outpl)
                                                        (strip_bitseq_true0 full)
                                                        (strip_bitseq_true0 markers)
                                                        Tr)).
      { destruct inpl; try reflexivity.
        destruct outpl; try reflexivity.
        destruct full; try reflexivity.
        destruct markers; try reflexivity.
        contradiction H2.
      }
      change ((fun z => @ctree_supports_asset (k, (bday, (obl, marker))) (S n) z (false,alpha)) (ctree_reduce_to_min_support inpl outpl full markers (inr (inr (inr (inr (Tl,Tr))))))).
      rewrite L2.
      simpl. exact H3.
Qed.

Opaque ctree_supports_asset.
Opaque ctree_reduce_to_min_support.

Lemma ctree_supports_tx_min tht sigt m (tx:Tx) (T:ctree 162) (f:statefun) fee rew :
  sf_valid f ->
  octree_approx_fun_p (Some T) f ->
  ctree_supports_tx tht sigt m tx T fee rew ->
  ctree_supports_tx tht sigt m tx
                    (ctree_reduce_to_min_support (fst tx) (map (@fst addr (prod obligation preasset)) (snd tx)) (full_needed (snd tx)) (map hashval_term_addr (output_markers (snd tx))) T)
                    fee rew.
destruct tx as [inpl outpl].
intros Hf HTf Hs. generalize Hs.
intros [Hs1 [[utot [Hs2 Hs3]] [[Hs4a Hs4b] [[Hs5a [Hs5b Hs5c]] [Hs6 [Hs7 Hs8]]]]]].
set (T' := (ctree_reduce_to_min_support (fst (inpl, outpl))
                                        (map (fst (B:=obligation * preasset)) (snd (inpl, outpl)))
                                        (full_needed (snd (inpl, outpl)))
                                        (map hashval_term_addr (output_markers (snd (inpl, outpl))))
                                        T)).
assert (La: forall (gamma : addr) (k : hashval) (bdayoblu : nat * (obligation * preasset)),
              In (gamma, k) (tx_inputs (inpl, outpl)) ->
              ctree_supports_asset (k, bdayoblu) T gamma ->
              ctree_supports_asset (k, bdayoblu) T' gamma).
{ intros gamma k [bday [obl u]] H1 H2.
  apply ctree_supports_tx_can_support in Hs.
  destruct Hs as [Hc1 _].
  generalize Hf. intros [_ [Hf2 _]].
  destruct (ctree_supports_assets_min inpl (map (@fst addr (prod obligation preasset)) outpl) (full_needed outpl) (map hashval_term_addr (output_markers (snd (inpl, outpl)))) T f Hf2 HTf Hc1 gamma k H1) as [[bday2 [obl2 v2]] H5].
  assert (L1: (k, (bday,(obl, u))) = (k, (bday2,(obl2, v2)))).
  { apply (ctree_valid_supports_asset_uniq (k,(bday,(obl,u))) (k,(bday2,(obl2,v2))) T gamma).
    - exists f. split.
      + exact Hf.
      + exact HTf.
    - exact H2.
    - revert H5. apply subqc_supports_asset.
      apply subqc_ctree_reduce_to_min_support.
    - reflexivity.
  }
  inversion L1. exact H5.
}
split.
- intros alpha u H5.
  apply (ctree_supports_addrs_min inpl (map (@fst addr (prod obligation preasset)) outpl) (full_needed outpl) (map hashval_term_addr (output_markers (snd (inpl, outpl)))) T).
  + intros beta H6. apply in_map_iff in H6.
    Opaque ctree_supports_addr.
    destruct H6 as [[gamma v] [H7 H8]].
    simpl in H7. subst gamma. revert beta v H8. exact Hs1.
  + apply in_map_iff. exists (alpha,u). split.
    * reflexivity.
    * exact H5.
- split.
  + exists utot. split.
    * { simpl in Hs2. simpl.
        apply (ctree_asset_value_in_min inpl (map (@fst (bitseq 162) (prod obligation preasset)) outpl) (full_needed outpl) (map hashval_term_addr (output_markers (snd (inpl, outpl)))) T utot f).
        - destruct Hf as [_ [Hf2 _]]. exact Hf2.
        - exact HTf.
        - exact Hs2.
        - apply ctree_supports_tx_can_support in Hs.
          destruct Hs as [Hc1 _]. exact Hc1.
        - intros a' H5. exact H5.
      }
    * exact Hs3.
  + split.
    * { split.
        - intros alpha b H1.
          destruct (Hs4a alpha b H1) as [H2 [H3 H4]].
          assert (L1: In (termaddr_addr alpha) (full_needed outpl)).
          { destruct H1 as [H1|[beta [obl [n H1]]]].
            - revert H1. apply In_full_needed_uses.
            - revert H1. apply In_full_needed_rights.
          }
          assert (L2: ctree_full_approx_addr T' (termaddr_addr alpha)).
          { apply (ctree_full_approx_min inpl (map (@fst (bitseq 162) (prod obligation preasset)) outpl) (full_needed outpl) (map hashval_term_addr (output_markers (snd (inpl, outpl)))) T (termaddr_addr alpha)).
            - exact H2.
            - exact L1.
          }
          repeat split.
          + exact L2.
          + intros [h' [bday' [obl' [beta' H5]]]]. apply H3.
            exists h'. exists bday'. exists obl'. exists beta'.
            revert H5. apply subqc_supports_asset.
            apply subqc_ctree_reduce_to_min_support.
          + intros rtot1 rtot2 h bday obl beta u H6 H7 H8.
            assert (L3: ctree_supports_asset (h, (bday,(obl, owns b beta (Some u)))) T (termaddr_addr alpha)).
            { revert H7. apply subqc_supports_asset.
              apply subqc_ctree_reduce_to_min_support.
            }
            destruct (H4 rtot1 rtot2 h bday obl beta u H6 L3 H8) as [rtot3 [rtot4 [H9 [H10 H11]]]].
            exists rtot3. exists rtot4. repeat split.
            * { revert H9.
                apply ctree_rights_consumed_min.
                - exact L1.
                - exact La.
              }
            * exact H10.
            * exact H11.
        - intros alpha b beta h bday obl n H1 H2.
          assert (L1: ctree_supports_asset (h, (bday, (obl, rights b n alpha))) T beta).
          { revert H2. apply subqc_supports_asset.
            apply subqc_ctree_reduce_to_min_support.
          }
          revert H1 L1. apply Hs4b.
      }
    * { split; [split; [|split]|].
        - intros obl gamma nonce d alpha H1.
          destruct (Hs5a obl gamma nonce d alpha H1) as [Hch [beta [h [bday' [obl' [H2 [H3 [H4 H5]]]]]]]].
          split.
          + exact Hch.
          + exists beta. exists h. exists bday'. exists obl'. repeat split.
            * exact H2.
            * exact H3.
            * exact H4.
            * revert H3 H5. apply La.
        - intros obl gamma nonce th d alpha H1.
          destruct (Hs5b obl gamma nonce th d alpha H1) as [Hch [beta [h [bday' [obl' [H2 [H3 [H4 H5]]]]]]]].
          split.
          + revert Hch. apply check_signaspec_p_markers.
            * { intros h' a' H6 H7.
                assert (L1: In (hashpair h' (hashstp a')) (output_markers outpl)).
                { revert H1 H6. apply signaspec_stp_markers_output_markers. }
                unfold T'. unfold ctree_lookup_stp.
                apply ctree_markers_min.
                - exact H7.
                - apply in_map_iff. exists (hashpair h' (hashstp a')).
                  split.
                  + reflexivity.
                  + exact L1.
              }
            * { intros h' H6 H7.
                assert (L1: In h' (output_markers outpl)).
                { revert H1 H6. apply signaspec_known_markers_output_markers. }
                unfold T'. unfold ctree_lookup_known.
                apply ctree_markers_min.
                - exact H7.
                - apply in_map_iff. exists h'.
                  split.
                  + reflexivity.
                  + exact L1.
              }
          + exists beta. exists h. exists bday'. exists obl'. repeat split.
            * exact H2.
            * exact H3.
            * exact H4.
            * revert H3 H5. apply La.
        - intros obl gamma nonce th d alpha H1.
          destruct (Hs5c obl gamma nonce th d alpha H1) as [Hch [beta [h [bday' [obl' [H2 [H3 [H4 H5]]]]]]]].
          split.
          + revert Hch. apply check_doc_p_markers.
            * { intros h' a' H6 H7.
                assert (L1: In (hashpair h' (hashstp a')) (output_markers outpl)).
                { revert H1 H6. apply doc_stp_markers_output_markers. }
                unfold T'. unfold ctree_lookup_stp.
                apply ctree_markers_min.
                - exact H7.
                - apply in_map_iff. exists (hashpair h' (hashstp a')).
                  split.
                  + reflexivity.
                  + exact L1.
              }
            * { intros h' H6 H7.
                assert (L1: In h' (output_markers outpl)).
                { revert H1 H6. apply doc_known_markers_output_markers. }
                unfold T'. unfold ctree_lookup_known.
                apply ctree_markers_min.
                - exact H7.
                - apply in_map_iff. exists h'.
                  split.
                  + reflexivity.
                  + exact L1.
              }
          + exists beta. exists h. exists bday'. exists obl'. repeat split.
            * exact H2.
            * exact H3.
            * exact H4.
            * revert H3 H5. apply La.
        - split.
          + intros alpha b obl beta r H1.
            destruct (Hs6 alpha b obl beta r H1) as [H2 H3].
            assert (L1: ctree_full_approx_addr T' (termaddr_addr alpha)).
            { apply ctree_full_approx_min.
              - exact H2.
              - apply In_full_needed_owns with (obl := obl) (b := b) (beta := beta) (r := r).
                exact H1.
            }
            split.
            * exact L1.
            * { destruct H3 as [[h [beta' [bday' [obl' [r' [H4 H5]]]]]]|[H4 H5]].
                - left. exists h. exists beta'. exists bday'. exists obl'. exists r'.
                  split.
                  + revert H5 H4. apply La.
                  + exact H5.
                - right. split.
                  + intros [h [beta' [bday' [obl' [r' H6]]]]].
                    apply H4.
                    exists h. exists beta'. exists bday'. exists obl'. exists r'.
                    revert H6.
                    apply subqc_supports_asset.
                    apply subqc_ctree_reduce_to_min_support.
                  + exact H5.
              }
          + split.
            * { intros k1 k2 b H1.
                destruct (Hs7 k1 k2 b H1) as [H2 H3].
                assert (L1: ctree_full_approx_addr T' (hashval_term_addr k1)).
                { apply ctree_full_approx_min.
                  - exact H2.
                  - revert H1. apply In_full_needed_creates.
                }
                split.
                - exact L1.
                - intros H4. apply H3.
                  intros [h' [beta' [bday' [obl' [r' H5]]]]].
                  apply H4. exists h'. exists beta'. exists bday'. exists obl'. exists r'.
                  revert L1 H5.
                  apply subqc_full_approx_supports_asset_conv.
                  apply subqc_ctree_reduce_to_min_support.
              }
            * { intros alpha h bday obl u H1 H2.
                assert (L1: ctree_supports_asset (h, (bday,(obl, bounty u))) T alpha).
                { revert H2. apply subqc_supports_asset.
                  apply subqc_ctree_reduce_to_min_support.
                }
                destruct (Hs8 alpha h bday obl u H1 L1) as [H3 [h' [bday' [obl' [beta [r [H4 [H5 H6]]]]]]]].
                assert (L2: ctree_full_approx_addr T' alpha).
                { apply ctree_full_approx_min.
                  - exact H3.
                  - revert H6. apply In_full_needed_owns.
                }
                split.
                - exact L2.
                - exists h'. exists bday'. exists obl'. exists beta. exists r. repeat split.
                  + exact H4.
                  + revert H4 H5. apply La.
                  + exact H6.
              }
      }
Qed.

Lemma octree_supports_tx_min tht sigt m (tx:Tx) (T:option (ctree 162)) (f:statefun) fee rew :
  sf_valid f ->
  octree_approx_fun_p T f ->
  octree_supports_tx tht sigt m tx T fee rew ->
  octree_supports_tx tht sigt m tx (octree_reduce_to_min_support_tx tx T) fee rew.
destruct tx as [inpl outpl]. destruct T as [T|].
- apply ctree_supports_tx_min.
- intros _ _. simpl. tauto.
Qed.

Definition nehlist_lub (hl1 hl2:nehlist) : nehlist :=
  match hl1 with
    | inl h1 => hl2
    | inr (h1,hr1) =>
      match hl2 with
        | inl h2 =>  hl1
        | inr(h2,hr2) => inr (h1,hlist_lub hr1 hr2)
      end
  end.

Definition ctree_singlebranch_lub {n} (gamma:bitseq n) (hl:nehlist) (T:ctree n) : ctree n :=
match ctreeLinv T with
| Some(delta,hl2) => (*** assume delta is gamma or this shouldn't have been called (incompat trees error) ***)
  ctreeL (nehlist_lub hl hl2) gamma
| None => ctreeL hl gamma (*** the only way this can happen with a compat tree is if there is some hash hiding T has a single leaf ***)
end.

Fixpoint ctree_lub {n} : ctree n -> ctree n -> ctree n :=
match n with
| O => fun (hl1 hl2:ctree 0) => (nehlist_lub hl1 hl2:ctree 0)
| S n => fun (T1 T2:ctree (S n)) =>
           match T1 with
             | inl (gamma1,hl1) => ctree_singlebranch_lub gamma1 hl1 T2
             | inr (inl _) => T2
             | inr (inr (inl T1l)) =>
               match T2 with
                 | inl (gamma2,hl2) => ctree_singlebranch_lub gamma2 hl2 T1
                 | inr (inl _) => T1
                 | inr (inr (inl T2l)) => ctreeBL (ctree_lub T1l T2l)
                 | inr (inr (inr (inl T2r))) => ctreeB T1l T2r (*** Apr 9: Actually this shouldn't happen ***)
                 | inr (inr (inr (inr (T2l,T2r)))) => ctreeB (ctree_lub T1l T2l) T2r (*** Shouldn't happen ***)
               end
             | inr (inr (inr (inl T1r))) =>
               match T2 with
                 | inl (gamma2,hl2) => ctree_singlebranch_lub gamma2 hl2 T1
                 | inr (inl _) => T1
                 | inr (inr (inl T2l)) => ctreeB T2l T1r
                 | inr (inr (inr (inl T2r))) => ctreeBR (ctree_lub T1r T2r)
                 | inr (inr (inr (inr (T2l,T2r)))) => ctreeB T2l (ctree_lub T1r T2r)
               end
             | inr (inr (inr (inr (T1l,T1r)))) =>
               match T2 with
                 | inl (gamma2,hl2) => ctree_singlebranch_lub gamma2 hl2 T1
                 | inr (inl _) => T1
                 | inr (inr (inl T2l)) => ctreeB (ctree_lub T1l T2l) T1r
                 | inr (inr (inr (inl T2r))) => ctreeB T1l (ctree_lub T1r T2r)
                 | inr (inr (inr (inr (T2l,T2r)))) => ctreeB (ctree_lub T1l T2l) (ctree_lub T1r T2r)
               end
           end
end.

Lemma nehlist_lub_eq_1 (hl1 hl2:nehlist) :
  nehlist_hashroot hl1 = nehlist_hashroot hl2 ->
  nehlist_hashroot (nehlist_lub hl1 hl2) = nehlist_hashroot hl1.
destruct hl1 as [h1|[a1 hr1]]; simpl.
- intros H1. symmetry. exact H1.
- destruct hl2 as [h2|[a2 hr2]]; simpl.
  + intros _. reflexivity.
  + intros H1. rewrite hlist_lub_eq_1.
    * reflexivity.
    * { unfold hashopair1 in H1.
        destruct (hlist_hashroot hr1) as [h1|]; destruct (hlist_hashroot hr2) as [h2|]; simpl in H1.
        - apply hashpairinj in H1. destruct H1 as [_ H1].
          apply hashpairinj in H1. destruct H1 as [_ H1].
          congruence.
        - exfalso. apply hashpairinj in H1. destruct H1 as [H1 _].
          apply hashnatinj in H1. omega.
        - exfalso. apply hashpairinj in H1. destruct H1 as [H1 _].
          apply hashnatinj in H1. omega.
        - reflexivity.
      }
Qed.

Lemma subqneh_lub_1 (hl1 hl2:nehlist) :
  nehlist_hashroot hl1 = nehlist_hashroot hl2 ->
  subqneh hl1 (nehlist_lub hl1 hl2).
destruct hl1 as [h1|[a1 hr1]]; simpl.
- tauto.
- destruct hl2 as [h2|[a2 hr2]]; simpl.
  + intros _. split.
    * reflexivity.
    * apply subqh_ref.
  + intros H1. split.
    * reflexivity.
    * { apply subqh_lub_1.
        unfold hashopair1 in H1.
        destruct (hlist_hashroot hr1) as [h1|]; destruct (hlist_hashroot hr2) as [h2|]; simpl in H1.
        - apply hashpairinj in H1. destruct H1 as [_ H1].
          apply hashpairinj in H1. destruct H1 as [_ H1].
          congruence.
        - exfalso. apply hashpairinj in H1. destruct H1 as [H1 _].
          apply hashnatinj in H1. omega.
        - exfalso. apply hashpairinj in H1. destruct H1 as [H1 _].
          apply hashnatinj in H1. omega.
        - reflexivity.
      }
Qed.

Lemma subqneh_lub_2 (hl1 hl2:nehlist) :
  nehlist_hashroot hl1 = nehlist_hashroot hl2 ->
  subqneh hl2 (nehlist_lub hl1 hl2).
destruct hl2 as [h2|[a2 hr2]]; simpl.
- destruct hl1 as [h1|[a1 hr1]]; simpl.
  + tauto.
  + intros H1. symmetry. exact H1.
- destruct hl1 as [h1|[a1 hr1]]; simpl.
  + intros _. split.
    * reflexivity.
    * apply subqh_ref.
  + intros H1.
    unfold hashopair1 in H1.
    assert (L1: a1 = a2 /\ hlist_hashroot hr1 = hlist_hashroot hr2).
    { simpl in H1; destruct (hlist_hashroot hr1) as [k1|]; destruct (hlist_hashroot hr2) as [k2|]; inversion H1.
      - apply hashpairinj in H0. destruct H0 as [_ H0].
        apply hashpairinj in H0. destruct H0 as [H2 H0].
        apply hashassetinj in H2. split; congruence.
      - exfalso.
        apply hashpairinj in H0. destruct H0 as [H0 _].
        apply hashnatinj in H0. discriminate H0.        
      - exfalso.
        apply hashpairinj in H0. destruct H0 as [H0 _].
        apply hashnatinj in H0. discriminate H0.        
      - apply hashpairinj in H0. destruct H0 as [_ H0].
        apply hashassetinj in H0. split; congruence.
    }
    destruct L1 as [L1a L1b].
    split.
    * congruence.
    * now apply subqh_lub_2.
Qed.

Lemma subqneh_subqh (hl1 hl2:nehlist) :
  subqneh hl1 hl2 <-> subqh (nehlist_hlist hl1) (nehlist_hlist hl2).
destruct hl1 as [h1|[a1 hr1]]; destruct hl2 as [h2|[a2 hr2]]; simpl.
- split; intros H1.
  + subst h2. apply subqh_ref.
  + inversion H1. simpl in H0. inversion H0. reflexivity.
- split; intros H1.
  + apply subqhH. subst h1. simpl.
    destruct (hlist_hashroot hr2); reflexivity.
  + inversion H1. simpl in H0.
    destruct (hlist_hashroot hr2) as [h2|].
    * inversion H0. reflexivity.
    * inversion H0. reflexivity.
- split; intros H1.
  + tauto.
  + inversion H1.
- split; intros H1.
  + destruct H1 as [H2 H3]. subst a2.
    apply subqhC. exact H3.
  + inversion H1. tauto.
Qed.

Transparent ctree_mtree.

Lemma subqm_singlebranch_subqneh (hl hr:nehlist) {n} (gamma:bitseq n) :
  subqneh hl hr ->
  subqm (singlebranch_mtree hl gamma) (singlebranch_mtree hr gamma).
induction n as [|n IH].
- simpl. intros H1. unfold subqc. simpl. now apply subqneh_subqh.
- destruct gamma as [[|] gamma]; simpl; intros H1; split.
  + apply subqm_ref.
  + now apply IH.
  + now apply IH.
  + apply subqm_ref.
Qed.

Lemma subqc_ctree_L_subqneh (hl hr:nehlist) {n} (gamma:bitseq n) :
  subqneh hl hr ->
  subqc (ctreeL hl gamma) (ctreeL hr gamma).
destruct n as [|n].
- exact (subqm_singlebranch_subqneh hl hr gamma).
- exact (subqm_singlebranch_subqneh hl hr gamma).
Qed.

Lemma mtree_hashroot_singlebranch_mtree_nehlist_hashroot (hl hr:nehlist) {n} (gamma delta:bitseq n) :
      mtree_hashroot (singlebranch_mtree hl gamma) =
      mtree_hashroot (singlebranch_mtree hr delta)
      ->
      gamma = delta /\
      nehlist_hashroot hl = nehlist_hashroot hr.
induction n as [|n IH].
- destruct gamma; destruct delta.
  simpl. destruct hl as [h1|[a1 hr1]]; destruct hr as [h2|[a2 hr2]]; simpl.
  + intros H1. inversion H1. tauto.
  + destruct (hlist_hashroot hr2) as [k|].
    * intros H1. inversion H1. tauto.
    * intros H1. inversion H1. tauto.
  + destruct (hlist_hashroot hr1) as [k|].
    * intros H1. inversion H1. tauto.
    * intros H1. inversion H1. tauto.
  + destruct (hlist_hashroot hr1) as [k1|]; destruct (hlist_hashroot hr2) as [k2|].
    * intros H1. inversion H1.
      apply hashpairinj in H0. destruct H0 as [_ H0].
      apply hashpairinj in H0. destruct H0 as [H2 H3].
      split; try tauto; congruence.
    * intros H1. exfalso. inversion H1.
      apply hashpairinj in H0. destruct H0 as [H0 _].
      apply hashnatinj in H0. omega.
    * intros H1. exfalso. inversion H1.
      apply hashpairinj in H0. destruct H0 as [H0 _].
      apply hashnatinj in H0. omega.
    * intros H1. inversion H1.
      apply hashpairinj in H0. destruct H0 as [_ H0].
      split; try tauto; congruence.
- destruct gamma as [[|] gamma]; destruct delta as [[|] delta].
  + simpl. intros H1. apply hashopairinj in H1.
    destruct H1 as [_ H2].
    apply IH in H2. destruct H2 as [H3 H4].
    split; congruence.
  + simpl. intros H1. exfalso. apply hashopairinj in H1.
    destruct H1 as [H2 _].
    rewrite mtree_hashroot_empty in H2.
    symmetry in H2. revert H2.
    apply mtree_hashroot_singlebranch_nonempty.
  + simpl. intros H1. exfalso. apply hashopairinj in H1.
    destruct H1 as [H2 _].
    rewrite mtree_hashroot_empty in H2.
    revert H2.
    apply mtree_hashroot_singlebranch_nonempty.
  + simpl. intros H1. apply hashopairinj in H1.
    destruct H1 as [H2 _].
    apply IH in H2. destruct H2 as [H3 H4].
    split; congruence.
Qed.

Lemma ctree_hashroot_ctreeL_nehlist_hashroot (hl hr:nehlist) {n} (gamma delta:bitseq n) :
      ctree_hashroot (ctreeL hl gamma) =
      ctree_hashroot (ctreeL hr delta)
      ->
      gamma = delta /\
      nehlist_hashroot hl = nehlist_hashroot hr.
induction n as [|n IH].
- destruct gamma; destruct delta.
  simpl. destruct hl as [h1|[a1 hr1]]; destruct hr as [h2|[a2 hr2]]; simpl.
  + intros H1. inversion H1. tauto.
  + destruct (hlist_hashroot hr2) as [k|].
    * intros H1. inversion H1. tauto.
    * intros H1. inversion H1. tauto.
  + destruct (hlist_hashroot hr1) as [k|].
    * intros H1. inversion H1. tauto.
    * intros H1. inversion H1. tauto.
  + destruct (hlist_hashroot hr1) as [k1|]; destruct (hlist_hashroot hr2) as [k2|].
    * intros H1. inversion H1.
      apply hashpairinj in H0. destruct H0 as [_ H0].
      apply hashpairinj in H0. destruct H0 as [H2 H3].
      split; try tauto; congruence.
    * intros H1. exfalso. inversion H1.
      apply hashpairinj in H0. destruct H0 as [H0 _].
      apply hashnatinj in H0. omega.
    * intros H1. exfalso. inversion H1.
      apply hashpairinj in H0. destruct H0 as [H0 _].
      apply hashnatinj in H0. omega.
    * intros H1. inversion H1.
      apply hashpairinj in H0. destruct H0 as [_ H0].
      split; try tauto; congruence.
- destruct gamma as [[|] gamma]; destruct delta as [[|] delta].
  + simpl. intros H1. apply hashpairinj in H1.
    destruct H1 as [_ H2].
    apply IH in H2. destruct H2 as [H3 H4].
    split; congruence.
  + simpl. intros H1. exfalso. apply hashpairinj in H1.
    destruct H1 as [H2 _].
    apply hashnatinj in H2. omega.
  + simpl. intros H1. exfalso. apply hashpairinj in H1.
    destruct H1 as [H2 _].
    apply hashnatinj in H2. omega.
  + simpl. intros H1. apply hashpairinj in H1.
    destruct H1 as [_ H2].
    apply IH in H2. destruct H2 as [H3 H4].
    split; congruence.
Qed.

Lemma subqm_ctree_singlebranch_lub {n} (T:ctree n) (hl:nehlist) (gamma:bitseq n) :
  ctree_hashroot T = ctree_hashroot (ctreeL hl gamma) ->
  subqc (ctreeL hl gamma)
        (ctree_singlebranch_lub gamma hl T).
unfold ctree_singlebranch_lub.
destruct (ctreeLinv T) as [[gamma2 hl2]|] eqn:E1.
- intros H1. apply subqc_ctree_L_subqneh. apply subqneh_lub_1.
  assert (L1: singlebranch_mtree hl2 gamma2 = ctree_mtree T) by exact (ctreeLinv_singlebranch _ _ _ E1).
  assert (L2: ctree_hashroot (ctreeL hl gamma) = ctree_hashroot (ctreeL hl2 gamma2)).
  { generalize (mtree_hashroot_ctree_hashroot T). intros H2.
    rewrite <- L1 in H2.
    generalize (mtree_hashroot_ctree_hashroot_L _ _ _ H2). intros H3.
    congruence.
  }
  assert (L3: gamma = gamma2 /\ nehlist_hashroot hl = nehlist_hashroot hl2).
  { now apply (ctree_hashroot_ctreeL_nehlist_hashroot hl hl2 gamma gamma2). }
  tauto.
- intros H1. unfold subqc. apply subqm_ref.
Qed.

Lemma subqm_ctree_mtree_singlebranch {n} (T:ctree n) (hl:nehlist) (gamma:bitseq n) :
  ctree_hashroot T = ctree_hashroot (ctreeL hl gamma) ->
  ctreeLinv T = None ->
  subqm (ctree_mtree T) (singlebranch_mtree hl gamma).
induction n as [|n IH].
- simpl. intros H1 H2. discriminate H2.
- intros H1 H2. destruct T as [[gamma1 hl1]|[h1|[Tl|[Tr|[Tl Tr]]]]].
  + simpl in H2. discriminate H2.
  + change (subqm (mtreeH n (Some h1)) (singlebranch_mtree hl gamma)).
    change (mtree_hashroot (singlebranch_mtree hl gamma) = Some h1).
    change (mtree_hashroot (ctree_mtree (ctreeL hl gamma)) = Some h1).
    change (h1 = ctree_hashroot (ctreeL hl gamma)) in H1.
    subst h1.
    apply mtree_hashroot_ctree_hashroot.
  + change (subqm (mtreeB (ctree_mtree Tl) (empty_mtree n)) (singlebranch_mtree hl gamma)).
    destruct gamma as [[|] gamma].
    * exfalso. simpl in H1.
      apply hashpairinj in H1. destruct H1 as [H1 _].
      apply hashnatinj in H1. omega.
    * { change (subqm (mtreeB (ctree_mtree Tl) (empty_mtree n)) (mtreeB (singlebranch_mtree hl gamma) (empty_mtree n))).
        split.
        - apply IH.
          + simpl in H1. apply hashpairinj in H1. tauto.
          + simpl in H2. destruct (ctreeLinv Tl) as [[delta kl]|].
            * discriminate H2.
            * reflexivity.
        - apply subqm_ref.
      }
  + change (subqm (mtreeB (empty_mtree n) (ctree_mtree Tr)) (singlebranch_mtree hl gamma)).
    destruct gamma as [[|] gamma].
    * { change (subqm (mtreeB (empty_mtree n) (ctree_mtree Tr)) (mtreeB (empty_mtree n) (singlebranch_mtree hl gamma))).
        split.
        - apply subqm_ref.
        - apply IH.
          + simpl in H1. apply hashpairinj in H1. tauto.
          + simpl in H2. destruct (ctreeLinv Tr) as [[delta kl]|].
            * discriminate H2.
            * reflexivity.
      }
    * exfalso. simpl in H1.
      apply hashpairinj in H1. destruct H1 as [H1 _].
      apply hashnatinj in H1. omega.
  + change (subqm (mtreeB (ctree_mtree Tl) (ctree_mtree Tr)) (singlebranch_mtree hl gamma)).
    destruct gamma as [[|] gamma].
    * exfalso. simpl in H1.
      apply hashpairinj in H1. destruct H1 as [H1 _].
      apply hashnatinj in H1. omega.
    * exfalso. simpl in H1.
      apply hashpairinj in H1. destruct H1 as [H1 _].
      apply hashnatinj in H1. omega.
Qed.

Lemma subqm_ctree_singlebranch_lub' {n} (T:ctree n) (hl:nehlist) (gamma:bitseq n) :
  ctree_hashroot T = ctree_hashroot (ctreeL hl gamma) ->
  subqc T (ctree_singlebranch_lub gamma hl T).
induction n as [|n IH].
- simpl. unfold ctree_singlebranch_lub. unfold ctreeLinv. unfold subqc. simpl.
  intros H1. apply subqneh_subqh. apply subqneh_lub_2. congruence.
- intros H1.
  unfold ctree_singlebranch_lub.
  destruct (ctreeLinv T) as [[gamma2 hl2]|] eqn:E1.
  + assert (L1: singlebranch_mtree hl2 gamma2 = ctree_mtree T) by exact (ctreeLinv_singlebranch _ _ _ E1).
    assert (L2: ctree_hashroot (ctreeL hl gamma) = ctree_hashroot (ctreeL hl2 gamma2)).
    { generalize (mtree_hashroot_ctree_hashroot T). intros H2.
      rewrite <- L1 in H2.
      generalize (mtree_hashroot_ctree_hashroot_L _ _ _ H2). intros H3.
      congruence.
    }
    assert (L3: gamma = gamma2 /\ nehlist_hashroot hl = nehlist_hashroot hl2).
    { now apply (ctree_hashroot_ctreeL_nehlist_hashroot hl hl2 gamma gamma2). }
    unfold subqc.
    rewrite <- L1.
    destruct L3 as [L3a L3b]. subst gamma2.
    change (subqm (singlebranch_mtree hl2 gamma)
                  (singlebranch_mtree (nehlist_lub hl hl2) gamma)).
    apply subqm_singlebranch_subqneh.
    apply subqneh_lub_2. exact L3b.
  + unfold subqc. apply subqm_ctree_mtree_singlebranch; assumption.
Qed.

Lemma subqc_lub_1 {n} (T1 T2:ctree n) :
  ctree_hashroot T1 = ctree_hashroot T2 ->
  subqc T1 (ctree_lub T1 T2).
unfold subqc.
induction n as [|n IH].
- simpl. intros H1. apply subqneh_lub_1 in H1.
  destruct T1 as [h1|[a1 hr1]]; destruct T2 as [h2|[a2 hr2]].
  + simpl in H1. subst h1. simpl. apply subqh_ref.
  + simpl. apply subqhH.
    apply subqneh_hashroot_eq in H1. simpl in H1.
    subst h1. simpl.
    destruct (hlist_hashroot hr2); reflexivity.
  + simpl. apply subqh_ref.
  + simpl. simpl in H1. destruct H1 as [_ H1].
    apply subqhC. exact H1.
- destruct T1 as [[gamma1 hl1]|[h1|[T1l|[T1r|[T1l T1r]]]]].
  + change (ctree_hashroot (ctreeL hl1 gamma1) = ctree_hashroot T2 ->
            subqm (ctree_mtree (ctreeL hl1 gamma1))
                  (ctree_mtree (ctree_lub (ctreeL hl1 gamma1) T2))).
    change (ctree_hashroot (ctreeL hl1 gamma1) = ctree_hashroot T2 ->
            subqm (ctree_mtree (ctreeL hl1 gamma1))
                  (ctree_mtree (ctree_singlebranch_lub gamma1 hl1 T2))).
    intros H1. apply subqm_ctree_singlebranch_lub.
    symmetry. exact H1.
  + change (h1 = ctree_hashroot T2 ->
            subqm (mtreeH n (Some h1)) (ctree_mtree T2)).
    intros H1.
    change (mtree_hashroot (ctree_mtree T2) = Some h1).
    rewrite mtree_hashroot_ctree_hashroot.
    congruence.
  + destruct T2 as [[gamma2 hl2]|[h2|[T2l|[T2r|[T2l T2r]]]]].
    * change (ctree_hashroot (ctreeBL T1l) = ctree_hashroot (ctreeL hl2 gamma2) ->
              subqm (ctree_mtree (ctreeBL T1l))
                    (ctree_mtree (ctree_lub (ctreeBL T1l) (ctreeL hl2 gamma2)))).
      change (ctree_hashroot (ctreeBL T1l) = ctree_hashroot (ctreeL hl2 gamma2) ->
              subqm (ctree_mtree (ctreeBL T1l))
                    (ctree_mtree (ctree_singlebranch_lub gamma2 hl2 (ctreeBL T1l)))).
      intros H1. apply subqm_ctree_singlebranch_lub'. exact H1.
    * change (ctree_hashroot (ctreeBL T1l) = ctree_hashroot (ctreeH (S n) h2) ->
              subqm (ctree_mtree (ctreeBL T1l))
                    (ctree_mtree (ctree_lub (ctreeBL T1l) (ctreeH (S n) h2)))).
      change (ctree_hashroot (ctreeBL T1l) = h2 ->
              subqm (ctree_mtree (ctreeBL T1l))
                    (ctree_mtree (ctreeBL T1l))).
      intros _. apply subqm_ref.
    * { change (ctree_hashroot (ctreeBL T1l) = ctree_hashroot (ctreeBL T2l) ->
                subqm (ctree_mtree (ctreeBL T1l))
                      (ctree_mtree (ctree_lub (ctreeBL T1l) (ctreeBL T2l)))).
        intros H1.
        change (subqm (mtreeB (ctree_mtree T1l) (empty_mtree n))
                      (ctree_mtree (ctreeBL (ctree_lub T1l T2l)))).
        change (subqm (mtreeB (ctree_mtree T1l) (empty_mtree n))
                      (mtreeB (ctree_mtree (ctree_lub T1l T2l)) (empty_mtree n))).
        split.
        - apply IH. simpl in H1. apply hashpairinj in H1. tauto.
        - apply subqm_ref.
      }
    * intros H1. exfalso. simpl in H1.
      apply hashpairinj in H1. destruct H1 as [H1 _].
      apply hashnatinj in H1. omega.
    * intros H1. exfalso. simpl in H1.
      apply hashpairinj in H1. destruct H1 as [H1 _].
      apply hashnatinj in H1. omega.
  + destruct T2 as [[gamma2 hl2]|[h2|[T2l|[T2r|[T2l T2r]]]]].
    * change (ctree_hashroot (ctreeBR T1r) = ctree_hashroot (ctreeL hl2 gamma2) ->
              subqm (ctree_mtree (ctreeBR T1r))
                    (ctree_mtree (ctree_lub (ctreeBR T1r) (ctreeL hl2 gamma2)))).
      change (ctree_hashroot (ctreeBR T1r) = ctree_hashroot (ctreeL hl2 gamma2) ->
              subqm (ctree_mtree (ctreeBR T1r))
                    (ctree_mtree (ctree_singlebranch_lub gamma2 hl2 (ctreeBR T1r)))).
      intros H1. apply subqm_ctree_singlebranch_lub'. exact H1.
    * change (ctree_hashroot (ctreeBR T1r) = ctree_hashroot (ctreeH (S n) h2) ->
              subqm (ctree_mtree (ctreeBR T1r))
                    (ctree_mtree (ctree_lub (ctreeBR T1r) (ctreeH (S n) h2)))).
      change (ctree_hashroot (ctreeBR T1r) = h2 ->
              subqm (ctree_mtree (ctreeBR T1r))
                    (ctree_mtree (ctreeBR T1r))).
      intros _. apply subqm_ref.
    * intros H1. exfalso. simpl in H1.
      apply hashpairinj in H1. destruct H1 as [H1 _].
      apply hashnatinj in H1. omega.
    * { change (ctree_hashroot (ctreeBR T1r) = ctree_hashroot (ctreeBR T2r) ->
                subqm (ctree_mtree (ctreeBR T1r))
                      (ctree_mtree (ctree_lub (ctreeBR T1r) (ctreeBR T2r)))).
        intros H1.
        change (subqm (mtreeB (empty_mtree n) (ctree_mtree T1r))
                      (ctree_mtree (ctreeBR (ctree_lub T1r T2r)))).
        change (subqm (mtreeB (empty_mtree n) (ctree_mtree T1r))
                      (mtreeB (empty_mtree n) (ctree_mtree (ctree_lub T1r T2r)))).
        split.
        - apply subqm_ref.
        - apply IH. simpl in H1. apply hashpairinj in H1. tauto.
      }
    * intros H1. exfalso. simpl in H1.
      apply hashpairinj in H1. destruct H1 as [H1 _].
      apply hashnatinj in H1. omega.
  + destruct T2 as [[[[|] gamma2] hl2]|[h2|[T2l|[T2r|[T2l T2r]]]]].
    * intros H1. exfalso. simpl in H1.
      apply hashpairinj in H1. destruct H1 as [H1 _].
      apply hashnatinj in H1. omega.
    * intros H1. exfalso. simpl in H1.
      apply hashpairinj in H1. destruct H1 as [H1 _].
      apply hashnatinj in H1. omega.
    * change (ctree_hashroot (ctreeB T1l T1r) = ctree_hashroot (ctreeH (S n) h2) ->
              subqm (ctree_mtree (ctreeB T1l T1r))
                    (ctree_mtree (ctree_lub (ctreeB T1l T1r) (ctreeH (S n) h2)))).
      change (ctree_hashroot (ctreeB T1l T1r) = h2 ->
              subqm (ctree_mtree (ctreeB T1l T1r))
                    (ctree_mtree (ctreeB T1l T1r))).
      intros _. apply subqm_ref.
    * intros H1. exfalso. simpl in H1.
      apply hashpairinj in H1. destruct H1 as [H1 _].
      apply hashnatinj in H1. omega.
    * intros H1. exfalso. simpl in H1.
      apply hashpairinj in H1. destruct H1 as [H1 _].
      apply hashnatinj in H1. omega.
    * { change (ctree_hashroot (ctreeB T1l T1r) = ctree_hashroot (ctreeB T2l T2r) ->
                subqm (ctree_mtree (ctreeB T1l T1r))
                      (ctree_mtree (ctree_lub (ctreeB T1l T1r) (ctreeB T2l T2r)))).
        intros H1.
        change (subqm (mtreeB (ctree_mtree T1l) (ctree_mtree T1r))
                      (ctree_mtree (ctreeB (ctree_lub T1l T2l) (ctree_lub T1r T2r)))).
        change (subqm (mtreeB (ctree_mtree T1l) (ctree_mtree T1r))
                      (mtreeB (ctree_mtree (ctree_lub T1l T2l)) (ctree_mtree (ctree_lub T1r T2r)))).
        assert (L1: ctree_hashroot T1l = ctree_hashroot T2l /\ ctree_hashroot T1r = ctree_hashroot T2r).
        { simpl in H1.
          apply hashpairinj in H1. destruct H1 as [_ H1].
          apply hashpairinj in H1. destruct H1 as [H2 H1].
          apply hashpairinj in H1. tauto.
        }
        split.
        - apply IH. tauto.
        - apply IH. tauto.
      }
Qed.      

Lemma ctree_lub_eq_1 {n} (T1 T2:ctree n) :
  ctree_hashroot T1 = ctree_hashroot T2 ->
  ctree_hashroot (ctree_lub T1 T2) = ctree_hashroot T1.
intros H1. symmetry. apply subqc_hashroot_eq. now apply subqc_lub_1.
Qed.

Lemma ctree_supports_tx_lub_1 tht sigt m tx (T1 T2:ctree 162) fee rew :
  ctree_valid T1 ->
  ctree_hashroot T1 = ctree_hashroot T2 ->
  ctree_supports_tx tht sigt m tx T1 fee rew ->
  ctree_supports_tx tht sigt m tx (ctree_lub T1 T2) fee rew.
intros H0 H1. apply subqc_supports_tx.
- revert H0. unfold ctree_valid.
  apply mtree_hashroot_eq_valid.
  rewrite mtree_hashroot_ctree_hashroot.
  rewrite mtree_hashroot_ctree_hashroot.
  f_equal. apply ctree_lub_eq_1. exact H1.
- apply subqc_lub_1. exact H1.
Qed.

Fixpoint ctree_filter_to_supported_addresses {n} : list (bitseq n) -> ctree n -> ctree n :=
  match n with
    | O => fun (al:list (bitseq 0)) (T:ctree 0) =>
             match al with
               | nil => ctreeH 0 (ctree_hashroot T)
               | _ => T
             end
    | S n => fun (al:list (bitseq (S n))) (T:ctree (S n)) =>
               match al with
                 | nil => ctreeH (S n) (ctree_hashroot T)
                 | _ =>
                   match T with
                     | inr (inr (inl Tl)) => ctreeBL (ctree_filter_to_supported_addresses (strip_bitseq_false0 al) Tl)
                     | inr (inr (inr (inl Tr))) => ctreeBR (ctree_filter_to_supported_addresses (strip_bitseq_true0 al) Tr)
                     | inr (inr (inr (inr (Tl,Tr)))) => ctreeB (ctree_filter_to_supported_addresses (strip_bitseq_false0 al) Tl) (ctree_filter_to_supported_addresses (strip_bitseq_true0 al) Tr)
                     | _ => T
                   end
               end
  end.

Lemma ctree_filter_to_supported_addresses_nil {n} (T:ctree n) :
  ctree_filter_to_supported_addresses nil T = ctreeH n (ctree_hashroot T).
destruct n as [|n]; reflexivity.
Qed.

Lemma subqc_ctree_filter_to_supported_addresses {n} (al:list (bitseq n)) (T:ctree n) :
  subqc (ctree_filter_to_supported_addresses al T) T.
induction n as [|n IH].
- destruct al as [|beta ar].
  + rewrite ctree_filter_to_supported_addresses_nil.
    unfold subqc. simpl. apply subqhH.
    destruct T as [h|[b hl]].
    * simpl. reflexivity.
    * simpl. destruct (hlist_hashroot hl); reflexivity.
  + simpl. apply subqm_ref.
- destruct al as [|beta ar].
  + rewrite ctree_filter_to_supported_addresses_nil.
    change (subqm (mtreeH n (Some (ctree_hashroot T))) (ctree_mtree T)).
    change (mtree_hashroot (ctree_mtree T) = Some (ctree_hashroot T)).
    apply mtree_hashroot_ctree_hashroot.
  + destruct T as [[gamma hl]|[h|[Tl|[Tr|[Tl Tr]]]]].
    * simpl. apply subqm_ref.
    * simpl. apply subqm_ref.
    * { split.
        - apply IH.
        - apply subqm_ref.
      }
    * { split.
        - apply subqm_ref.
        - apply IH.
      }
    * { split.
        - apply IH.
        - apply IH.
      }
Qed.

Lemma ctree_filter_to_supported_addresses_supports_addr {n} (alpha:bitseq n) (al:list (bitseq n)) (T:ctree n) :
  In alpha al ->
  ctree_supports_addr T alpha ->
  ctree_supports_addr (ctree_filter_to_supported_addresses al T) alpha.
induction n as [|n IH].
- intros _ _. change True. tauto.
- intros H1. destruct al as [|beta al].
  + contradiction H1.
  + destruct T as [[gamma hl]|[h|[Tl|[Tr|[Tl Tr]]]]].
    * simpl. tauto.
    * simpl. tauto.
    * { destruct alpha as [[|] alpha]; simpl.
        - intros _. change True. tauto.
        - change (ctree_supports_addr Tl alpha ->
                  ctree_supports_addr
                    (ctree_filter_to_supported_addresses
                       (strip_bitseq_false0 (beta :: al)) Tl) alpha).
          apply IH.
          now apply strip_bitseq_false0_iff.
      }
    * { destruct alpha as [[|] alpha]; simpl.
        - change (ctree_supports_addr Tr alpha ->
                  ctree_supports_addr
                    (ctree_filter_to_supported_addresses
                       (strip_bitseq_true0 (beta :: al)) Tr) alpha).
          apply IH.
          now apply strip_bitseq_true0_iff.
        - intros _. change True. tauto.
      }
    * { destruct alpha as [[|] alpha]; simpl.
        - change (ctree_supports_addr Tr alpha ->
                  ctree_supports_addr
                    (ctree_filter_to_supported_addresses
                       (strip_bitseq_true0 (beta :: al)) Tr) alpha).
          apply IH.
          now apply strip_bitseq_true0_iff.
        - change (ctree_supports_addr Tl alpha ->
                  ctree_supports_addr
                    (ctree_filter_to_supported_addresses
                       (strip_bitseq_false0 (beta :: al)) Tl) alpha).
          apply IH.
          now apply strip_bitseq_false0_iff.
      }
Qed.

Lemma ctree_filter_to_supported_addresses_supports_asset (a:asset) {n} (alpha:bitseq n) (al:list (bitseq n)) (T:ctree n) :
  In alpha al ->
  ctree_supports_asset a T alpha ->
  ctree_supports_asset a (ctree_filter_to_supported_addresses al T) alpha.
induction n as [|n IH].
- intros H1 H2. destruct al as [|beta al].
  + contradiction H1.
  + exact H2.
- intros H1. destruct al as [|beta al].
  + contradiction H1.
  + destruct T as [[gamma hl]|[h|[Tl|[Tr|[Tl Tr]]]]].
    * simpl. tauto.
    * simpl. tauto.
    * { destruct alpha as [[|] alpha]; simpl.
        - intros H2. contradiction H2.
        - change (ctree_supports_asset a Tl alpha ->
                  ctree_supports_asset a
                    (ctree_filter_to_supported_addresses
                       (strip_bitseq_false0 (beta :: al)) Tl) alpha).
          apply IH.
          now apply strip_bitseq_false0_iff.
      }
    * { destruct alpha as [[|] alpha]; simpl.
        - change (ctree_supports_asset a Tr alpha ->
                  ctree_supports_asset a
                    (ctree_filter_to_supported_addresses
                       (strip_bitseq_true0 (beta :: al)) Tr) alpha).
          apply IH.
          now apply strip_bitseq_true0_iff.
        - intros H2. contradiction H2.
      }
    * { destruct alpha as [[|] alpha]; simpl.
        - change (ctree_supports_asset a Tr alpha ->
                  ctree_supports_asset a
                    (ctree_filter_to_supported_addresses
                       (strip_bitseq_true0 (beta :: al)) Tr) alpha).
          apply IH.
          now apply strip_bitseq_true0_iff.
        - change (ctree_supports_asset a Tl alpha ->
                  ctree_supports_asset a
                    (ctree_filter_to_supported_addresses
                       (strip_bitseq_false0 (beta :: al)) Tl) alpha).
          apply IH.
          now apply strip_bitseq_false0_iff.
      }
Qed.

Definition octree_totalassets {n} (T:option (ctree n)) (al:list asset) : Prop :=
  mtree_totalassets (octree_mtree T) al.

Lemma octree_approx_fun_p_totalassets {n} (T:option (ctree n)) (f:bitseq n -> list asset) (al:list asset) :
  octree_approx_fun_p T f ->
  (octree_totalassets T al <-> totalassets_ f = al).
intros H1. unfold octree_totalassets.
apply (mtree_approx_fun_p_totalassets (octree_mtree T) f al).
exact H1.
Qed.

Lemma octree_totalunits_lem (T:option (ctree 162)) (f:statefun) (al:list asset) :
  octree_approx_fun_p T f ->
  octree_totalassets T al ->
  asset_value_sum al = statefun_totalunits f.
exact (mtree_totalunits_lem (octree_mtree T) f al).
Qed.

Definition octree_valid (T:option (ctree 162)) : Prop :=
  match T with
    | Some T => ctree_valid T
    | None => True
  end.

Opaque mtree_totalassets.

Lemma octree_valid_mtree_valid (T:option (ctree 162)) :
  octree_valid T -> mtree_valid (octree_mtree T).
destruct T as [T|].
- exact (fun H => H).
- exists (fun alpha:addr => nil). split.
  + assert (L1: forall n, forall alphapre, sf_valid_ alphapre (fun alpha:bitseq n => nil)).
    { intros n alphapre.
      split.
      - intros _. apply no_dups_nil.
      - split.
        + intros h alpha u alpha' u' [].
        + split.
          * intros h bday u alpha [].
          * { split.
              - intros h H1 [_ []].
              - intros alpha b h bday obl u beta h' bday' obl' u' beta' [].
            }
    }
    exact (L1 162 (fun alpha => alpha)).
  + assert (L2: forall n, mtree_approx_fun_p (empty_mtree n) (fun alpha:bitseq n => nil)).
    { induction n as [|n IH].
      - reflexivity.
      - exists (empty_mtree n). exists (empty_mtree n). repeat split.
        + rewrite mtree_hashroot_empty. reflexivity.
        + exact IH.
        + exact IH.
    }
    unfold octree_mtree.
    apply L2.
Qed.

Theorem octree_tx_asset_value_sum tht sigt (blockheight:nat) (T:option (ctree 162)) (tx:Tx) (fee rew:nat) (al bl:list asset) :
  octree_valid T ->
  tx_valid tx ->
  octree_supports_tx tht sigt blockheight tx T fee rew ->
  octree_totalassets T al ->
  octree_totalassets (tx_octree_trans blockheight tx T) bl ->
  asset_value_sum bl + fee + out_burncost (tx_outputs tx) = asset_value_sum al + rew.
intros H1 H2 H3 H4 H5.
assert (L1: mtree_valid (octree_mtree T)) by exact (octree_valid_mtree_valid _ H1).
apply (mtree_normalize_tx_asset_value_sum tht sigt blockheight (octree_mtree T) tx fee rew al bl L1 H2).
- now apply octree_mtree_supports_tx.
- unfold octree_totalassets in H4. exact H4.
- unfold octree_totalassets in H5.
  rewrite (tx_trans_mtree_octree_eq tht sigt blockheight tx T fee rew H3) in H5.
  exact H5.
Qed.

Definition ctree_unique_supported_assets {n} (T:ctree n) : Prop :=
  forall h alpha u beta v,
    ctree_supports_asset (h,u) T alpha ->
    ctree_supports_asset (h,v) T beta ->
    alpha = beta /\ u = v.

Opaque ctree.
Opaque ctreeLinv.
Opaque ctree_mtree.
Opaque mtree_octree.
Opaque tx_octree_trans_.
Opaque ctree_hashroot.

Lemma ctree_valid_unique_supported_assets (T:ctree 162) :
  octree_valid (Some T) ->
  ctree_unique_supported_assets T.
intros [f [[H1 [H2 [H3 H4]]] H5]].
intros h alpha u beta v H6 H7.
apply ctree_mtree_supports_asset in H6.
apply ctree_mtree_supports_asset in H7.
unfold octree_mtree in H5.
apply (mtree_supports_asset_In_statefun _ _ f _ H5) in H6.
apply (mtree_supports_asset_In_statefun _ _ f _ H5) in H7.
exact (H2 h alpha u beta v H6 H7).
Qed.

Theorem octree_valid_tx_octree_trans tht sigt m tx T fee rew :
  tx_valid tx ->
  ctree_supports_tx tht sigt m tx T fee rew ->
  ctree_valid T ->
  octree_valid (tx_octree_trans m tx (Some T)).
intros H0 H1 [f [H2 H3]].
destruct (tx_octree_trans m tx (Some T)) as [T'|] eqn:E1.
- simpl.
  exists (tx_statefun_trans m tx f). split.
  + apply sf_tx_valid_thm with (tht := tht) (sigt := sigt) (bday := m) (fee := fee) (rew := rew).
    * exact H2.
    * exact H0.
    * { change (octree_supports_tx tht sigt m tx (Some T) fee rew) in H1.
        apply octree_mtree_supports_tx in H1.
        apply mtree_supports_tx_statefun with (f := f) in H1.
        - exact H1.
        - destruct H2 as [_ [Hf2 _]]. exact Hf2.
        - exact H3.
      }
  + change (mtree_approx_fun_p (octree_mtree (Some T')) (tx_statefun_trans m tx f)).
    rewrite <- E1.
    rewrite tx_trans_mtree_octree_eq with (tht := tht) (sigt := sigt) (fee := fee) (rew := rew).
    * { apply mtree_normal_approx_trans with (tht := tht) (sigt := sigt) (fee := fee) (rew := rew).
        - exact H2.
        - apply octree_mtree_supports_tx. exact H1.
        - exact H3.
      }
    * exact H1.
- simpl. tauto.
Qed.

(*** Alt Proof:
intros H0 H1 H2.
unfold octree_valid.
rewrite tx_trans_mtree_octree_eq with (fee := fee) (rew := rew).
- apply mtree_valid_normalize.
  apply mtree_valid_tx_mtree_trans with (m := m) (fee := fee) (rew := rew).
  + exact H0.
  + apply octree_mtree_supports_tx. exact H1.
  + exact H2.
- exact H1.
Qed.
***)
