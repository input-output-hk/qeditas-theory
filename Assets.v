(** Copyright (c) 2015 Bill White **)
(** Distributed under the MIT/X11 software license **)
(** See http://www.opensource.org/licenses/mit-license.php **)

(** Assets: Representation of assets as 4-tuples:
    (hashval) id
    (birthday) block height at which asset was confirmed
    (obligation) obligations to be met in order to spend the asset [default of None means the holder signs for it]
    (preasset) the kind of asset
    The preassets include currency units, bounties (for proving a conjecture),
    owns (ownership of objs/props), rights (for using an obj/prop), intention (as
    part of a publication protocol) and publication (for formal documents).
    The usereq is (al,(m,n)) where al is a list of addresses that can sign to spend,
    m is the number of addresses that must sign, and n is the block height
    at which spending is first allowed.
 **)

Require Export MathData.

Inductive preasset : Type :=
| currency : nat -> preasset (*** currency u is u units of currency ***)
| bounty : nat -> preasset (*** Idea: If alpha holds this, then the bounty can be converted (back) to currency units sent to beta in a transaction in which beta publishes a 'soln' to alpha. This is an example where the required signer is not the holder. ***)
| owns : bool -> addr -> option nat -> preasset (*** Idea: If beta holds owns alpha n, then alpha controls who can obtain the rights to use the data that hashes to beta. People can create such rights by paying n units to alpha, unless n is None, in which case only the owner can use it. The initial bool is just to distinguish between owning objects (owns false) and owning propositions (owns true). ***)
| rights : bool -> nat -> addr -> preasset (*** Idea: If alpha has rights n beta, then alpha can use this to use the data that hashes to beta up to n times. Could have another version with an expiration block. ***)
| intention : addr -> preasset (*** Idea: If alpha has intention beta, then beta and only beta can publish a nonced document which hashes to alpha. (If someone else sees the document they can create a different nonced document, add the corresponding commitment and then try to publish their copy of the document. Presumably this would be too late to have priority over beta.) ***)
| theorypublication : nat -> theory -> preasset (*** nonce and data ***)
| signapublication : nat -> option hashval -> signa -> preasset (*** nonce and data ***)
| docpublication : nat -> option hashval -> doc -> preasset (*** nonce and data ***)
.

(*** obligation (a,b) : a : address, b : nat
 means to spend the asset the block height must be at least b
 and a signature/script for address a is required.
 The obligation can also be met via endorsement to another address a' which then signs it.
 None means that the holder signs for it and the block height restriction is effectively 0.
 ***)
Definition obligation : Type := option (prod addr nat).

Definition preasset_value (u:preasset) : option nat :=
  match u with
    | currency v => Some v
    | bounty v => Some v
    | _ => None
  end.

Definition asset : Type := prod hashval (prod nat (prod obligation preasset)).

Definition assetid (a:asset) : hashval := fst a.
Definition assetbday (a:asset) : nat := fst (snd a).
Definition assetobl (a:asset) : obligation := fst (snd (snd a)).
Definition assetpre (a:asset) : preasset := snd (snd (snd a)).

Definition asset_value (a:asset) : option nat := preasset_value (assetpre a).

Definition hashpreasset (a:preasset) : hashval :=
match a with
| currency u => hashpair (hashnat 0) (hashnat u)
| bounty u => hashpair (hashnat 1) (hashnat u)
| owns false alpha (Some u) => hashpair (hashnat 2) (hashpair (hashaddr alpha) (hashnat u))
| owns true alpha (Some u) => hashpair (hashnat 3) (hashpair (hashaddr alpha) (hashnat u))
| owns false alpha None => hashpair (hashnat 4) (hashaddr alpha)
| owns true alpha None => hashpair (hashnat 5) (hashaddr alpha)
| rights false n alpha => hashpair (hashnat 6) (hashpair (hashnat n) (hashaddr alpha))
| rights true n alpha => hashpair (hashnat 7) (hashpair (hashnat n) (hashaddr alpha))
| intention alpha => hashpair (hashnat 8) (hashaddr alpha)
| theorypublication n d => hashpair (hashnat 9) (hashpair (hashnat n) (hashtheory d))
| signapublication n th d => hashpair (hashnat 10) (hashpair (hashnat n) (hashopair2 th (hashsigna d)))
| docpublication n th d => hashpair (hashnat 11) (hashpair (hashnat n) (hashopair2 th (hashdoc d)))
end.

Definition hashobligation (obl:obligation) : hashval :=
match obl with
| None => hashnat 0
| Some(a,b) => hashpair (hashaddr a) (hashnat b)
end.

Definition hashasset (a:asset) : hashval :=
match a with
| (h,(bday,(obl,p))) =>
  hashpair h (hashpair (hashnat bday) (hashpair (hashobligation obl) (hashpreasset p)))
end.

Lemma hashpreassetinj a b :
hashpreasset a = hashpreasset b -> a = b.
destruct a as [u|u|[|] alpha [u|]|[|] k alpha|alpha|m d|m th d|m th d]; destruct b as [v|v|[|] beta [v|]|[|] k' beta|beta|n d'|n th' d'|n th' d'];
  try (simpl; intros H1; exfalso; apply hashpairinj in H1; destruct H1 as [H1 _]; apply hashnatinj in H1; omega).
- simpl. intros H1.
  apply hashpairinj in H1. destruct H1 as [_ H1].
  apply hashnatinj in H1.
  congruence.
- simpl. intros H1. apply hashpairinj in H1. destruct H1 as [_ H1].
  apply hashnatinj in H1.
  congruence.
- simpl. intros H1. apply hashpairinj in H1. destruct H1 as [_ H1].
  apply hashpairinj in H1. destruct H1 as [H2 H3].
  apply hashaddrinj in H2.
  apply hashnatinj in H3.
  congruence.
- simpl. intros H1. apply hashpairinj in H1. destruct H1 as [_ H1].
  apply hashaddrinj in H1.
  congruence.
- simpl. intros H1. apply hashpairinj in H1. destruct H1 as [_ H1].
  apply hashpairinj in H1. destruct H1 as [H2 H3].
  apply hashaddrinj in H2.
  apply hashnatinj in H3.
  congruence.
- simpl. intros H1. apply hashpairinj in H1. destruct H1 as [_ H1].
  apply hashaddrinj in H1.
  congruence.
- simpl. intros H1. apply hashpairinj in H1. destruct H1 as [_ H1].
  apply hashpairinj in H1. destruct H1 as [H2 H3].
  apply hashnatinj in H2.
  apply hashaddrinj in H3.
  congruence.
- simpl. intros H1. apply hashpairinj in H1. destruct H1 as [_ H1].
  apply hashpairinj in H1. destruct H1 as [H2 H3].
  apply hashnatinj in H2.
  apply hashaddrinj in H3.
  congruence.
- simpl. intros H1. apply hashpairinj in H1. destruct H1 as [_ H1].
  apply hashaddrinj in H1.
  congruence.
- simpl. intros H1. apply hashpairinj in H1. destruct H1 as [_ H1].
  apply hashpairinj in H1. destruct H1 as [H2 H3].
  apply hashnatinj in H2.
  f_equal.
  + congruence.
  + revert H3. apply hashtheoryinj.
- simpl. intros H1. apply hashpairinj in H1. destruct H1 as [_ H1].
  apply hashpairinj in H1. destruct H1 as [H2 H3].
  apply hashopair2inj in H3. destruct H3 as [H4 H5].
  apply hashsignainj in H5.
  apply hashnatinj in H2.
  congruence.
- simpl. intros H1. apply hashpairinj in H1. destruct H1 as [_ H1].
  apply hashpairinj in H1. destruct H1 as [H2 H3].
  apply hashopair2inj in H3. destruct H3 as [H4 H5].
  apply hashdocinj in H5.
  apply hashnatinj in H2.
  congruence.
Qed.

Lemma hashobligationinj (obl obl':obligation) :
  hashobligation obl = hashobligation obl' -> obl = obl'.
destruct obl as [[a b]|]; destruct obl' as [[a' b']|]; simpl; intros H1.
- apply hashpairinj in H1. destruct H1 as [H2 H3].
  apply hashaddrinj in H2. apply hashnatinj in H3.
  congruence.
- symmetry in H1. apply hashnatpairdiscr in H1. tauto.
- apply hashnatpairdiscr in H1. tauto.
- reflexivity.
Qed.

Lemma hashassetinj a b :
hashasset a = hashasset b -> a = b.
destruct a as [h [bday [obl u]]]. destruct b as [k [bday' [obl' v]]].
simpl. intros H1.
apply hashpairinj in H1. destruct H1 as [H2 H3].
apply hashpairinj in H3. destruct H3 as [H4 H5].
apply hashpairinj in H5. destruct H5 as [H6 H7].
apply hashnatinj in H4.
apply hashobligationinj in H6.
apply hashpreassetinj in H7.
congruence.
Qed.

Definition addr_assetid : Type := prod addr hashval.
Definition addr_preasset : Type := prod addr (prod obligation preasset).
Definition addr_asset : Type := prod addr asset.

Definition hash_addr_assetid (aa : addr_assetid) : hashval :=
let (alpha,h) := aa in
hashpair (hashaddr alpha) h.

Definition hash_addr_preasset (au : addr_preasset) : hashval :=
match au with
| (alpha,(obl,u)) => hashlist ((hashaddr alpha)::(hashobligation obl)::(hashpreasset u)::nil)
end.

Lemma hash_addr_assetidinj alpha a beta b :
 hash_addr_assetid (alpha,a) = hash_addr_assetid (beta,b)
 -> alpha = beta /\ a = b.
unfold hash_addr_assetid. intros H1.
apply hashpairinj in H1. destruct H1 as [H2 H3].
apply hashaddrinj in H2. tauto.
Qed.

Lemma map_hash_addr_assetidinj inpl inpl' :
 map hash_addr_assetid inpl = map hash_addr_assetid inpl'
 -> inpl = inpl'.
revert inpl'. induction inpl as [|[alpha a] inpr IH].
- intros [|[beta b] inpr'].
  + reflexivity.
  + intros H1. discriminate H1.
- intros [|[beta b] inpr'].
  + intros H1. discriminate H1.
  + intros H1.
    change ((hash_addr_assetid (alpha, a) :: map hash_addr_assetid inpr) =
            (hash_addr_assetid (beta, b) :: map hash_addr_assetid inpr')) in H1.
    f_equal.
    * assert (L1: alpha = beta /\ a = b).
      { apply hash_addr_assetidinj. congruence. }
      destruct L1 as [L1a L1b]. congruence.
    * apply IH. congruence.
Qed.

Lemma hash_addr_preassetinj au bv :
  hash_addr_preasset au = hash_addr_preasset bv
  -> au = bv.
destruct au as [alpha [obl u]], bv as [beta [obl' v]].
intros H1. unfold hash_addr_preasset in H1.
apply hashlistinj in H1.
inversion H1. apply hashaddrinj in H0. subst beta.
apply hashobligationinj in H2.
apply hashpreassetinj in H3.
congruence.
Qed.

Lemma map_hash_addr_preassetinj outpl outpl' :
 map hash_addr_preasset outpl = map hash_addr_preasset outpl'
 -> outpl = outpl'.
revert outpl'. induction outpl as [|[alpha u] outpr IH].
- intros [|[beta v] outpr'].
  + reflexivity.
  + intros H1. discriminate H1.
- intros [|[beta v] outpr'].
  + intros H1. discriminate H1.
  + intros H1.
    change ((hash_addr_preasset (alpha, u) :: map hash_addr_preasset outpr) =
            (hash_addr_preasset (beta, v) :: map hash_addr_preasset outpr')) in H1.
    f_equal.
    * apply hash_addr_preassetinj. congruence.
    * apply IH. congruence.
Qed.

Fixpoint asset_value_out (outpl:list addr_preasset) : nat :=
match outpl with
| (alpha,(obl,currency u))::outpr => u + asset_value_out outpr
| (alpha,(obl,bounty u))::outpr => u + asset_value_out outpr
| (alpha,_)::outpr => asset_value_out outpr
| nil => 0
end.

Lemma asset_value_out_app (l r:list addr_preasset) :
  asset_value_out (l ++ r) = asset_value_out l + asset_value_out r.
induction l as [|[beta [obl u]] l IH].
- simpl. reflexivity.
- simpl. destruct u as [u|u|[|] alpha [u|]|[|] k alpha|alpha|m d|m th d|m th d]; simpl; omega.
Qed.

Definition preasset_eq_dec (a1 a2:preasset) : {a1 = a2} + {a1 <> a2}.
destruct a1 as [u|u|[|] alpha [u|]|[|] k alpha|alpha|m d|m th d|m th d]; destruct a2 as [v|v|[|] beta [v|]|[|] k' beta|beta|n d'|n th' d'|n th' d']; try (right; discriminate).
- destruct (eq_nat_dec u v) as [D1|D1].
  + left. congruence.
  + right. intros H1. inversion H1. tauto.
- destruct (eq_nat_dec u v) as [D1|D1].
  + left. congruence.
  + right. intros H1. inversion H1. tauto.
- destruct (eq_nat_dec u v) as [D1|D1].
  + destruct (addr_eq_dec alpha beta) as [D2|D2].
    * left. congruence.
    * right. intros H1. inversion H1. tauto.
  + right. intros H1. inversion H1. tauto.
- destruct (addr_eq_dec alpha beta) as [D1|D1].
  + left. congruence.
  + right. intros H1. inversion H1. tauto.
- destruct (eq_nat_dec u v) as [D1|D1].
  + destruct (addr_eq_dec alpha beta) as [D2|D2].
    * left. congruence.
    * right. intros H1. inversion H1. tauto.
  + right. intros H1. inversion H1. tauto.
- destruct (addr_eq_dec alpha beta) as [D1|D1].
  + left. congruence.
  + right. intros H1. inversion H1. tauto.
- destruct (eq_nat_dec k k') as [D1|D1].
  + destruct (addr_eq_dec alpha beta) as [D2|D2].
    * left. congruence.
    * right. intros H1. inversion H1. tauto.
  + right. intros H1. inversion H1. tauto.
- destruct (eq_nat_dec k k') as [D1|D1].
  + destruct (addr_eq_dec alpha beta) as [D2|D2].
    * left. congruence.
    * right. intros H1. inversion H1. tauto.
  + right. intros H1. inversion H1. tauto.
- destruct (addr_eq_dec alpha beta) as [D1|D1].
  + left. congruence.
  + right. intros H1. inversion H1. tauto.
- destruct (eq_nat_dec m n) as [D1|D1].
  + destruct (theory_eq_dec d d') as [D2|D2].
    * left. congruence.
    * right. intros H1. inversion H1. tauto.
  + right. intros H1. inversion H1. tauto.
- destruct (eq_nat_dec m n) as [D1|D1].
  + destruct (signa_eq_dec d d') as [D2|D2].
    * { destruct (ohashval_eq_dec th th') as [D3|D3].
        - left. congruence.
        - right. intros H1. inversion H1. tauto.
      }
    * right. intros H1. inversion H1. tauto.
  + right. intros H1. inversion H1. tauto.
- destruct (eq_nat_dec m n) as [D1|D1].
  + destruct (doc_eq_dec d d') as [D2|D2].
    * { destruct (ohashval_eq_dec th th') as [D3|D3].
        - left. congruence.
        - right. intros H1. inversion H1. tauto.
      }
    * right. intros H1. inversion H1. tauto.
  + right. intros H1. inversion H1. tauto.
Defined.

Definition obligation_eq_dec (obl1 obl2 : obligation) : { obl1 = obl2 } + { obl1 <> obl2 }.
destruct obl1 as [[a1 b1]|]; destruct obl2 as [[a2 b2]|]; try (right; congruence).
- destruct (addr_eq_dec a1 a2) as [D1|D1]; try (right; congruence).
  destruct (eq_nat_dec b1 b2) as [D2|D2]; try (right; congruence).
  left; congruence.
- left; reflexivity.
Defined.

Definition asset_eq_dec (a1 a2:asset) : {a1 = a2} + {a1 <> a2}.
destruct a1 as [h1 [bday1 [obl1 u1]]], a2 as [h2 [bday2 [obl2 u2]]].
destruct (hashval_eq_dec h1 h2).
- destruct (eq_nat_dec bday1 bday2).
  + destruct (obligation_eq_dec obl1 obl2).
    * { destruct (preasset_eq_dec u1 u2).
        - left. congruence.
        - right. congruence.
      }
    * right. congruence.
  + right. congruence.
- right. congruence.
Defined.

Fixpoint new_assets (bday:nat) (alpha:addr) (aul:list addr_preasset) (txh:hashval) (i:nat) : list asset :=
match aul with
  | nil => nil
  | (beta,(obl,u))::aul' =>
    if addr_eq_dec alpha beta then
      (hashpair txh (hashnat i),(bday,(obl,u)))::(new_assets bday alpha aul' txh (S i))
    else
      new_assets bday alpha aul' txh (S i)
end.

Fixpoint remove_assets (al:list asset) (spent:list hashval) : list asset :=
match al with
| nil => nil
| a::al' =>
  if in_dec hashval_eq_dec (assetid a) spent then
    remove_assets al' spent
  else
    cons a (remove_assets al' spent)
end.

Fixpoint get_spent (alpha:addr) (inpl:list addr_assetid) : list hashval :=
match inpl with
| nil => nil
| cons (beta,a) inpl' =>
  if addr_eq_dec alpha beta then
    cons a (get_spent alpha inpl')
  else
    get_spent alpha inpl'
end.

Fixpoint add_vout (bday:nat) (txh:hashval) (outpl:list addr_preasset) (i:nat) : list (addr * asset)%type :=
match outpl with
| nil => nil
| cons (alpha,(obl,u)) outpl' => cons (alpha,(hashpair txh (hashnat i),(bday,(obl,u)))) (add_vout bday txh outpl' (S i))
end.

Lemma new_assets_iff bday a alpha aul txh i :
  In a (new_assets bday alpha aul txh i)
  <->
  (bday = assetbday a /\
   exists j, nth_error aul j = value (alpha,(assetobl a,assetpre a)) /\ assetid a = hashpair txh (hashnat (i+j))).
destruct a as [h [bday' [obl u]]]. revert i. induction aul as [|[beta [obl' v]] aur IH].
- intros i. split.
  + simpl. tauto.
  + intros [Hb [[|j] [H1 _]]] ; discriminate H1.
- simpl. intros i. destruct (addr_eq_dec alpha beta) as [H1|H1]; split.
  + intros [H2|H2].
    * { split.
        - inversion H2. reflexivity.
        - exists 0. simpl. split.
          + inversion H2. subst beta. reflexivity.
          + assert (L1: i + 0 = i) by omega.
            rewrite L1.
            congruence.
      }
    * { apply IH in H2. destruct H2 as [Hb [j [H3 H4]]]. split.
        - exact Hb.
        - exists (S j). split.
          + exact H3.
          + assert (L1: i + S j = S i + j) by omega.
            rewrite L1.
            exact H4.
      }
  + intros [Hb [[|j] [H2 H3]]]; simpl in *|-*.
    * { left. inversion H2. f_equal.
        - assert (L1: i + 0 = i) by omega.
          rewrite L1 in H3. now symmetry.
        - rewrite Hb. reflexivity.
       }
    * { right. apply IH. split.
        - exact Hb.
        - exists j. split.
          + assumption.
          + assert (L1: S i + j = i + S j) by omega.
            rewrite L1. assumption.
      }
  + intros H2. apply IH in H2. destruct H2 as [Hb [j [H3 H4]]]. split.
    * exact Hb.
    * { exists (S j). split.
        - exact H3.
        - assert (L1: i + S j = S i + j) by omega.
          rewrite L1. assumption.
      }
  + intros [Hb [[|j] [H2 H3]]].
    * exfalso. simpl in H2. inversion H2. congruence.
    * { apply IH. split.
        - exact Hb.
        - exists j. split.
          + exact H2.
          + assert (L1: S i + j = i + S j) by omega.
            rewrite L1. assumption.
      }
Qed.

Lemma remove_assets_iff a al spent :
  In a (remove_assets al spent)
  <->
  In a al /\ ~In (assetid a) spent.
destruct a as [h [obl u]]. induction al as [|[h' [obl' u']] ar IH].
- simpl. tauto.
- simpl. destruct (in_dec hashval_eq_dec h' spent) as [H1|H1]; split.
  + intros H2. apply IH in H2. tauto.
  + intros [[H2|H2] H3].
    * congruence.
    * apply IH. tauto.
  + intros [H2|H2].
    * { split.
        - tauto.
        - inversion H2. subst h'. assumption.
      }
    * tauto.
  + intros [[H2|H2] H3].
    * now left.
    * right. tauto.
Qed.

Lemma get_spent_iff h alpha inpl :
In h (get_spent alpha inpl)
<->
In (alpha,h) inpl.
induction inpl as [|[beta h'] inpr IH].
- simpl. tauto.
- simpl. destruct (addr_eq_dec alpha beta) as [H1|H1]; split.
  + intros [H2|H2].
    * left. congruence.
    * right. tauto.
  + intros [H2|H2].
    * left. inversion H2. reflexivity.
    * right. tauto.
  + tauto.
  + intros [H2|H2].
    * congruence.
    * tauto.
Qed.

Lemma no_dups_new_assets bday alpha aul txh i :
  no_dups (new_assets bday alpha aul txh i).
revert i. induction aul as [|[beta [obl v]] aur IH]; intros i.
- simpl. apply no_dups_nil.
- simpl. destruct (addr_eq_dec alpha beta) as [H1|H1].
  + apply no_dups_cons.
    * intros H2. apply new_assets_iff in H2. destruct H2 as [Hb [j [H3 H4]]].
      apply hashpairinj in H4. destruct H4 as [_ H4].
      apply hashnatinj in H4. omega.
    * apply IH.
  + apply IH.
Qed.

Lemma no_dups_remove_assets al spent :
no_dups al -> no_dups (remove_assets al spent).
intros H. induction H as [|[h [obl u]] al H1 H2 IH].
- simpl. apply no_dups_nil.
- simpl. destruct (in_dec hashval_eq_dec h spent) as [H3|H3].
  + assumption.
  + apply no_dups_cons.
    * intros H4. apply remove_assets_iff in H4. tauto.
    * assumption.
Qed.

Lemma remove_assets_noint_eq (al:list asset) (rem:list hashval) :
  (forall k, In k rem -> ~In_dom k al) ->
  remove_assets al rem = al.
induction al as [|[h [obl u]] ar IH].
- intros _. reflexivity.
- intros H1. simpl. destruct (in_dec hashval_eq_dec h rem) as [D1|D1].
  + exfalso. apply (H1 h D1). now left.
  + f_equal. apply IH. intros k H2 H3. apply (H1 k H2). now right.
Qed.

Lemma fnl_remove_assets (al:list asset) (rem:list hashval) :
  fnl al -> fnl (remove_assets al rem).
intros H. induction H as [|h u al H1 H2 IH].
- apply fnl_N.
- simpl. destruct (in_dec hashval_eq_dec h rem) as [H3|H3].
  + exact IH.
  + apply fnl_C.
    * intros H4. apply H1. apply In_In_dom_lem in H4.
      destruct H4 as [v H4].
      apply remove_assets_iff in H4. destruct H4 as [H5 H6].
      apply In_In_dom_lem. exists v. assumption.
    * exact IH.
Qed.

Definition hashassetlist (al:list asset) : option hashval := ohashlist (map hashasset al).

Lemma hashassetlistinj al bl : hashassetlist al = hashassetlist bl -> al = bl.
intros H1.
change (ohashlist (map hashasset al) = ohashlist (map hashasset bl)) in H1.
apply ohashlistinj in H1.
revert bl H1. induction al as [|a al IH]; intros [|b bl] H1.
- reflexivity.
- discriminate H1.
- discriminate H1.
- simpl in H1. inversion H1. apply hashassetinj in H0. subst b. f_equal.
  now apply IH.
Qed.

Definition asset_value_sum (al:list asset) : nat :=
fold_right plus 0 (map (fun a => match asset_value a with Some u => u | None => 0 end) al).

Lemma asset_value_sum_value_nil :
  asset_value_sum nil = 0.
reflexivity.
Qed.

Lemma asset_value_sum_value_cons a al u :
  asset_value a = Some u ->
  asset_value_sum (a::al) = u + asset_value_sum al.
intros H1. unfold asset_value_sum. simpl. rewrite H1.
reflexivity.
Qed.

Lemma asset_value_sum_novalue_cons a al :
  asset_value a = None ->
  asset_value_sum (a::al) = asset_value_sum al.
intros H1. unfold asset_value_sum. simpl. rewrite H1.
reflexivity.
Qed.

Lemma asset_value_sum_app (l r:list asset) :
asset_value_sum l
+
asset_value_sum r
= 
asset_value_sum (l ++ r).
unfold asset_value_sum. induction l as [|[h u] l IH].
- simpl. reflexivity.
- simpl. rewrite <- plus_assoc. rewrite IH. reflexivity.
Qed.

Lemma app_perm_asset_value_sum (l r:list asset) :
  app_perm l r ->
  asset_value_sum l = asset_value_sum r.
intros H. induction H as [l r|l1 r1 l2 r2 H1 IH1 H2 IH2|l|l r H1 IH1|l r s H1 IH1 H2 IH2].
- rewrite <- asset_value_sum_app. rewrite <- asset_value_sum_app. omega.
- rewrite <- asset_value_sum_app. rewrite <- asset_value_sum_app. omega.
- omega.
- omega.
- omega.
Qed.

Lemma remove_assets_app (al bl:list asset) (rl:list hashval) :
  remove_assets (al ++ bl) rl = (remove_assets al rl) ++ (remove_assets bl) rl.
induction al as [|[h u] al IH].
- reflexivity.
- simpl. destruct (in_dec hashval_eq_dec h rl) as [H1|H1].
  + exact IH.
  + rewrite IH. reflexivity.
Qed.

Lemma remove_assets_nil (l:list asset) :
  remove_assets l nil = l.
induction l as [|[h u] l IH].
- reflexivity.
- simpl. rewrite IH. reflexivity.
Qed.

Lemma remove_assets_nIn_cons (l:list asset) (h:hashval) (rem:list hashval) :
  (~exists u, In (h,u) l) ->
  remove_assets l (h::rem) = remove_assets l rem.
induction l as [|[k v] l IH]; intros H1.
- reflexivity.
- simpl. destruct (hashval_eq_dec h k) as [D1|D1].
  + exfalso. apply H1. exists v. left. congruence.
  + destruct (in_dec hashval_eq_dec k rem) as [D2|D2].
    * apply IH. intros [u H2]. apply H1. exists u. now right.
    * f_equal. apply IH. intros [u H2]. apply H1. exists u. now right.
Qed.

Lemma remove_assets_app2 (l:list asset) (rem1 rem2:list hashval) :
  remove_assets l (rem1 ++ rem2) = remove_assets (remove_assets l rem1) rem2.
induction l as [ |[k v] l IH].
- reflexivity.
- simpl. destruct (in_dec hashval_eq_dec k (rem1 ++ rem2)) as [D1|D1].
  + destruct (in_dec hashval_eq_dec k rem1) as [D2|D2].
    * exact IH.
    * { simpl. destruct (in_dec hashval_eq_dec k rem2) as [D3|D3].
        - exact IH.
        - exfalso. apply in_app_or in D1. tauto.
      }
  + destruct (in_dec hashval_eq_dec k rem1) as [D2|D2].
    * exfalso. apply D1. apply in_or_app. tauto.
    * { simpl. destruct (in_dec hashval_eq_dec k rem2) as [D3|D3].
        - exfalso. apply D1. apply in_or_app. tauto.
        - f_equal. exact IH.
      } 
Qed.

Lemma remove_assets_eq (l:list asset) (rl1 rl2:list hashval) :
  (forall h, In_dom h l -> (In h rl1 <-> In h rl2)) ->
  remove_assets l rl1 = remove_assets l rl2.
induction l as [|[h u] l IH].
- intros _. reflexivity.
- intros H1. simpl.
  destruct (in_dec hashval_eq_dec h rl1) as [H2|H2];
  destruct (in_dec hashval_eq_dec h rl2) as [H3|H3].
  + apply IH. intros k H4. apply H1. now right.
  + exfalso. apply H3. apply H1.
    * now left.
    * assumption.
  + exfalso. apply H2. apply H1.
    * now left.
    * assumption.
  + f_equal. apply IH. intros k H4. apply H1. now right.
Qed.

Lemma asset_value_sum_asset_shift (al:list asset) h a u rl :
  fnl al ->
  no_dups (h::rl) ->
  In (h,a) al ->
  asset_value (h,a) = Some u ->
  u + asset_value_sum (remove_assets al (h::rl)) = asset_value_sum (remove_assets al rl).
intros H H0. induction H as [|k v al H1 H2 IH].
- simpl. tauto.
- simpl. intros H3 E0. destruct (hashval_eq_dec h k) as [H4|H4].
  + destruct (in_dec hashval_eq_dec k rl) as [H5|H5].
    * exfalso. inversion H0. subst k. contradiction.
    * { destruct H3 as [H3|H3].
        - inversion H3.
          rewrite (asset_value_sum_value_cons _ _ _ E0).
          f_equal.
          subst k.
          apply app_perm_asset_value_sum.
          rewrite (remove_assets_eq al (h::rl) rl).
          + apply app_perm_ref.
          + intros k H8. split.
            * { intros [H9|H9].
                - exfalso. apply H1. subst k. assumption.
                - assumption.
              }
            * intros H9. now right.
        - exfalso. apply H1. apply In_In_dom_lem. exists a. subst k. assumption.
      }
  + destruct (in_dec hashval_eq_dec k rl) as [H5|H5].
    * { destruct H3 as [H3|H3].
        - inversion H3. exfalso. congruence.
        - now apply IH.
      } 
    * { destruct H3 as [H3|H3].
        - inversion H3. exfalso. congruence.
        - destruct (asset_value (k,v)) as [w|] eqn: E1.
          + rewrite (asset_value_sum_value_cons _ _ _ E1).
            rewrite (asset_value_sum_value_cons _ _ _ E1).
            apply IH in H3.
            * omega.
            * exact E0.
          + rewrite (asset_value_sum_novalue_cons _ _ E1).
            rewrite (asset_value_sum_novalue_cons _ _ E1).
            exact (IH H3 E0).
      } 
Qed.

Lemma asset_value_sum_asset_shift_non (al:list asset) h a rl :
  fnl al ->
  no_dups (h::rl) ->
  In (h,a) al ->
  asset_value (h,a) = None ->
  asset_value_sum (remove_assets al (h::rl)) = asset_value_sum (remove_assets al rl).
intros H H0. induction H as [|k v al H1 H2 IH].
- simpl. tauto.
- simpl. intros H3 H3'. destruct (hashval_eq_dec h k) as [H4|H4].
  + destruct (in_dec hashval_eq_dec k rl) as [H5|H5].
    * exfalso. inversion H0. subst k. contradiction.
    * { destruct H3 as [H3|H3].
        - inversion H3.
          rewrite (asset_value_sum_novalue_cons _ _ H3').
          change (asset_value_sum (remove_assets al (h :: rl)) = asset_value_sum (remove_assets al rl)).
          subst k.
          apply app_perm_asset_value_sum.
          rewrite (remove_assets_eq al (h::rl) rl).
          + apply app_perm_ref.
          + intros k H8. split.
            * { intros [H9|H9].
                - exfalso. apply H1. subst k. assumption.
                - assumption.
              }
            * intros H9. now right.
        - exfalso. apply H1. apply In_In_dom_lem. exists a. subst k. assumption.
      }
  + destruct (in_dec hashval_eq_dec k rl) as [H5|H5].
    * { destruct H3 as [H3|H3].
        - inversion H3. exfalso. congruence.
        - now apply IH.
      } 
    * { destruct H3 as [H3|H3].
        - inversion H3. exfalso. congruence.
        - destruct (asset_value (k,v)) as [w|] eqn: E1.
          + rewrite (asset_value_sum_value_cons _ _ _ E1).
            rewrite (asset_value_sum_value_cons _ _ _ E1).
            apply IH in H3.
            * omega.
            * exact H3'.
          + rewrite (asset_value_sum_novalue_cons _ _ E1).
            rewrite (asset_value_sum_novalue_cons _ _ E1).
            exact (IH H3 H3').
      } 
Qed.

Lemma add_vout_lem (bday bday':nat) (txh:hashval) (outpl:list addr_preasset) (i:nat) alpha h u :
In (alpha,(h,(bday,u))) (add_vout bday' txh outpl i)
<->
(bday = bday' /\
 exists j, nth_error outpl j = value (alpha,u)
           /\ h = hashpair txh (hashnat (i + j))).
revert i. induction outpl as [|[k [obl v]] outpr IH]; intros i.
- simpl. split.
  + tauto.
  + intros [Hb [[|j] [H1 _]]]; discriminate H1.
- simpl. split.
  + intros [H1|H1].
    * { inversion H1. split.
        - reflexivity.
        - exists 0. split.
          + reflexivity.
          + f_equal. f_equal. omega.
      }
    * { apply IH in H1. destruct H1 as [Hb [j [H2 H3]]]. split.
        - exact Hb.
        - exists (S j). split.
          + exact H2.
          + rewrite H3. f_equal. f_equal. omega.
      }
  + intros [Hb [[|j] [H1 H2]]].
    * { left. simpl in H1. inversion H1. rewrite H2.
        f_equal. f_equal.
        - f_equal. f_equal. omega.
        - congruence.
      } 
    * { right. apply IH. split.
        - exact Hb.
        - exists j. split.
          + exact H1.
          + rewrite H2. f_equal. f_equal. omega.
      }
Qed.

Fixpoint output_uses (b:bool) (outpl:list addr_preasset) : list addr :=
  match outpl with
    | (_,(_,signapublication _ th d))::outpr =>
      if b then
        (map hashval_term_addr (signa_uses_props th d)) ++ output_uses b outpr
      else
        (map hashval_term_addr (signa_uses_objs d)) ++ output_uses b outpr
    | (_,(_,docpublication _ th d))::outpr =>
      if b then
        (map hashval_term_addr (doc_uses_props th d)) ++ output_uses b outpr
      else
        (map hashval_term_addr (doc_uses_objs d)) ++ output_uses b outpr
    | _::outpr => output_uses b outpr
    | nil => nil
  end.

Lemma output_uses_nil b : output_uses b nil = nil.
destruct b; reflexivity.
Qed.

Lemma output_uses_app b outpl1 outpl2 :
  output_uses b (outpl1 ++ outpl2) = output_uses b outpl1 ++ output_uses b outpl2.
induction outpl1 as [|[beta [obl [u|u|[|] gamma [u|]|[|] k gamma|gamma|m d|m th d|m th d]]] outpl1 IH]; try (simpl; tauto).
- simpl. destruct b; rewrite IH; apply app_assoc.
- simpl. destruct b; rewrite IH; apply app_assoc.
Qed.

Lemma output_uses_app_or alpha b l r :
  In alpha (output_uses b (l ++ r))
  <->
  (In alpha (output_uses b l) \/ In alpha (output_uses b r)).
rewrite output_uses_app. split.
- apply in_app_or.
- apply in_or_app.
Qed.

Fixpoint rights_out_objs (outpl:list addr_preasset) (alpha:addr) : nat :=
  match outpl with
    | (_,(_,rights false n beta))::outpr =>
      if addr_eq_dec alpha beta then
        n + rights_out_objs outpr alpha
      else
        rights_out_objs outpr alpha
    | _::outpr => rights_out_objs outpr alpha
    | nil => 0
  end.

Fixpoint rights_out_props (outpl:list addr_preasset) (alpha:addr) : nat :=
  match outpl with
    | (_,(_,rights true n beta))::outpr =>
      if addr_eq_dec alpha beta then
        n + rights_out_props outpr alpha
      else
        rights_out_props outpr alpha
    | _::outpr => rights_out_props outpr alpha
    | nil => 0
  end.

Definition rights_out (b:bool) (outpl:list addr_preasset) (alpha:addr) : nat :=
if b then rights_out_props outpl alpha else rights_out_objs outpl alpha.

Lemma rights_out_nil b alpha :
  rights_out b nil alpha = 0.
destruct b; reflexivity.
Qed.

Lemma rights_out_app b outpl1 outpl2 alpha :
  rights_out b (outpl1 ++ outpl2) alpha = rights_out b outpl1 alpha + rights_out b outpl2 alpha.
induction outpl1 as [|[beta [obl [u|u|[|] gamma [u|]|[|] k gamma|gamma|m d|m th d|m th d]]] outpl1 IH]; try (simpl; tauto).
- destruct b; reflexivity.
- destruct b; simpl.
  + destruct (addr_eq_dec alpha gamma) as [D|D].
    * simpl in IH. rewrite IH. apply plus_assoc.
    * exact IH.
  + exact IH.
- destruct b; simpl.
  + exact IH.
  + destruct (addr_eq_dec alpha gamma) as [D|D].
    * simpl in IH. rewrite IH. apply plus_assoc.
    * exact IH.
Qed.

Fixpoint count_rights_used (bl:list addr) (alpha:addr) : nat :=
  match bl with
    | beta::br =>
      if addr_eq_dec beta alpha then
        S (count_rights_used br alpha)
      else
        count_rights_used br alpha
    | nil => 0
  end.

Lemma count_rights_used_none bl alpha :
  ~In alpha bl -> count_rights_used bl alpha = 0.
induction bl as [|beta bl1 IH].
- simpl. tauto.
- intros H1. simpl. destruct (addr_eq_dec beta alpha) as [D|D].
  + exfalso. apply H1. subst beta. now left.
  + apply IH. intros H2. apply H1. now right.
Qed.

Lemma count_rights_used_app bl1 bl2 alpha :
  count_rights_used (bl1 ++ bl2) alpha = count_rights_used bl1 alpha + count_rights_used bl2 alpha.
induction bl1 as [|beta bl1 IH].
- simpl. reflexivity.
- simpl. destruct (addr_eq_dec beta alpha) as [D|D].
  + rewrite IH. reflexivity.
  + exact IH.
Qed.

Definition rights_mentioned (alpha:addr) (b:bool) (outpl:list addr_preasset) : Prop :=
  In alpha (output_uses b outpl) \/ (exists beta obl n, In (beta,(obl,rights b n alpha)) outpl).

Definition rights_mentioned_dec alpha b outpl :
  { rights_mentioned alpha b outpl } + { ~ rights_mentioned alpha b outpl }.
induction outpl as [|[beta [obl u]] outpr IH].
- right. intros [H1|[beta [obl [n H1]]]].
  + contradiction H1.
  + contradiction H1.
- destruct IH as [H1|H1].
  + left. destruct H1 as [H1|[beta' [obl' [n' H1]]]].
    * left.
      change (In alpha (output_uses b (((beta,(obl,u))::nil) ++ outpr))).
      apply output_uses_app_or. now right.
    * right. exists beta'. exists obl'. exists n'. now right.
  + destruct u as [u|u|c gamma [u|]|c k gamma|gamma|m d|m th d|m th d].
    * { right. intros [H2|[beta' [obl' [n' [H2|H2]]]]].
        - apply H1. now left.
        - discriminate H2.
        - apply H1. right. exists beta'. exists obl'. exists n'. exact H2.
      }
    * { right. intros [H2|[beta' [obl' [n' [H2|H2]]]]].
        - apply H1. now left.
        - discriminate H2.
        - apply H1. right. exists beta'. exists obl'. exists n'. exact H2.
      }
    * { right. intros [H2|[beta' [obl' [n' [H2|H2]]]]].
        - apply H1. now left.
        - discriminate H2.
        - apply H1. right. exists beta'. exists obl'. exists n'. exact H2.
      }
    * { right. intros [H2|[beta' [obl' [n' [H2|H2]]]]].
        - apply H1. now left.
        - discriminate H2.
        - apply H1. right. exists beta'. exists obl'. exists n'. exact H2.
      }
    * { assert (L1 : { b = c /\ alpha = gamma } + { ~ (b = c /\ alpha = gamma) }).
        { destruct (addr_eq_dec alpha gamma) as [D1|D1].
          - destruct b; destruct c.
            + left. tauto.
            + right. intros [H2 _]. discriminate H2.
            + right. intros [H2 _]. discriminate H2.
            + left. tauto.
          - right. tauto.
        }
        destruct L1 as [[E1 E2]|D1].
        - left. subst c. subst gamma. right. exists beta. exists obl. exists k. now left.
        - right. intros [H2|[beta' [obl' [n' [H2|H2]]]]].
          + apply H1. now left.
          + inversion H2.  apply D1. split; congruence.
          + apply H1. right. exists beta'. exists obl'. exists n'. exact H2.
      }
    * { right. intros [H2|[beta' [obl' [n' [H2|H2]]]]].
        - apply H1. now left.
        - discriminate H2.
        - apply H1. right. exists beta'. exists obl'. exists n'. exact H2.
      }
    * { right. intros [H2|[beta' [obl' [n' [H2|H2]]]]].
        - apply H1. now left.
        - discriminate H2.
        - apply H1. right. exists beta'. exists obl'. exists n'. exact H2.
      }
    * { destruct b.
        - destruct (in_dec addr_eq_dec alpha (map hashval_term_addr (signa_uses_props th d))) as [D1|D1].
          + left. left. simpl. apply in_or_app. left. exact D1.
          + right. intros [H2|[beta' [obl' [n' [H2|H2]]]]].
            * { apply H1. simpl in H2. apply in_app_or in H2.
                destruct H2 as [H2|H2].
                - contradiction (D1 H2).
                - now left.
              }
            * discriminate H2.
            * apply H1. right. exists beta'. exists obl'. exists n'. exact H2.
        - destruct (in_dec addr_eq_dec alpha (map hashval_term_addr (signa_uses_objs d))) as [D1|D1].
          + left. left. simpl. apply in_or_app. left. exact D1.
          + right. intros [H2|[beta' [obl' [n' [H2|H2]]]]].
            * { apply H1. simpl in H2. apply in_app_or in H2.
                destruct H2 as [H2|H2].
                - contradiction (D1 H2).
                - now left.
              }
            * discriminate H2.
            * apply H1. right. exists beta'. exists obl'. exists n'. exact H2.
      }
    * { destruct b.
        - destruct (in_dec addr_eq_dec alpha (map hashval_term_addr (doc_uses_props th d))) as [D1|D1].
          + left. left. simpl. apply in_or_app. left. exact D1.
          + right. intros [H2|[beta' [obl' [n' [H2|H2]]]]].
            * { apply H1. simpl in H2. apply in_app_or in H2.
                destruct H2 as [H2|H2].
                - contradiction (D1 H2).
                - now left.
              }
            * discriminate H2.
            * apply H1. right. exists beta'. exists obl'. exists n'. exact H2.
        - destruct (in_dec addr_eq_dec alpha (map hashval_term_addr (doc_uses_objs d))) as [D1|D1].
          + left. left. simpl. apply in_or_app. left. exact D1.
          + right. intros [H2|[beta' [obl' [n' [H2|H2]]]]].
            * { apply H1. simpl in H2. apply in_app_or in H2.
                destruct H2 as [H2|H2].
                - contradiction (D1 H2).
                - now left.
              }
            * discriminate H2.
            * apply H1. right. exists beta'. exists obl'. exists n'. exact H2.
      }
Defined.

(***
Lemma count_rights_used_prop_pos_mentioned d alpha :
  count_rights_used (map hashval_addr (data_uses_props d)) alpha > 0 ->
***)  

Lemma rights_mentioned_cons alpha b gamma oblu outpl :
  rights_mentioned alpha b outpl ->
  rights_mentioned alpha b ((gamma,oblu)::outpl).
intros [H1|[beta [obl [n H1]]]].
- left. change (In alpha (output_uses b (((gamma, oblu)::nil) ++ outpl))).
  apply output_uses_app_or. now right.
- right. exists beta. exists obl. exists n. now right.
Qed.

Lemma rights_unmentioned_no_rights_out alpha b outpl :
  ~rights_mentioned alpha b outpl ->
  rights_out b outpl alpha = 0.
induction outpl as [|[beta [obl u]] outpr IH].
- intros _. destruct b; reflexivity.
- intros H1. destruct b; destruct u as [u|u|c gamma [u|]|c k gamma|gamma|m d|m th d|m th d].
  + simpl. apply IH. intros H2. apply H1. now apply rights_mentioned_cons.
  + simpl. apply IH. intros H2. apply H1. now apply rights_mentioned_cons.
  + simpl. apply IH. intros H2. apply H1. now apply rights_mentioned_cons.
  + simpl. apply IH. intros H2. apply H1. now apply rights_mentioned_cons.
  + simpl. destruct c.
    * { destruct (addr_eq_dec alpha gamma) as [D|D].
        - exfalso. apply H1. right. exists beta. exists obl. exists k.
          subst gamma. now left.
        - apply IH. intros H2. apply H1. now apply rights_mentioned_cons.
      }
    * apply IH. intros H2. apply H1. now apply rights_mentioned_cons.
  + simpl. apply IH. intros H2. apply H1. now apply rights_mentioned_cons.
  + simpl. apply IH. intros H2. apply H1. now apply rights_mentioned_cons.
  + simpl. apply IH. intros H2. apply H1. now apply rights_mentioned_cons.
  + simpl. apply IH. intros H2. apply H1. now apply rights_mentioned_cons.
  + simpl. apply IH. intros H2. apply H1. now apply rights_mentioned_cons.
  + simpl. apply IH. intros H2. apply H1. now apply rights_mentioned_cons.
  + simpl. apply IH. intros H2. apply H1. now apply rights_mentioned_cons.
  + simpl. apply IH. intros H2. apply H1. now apply rights_mentioned_cons.
  + simpl. destruct c.
    * apply IH. intros H2. apply H1. now apply rights_mentioned_cons.
    * { destruct (addr_eq_dec alpha gamma) as [D|D].
        - exfalso. apply H1. right. exists beta. exists obl. exists k.
          subst gamma. now left.
        - apply IH. intros H2. apply H1. now apply rights_mentioned_cons.
      }
  + simpl. apply IH. intros H2. apply H1. now apply rights_mentioned_cons.
  + simpl. apply IH. intros H2. apply H1. now apply rights_mentioned_cons.
  + simpl. apply IH. intros H2. apply H1. now apply rights_mentioned_cons.
  + simpl. apply IH. intros H2. apply H1. now apply rights_mentioned_cons.
Qed.

Lemma rights_unmentioned_no_rights_used alpha b outpl :
  ~rights_mentioned alpha b outpl ->
  count_rights_used (output_uses b outpl) alpha = 0.
induction outpl as [|[beta [obl u]] outpr IH].
- intros _. destruct b; reflexivity.
- intros H1. destruct b; destruct u as [u|u|c gamma [u|]|c k gamma|gamma|m d|m th d|m th d].
  + simpl. apply IH. intros H2. apply H1. now apply rights_mentioned_cons.
  + simpl. apply IH. intros H2. apply H1. now apply rights_mentioned_cons.
  + simpl. apply IH. intros H2. apply H1. now apply rights_mentioned_cons.
  + simpl. apply IH. intros H2. apply H1. now apply rights_mentioned_cons.
  + simpl. apply IH. intros H2. apply H1. now apply rights_mentioned_cons.
  + simpl. apply IH. intros H2. apply H1. now apply rights_mentioned_cons.
  + simpl. apply IH. intros H2. apply H1. now apply rights_mentioned_cons.
  + simpl. rewrite count_rights_used_app.
    rewrite IH.
    * { destruct (in_dec addr_eq_dec alpha (map hashval_term_addr (signa_uses_props th d))) as [D1|D1].
        - exfalso. apply H1. left.
          change (In alpha (output_uses true (((beta, (obl, signapublication m th d)) :: nil) ++ outpr))).
          apply output_uses_app_or.
          left. simpl. rewrite app_nil_r. exact D1.
        - apply count_rights_used_none in D1. rewrite D1. reflexivity.
      }
    * intros H2. apply H1. now apply rights_mentioned_cons.
  + simpl. rewrite count_rights_used_app.
    rewrite IH.
    * { destruct (in_dec addr_eq_dec alpha (map hashval_term_addr (doc_uses_props th d))) as [D1|D1].
        - exfalso. apply H1. left.
          change (In alpha (output_uses true (((beta, (obl, docpublication m th d)) :: nil) ++ outpr))).
          apply output_uses_app_or.
          left. simpl. rewrite app_nil_r. exact D1.
        - apply count_rights_used_none in D1. rewrite D1. reflexivity.
      }
    * intros H2. apply H1. now apply rights_mentioned_cons.
  + simpl. apply IH. intros H2. apply H1. now apply rights_mentioned_cons.
  + simpl. apply IH. intros H2. apply H1. now apply rights_mentioned_cons.
  + simpl. apply IH. intros H2. apply H1. now apply rights_mentioned_cons.
  + simpl. apply IH. intros H2. apply H1. now apply rights_mentioned_cons.
  + simpl. apply IH. intros H2. apply H1. now apply rights_mentioned_cons.
  + simpl. apply IH. intros H2. apply H1. now apply rights_mentioned_cons.
  + simpl. apply IH. intros H2. apply H1. now apply rights_mentioned_cons.
  + simpl. rewrite count_rights_used_app.
    rewrite IH.
    * { destruct (in_dec addr_eq_dec alpha (map hashval_term_addr (signa_uses_objs d))) as [D1|D1].
        - exfalso. apply H1. left.
          change (In alpha (output_uses false (((beta, (obl, signapublication m th d)) :: nil) ++ outpr))).
          apply output_uses_app_or.
          left. simpl. rewrite app_nil_r. exact D1.
        - apply count_rights_used_none in D1. rewrite D1. reflexivity.
      }
    * intros H2. apply H1. now apply rights_mentioned_cons.
  + simpl. rewrite count_rights_used_app.
    rewrite IH.
    * { destruct (in_dec addr_eq_dec alpha (map hashval_term_addr (doc_uses_objs d))) as [D1|D1].
        - exfalso. apply H1. left.
          change (In alpha (output_uses false (((beta, (obl, docpublication m th d)) :: nil) ++ outpr))).
          apply output_uses_app_or.
          left. simpl. rewrite app_nil_r. exact D1.
        - apply count_rights_used_none in D1. rewrite D1. reflexivity.
      }
    * intros H2. apply H1. now apply rights_mentioned_cons.
Qed.

(*** only count the ones with no external obligation ***)
Fixpoint units_sent_to_addr (beta:addr) (outpl:list addr_preasset) : nat :=
match outpl with
| (alpha,(None,currency u))::outpr =>
  if addr_eq_dec alpha beta then
    u + units_sent_to_addr beta outpr
  else
    units_sent_to_addr beta outpr
| _::outpr => units_sent_to_addr beta outpr
| nil => 0
end.

Lemma units_sent_to_addr_app beta outpl1 outpl2 :
  units_sent_to_addr beta (outpl1 ++ outpl2) = units_sent_to_addr beta outpl1 + units_sent_to_addr beta outpl2.
induction outpl1 as [|[alpha [[[a [|n]]|] [u|u|[|] gamma [u|]|[|] k gamma|gamma|m' d|m' th d|m' th d]]] outpl1 IH]; try exact IH.
- reflexivity.
- simpl. destruct (addr_eq_dec alpha beta) as [D|D].
  + rewrite IH. apply plus_assoc.
  + exact IH.
Qed.

