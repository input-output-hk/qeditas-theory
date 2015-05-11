(** Copyright (c) 2015 Bill White **)
(** Distributed under the MIT/X11 software license **)
(** See http://www.opensource.org/licenses/mit-license.php **)

(** MTrees: Merkle tree representations of ledger functions. Hash values
    are represented by option hashval where None always represents 'empty' data.
    The empty asset list hashes to None, and if a node in the tree has two empty
    children then its corresponding hash is also None.
    The type hlist allows the approximation of asset lists by only listing
    a prefix of the list and representing the rest by a hash value.
    The type mtree n is a binary tree of depth n where a node may be
    replaced by hash values representing the missing part.
    The leaves are mtree 0 and consist of hlists which may approximate asset lists.
    mtree 162 is the type of Merkle trees that may correspond to ledger functions.
    In general mtree_approx_fun_p T f means (T:mtree n) approximates (f:bitseq n -> list asset).
    An mtree is valid if it approximates a valid ledger function.
    The function mtree_hashroot computes the hashvals corresponding to the given tree.
    subqm T T' means T' has at least as much information at T.
    equi T T' is an equivalence relation on trees.
    mtree_supports_tx defines when a tree supports a transaction.
    If T approximates f and T supports a transaction, then f also
    supports the transaction (mtree_supports_tx_statefun).
    Under some conditions on T, the converse also holds (mtree_supports_tx_statefun_conv).
    The function tx_mtree_trans transforms an mtree using a transaction.
    Together these results mean that if T has sufficient information about the ledger,
    then it can be used to determine if the corresponding ledger function supports the transaction.
    If T approximates f and the transaction is supported by T, then the
    transformed T approximates the transformed f (mtree_approx_trans).
    An mtree is normal if it does not contain nodes with empty children.
    The function normalize_mtree normalizes mtree. If we normalize T after
    transforming via a transaction, it also approximtes the transformed
    ledger function (mtree_normal_approx_trans).
    Transformations change the value of the assets in the ledger according to the
    rewards/fees of the supported transaction (mtree_valid_tx_mtree_trans).
 **)

Require Export LedgerStates.

(*** Approximation Code ***)
Inductive hlist : Type :=
| hlistH : hashval -> hlist
| hlistN : hlist
| hlistC : asset -> hlist -> hlist.

Inductive In_hlist (a:asset) : hlist -> Prop :=
| In_hlist_H hl : In_hlist a (hlistC a hl)
| In_hlist_C b hl : In_hlist a hl -> In_hlist a (hlistC b hl)
.

Fixpoint mtree (n:nat) : Type :=
  match n with
    | 0 => hlist
    | S n => sum (option hashval) (mtree n * mtree n)
  end.

Definition nehlist : Type := sum hashval (asset * hlist).

Definition nehlist_hlist (hl:nehlist) : hlist :=
match hl with
| inl h => hlistH h
| inr (a,hl) => hlistC a hl
end.

Definition hlist_nehlist (al:hlist) : option nehlist :=
match al with
| hlistH h => Some (inl h)
| hlistC a al' => Some (inr (a,al'))
| hlistN => None
end.

Fixpoint hlist_hashroot (al:hlist) : option hashval :=
match al with
| hlistH h => Some(h)
| hlistN => None
| hlistC a al' =>
  match hlist_hashroot al' with
    | None => Some (hashpair (hashnat 3) (hashasset a))
    | Some k => Some (hashpair (hashnat 4) (hashpair (hashasset a) k))
  end
end.

Fixpoint mtree_hashroot {n} : forall (T:mtree n), option hashval :=
  match n with
    | O => fun (hl:mtree 0) => hlist_hashroot hl
    | S n' => fun (T:mtree (S n')) =>
                match T with
                  | inl h => h
                  | inr (Tl,Tr) => hashopair (mtree_hashroot Tl) (mtree_hashroot Tr)
                end
  end.

Inductive approx_assetlist : hlist -> list asset -> Prop :=
| approx_assetlist_H h al : Some(h) = hashassetlist al -> approx_assetlist (hlistH h) al
| approx_assetlist_N : approx_assetlist hlistN nil
| approx_assetlist_C a hl al :
  approx_assetlist hl al ->
  approx_assetlist (hlistC a hl) (cons a al)
.

Definition mtreeH (n:nat) (h:option hashval) : mtree (S n) := inl h.

Definition mtreeB {n} (Tl Tr:mtree n) : mtree (S n) := inr (Tl,Tr).

Fixpoint mtree_approx_fun_p {n} : mtree n -> (bitseq n -> list asset) -> Prop :=
match n with
| O => fun (hl:mtree 0) (f:bitseq 0 -> list asset) =>
         hashassetlist (f tt) = hlist_hashroot hl
| S n => fun (T:mtree (S n)) (f:bitseq (S n) -> list asset) =>
           match T with
             | inl h => exists Tl Tr:mtree n, h = hashopair (mtree_hashroot Tl) (mtree_hashroot Tr)
                                              /\ mtree_approx_fun_p Tl (fun alpha => f (false,alpha))
                                              /\ mtree_approx_fun_p Tr (fun alpha => f (true,alpha))
             | inr (Tl,Tr) => mtree_approx_fun_p Tl (fun alpha => f (false,alpha))
                              /\ mtree_approx_fun_p Tr (fun alpha => f (true,alpha))
           end
end.

Lemma mtree_hashroot_mtree_approx_fun_p {n} (T T':mtree n) (f:bitseq n -> list asset) :
  mtree_hashroot T = mtree_hashroot T' ->
  mtree_approx_fun_p T f ->
  mtree_approx_fun_p T' f.
revert T T' f. induction n as [|n IH].
- intros hl hl' f. simpl. congruence.
- intros [h|[Tl Tr]] [h'|[Tl' Tr']] f.
  + intros H1. simpl in H1. congruence.
  + simpl. intros H1. intros [Tl [Tr [H2 [H3 H4]]]].
    assert (L1: hashopair (mtree_hashroot Tl) (mtree_hashroot Tr) = hashopair (mtree_hashroot Tl') (mtree_hashroot Tr')) by congruence.
    apply hashopairinj in L1. destruct L1 as [L1a L1b].
    split.
    * revert L1a H3. apply IH.
    * revert L1b H4. apply IH.
  + simpl. intros H1 [H2 H3].
    exists Tl. exists Tr. repeat split.
    * congruence.
    * assumption.
    * assumption.
  + simpl. intros H1 [H2 H3].
    assert (L1: hashopair (mtree_hashroot Tl) (mtree_hashroot Tr) = hashopair (mtree_hashroot Tl') (mtree_hashroot Tr')) by congruence.
    apply hashopairinj in L1. destruct L1 as [L1a L1b].
    split.
    * revert L1a H2. apply IH.
    * revert L1b H3. apply IH.
Qed.

Definition mtree_valid_ {n} (alphapre:bitseq n -> addr) (T:mtree n) : Prop :=
  exists f:bitseq n -> list asset,
    sf_valid_ alphapre f /\ mtree_approx_fun_p T f.

Definition mtree_valid (T:mtree 162) : Prop := mtree_valid_ (fun alpha => alpha) T.

(*** This may be interesting, but it's no longer needed. ***)
Inductive partofmtree {n} (T:mtree n) : forall m, mtree m -> Prop :=
| partofmtreeH : partofmtree T n T
| partofmtreeL m Tl Tr : partofmtree T m Tl -> partofmtree T (S m) (inr (Tl,Tr))
| partofmtreeR m Tl Tr : partofmtree T m Tr -> partofmtree T (S m) (inr (Tl,Tr))
| partofmtreeLH m Tl Tr h : partofmtree T m Tl -> @mtree_hashroot (S m) (inr (Tl,Tr)) = h -> partofmtree T (S m) (inl h)
| partofmtreeRH m Tl Tr h : partofmtree T m Tr -> @mtree_hashroot (S m) (inr (Tl,Tr)) = h -> partofmtree T (S m) (inl h)
.

Lemma mtree_hashroot_eq_valid_ {n} (alphapre:bitseq n -> addr) (T1 T2:mtree n) :
  mtree_hashroot T1 = mtree_hashroot T2 ->
  (mtree_valid_ alphapre T1 -> mtree_valid_ alphapre T2).
intros H1 [f [H2 H3]]. exists f. split.
- exact H2.
- revert H3. now apply mtree_hashroot_mtree_approx_fun_p.
Qed.

Lemma mtree_hashroot_eq_valid (T1 T2:mtree 162) :
  mtree_hashroot T1 = mtree_hashroot T2 ->
  (mtree_valid T1 <-> mtree_valid T2).
intros H1. split.
- exact (mtree_hashroot_eq_valid_ (fun alpha => alpha) T1 T2 H1).
- symmetry in H1.
  exact (mtree_hashroot_eq_valid_ (fun alpha => alpha) T2 T1 H1).
Qed.

Lemma approx_fun_fnl {n} (Tf Tg:mtree n) f g :
  mtree_hashroot Tf = mtree_hashroot Tg ->
  mtree_approx_fun_p Tf f ->
  mtree_approx_fun_p Tg g ->
  forall alpha, f alpha = g alpha.
Proof.
  induction n as [|n IH].
  - simpl. intros Hfg H1 H2 []. rewrite Hfg in H1. rewrite <- H2 in H1. apply hashassetlistinj in H1. assumption.
  - destruct Tf as [hf|[Tfl Tfr]]; destruct Tg as [hg|[Tgl Tgr]].
    + simpl. intros Hfg [Tfl [Tfr [H1a [H1b H1c]]]] [Tgl [Tgr [H2a [H2b H2c]]]] [[|] alpha].
      * rewrite Hfg in H1a. rewrite H1a in H2a. apply hashopairinj in H2a. destruct H2a as [H3 H4].
        apply (IH Tfr Tgr (fun alpha => f (true,alpha)) (fun alpha => g (true,alpha)) H4 H1c H2c).
      * rewrite Hfg in H1a. rewrite H1a in H2a. apply hashopairinj in H2a. destruct H2a as [H3 H4].
        apply (IH Tfl Tgl (fun alpha => f (false,alpha)) (fun alpha => g (false,alpha)) H3 H1b H2b).
    + simpl. intros Hfg [Tfl [Tfr [H1a [H1b H1c]]]] [H2b H2c] [[|] alpha].
      * rewrite Hfg in H1a. apply hashopairinj in H1a. destruct H1a as [H3 H4].
        symmetry in H4.
        apply (IH Tfr Tgr (fun alpha => f (true,alpha)) (fun alpha => g (true,alpha)) H4 H1c H2c).
      * rewrite Hfg in H1a. apply hashopairinj in H1a. destruct H1a as [H3 H4].
        symmetry in H3.
        apply (IH Tfl Tgl (fun alpha => f (false,alpha)) (fun alpha => g (false,alpha)) H3 H1b H2b).
    + simpl. intros Hfg [H1b H1c] [Tgl [Tgr [H2a [H2b H2c]]]] [[|] alpha].
      * rewrite <- Hfg in H2a. apply hashopairinj in H2a. destruct H2a as [H3 H4].
        apply (IH Tfr Tgr (fun alpha => f (true,alpha)) (fun alpha => g (true,alpha)) H4 H1c H2c).
      * rewrite <- Hfg in H2a. apply hashopairinj in H2a. destruct H2a as [H3 H4].
        apply (IH Tfl Tgl (fun alpha => f (false,alpha)) (fun alpha => g (false,alpha)) H3 H1b H2b).
    + simpl. intros Hfg [H1b H1c] [H2b H2c] [[|] alpha].
      * apply hashopairinj in Hfg. destruct Hfg as [H3 H4].
        apply (IH Tfr Tgr (fun alpha => f (true,alpha)) (fun alpha => g (true,alpha)) H4 H1c H2c).
      * apply hashopairinj in Hfg. destruct Hfg as [H3 H4].
        apply (IH Tfl Tgl (fun alpha => f (false,alpha)) (fun alpha => g (false,alpha)) H3 H1b H2b).
Qed.

Fixpoint hlist_full_approx (hl:hlist) : Prop :=
  match hl with
    | hlistH _ => False
    | hlistN => True
    | hlistC _ hr => hlist_full_approx hr
  end.

Fixpoint mtree_full_approx_addr {n} : mtree n -> bitseq n -> Prop :=
match n with
| O => fun (T:mtree 0) (alpha:bitseq 0) => hlist_full_approx T
| S n => fun (T:mtree (S n)) (alpha:bitseq (S n)) =>
           match T with
             | inl None => True
             | inl _ => False
             | inr (Tl,Tr) =>
               match alpha with
                 | (false,alphar) => mtree_full_approx_addr Tl alphar
                 | (true,alphar) => mtree_full_approx_addr Tr alphar
               end
           end
end.

Fixpoint mtree_supports_addr {n} : mtree n -> bitseq n -> Prop :=
match n with
| O => fun (T:mtree 0) (alpha:bitseq 0) => True
| S n => fun (T:mtree (S n)) (alpha:bitseq (S n)) =>
           match T with
             | inl None => True
             | inl _ => False
             | inr (Tl,Tr) =>
               match alpha with
                 | (false,alphar) => mtree_supports_addr Tl alphar
                 | (true,alphar) => mtree_supports_addr Tr alphar
               end
           end
end.

Fixpoint mtree_supports_asset (a:asset) {n} : mtree n -> bitseq n -> Prop :=
match n with
| O => fun (hl:mtree 0) (alpha:bitseq 0) => In_hlist a hl
| S n => fun (T:mtree (S n)) (alpha:bitseq (S n)) =>
           match T with
             | inl _ => False
             | inr (Tl,Tr) =>
               match alpha with
                 | (false,alphar) => mtree_supports_asset a Tl alphar
                 | (true,alphar) => mtree_supports_asset a Tr alphar
               end
           end
end.
                   
Inductive mtree_asset_value_in T : list addr_assetid -> nat -> Prop :=
| mtree_asset_value_in_nil : mtree_asset_value_in T nil 0
| mtree_asset_value_in_cons h a u inpl alpha v :
    mtree_asset_value_in T inpl v ->
    mtree_supports_asset a T alpha ->
    asset_value a = Some u ->
    h = assetid a ->
    mtree_asset_value_in T ((alpha,h)::inpl) (u+v)
| mtree_asset_value_in_skip h a inpl alpha v :
    mtree_asset_value_in T inpl v ->
    mtree_supports_asset a T alpha ->
    asset_value a = None ->
    h = assetid a ->
    mtree_asset_value_in T ((alpha,h)::inpl) v
.

(*** Precondition for checking if tx is a valid tx. ***)
Definition mtree_can_support_tx (tx:Tx) (T : mtree 162) : Prop :=
(forall alpha h, In (alpha,h) (tx_inputs tx) -> exists u, mtree_supports_asset (h,u) T alpha)
/\
(forall alpha u, In (alpha,u) (tx_outputs tx) -> mtree_supports_addr T alpha)
/\
(forall alpha obl b n beta, In (alpha,(obl,rights b n beta)) (tx_outputs tx) -> mtree_full_approx_addr T (termaddr_addr beta))
/\
(forall alpha b, In alpha (output_uses b (tx_outputs tx)) -> mtree_full_approx_addr T (termaddr_addr alpha))
/\
(forall k1 k2 b, In (k1,k2) (output_creates b (tx_outputs tx)) -> mtree_full_approx_addr T (hashval_term_addr k1))
/\
(forall alpha obl b beta r, In (termaddr_addr alpha,(obl,owns b beta r)) (tx_outputs tx) -> mtree_full_approx_addr T (termaddr_addr alpha))
/\
(forall obl gamma nonce th d alpha h,
   In (alpha,(obl,signapublication gamma nonce th d)) (tx_outputs tx) ->
   In h (signaspec_stp_markers d) \/ In h (signaspec_known_markers th d) ->
   exists k bday obl', mtree_supports_asset (k,(bday,(obl',marker))) T (hashval_term_addr h))
/\
(forall obl gamma nonce th d alpha h,
   In (alpha,(obl,docpublication gamma nonce th d)) (tx_outputs tx) ->
   In h (doc_stp_markers d) \/ In h (doc_known_markers th d) ->
   exists k bday obl', mtree_supports_asset (k,(bday,(obl',marker))) T (hashval_term_addr h))
.

Inductive mtree_rights_consumed (b:bool) (alpha:termaddr) (T:mtree 162) : list addr_assetid -> nat -> Prop :=
| mtree_rights_consumed_nil : mtree_rights_consumed b alpha T nil 0
| mtree_rights_consumed_cons beta h inpr r1 bday obl r2:
    mtree_rights_consumed b alpha T inpr r1 ->
    mtree_supports_asset (h,(bday,(obl,rights b r2 alpha))) T beta ->
    mtree_rights_consumed b alpha T ((beta,h)::inpr) (r1 + r2)
| mtree_rights_consumed_skip beta h inpr r1 bday obl u:
    mtree_rights_consumed b alpha T inpr r1 ->
    mtree_supports_asset (h,(bday,(obl,u))) T beta ->
    (~exists r2, u = rights b r2 alpha) ->
    mtree_rights_consumed b alpha T ((beta,h)::inpr) r1
.

Definition mtree_rights_balanced (T:mtree 162) (alpha:termaddr) (b:bool) (inpl:list addr_assetid) (outpl:list addr_preasset) : Prop :=
   (forall (rtot1 rtot2 : nat) (h : hashval) (bday : nat) (obl : obligation) 
      (beta : payaddr) (u : nat),
    count_rights_used (output_uses b outpl) alpha = rtot1 ->
    mtree_supports_asset (h, (bday,(obl, owns b beta (Some u)))) T (termaddr_addr alpha) ->
    rights_out b outpl alpha = rtot2 ->
    exists rtot3 rtot4 : nat,
      mtree_rights_consumed b alpha T inpl rtot3 /\
      rtot4 * u <= units_sent_to_addr (payaddr_addr beta) outpl /\
      rtot1 + rtot2 = rtot3 + rtot4).

(*** A marker at the term address for #(#_{th}trm,#a) means trm has type a in theory with hash th. ***)
Definition mtree_lookup_stp (T:mtree 162) (h:hashval) (a:stp) : Prop :=
  exists k bday obl,
    mtree_supports_asset (k,(bday,(obl,marker))) T (hashval_term_addr (hashpair h (hashstp a))).

(*** A marker at the term address for #_{th}trm means trm has been proven in theory with hash th. ***)
Definition mtree_lookup_known (T:mtree 162) (h:hashval) : Prop :=
  exists k bday obl,
    mtree_supports_asset (k,(bday,(obl,marker))) T (hashval_term_addr h).

Definition mtree_supports_tx (tht:option (ttree 160)) (sigt:option (stree 160)) blkheight (tx:Tx) (T : mtree 162) fee rew : Prop :=
(forall alpha u, In (alpha,u) (tx_outputs tx) -> mtree_supports_addr T alpha)
/\
(exists utot:nat,
mtree_asset_value_in T (tx_inputs tx) utot (*** this condition also ensures all assets are supported ***)
/\
asset_value_out (tx_outputs tx) + fee + out_burncost (tx_outputs tx) = utot + rew)
/\
(*** if rights are being output and/or used, then they must be transfered or purchased from the owner (who creates them) ***)
((forall alpha b,
    (*** these are the rights being used up to publish documents that use alpha in this transaction ***)
    rights_mentioned alpha b (tx_outputs tx) ->
    (mtree_full_approx_addr T (termaddr_addr alpha)) (*** need all assets to be visible here ***)
    /\
    (*** it's not owned by someone blocking its use and... ***)
    ((~exists h' bday' obl' beta', mtree_supports_asset (h',(bday',(obl',owns b beta' None))) T (termaddr_addr alpha))
     /\
     mtree_rights_balanced T alpha b (tx_inputs tx) (tx_outputs tx)))
 /\
 (*** and if some rights are in the input, then the rights must be mentioned in the output ***)
 (forall alpha b beta h bday obl n,
    In (beta,h) (tx_inputs tx) ->
    mtree_supports_asset (h,(bday,(obl,rights b n alpha))) T beta ->
    rights_mentioned alpha b (tx_outputs tx)))
/\
(*** publications were declared in advance by a currently usable intention and are correct ***)
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
      mtree_supports_asset (h,(bday,(obl,marker))) T beta)
 /\
 (forall obl gamma nonce th d alpha,
    In (alpha,(obl,signapublication gamma nonce th d)) (tx_outputs tx) ->
    check_signaspec_p (mtree_lookup_stp T) (mtree_lookup_known T) tht sigt th d
    /\
    exists beta h bday obl,
      beta = hashval_publication_addr (hashpair (hashaddr (payaddr_addr gamma)) (hashpair (hashnat nonce) (hashopair2 th (hashsignaspec d))))
      /\
      In (beta,h) (tx_inputs tx)
      /\
      bday + intention_minage <= blkheight
      /\
      mtree_supports_asset (h,(bday,(obl,marker))) T beta)
 /\
 (forall obl gamma nonce th d alpha,
    In (alpha,(obl,docpublication gamma nonce th d)) (tx_outputs tx) ->
    check_doc_p (mtree_lookup_stp T) (mtree_lookup_known T) tht sigt th d
    /\
    exists beta h bday obl,
      beta = hashval_publication_addr (hashpair (hashaddr (payaddr_addr gamma)) (hashpair (hashnat nonce) (hashopair2 th (hashdoc d))))
      /\
      In (beta,h) (tx_inputs tx)
      /\
      bday + intention_minage <= blkheight
      /\
      mtree_supports_asset (h,(bday,(obl,marker))) T beta))
/\
(*** newly claimed ownership must be new and must be supported by a document in the tx ***)
(forall alpha b obl beta r,
    In (termaddr_addr alpha,(obl,owns b beta r)) (tx_outputs tx) ->
    mtree_full_approx_addr T (termaddr_addr alpha) (*** need to view the whole asset list to ensure no current owner of obj ***)
    /\
    ((exists h beta' bday' obl' r', mtree_supports_asset (h,(bday',(obl',owns b beta' r'))) T (termaddr_addr alpha)
                              /\ In (termaddr_addr alpha,h) (tx_inputs tx))
     \/
     ((~exists h beta' bday' obl' r', mtree_supports_asset (h,(bday',(obl',owns b beta' r'))) T (termaddr_addr alpha))
      /\
      exists k1 k2,
        In (k1,k2) (output_creates b (tx_outputs tx))
        /\
        alpha = hashval_termaddr k1)))
/\
(*** new objects and props must be given ownership by the tx publishing the document ***)
(forall k1 k2 b,
   In (k1,k2) (output_creates b (tx_outputs tx)) ->
   mtree_full_approx_addr T (hashval_term_addr k1) (*** need to view the whole asset list to ensure no current owner of prop ***)
   /\
   (~(exists h' beta' bday' obl' r', mtree_supports_asset (h',(bday',(obl',owns b beta' r'))) T (hashval_term_addr k1)) ->
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
   mtree_supports_asset (h,(bday,(obl,bounty u))) T alpha ->
   mtree_full_approx_addr T alpha
   /\
   exists h' bday' obl' beta r,
     In (alpha,h') (tx_inputs tx)
     /\
     mtree_supports_asset (h',(bday',(obl',owns true beta r))) T alpha
     /\
     In (alpha,(obl',owns true beta r)) (tx_outputs tx))
.

(*** assumes hl1 and hl2 have the same hashroot and so are both hash reps of the same asset list ***)
Fixpoint hlist_lub (hl1 hl2:hlist) : hlist :=
match hl1 with
| hlistC h hr1 =>
  match hl2 with
    | hlistC _ hr2 =>
      hlistC h (hlist_lub hr1 hr2)
    | _ => hl1
  end
| _ => hl2
end.

(*** assumes the two mtrees have the same hashroot and so are both Merkle Tree reps of the same statefun ***)
Fixpoint mtree_lub {n} : mtree n -> mtree n -> mtree n :=
match n with
| O => fun (hl1 hl2:mtree 0) => hlist_lub hl1 hl2
| S n => fun (T1 T2:mtree (S n)) =>
           match T1 with
             | inl _ => T2
             | inr (T1l,T1r) =>
               match T2 with
                 | inl _ => T1
                 | inr (T2l,T2r) =>
                   inr (mtree_lub T1l T2l,mtree_lub T1r T2r)
               end
           end
end.

Definition empty_mtree (n:nat) : mtree n :=
match n with
  | O => hlistN
  | S n => mtreeH n None
end.

Lemma mtree_hashroot_empty {n} : mtree_hashroot (empty_mtree n) = None.
destruct n as [|n]; reflexivity.
Qed.

Fixpoint empty_mtree_p {n:nat} : mtree n -> Prop :=
match n with
| O => fun hl => hl = hlistN
| S n => fun T =>
           match T with
             | inl None => True
             | inl _ => False
             | inr (Tl,Tr) => empty_mtree_p Tl /\ empty_mtree_p Tr
           end
end.

Lemma mtree_hashroot_None_empty_mtree_p {n:nat} (T:mtree n) :
  mtree_hashroot T = None <-> empty_mtree_p T.
induction n as [|n IH].
- destruct T as [h| |h hl]; simpl.
  + split; discriminate.
  + tauto.
  + destruct (hlist_hashroot hl); split; discriminate.
- destruct T as [[h|]|[Tl Tr]].
  + simpl. split.
    * discriminate.
    * tauto.
  + simpl. tauto.
  + simpl. split.
    * generalize (IH Tl). generalize (IH Tr).
      destruct (mtree_hashroot Tl); destruct (mtree_hashroot Tr); simpl; try discriminate.
      tauto.
    * intros [H1 H2]. apply IH in H1. apply IH in H2.
      rewrite H1. rewrite H2. reflexivity.
Qed.

Lemma empty_mtree_p_empty_mtree n : empty_mtree_p (empty_mtree n).
apply mtree_hashroot_None_empty_mtree_p. destruct n; reflexivity.
Qed.

Inductive subqh : hlist -> hlist -> Prop :=
| subqhH h hl2 : hlist_hashroot hl2 = Some(h) -> subqh (hlistH h) hl2
| subqhN : subqh hlistN hlistN
| subqhC h hr1 hr2 : subqh hr1 hr2 -> subqh (hlistC h hr1) (hlistC h hr2).

Fixpoint subqm {n:nat} : mtree n -> mtree n -> Prop :=
match n with
| O => fun hl1 hl2 => subqh hl1 hl2
| S n => fun (T1 T2:mtree (S n)) =>
           match T1 with
             | inl h => mtree_hashroot T2 = h
             | inr (T1l,T1r) =>
               match T2 with
                 | inl _ => False
                 | inr (T2l,T2r) => subqm T1l T2l /\ subqm T1r T2r
               end
           end
end.

Lemma subqh_ref hl : subqh hl hl.
induction hl as [h| |h hr IH]; simpl.
- apply subqhH. reflexivity.
- apply subqhN.
- apply subqhC. exact IH.
Qed.

Lemma subqh_lub_1 hl1 hl2 :
  hlist_hashroot hl1 = hlist_hashroot hl2 ->
  subqh hl1 (hlist_lub hl1 hl2).
revert hl2. induction hl1 as [h1| |h1 hr1 IH]; simpl.
- intros hl2 H1. apply (subqhH h1 hl2). congruence.
- intros [h2| |h2 hr2] H1.
  + discriminate H1.
  + apply subqhN.
  + simpl in H1. destruct (hlist_hashroot hr2); discriminate H1.
- intros [h2| |h2 hr2] H1.
  + apply subqh_ref.
  + apply subqh_ref.
  + apply subqhC. apply IH. simpl in H1.
    destruct (hlist_hashroot hr1) as [k1|] eqn: E1;
      destruct (hlist_hashroot hr2) as [k2|] eqn: E2.
    * inversion H1.
      apply hashpairinj in H0. destruct H0 as [_ H0].
      apply hashpairinj in H0. destruct H0 as [_ H0].
      congruence.
    * exfalso. inversion H1.
      apply hashpairinj in H0. destruct H0 as [H0 _].
      apply hashnatinj in H0. omega.
    * exfalso. inversion H1.
      apply hashpairinj in H0. destruct H0 as [H0 _].
      apply hashnatinj in H0. omega.
    * reflexivity.
Qed.

Lemma subqh_lub_2 hl1 hl2 :
  hlist_hashroot hl1 = hlist_hashroot hl2 ->
  subqh hl2 (hlist_lub hl1 hl2).
revert hl2. induction hl1 as [h1| |h1 hr1 IH]; simpl.
- intros hl2 H1. apply subqh_ref.
- intros [h2| |h2 hr2] H1.
  + discriminate H1.
  + apply subqhN.
  + simpl in H1. destruct (hlist_hashroot hr2); discriminate H1.
- intros [h2| |h2 hr2] H1.
  + apply subqhH. exact H1.
  + exfalso. destruct (hlist_hashroot hr1); discriminate H1.
  + assert (L1: h2 = h1 /\ hlist_hashroot hr1 = hlist_hashroot hr2).
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
    subst h2. apply subqhC. apply IH. exact L1b.
Qed.

Lemma subqm_ref {n} (T:mtree n) : subqm T T.
induction n as [|n IH].
- simpl. apply subqh_ref.
- destruct T as [h|[Tl Tr]]; simpl.
  + reflexivity.
  + split; apply IH.
Qed.

Lemma subqm_lub_1 {n} (T1 T2:mtree n) :
  mtree_hashroot T1 = mtree_hashroot T2 ->
  subqm T1 (mtree_lub T1 T2).
induction n as [|n IH].
- simpl. apply subqh_lub_1.
- destruct T1 as [h1|[T1l T1r]]; destruct T2 as [h2|[T2l T2r]]; simpl.
  + congruence.
  + congruence.
  + intros _. split; apply subqm_ref.
  + intros H1. apply hashopairinj in H1. destruct H1 as [H2 H3]. split.
    * apply (IH _ _ H2).
    * apply (IH _ _ H3).
Qed.

Lemma subqh_hashroot_eq hl1 hl2 : subqh hl1 hl2 -> hlist_hashroot hl1 = hlist_hashroot hl2.
intros H. induction H as [h hl2 H1| |h hr1 hr2 H1 IH].
- simpl; congruence.
- simpl; congruence.
- simpl. rewrite IH. reflexivity.
Qed.

Theorem subqm_hashroot_eq {n} (T1 T2:mtree n) : subqm T1 T2 -> mtree_hashroot T1 = mtree_hashroot T2.
induction n as [|n IH].
- simpl. apply subqh_hashroot_eq.
- destruct T1 as [h1|[T1l T1r]]; destruct T2 as [h2|[T2l T2r]]; simpl; try congruence; try tauto.
  intros [H1 H2]. generalize (IH _ _ H1). generalize (IH _ _ H2). congruence.
Qed.

Lemma subqh_tra hl1 hl2 hl3 : subqh hl1 hl2 -> subqh hl2 hl3 -> subqh hl1 hl3.
intros H1. revert hl3. induction H1 as [h hl H1| |h hr1 hr2 H1 IH1 H2 IH2].
- intros hl3 H2. apply subqhH. apply subqh_hashroot_eq in H2. congruence.
- tauto.
- intros hl3 H2. inversion H2. apply subqhC. now apply IH1.
Qed.

Lemma subqm_tra {n} (T1 T2 T3:mtree n) : subqm T1 T2 -> subqm T2 T3 -> subqm T1 T3.
induction n as [|n IH].
- simpl. apply subqh_tra.
- destruct T1 as [[h1|]|[T1l T1r]]; destruct T2 as [[h2|]|[T2l T2r]]; simpl; intros H1; inversion H1; destruct T3 as [[h3|]|[T3l T3r]]; simpl; intros H2; inversion H2; try tauto.
  + rewrite (subqm_hashroot_eq _ _ H). rewrite (subqm_hashroot_eq _ _ H3).
    reflexivity.
  + rewrite (subqm_hashroot_eq _ _ H). rewrite (subqm_hashroot_eq _ _ H3).
    reflexivity.
  + split.
    * apply (IH _ _ _ H H3).
    * apply (IH _ _ _ H0 H4).
Qed.

Lemma hlist_lub_eq_1 (hl1 hl2:hlist) :
  hlist_hashroot hl1 = hlist_hashroot hl2 ->
  hlist_hashroot (hlist_lub hl1 hl2) = hlist_hashroot hl1.
intros H1. symmetry. apply subqh_hashroot_eq. now apply subqh_lub_1.
Qed.

Lemma hlist_lub_eq_2 (hl1 hl2:hlist) :
  hlist_hashroot hl1 = hlist_hashroot hl2 ->
  hlist_hashroot (hlist_lub hl1 hl2) = hlist_hashroot hl2.
intros H1. generalize (hlist_lub_eq_1 hl1 hl2 H1). congruence.
Qed.

Lemma mtree_lub_eq_1 {n} (T1 T2:mtree n) :
  mtree_hashroot T1 = mtree_hashroot T2 ->
  mtree_hashroot (mtree_lub T1 T2) = mtree_hashroot T1.
intros H1. symmetry. apply subqm_hashroot_eq. now apply subqm_lub_1.
Qed.

Lemma mtree_lub_eq_2 {n} (T1 T2:mtree n) :
  mtree_hashroot T1 = mtree_hashroot T2 ->
  mtree_hashroot (mtree_lub T1 T2) = mtree_hashroot T2.
intros H1. generalize (mtree_lub_eq_1 T1 T2 H1). congruence.
Qed.

Lemma subqh_In_hlist h hl1 hl2 : subqh hl1 hl2 -> In_hlist h hl1 -> In_hlist h hl2.
intros H. induction H as [k hl2| |k hr1 hr2 H IH].
- intros H1. inversion H1.
- intros H1. inversion H1.
- intros H1. inversion H1.
  + apply In_hlist_H.
  + apply In_hlist_C. now apply IH.
Qed.

Lemma empty_supports_addr_lem {n:nat} :
  forall T:mtree n, forall alpha:bitseq n,
    mtree_hashroot T = None ->
    mtree_supports_addr T alpha.
induction n as [|n IH].
- intros [h| |h hl] [].
  + simpl. discriminate.
  + simpl. tauto.
  + simpl. destruct (hlist_hashroot hl); discriminate.
- intros [[h|]|[Tl Tr]].
  + simpl. discriminate.
  + simpl. tauto.
  + intros [[|] gamma] H1; simpl in H1; simpl.
    * apply IH. destruct (mtree_hashroot Tr); try tauto.
      destruct (mtree_hashroot Tl); discriminate H1.
    * apply IH. destruct (mtree_hashroot Tl); try tauto.
      destruct (mtree_hashroot Tr); discriminate H1.
Qed.

Lemma subqh_full_approx (hl1 hl2:hlist) :
  subqh hl1 hl2 -> hlist_full_approx hl1 -> hlist_full_approx hl2.
revert hl2. induction hl1 as [h1| |h1 hr1 IH].
- simpl. tauto.
- intros hl2 H1. inversion H1. simpl. tauto.
- intros hl2 H1. inversion H1. simpl. now apply IH.
Qed.

Lemma empty_mtree_full_approx_addr {n} (alpha:bitseq n) :
  mtree_full_approx_addr (empty_mtree n) alpha.
induction n as [|n IH].
- simpl. tauto.
- simpl. tauto.
Qed.

Lemma subqm_empty {n} (T:mtree n) :
  empty_mtree_p T -> subqm (empty_mtree n) T.
induction n as [|n IH].
- simpl. intros H. subst T. apply subqhN.
- destruct T as [[h|]|[Tl Tr]]; try (simpl; tauto).
  intros [H1 H2]. simpl.
  apply mtree_hashroot_None_empty_mtree_p in H1.
  apply mtree_hashroot_None_empty_mtree_p in H2.
  rewrite H1. rewrite H2. reflexivity.
Qed.

Lemma mtree_hashroot_empty_p {n} (T:mtree n) :
  empty_mtree_p T -> mtree_hashroot T = None.
intros H1. apply subqm_empty in H1.
apply subqm_hashroot_eq in H1. rewrite <- H1.
apply mtree_hashroot_empty.
Qed.

Lemma subqm_full_approx_addr {n} (T1 T2:mtree n) (alpha:bitseq n) :
  subqm T1 T2
  -> mtree_full_approx_addr T1 alpha
  -> mtree_full_approx_addr T2 alpha.
induction n as [|n IH].
- simpl. apply subqh_full_approx.
- destruct T1 as [[h1|]|[T1l T1r]]; destruct T2 as [[h2|]|[T2l T2r]]; try (simpl; tauto); try (simpl; discriminate).
  + destruct alpha as [[|] alpha].
    * { simpl. intros H1 _. apply (IH (empty_mtree n)).
        - assert (L1: mtree_hashroot T2r = None).
          { destruct (mtree_hashroot T2r) as [kr|]; try reflexivity.
            destruct (mtree_hashroot T2l); discriminate H1.
          }
          apply mtree_hashroot_None_empty_mtree_p in L1.
          now apply subqm_empty.
        - apply empty_mtree_full_approx_addr.
      }
    * { simpl. intros H1 _. apply (IH (empty_mtree n)).
        - assert (L1: mtree_hashroot T2l = None).
          { destruct (mtree_hashroot T2l) as [kl|]; try reflexivity.
            destruct (mtree_hashroot T2r); discriminate H1.
          }
          apply mtree_hashroot_None_empty_mtree_p in L1.
          now apply subqm_empty.
        - apply empty_mtree_full_approx_addr.
      }
  + destruct alpha as [[|] alpha].
    * simpl. intros [H1 H2]. revert H2. apply IH.
    * simpl. intros [H1 H2]. revert H1. apply IH.
Qed.

Lemma subqm_supports_addr {n} (T1 T2:mtree n) (alpha:bitseq n) :
  subqm T1 T2
  -> mtree_supports_addr T1 alpha
  -> mtree_supports_addr T2 alpha.
induction n as [|n IH].
- simpl. tauto.
- destruct T1 as [[h1|]|[T1l T1r]]; destruct T2 as [[h2|]|[T2l T2r]]; try (simpl; tauto).
  + discriminate.
  + intros H1 _. apply empty_supports_addr_lem. exact H1.
  + intros [Hl Hr].
    destruct alpha as [[|] alphar].
    * now apply IH.
    * now apply IH.
Qed.

Lemma empty_mtree_p_not_supports_asset (a:asset) {n} (T:mtree n) (alpha:bitseq n) :
  empty_mtree_p T
  -> ~ mtree_supports_asset a T alpha.
induction n as [|n IH].
- simpl. intros H1 H2. subst T. inversion H2.
- destruct alpha as [[|] alpha].
  + simpl. destruct T as [[h|]|[Tl Tr]].
    * tauto.
    * tauto.
    * intros [H1 H2]. now apply IH.
  + simpl. destruct T as [[h|]|[Tl Tr]].
    * tauto.
    * tauto.
    * intros [H1 H2]. now apply IH.
Qed.

Lemma subqm_supports_asset (a:asset) {n} (T1 T2:mtree n) (alpha:bitseq n) :
  subqm T1 T2
  -> mtree_supports_asset a T1 alpha
  -> mtree_supports_asset a T2 alpha.
induction n as [|n IH].
- simpl. apply subqh_In_hlist.
- destruct T1 as [h1|[T1l T1r]]; destruct T2 as [h2|[T2l T2r]]; simpl; try tauto.
  intros [Hl Hr].
  destruct alpha as [[|] alphar].
  + now apply IH.
  + now apply IH.
Qed.

Lemma subqm_asset_value_in (T1 T2:mtree 162) (inpl:list addr_assetid) (utot:nat) :
  subqm T1 T2
  -> mtree_asset_value_in T1 inpl utot
  -> mtree_asset_value_in T2 inpl utot.
intros H1 H2. induction H2 as [|h a u inpl alpha v H2 IH H3|h a inpl alpha v H2 IH H3 H3'].
- apply mtree_asset_value_in_nil.
- apply mtree_asset_value_in_cons with (a := a).
  + exact IH.
  + revert H3. apply subqm_supports_asset. exact H1.
  + assumption.
  + assumption.
- apply mtree_asset_value_in_skip with (a := a).
  + exact IH.
  + revert H3. apply subqm_supports_asset. exact H1.
  + exact H3'.
  + assumption.
Qed.

Lemma subqm_rights_consumed (T1 T2:mtree 162) (b:bool) (alpha:termaddr) (inpl:list addr_assetid) (utot:nat) :
  subqm T1 T2
  -> mtree_rights_consumed b alpha T1 inpl utot
  -> mtree_rights_consumed b alpha T2 inpl utot.
intros H1 H2. induction H2 as [|beta h inpr r1 bday obl r2 H2 IH H3|beta h inpr r1 bday obl u H2 IH H3].
- apply mtree_rights_consumed_nil.
- apply mtree_rights_consumed_cons with (bday := bday) (obl := obl).
  + exact IH.
  + revert H3. apply subqm_supports_asset. exact H1.
- apply mtree_rights_consumed_skip with (bday := bday) (obl := obl) (u := u).
  + exact IH.
  + revert H3. apply subqm_supports_asset. exact H1.
  + assumption.
Qed.

Lemma subqh_full_approx_In_conv (a:asset) (hl1 hl2:hlist) :
  subqh hl1 hl2 ->
  hlist_full_approx hl1 ->
  In_hlist a hl2 ->
  In_hlist a hl1.
intros H. induction H as [h hl2 H1| |h hr1 hr2 H1 IH].
- simpl. tauto.
- simpl. tauto.
- simpl. intros H2 H3. inversion H3.
  + apply In_hlist_H.
  + apply In_hlist_C. now apply IH.
Qed.

Lemma subqm_full_approx_supports_asset_conv (a:asset) {n} (T1 T2:mtree n) (alpha:bitseq n) :
  subqm T1 T2 ->
  mtree_full_approx_addr T1 alpha ->
  mtree_supports_asset a T2 alpha ->
  mtree_supports_asset a T1 alpha.
induction n as [|n IH].
- simpl. apply subqh_full_approx_In_conv.
- destruct T1 as [[h1|]|[T1l T1r]]; destruct T2 as [[h2|]|[T2l T2r]]; simpl; try tauto.
  + destruct alpha as [[|] alpha].
    * intros H1 _.
      assert (L1: mtree_hashroot T2r = None).
      { destruct (mtree_hashroot T2r) as [kr|]; try reflexivity.
        destruct (mtree_hashroot T2l); discriminate H1.
      }
      apply mtree_hashroot_None_empty_mtree_p in L1.
      now apply empty_mtree_p_not_supports_asset.
    * intros H1 _.
      assert (L1: mtree_hashroot T2l = None).
      { destruct (mtree_hashroot T2l) as [kl|]; try reflexivity.
        destruct (mtree_hashroot T2r); discriminate H1.
      }
      apply mtree_hashroot_None_empty_mtree_p in L1.
      now apply empty_mtree_p_not_supports_asset.
  + destruct alpha as [[|] alpha].
    * intros [H1 H2]. now apply IH.
    * intros [H1 H2]. now apply IH.
Qed.

Lemma In_hlist_In_assetlist (a:asset) (hl:hlist) (al:list asset) :
  hashassetlist al = hlist_hashroot hl ->
  In_hlist a hl -> In a al.
intros H1 H. revert al H1. induction H as [hl|b hl H IH].
- intros [|c al].
  + simpl. destruct (hlist_hashroot hl); discriminate.
  + intros H1. left.
    change (match hashassetlist al with
              | Some k => Some (hashpair (hashnat 4) (hashpair (hashasset c) k))
              | None => Some (hashpair (hashnat 3) (hashasset c))
            end =
            match hlist_hashroot hl with
              | Some k => Some (hashpair (hashnat 4) (hashpair (hashasset a) k))
              | None => Some (hashpair (hashnat 3) (hashasset a))
            end) in H1.
    destruct (hashassetlist al) as [k1|] eqn: E1; destruct (hlist_hashroot hl) as [k2|] eqn: E2.
    * inversion H1.
      apply hashpairinj in H0. destruct H0 as [_ H0].
      apply hashpairinj in H0. destruct H0 as [H0 _].
      now apply hashassetinj.
    * exfalso. inversion H1.
      apply hashpairinj in H0. destruct H0 as [H0 _].
      apply hashnatinj in H0. omega.
    * exfalso. inversion H1.
      apply hashpairinj in H0. destruct H0 as [H0 _].
      apply hashnatinj in H0. omega.
    * inversion H1.
      apply hashpairinj in H0. destruct H0 as [_ H0].
      now apply hashassetinj.
- intros [|c al].
  + simpl. destruct (hlist_hashroot hl); discriminate.
  + intros H1.
    change (match hashassetlist al with
              | Some k => Some (hashpair (hashnat 4) (hashpair (hashasset c) k))
              | None => Some (hashpair (hashnat 3) (hashasset c))
            end =
            match hlist_hashroot hl with
              | Some k => Some (hashpair (hashnat 4) (hashpair (hashasset b) k))
              | None => Some (hashpair (hashnat 3) (hashasset b))
            end) in H1.
    right. apply IH.
    destruct (hashassetlist al) as [k1|] eqn: E1; destruct (hlist_hashroot hl) as [k2|] eqn: E2.
    * inversion H1.
      apply hashpairinj in H2. destruct H2 as [_ H2].
      apply hashpairinj in H2. destruct H2 as [_ H2].
      congruence.
    * exfalso. inversion H1.
      apply hashpairinj in H2. destruct H2 as [H2 _].
      apply hashnatinj in H2. omega.
    * exfalso. inversion H1.
      apply hashpairinj in H2. destruct H2 as [H2 _].
      apply hashnatinj in H2. omega.
    * reflexivity.
Qed.

Lemma mtree_supports_asset_In_statefun (a:asset) {n} :
  forall (T:mtree n) (f:bitseq n -> list asset),
    forall (alpha:bitseq n),
      mtree_approx_fun_p T f ->
      mtree_supports_asset a T alpha -> In a (f alpha).
induction n as [|n IHn].
- intros hl f [] H1 H2. simpl in *|-*.
  now apply In_hlist_In_assetlist with (hl := hl).
- intros [h|[Tl Tr]].
  + intros f alpha H1 [].
  + intros f [[|] alpha] [H1a H1b] H2; simpl in H2.
    * now apply (IHn _ _ _ H1b).
    * now apply (IHn _ _ _ H1a).
Qed.

Lemma In_hlist_In_assetlist_conv (a:asset) (hl:hlist) (al:list asset) :
  hashassetlist al = hlist_hashroot hl ->
  hlist_full_approx hl ->
  In a al -> In_hlist a hl.
revert al. induction hl as [h| |h hr IH].
- simpl. tauto.
- intros [|b ar].
  + simpl. tauto.
  + unfold hashassetlist. simpl.
    destruct (ohashlist (map hashasset ar)); discriminate.
- intros [|b ar]; simpl.
  + destruct (hlist_hashroot hr); discriminate.
  + unfold hashassetlist. simpl.
    destruct (ohashlist (map hashasset ar)) as [k1|] eqn:E1;
      destruct (hlist_hashroot hr) as [k2|] eqn:E2.
    * { intros H1. inversion H1.
        apply hashpairinj in H0. destruct H0 as [_ H0].
        apply hashpairinj in H0. destruct H0 as [H2 H3].
        apply hashassetinj in H2.
        intros H4 [H5|H5].
        - subst h. subst a. apply In_hlist_H.
        - apply In_hlist_C. revert H5. apply IH.
          + subst k2. exact E1.
          + exact H4.
      }
    * intros H1. exfalso. inversion H1.
      apply hashpairinj in H0. destruct H0 as [H0 _].
      apply hashnatinj in H0. omega.
    * intros H1. exfalso. inversion H1.
      apply hashpairinj in H0. destruct H0 as [H0 _].
      apply hashnatinj in H0. omega.
    * { intros H1. inversion H1.
        apply hashpairinj in H0. destruct H0 as [_ H0].
        apply hashassetinj in H0.
        intros H4 [H5|H5].
        - subst h. subst a. apply In_hlist_H.
        - exfalso. destruct ar as [|b' ar'].
          + contradiction H5.
          + simpl in E1.
            destruct (ohashlist (map hashasset ar')); discriminate E1.
      }
Qed.

Lemma empty_mtree_p_full_approx_addr {n} (T:mtree n) (alpha:bitseq n) :
  empty_mtree_p T ->
  mtree_full_approx_addr T alpha.
induction n as [|n IH].
- simpl. intros H1. subst T. simpl. tauto.
- destruct T as [[h|]|[Tl Tr]].
  + simpl. tauto.
  + simpl. tauto.
  + intros [Hl Hr]. destruct alpha as [[|] alpha].
    * simpl. revert Hr. apply IH.
    * simpl. revert Hl. apply IH.
Qed.
  
Lemma mtree_supports_asset_In_statefun_conv (a:asset) {n} :
  forall (T:mtree n) (f:bitseq n -> list asset),
    forall (alpha:bitseq n),
      mtree_approx_fun_p T f ->
      mtree_full_approx_addr T alpha ->
      In a (f alpha) -> mtree_supports_asset a T alpha.
induction n as [|n IHn].
- intros hl f [] H1 H2 H3. simpl in *|-*.
  now apply In_hlist_In_assetlist_conv with (hl := hl) (al := f tt).
- intros [[h|]|[Tl Tr]].
  + intros f alpha H1 H2 H3. contradiction H2.
  + intros f [[|] alpha] [Tl [Tr [H1a [H1b H1c]]]] H2 H3. simpl.
    * assert (L1: mtree_hashroot Tr = None).
      { destruct (mtree_hashroot Tr); try reflexivity.
        destruct (mtree_hashroot Tl); discriminate H1a.
      }
      apply mtree_hashroot_None_empty_mtree_p in L1.
      assert (L2: mtree_supports_asset a Tr alpha).
      { apply (IHn Tr (fun alpha => f (true, alpha)) alpha H1c).
        - revert L1. apply empty_mtree_p_full_approx_addr.
        - exact H3.
      }
      revert L1 L2. apply empty_mtree_p_not_supports_asset.
    * assert (L1: mtree_hashroot Tl = None).
      { destruct (mtree_hashroot Tl); try reflexivity.
        destruct (mtree_hashroot Tr); discriminate H1a.
      }
      apply mtree_hashroot_None_empty_mtree_p in L1.
      assert (L2: mtree_supports_asset a Tl alpha).
      { apply (IHn Tl (fun alpha => f (false, alpha)) alpha H1b).
        - revert L1. apply empty_mtree_p_full_approx_addr.
        - exact H3.
      }
      revert L1 L2. apply empty_mtree_p_not_supports_asset.
  + intros f [[|] alpha] [H1a H1b] H2; simpl in H2.
    * now apply (IHn _ _ _ H1b).
    * now apply (IHn _ _ _ H1a).
Qed.

Opaque mtree_supports_asset.

Lemma mtree_valid_supports_asset_uniq (a1 a2:asset) (T:mtree 162) (alpha:addr) :
  mtree_valid T ->
  mtree_supports_asset a1 T alpha ->
  mtree_supports_asset a2 T alpha ->
  assetid a1 = assetid a2 -> a1 = a2.
intros [f [[_ [Hf2 _]] HTf]] H1 H2 H3.
assert (L1: In a1 (f alpha)).
{ revert H1. apply mtree_supports_asset_In_statefun. exact HTf. }
assert (L2: In a2 (f alpha)).
{ revert H2. apply mtree_supports_asset_In_statefun. exact HTf. }
destruct a1 as [h oblu1].
destruct a2 as [h2 oblu2].
simpl in H3. subst h2.
destruct (Hf2 h alpha oblu1 alpha oblu2 L1 L2) as [_ H4].
congruence.
Qed.

Lemma mtree_check_signaspec_r_marker sigt T th thy d h :
  In h (signaspec_stp_markers d) \/ In h (signaspec_known_markers th d) ->
  check_signaspec_r (mtree_lookup_stp T) (mtree_lookup_known T) sigt th thy d ->
  exists (k : hashval) (bday : nat) (obl : obligation),
    mtree_supports_asset (k, (bday, (obl, marker))) T (hashval_term_addr h).
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

Lemma mtree_check_signaspec_p_marker tht sigt T th d h :
  In h (signaspec_stp_markers d) \/ In h (signaspec_known_markers th d) ->
  check_signaspec_p (mtree_lookup_stp T) (mtree_lookup_known T) tht sigt th d ->
  exists (k : hashval) (bday : nat) (obl' : obligation),
    mtree_supports_asset (k, (bday, (obl', marker))) T (hashval_term_addr h).
unfold check_signaspec_p. destruct th as [th|].
- destruct tht as [tht|].
  + apply mtree_check_signaspec_r_marker.
  + tauto.
- apply mtree_check_signaspec_r_marker.
Qed.

Lemma mtree_check_doc_r_marker sigt T th thy d h :
  In h (doc_stp_markers d) \/ In h (doc_known_markers th d) ->
  check_doc_r (mtree_lookup_stp T) (mtree_lookup_known T) sigt th thy d ->
  exists (k : hashval) (bday : nat) (obl : obligation),
    mtree_supports_asset (k, (bday, (obl, marker))) T (hashval_term_addr h).
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

Lemma mtree_check_doc_p_marker tht sigt T th d h :
  In h (doc_stp_markers d) \/ In h (doc_known_markers th d) ->
  check_doc_p (mtree_lookup_stp T) (mtree_lookup_known T) tht sigt th d ->
  exists (k : hashval) (bday : nat) (obl' : obligation),
    mtree_supports_asset (k, (bday, (obl', marker))) T (hashval_term_addr h).
unfold check_doc_p. destruct th as [th|].
- destruct tht as [tht|].
  + apply mtree_check_doc_r_marker.
  + tauto.
- apply mtree_check_doc_r_marker.
Qed.

Theorem mtree_supports_tx_can_support tht sigt m tx (T:mtree 162) fee rew :
  mtree_supports_tx tht sigt m tx T fee rew ->
  mtree_can_support_tx tx T.
intros [Hs1 [[utot [Hs2 Hs3]] [[Hs4a Hs4b] [[Hs5a [Hs5b Hs5c]] [Hs6 [Hs7 Hs8]]]]]]. repeat split.
- destruct tx as [inpl outpl]. simpl. simpl in Hs2.
  clear Hs1 fee rew Hs3 Hs4a Hs4b Hs5a Hs5b Hs5c Hs6 Hs7 Hs8.
  induction Hs2 as [|h a u inpl alpha v H1 IH H2 H3 H4|h a inpl alpha v H1 IH H2 H3 H4].
  + intros alpha h [].
  + intros beta k [H5|H5].
    * inversion H5. subst beta. subst k. subst h. exists (assetbday a,(assetobl a,assetpre a)).
      destruct a as [h [bday [obl w]]]; exact H2.
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
  revert H2 H3. apply mtree_check_signaspec_p_marker.
- intros obl gamma nonce th d alpha h H1 H2.
  destruct (Hs5c obl gamma nonce th d alpha H1) as [H3 _].
  revert H2 H3. apply mtree_check_doc_p_marker.
Qed.

Lemma subqm_lookup_stp (T1 T2:mtree 162) h a :
  subqm T1 T2 ->
  mtree_lookup_stp T1 h a ->
  mtree_lookup_stp T2 h a.
unfold mtree_lookup_stp. intros H1 [k [bday [obl H2]]].
exists k. exists bday. exists obl. revert H2.
apply subqm_supports_asset. exact H1.
Qed.

Lemma subqm_lookup_known (T1 T2:mtree 162) h :
  subqm T1 T2 ->
  mtree_lookup_known T1 h ->
  mtree_lookup_known T2 h.
unfold mtree_lookup_stp. intros H1 [k [bday [obl H2]]].
exists k. exists bday. exists obl. revert H2.
apply subqm_supports_asset. exact H1.
Qed.

Theorem subqm_supports_tx tht sigt m tx (T1 T2:mtree 162) fee rew :
  mtree_valid T2 ->
  subqm T1 T2 ->
  mtree_supports_tx tht sigt m tx T1 fee rew ->
  mtree_supports_tx tht sigt m tx T2 fee rew.
intros H0 H1 Hs. generalize Hs. intros [Hs1 [[utot [Hs2 Hs3]] [[Hs4a Hs4b] [[Hs5a [Hs5b Hs5c]] [Hs6 [Hs7 Hs8]]]]]].
apply mtree_supports_tx_can_support in Hs.
destruct Hs as [Hc1 [Hc2 [Hc3 [Hc4 Hc5]]]].
split.
- intros alpha u H2. generalize (Hs1 alpha u H2).
  apply subqm_supports_addr. exact H1.
- split.
  + exists utot. split.
    * revert Hs2. apply subqm_asset_value_in. exact H1.
    * exact Hs3.
  + split.
    * { split.
        - intros alpha b H2.
          destruct (Hs4a alpha b H2) as [Hs4aa [Hs4ab Hs4ac]].
          repeat split.
          + revert Hs4aa. apply subqm_full_approx_addr. exact H1.
          + intros [h' [bday' [obl' [beta' H3]]]]. apply Hs4ab.
            exists h'. exists bday'. exists obl'. exists beta'.
            revert H1 Hs4aa H3. apply subqm_full_approx_supports_asset_conv.
          + intros rtot1 rtot2 h bday obl beta u H3 H4 H5.
            assert (L1: mtree_supports_asset (h, (bday,(obl, owns b beta (Some u)))) T1 (termaddr_addr alpha)).
            { revert H4. apply subqm_full_approx_supports_asset_conv.
              - exact H1.
              - exact Hs4aa.
            }
            destruct (Hs4ac rtot1 rtot2 h bday obl beta u H3 L1 H5) as [rtot3 [rtot4 [H6 [H7 H8]]]].
            * { exists rtot3. exists rtot4. repeat split.
                - revert H1 H6. apply subqm_rights_consumed.
                - exact H7.
                - exact H8.
              }
        - intros alpha b beta h bday obl n H2 H3.
          assert (L1: mtree_supports_asset (h, (bday,(obl, rights b n alpha))) T1 beta).
          { destruct (Hc1 _ _ H2) as [[bday' [obl' v]] H4].
            generalize (subqm_supports_asset _ T1 T2 beta H1 H4).
            intros H5.
            assert (L1a: (h, (bday',(obl', v))) = (h, (bday,(obl, rights b n alpha)))).
            { apply (mtree_valid_supports_asset_uniq (h,(bday',(obl',v))) (h,(bday,(obl,rights b n alpha))) T2 beta H0 H5 H3).
              reflexivity.
            }
            inversion L1a.
            subst bday'. subst obl'. subst v.
            exact H4.
          }
          revert H2 L1. apply Hs4b.
      }
    * { split.
        - split.
          + intros obl gamma nonce d alpha H2.
            destruct (Hs5a obl gamma nonce d alpha H2) as [Hch [beta [h [bday' [obl' [H3 [H4 [H5 H6]]]]]]]].
            split; try exact Hch.
            exists beta. exists h. exists bday'. exists obl'. repeat split.
            * exact H3.
            * exact H4.
            * exact H5.
            * revert H1 H6. apply subqm_supports_asset.
          + split.
            * { intros obl gamma nonce th d alpha H2.
                destruct (Hs5b obl gamma nonce th d alpha H2) as [Hch [beta [h [bday' [obl' [H3 [H4 [H5 H6]]]]]]]].
                split.
                - revert Hch. apply check_signaspec_p_subq.
                  + intros h' a'. apply subqm_lookup_stp. exact H1.
                  + intros h'. apply subqm_lookup_known. exact H1.
                - exists beta. exists h. exists bday'. exists obl'. repeat split.
                  + exact H3.
                  + exact H4.
                  + exact H5.
                  + revert H1 H6. apply subqm_supports_asset.
              }
            * { intros obl gamma nonce th d alpha H2.
                destruct (Hs5c obl gamma nonce th d alpha H2) as [Hch [beta [h [bday' [obl' [H3 [H4 [H5 H6]]]]]]]].
                split.
                - revert Hch. apply check_doc_p_subq.
                  + intros h' a'. apply subqm_lookup_stp. exact H1.
                  + intros h'. apply subqm_lookup_known. exact H1.
                - exists beta. exists h. exists bday'. exists obl'. repeat split.
                  + exact H3.
                  + exact H4.
                  + exact H5.
                  + revert H1 H6. apply subqm_supports_asset.
              }
        - split.
          + intros alpha b obl beta r H2.
            destruct (Hs6 alpha b obl beta r H2) as [H3 [[h [beta' [bday' [obl' [r' [H4 H5]]]]]]|[H4 H5]]]; split.
            * revert H1 H3. apply subqm_full_approx_addr.
            * { left. exists h. exists beta'. exists bday'. exists obl'. exists r'. split.
                - revert H1 H4. apply subqm_supports_asset.
                - exact H5.
              }
            * revert H1 H3. apply subqm_full_approx_addr.
            * { right. split.
                - intros [h [beta' [bday' [obl' [r' H6]]]]]. apply H4.
                  exists h. exists beta'. exists bday'. exists obl'. exists r'.
                  revert H1 H3 H6. apply subqm_full_approx_supports_asset_conv.
                - exact H5.
              }
          + split.
            * { intros k1 k2 b H2.
                destruct (Hs7 k1 k2 b H2) as [H3 H4]. split.
                - revert H1 H3. apply subqm_full_approx_addr.
                - intros H5. apply H4. intros [h' [beta' [bday' [obl' [r' H6]]]]].
                  apply H5. exists h'. exists beta'. exists bday'. exists obl'. exists r'.
                  revert H1 H6. apply subqm_supports_asset.
              }
            * { intros alpha h bday obl u H2 H3.
                generalize H2. intros H2a.
                apply Hc1 in H2a.
                destruct H2a as [[bday' [obl' v]] H4].
                generalize (subqm_supports_asset _ T1 T2 alpha H1 H4).
                intros H5.
                assert (L1: (h, (bday', (obl', v))) = (h, (bday, (obl, bounty u)))).
                { apply (mtree_valid_supports_asset_uniq _ _ T2 alpha H0 H5 H3).
                  reflexivity.
                }
                inversion L1.
                subst bday'. subst obl'. subst v.
                destruct (Hs8 alpha h bday obl u H2 H4) as [H6 [h' [bday' [obl' [beta [r [H7 [H8 H9]]]]]]]].
                split.
                - revert H1 H6. apply subqm_full_approx_addr.
                - exists h'. exists bday'. exists obl'. exists beta. exists r. repeat split.
                  + exact H7.
                  + revert H1 H8. apply subqm_supports_asset.
                  + exact H9.
              }
      }
Qed.

Theorem mtree_supports_tx_lub_1 tht sigt m tx (T1 T2:mtree 162) fee rew :
  mtree_valid T1 ->
  mtree_hashroot T1 = mtree_hashroot T2 ->
  mtree_supports_tx tht sigt m tx T1 fee rew ->
  mtree_supports_tx tht sigt m tx (mtree_lub T1 T2) fee rew.
intros H0 H1. apply subqm_supports_tx.
- revert H0. apply mtree_hashroot_eq_valid.
  apply mtree_lub_eq_1. exact H1.
- apply subqm_lub_1. exact H1.
Qed.

Fixpoint equi {n:nat} : mtree n -> mtree n -> Prop :=
match n with
| O => fun T1 T2 => T1 = T2
| S n => fun T1 T2 =>
           match T1,T2 with
             | inl h1, inl h2 => h1 = h2
             | inr (T1l,T1r),inr (T2l,T2r) => equi T1l T2l /\ equi T1r T2r
             | inl None,inr (T2l,T2r) => empty_mtree_p T2l /\ empty_mtree_p T2r
             | inr (T1l,T1r),inl None => empty_mtree_p T1l /\ empty_mtree_p T1r
             | _,_ => False
           end
end.

Lemma equi_ref {n:nat} (T:mtree n) : equi T T.
induction n as [|n IH].
- simpl. reflexivity.
- destruct T as [[h|]|[Tl Tr]]; simpl.
  + reflexivity.
  + reflexivity.
  + split; apply IH.
Qed.

Lemma equi_sym {n:nat} (T1 T2:mtree n) : equi T1 T2 -> equi T2 T1.
induction n as [|n IH].
- simpl. now symmetry.
- destruct T1 as [[h1|]|[T1l T1r]]; destruct T2 as [[h2|]|[T2l T2r]]; simpl; try tauto; try discriminate.
  + intros H1. symmetry. assumption.
  + intros [H1 H2]. split; now apply IH.
Qed.

Lemma equi_empty_lem {n} : equi (mtreeH n None) (mtreeB (empty_mtree n) (empty_mtree n)).
simpl. split; apply empty_mtree_p_empty_mtree.
Qed.

Lemma equi_empty_1 {n:nat} (T1 T2:mtree n) : empty_mtree_p T1 -> equi T1 T2 -> empty_mtree_p T2.
induction n as [|n IH].
- simpl. congruence.
- destruct T1 as [[h1|]|[T1l T1r]]; destruct T2 as [[h2|]|[T2l T2r]]; simpl; try tauto; try discriminate; try congruence.
  intros [H1 H2] [H3 H4]. split.
  * apply (IH _ _ H1 H3).
  * apply (IH _ _ H2 H4).
Qed.

Lemma equi_empty_2 {n:nat} (T1 T2:mtree n) : empty_mtree_p T1 -> empty_mtree_p T2 -> equi T1 T2.
induction n as [|n IH].
- simpl. congruence.
- destruct T1 as [[h1|]|[T1l T1r]]; destruct T2 as [[h2|]|[T2l T2r]]; simpl; try tauto; try discriminate; try congruence.
  intros [H1 H2] [H3 H4]. split.
  * apply (IH _ _ H1 H3).
  * apply (IH _ _ H2 H4).
Qed.

Lemma equi_tra {n:nat} (T1 T2 T3:mtree n) : equi T1 T2 -> equi T2 T3 -> equi T1 T3.
induction n as [|n IH].
- simpl. congruence.
- destruct T1 as [[h1|]|[T1l T1r]]; destruct T2 as [[h2|]|[T2l T2r]]; destruct T3 as [[h3|]|[T3l T3r]]; simpl; try tauto; try discriminate; try congruence.
  + intros [H1 H2] [H3 H4]. split.
    * exact (equi_empty_1 _ _ H1 H3).
    * exact (equi_empty_1 _ _ H2 H4).
  + intros [H1 H2] [H3 H4]. split.
    * exact (equi_empty_2 _ _ H1 H3).
    * exact (equi_empty_2 _ _ H2 H4).
  + intros [H1 H2] [H3 H4]. split.
    * apply equi_sym in H1. exact (equi_empty_1 _ _ H3 H1).
    * apply equi_sym in H2. exact (equi_empty_1 _ _ H4 H2).
  + intros [H1 H2] [H3 H4]. split.
    * now apply (IH _ _ _ H1).
    * now apply (IH _ _ _ H2).
Qed.

Lemma mtreeB_equi {n} (Tl Tr Tl' Tr':mtree n) :
  equi Tl Tl' -> equi Tr Tr' -> equi (mtreeB Tl Tr) (mtreeB Tl' Tr').
induction n as [|n].
- simpl. tauto.
- intros H1 H2. split; assumption.
Qed.

Lemma mtree_hashroot_equi {n} (T1 T2:mtree n) : equi T1 T2 -> mtree_hashroot T1 = mtree_hashroot T2.
induction n as [|n IH].
- simpl. unfold equi. intros H1. congruence.
- destruct T1 as [[h1|]|[T1l T1r]]; destruct T2 as [[h2|]|[T2l T2r]]; simpl; try tauto.
  + intros [H1 H2].
    rewrite (mtree_hashroot_empty_p _ H1).
    rewrite (mtree_hashroot_empty_p _ H2).
    reflexivity.
  + intros [H1 H2].
    rewrite (mtree_hashroot_empty_p _ H1).
    rewrite (mtree_hashroot_empty_p _ H2).
    reflexivity.
  + intros [H1 H2]. apply IH in H1. apply IH in H2.
    congruence.
Qed.

Fixpoint hlist_new_assets (nw:list asset) (old:hlist) : hlist :=
match nw with
| nil => old
| cons u nw' => hlistC u (hlist_new_assets nw' old)
end.

Fixpoint remove_assets_hlist (hl:hlist) (spent:list hashval) : hlist :=
match hl with
| hlistC (h,u) hl' =>
  if in_dec hashval_eq_dec h spent then
    remove_assets_hlist hl' spent
  else
    hlistC (h,u) (remove_assets_hlist hl' spent)
| _ => hl
end.

Lemma remove_assets_hlist_iff h u hl spent :
  In_hlist (h,u) (remove_assets_hlist hl spent)
  <->
  In_hlist (h,u) hl /\ ~In h spent.
induction hl as [h'| |[h' u'] ar IH].
- simpl. split.
  + intros H1. inversion H1.
  + intros [H1 _]. inversion H1.
- simpl. split.
  + intros H1. inversion H1.
  + intros [H1 _]. inversion H1.
- simpl. destruct (in_dec hashval_eq_dec h' spent) as [H1|H1]; split.
  + intros H2. apply IH in H2. split.
    * apply In_hlist_C. tauto.
    * tauto.
  + intros [H2 H3]. inversion H2.
    * exfalso. congruence.
    * apply IH. tauto.
  + intros H2. inversion H2.
    * { split.
        - apply In_hlist_H.
        - subst h'. assumption.
      }
    * { apply IH in H0. split.
        - apply In_hlist_C. tauto.
        - tauto.
      }
  + intros [H2 H3]. inversion H2.
    * apply In_hlist_H.
    * apply In_hlist_C. apply IH. tauto.
Qed.

Fixpoint tx_mtree_trans_ {n:nat} : forall (inpl:list (bitseq n * hashval)%type) (outpl:list (bitseq n * asset)%type) (T:mtree n), mtree n :=
  match n with
    | 0 =>
      fun inpl outpl =>
        match inpl,outpl with
          | nil,nil => fun hl:mtree 0 => hl
          | _,_ => fun hl:mtree 0 =>
                     hlist_new_assets (map (@snd (bitseq 0) asset) outpl) (remove_assets_hlist hl (map (@snd (bitseq 0) hashval) inpl))
        end
    | S n =>
      fun inpl outpl =>
        match inpl,outpl with
          | nil,nil => fun (T:mtree (S n)) => T
          | _,_ => fun (T:mtree (S n)) =>
            match T with
              | inl (Some h) => mtreeH n (Some h) (*** error actually ***)
              | inl None => (*** assume inpl is nil but outpl isn't ***)
                let outpll := strip_bitseq_false outpl in
                let outplr := strip_bitseq_true outpl in
                mtreeB (tx_mtree_trans_ nil outpll (empty_mtree n)) (tx_mtree_trans_ nil outplr (empty_mtree n))
              | inr (Tl,Tr) =>
                let inpll := strip_bitseq_false inpl in
                let inplr := strip_bitseq_true inpl in
                let outpll := strip_bitseq_false outpl in
                let outplr := strip_bitseq_true outpl in
                mtreeB (tx_mtree_trans_ inpll outpll Tl) (tx_mtree_trans_ inplr outplr Tr)
            end
        end
  end.

Definition tx_mtree_trans (m:nat) (tx:Tx) (T:mtree 162) : mtree 162 :=
tx_mtree_trans_ (tx_inputs tx) (add_vout m (hashtx tx) (tx_outputs tx) 0) T.

Lemma tx_mtree_trans_nochange_lem {n} :
  forall T:mtree n,
    tx_mtree_trans_ nil nil T = T.
destruct n as [|n].
- intros T. simpl. reflexivity.
- intros T. simpl. reflexivity.
Qed.

Fixpoint singlebranch_mtree (hl:nehlist) {n} : bitseq n -> mtree n :=
  match n as n' return bitseq n' -> mtree n' with
    | O => fun (alpha:bitseq 0) => nehlist_hlist hl
    | S n => fun (alpha:bitseq (S n)) =>
      match alpha with
        | (false,alphar) => mtreeB (singlebranch_mtree hl alphar) (empty_mtree n)
        | (true,alphar) => mtreeB (empty_mtree n) (singlebranch_mtree hl alphar)
      end
end.

Lemma empty_mtree_supports_addr {n} (alpha:bitseq n) :
  mtree_supports_addr (empty_mtree n) alpha.
destruct n as [|n]; simpl; tauto.
Qed.

Lemma singlebranch_mtree_supports_addr (hl:nehlist) {n} (gamma alpha:bitseq n) :
  mtree_supports_addr (singlebranch_mtree hl gamma) alpha.
induction n as [|n IH].
- simpl. tauto.
- destruct gamma as [[|] gamma]; destruct alpha as [[|] alpha].
  + simpl. apply IH.
  + simpl. apply empty_mtree_supports_addr.
  + simpl. apply empty_mtree_supports_addr.
  + simpl. apply IH.
Qed.

Definition nehlist_full_approx (hl:nehlist) : Prop :=
match hl with
| inl _ => False
| inr (h,hr) => hlist_full_approx hr
end.

Lemma singlebranch_mtree_full_approx_addr (hl:nehlist) {n} (gamma alpha:bitseq n) :
  gamma <> alpha \/ nehlist_full_approx hl ->
  mtree_full_approx_addr (singlebranch_mtree hl gamma) alpha.
induction n as [|n IH].
- destruct alpha as []. destruct gamma as []. 
  destruct hl as [h|[h hl]].
  + simpl. tauto.
  + simpl. tauto.
- destruct gamma as [[|] gamma]; destruct alpha as [[|] alpha].
  + simpl. intros H1. apply IH.
    destruct H1 as [H1|H1].
    * left. congruence.
    * now right.
  + simpl. intros _. apply empty_mtree_full_approx_addr.
  + simpl. intros _. apply empty_mtree_full_approx_addr.
  + simpl. intros H1. apply IH.
    destruct H1 as [H1|H1].
    * left. congruence.
    * now right.
Qed.

Lemma singlebranch_mtree_full_approx_addr_conv (hl:nehlist) {n} (gamma alpha:bitseq n) :
  mtree_full_approx_addr (singlebranch_mtree hl gamma) alpha ->
  gamma <> alpha \/ nehlist_full_approx hl.
induction n as [|n IH].
- simpl. destruct hl as [h|[h hl]].
  + simpl. tauto.
  + simpl. tauto.
- destruct gamma as [[|] gamma]; destruct alpha as [[|] alpha].
  + simpl. intros H1. apply IH in H1.
    destruct H1 as [H1|H1].
    * left. congruence.
    * now right.
  + simpl. intros _. left. discriminate.
  + simpl. intros _. left. discriminate.
  + simpl. intros H1. apply IH in H1.
    destruct H1 as [H1|H1].
    * left. congruence.
    * now right.
Qed.

Transparent mtree_supports_asset.

Lemma singlebranch_mtree_supports_asset_conv (a:asset) {n} (hl:nehlist) (gamma alpha:bitseq n) :
   mtree_supports_asset a (singlebranch_mtree hl gamma) alpha ->
   gamma = alpha /\ In_hlist a (nehlist_hlist hl).
intros H1. induction n as [|n IH].
- simpl in H1. destruct gamma as []. destruct alpha as [].
  tauto.
- destruct gamma as [[|] gamma]; destruct alpha as [[|] alpha].
  + simpl. destruct (IH gamma alpha H1) as [IH1 IH2]. subst gamma. tauto.
  + exfalso. revert H1. simpl. apply empty_mtree_p_not_supports_asset.
    apply empty_mtree_p_empty_mtree.
  + exfalso. revert H1. simpl. apply empty_mtree_p_not_supports_asset.
    apply empty_mtree_p_empty_mtree.
  + simpl. destruct (IH gamma alpha H1) as [IH1 IH2]. subst gamma. tauto.
Qed.

Opaque mtree_supports_asset.

(*** Replaces "(None . None)" with "None" ***)
Fixpoint normalize_mtree {n} : mtree n -> mtree n :=
match n with
  | O => fun hl:mtree 0 => hl
  | S n => fun T:mtree (S n) =>
             match T with
               | inl h => inl h
               | inr (Tl,Tr) =>
                 let Tl' := normalize_mtree Tl in
                 let Tr' := normalize_mtree Tr in
                 match mtree_hashroot Tl',mtree_hashroot Tr' with
                   | None,None => inl None
                   | _,_ => inr (Tl',Tr')
                 end
             end
end.

(*** Rule out mtrees like "(None . None)" in favor of simply "None" ***)
Fixpoint mtree_normal_p {n} : mtree n -> Prop :=
match n with
| O => fun hl:mtree 0 => True
| S n => fun T:mtree (S n) =>
  match T with
    | inl h => True
    | inr (Tl,Tr) => mtree_normal_p Tl /\ mtree_normal_p Tr /\ (mtree_hashroot Tl <> None \/ mtree_hashroot Tr <> None)
  end
end.

Lemma normalize_mtree_normal_p {n} :
  forall T:mtree n, mtree_normal_p (normalize_mtree T).
induction n as [|n IH].
- intros hl. simpl. tauto.
- intros [h|[Tl Tr]].
  + simpl. tauto.
  + simpl.
    destruct (mtree_hashroot (normalize_mtree Tl)) as [hl|] eqn: ETlh.
    * { repeat split.
        - apply IH.
        - apply IH.
        - left. rewrite ETlh. discriminate.
      }
    * { destruct (mtree_hashroot (normalize_mtree Tr)) as [hr|] eqn: ETrh.
        - repeat split.
          + apply IH.
          + apply IH.
          + right. rewrite ETrh. discriminate.
        - tauto.
      }
Qed.

Lemma normalize_mtree_normal_p_id {n} :
  forall T:mtree n, mtree_normal_p T -> normalize_mtree T = T.
induction n as [|n IH].
- intros hl. simpl. tauto.
- intros [h|[Tl Tr]].
  + simpl. tauto.
  + simpl. intros [H1 [H2 [H3|H3]]].
    * rewrite (IH _ H1). rewrite (IH _ H2).
      destruct (mtree_hashroot Tl); tauto.
    * rewrite (IH _ H1). rewrite (IH _ H2).
      destruct (mtree_hashroot Tl); destruct (mtree_hashroot Tr); tauto.
Qed.

Lemma normalize_mtree_approx_fun_p {n} :
  forall T:mtree n, forall f:bitseq n -> list asset,
    mtree_approx_fun_p T f ->
    mtree_approx_fun_p (normalize_mtree T) f.
induction n as [|n IH].
- intros hl f. simpl. tauto.
- intros [h|[Tl Tr]] f.
  + simpl. tauto.
  + simpl. intros [H1 H2].
    destruct (mtree_hashroot (normalize_mtree Tl)) as [hl|] eqn: ETlh.
    * { split.
        - revert H1. apply IH.
        - revert H2. apply IH.
      }
    * { destruct (mtree_hashroot (normalize_mtree Tr)) as [hr|] eqn: ETrh.
        - split.
          + revert H1. apply IH.
          + revert H2. apply IH.
        - exists (normalize_mtree Tl). exists (normalize_mtree Tr). repeat split.
          + rewrite ETlh. rewrite ETrh. reflexivity.
          + revert H1. apply IH.
          + revert H2. apply IH.
      }
Qed.

Lemma empty_mtree_normal (n:nat) : mtree_normal_p (empty_mtree n).
destruct n; simpl; tauto.
Qed.

Lemma mtree_hashroot_singlebranch_nonempty (hl:nehlist) {n:nat} :
  forall gamma:bitseq n,
  mtree_hashroot (singlebranch_mtree hl gamma) <> None.
induction n as [|n IH].
- intros []. simpl. destruct hl as [h|[h hr]]; simpl.
  + discriminate.
  + destruct (hlist_hashroot hr); discriminate.
- intros [[|] gamma]; simpl.
  + rewrite mtree_hashroot_empty. simpl. specialize (IH gamma).
    destruct (mtree_hashroot (singlebranch_mtree hl gamma)) as [H2|H2].
    * discriminate.
    * exfalso. tauto.
  + rewrite mtree_hashroot_empty. simpl. specialize (IH gamma).
    destruct (mtree_hashroot (singlebranch_mtree hl gamma)) as [H2|H2].
    * discriminate.
    * exfalso. tauto.
Qed.

Lemma singlebranch_mtree_normal (hl:nehlist) {n:nat} :
  forall gamma:bitseq n,
  mtree_normal_p (singlebranch_mtree hl gamma).
induction n as [|n IH].
- intros []. simpl. tauto.
- intros [[|] gamma]; simpl; repeat split.
  + apply empty_mtree_normal.
  + apply IH.
  + right. apply mtree_hashroot_singlebranch_nonempty.
  + apply IH.
  + apply empty_mtree_normal.
  + left. apply mtree_hashroot_singlebranch_nonempty.
Qed.

Lemma equi_normalize_mtree_1 {n} (T:mtree n) : equi T (normalize_mtree T).
  induction n as [|n IH].
  - simpl. reflexivity.
  - destruct T as [[h|]|[Tl Tr]].
    + simpl. reflexivity.
    + simpl. reflexivity.
    + simpl. destruct (mtree_hashroot (normalize_mtree Tl)) eqn:H1.
      * split; apply IH.
      * { destruct (mtree_hashroot (normalize_mtree Tr)) eqn:H2.
          - split; apply IH.
          - split.
            + specialize (IH Tl). apply equi_sym in IH.
              revert IH. apply equi_empty_1.
              now apply mtree_hashroot_None_empty_mtree_p.
            + specialize (IH Tr). apply equi_sym in IH.
              revert IH. apply equi_empty_1.
              now apply mtree_hashroot_None_empty_mtree_p.
        }
Qed.

Lemma equi_normalize_mtree_2 {n} (T1 T2:mtree n) :
  equi T1 T2 -> normalize_mtree T1 = normalize_mtree T2.
induction n as [|n IH].
- simpl. tauto.
- destruct T1 as [[h1|]|[T1l T1r]]; destruct T2 as [[h2|]|[T2l T2r]]; simpl; try discriminate; try tauto.
  + congruence.
  + intros [H1 H2].
    generalize (equi_empty_1 _ _ H1 (equi_normalize_mtree_1 T2l)).
    intros H3. apply mtree_hashroot_None_empty_mtree_p in H3.
    generalize (equi_empty_1 _ _ H2 (equi_normalize_mtree_1 T2r)).
    intros H4. apply mtree_hashroot_None_empty_mtree_p in H4.
    rewrite H3. rewrite H4.
    reflexivity.
  + intros [H1 H2].
    generalize (equi_empty_1 _ _ H1 (equi_normalize_mtree_1 T1l)).
    intros H3. apply mtree_hashroot_None_empty_mtree_p in H3.
    generalize (equi_empty_1 _ _ H2 (equi_normalize_mtree_1 T1r)).
    intros H4. apply mtree_hashroot_None_empty_mtree_p in H4.
    rewrite H3. rewrite H4.
    reflexivity.
  + intros [H1 H2].
    rewrite (IH _ _ H1).
    rewrite (IH _ _ H2).
    reflexivity.
Qed.

Lemma mtree_valid_normalize T :
  mtree_valid T ->
  mtree_valid (normalize_mtree T).
apply mtree_hashroot_eq_valid.
symmetry.
apply mtree_hashroot_equi.
apply equi_normalize_mtree_1.
Qed.

Opaque equi.

Lemma equi_rew_lem1 {n} {T:mtree (S n)} {Tl Tr Tl' Tr':mtree n} :
  equi Tl Tl' ->
  equi Tr Tr' ->
  equi T (mtreeB Tl Tr) ->
  equi T (mtreeB Tl' Tr').
intros H1 H2 H3.
generalize (mtreeB_equi _ _ _ _ H1 H2). intros H4.
exact (equi_tra _ _ _ H3 H4).
Qed.

Fixpoint assets_hlist (al : list asset) : hlist :=
match al with
  | a::ar => hlistC a (assets_hlist ar)
  | nil => hlistN
end.

Lemma assets_hlist_approx (al : list asset) :
  approx_assetlist (assets_hlist al) al.
induction al as [|a ar IH].
- simpl. apply approx_assetlist_N.
- simpl. apply approx_assetlist_C. exact IH.
Qed.

Definition mtreeHinv {n} : mtree n -> option (option hashval) :=
match n as n' return mtree n' -> option (option hashval) with
| O => fun hl => match hl with
                   | hlistN => Some(None)
                   | hlistH(h) => Some(Some(h))
                   | _ => None
                 end
| S n => fun T =>
           match T with
             | inl h => Some(h)
             | _ => None
           end
end.

Fixpoint statefun_mtree {n} : (bitseq n -> list asset) -> mtree n :=
match n as n' return (bitseq n' -> list asset) -> mtree n' with
  | O => fun f:bitseq 0 -> list asset => assets_hlist (f tt)
  | S n => fun f:bitseq (S n) -> list asset =>
             let Tl := statefun_mtree (fun alpha => f (false,alpha)) in
             let Tr := statefun_mtree (fun alpha => f (true,alpha)) in
             match mtreeHinv Tl,mtreeHinv Tr with
               | Some(None),Some(None) => inl None
               | _,_ => mtreeB Tl Tr
             end
end.

Lemma mtreeHinv_hashroot {n} : forall T:mtree n, forall h:option hashval,
  mtreeHinv T = Some(h) -> mtree_hashroot T = h.
induction n as [|n IHn].
- intros [h1| |h1 hl] h.
  + simpl. congruence.
  + unfold mtreeHinv. intros H1. inversion H1. simpl. reflexivity.
  + simpl. intros H1. exfalso. discriminate H1.
- intros [h1|[Tl Tr]]; simpl.
  + congruence.
  + intros h H1. exfalso. discriminate H1.
Qed.

Lemma mtree_normal_hashroot_None_mtreeHinv {n} :
  forall T:mtree n,
    mtree_normal_p T -> mtree_hashroot T = None ->
    mtreeHinv T = Some(None).
destruct n as [|n].
- intros [h1| |h1 hl] h; simpl.
  + discriminate.
  + intros _. reflexivity.
  + destruct (hlist_hashroot hl); discriminate.
- intros [h1|[Tl Tr]]; simpl.
  + congruence.
  + intros [H1 [H2 [H3|H3]]] H4; exfalso.
    * { destruct (mtree_hashroot Tl); simpl in H4.
        - destruct (mtree_hashroot Tr); discriminate H4.
        - tauto.
      }
    * { destruct (mtree_hashroot Tr); simpl in H4.
        - destruct (mtree_hashroot Tl); discriminate H4.
        - tauto.
      }
Qed.

Lemma statefun_mtree_approx {n} :
  forall f:bitseq n -> list asset, mtree_approx_fun_p (statefun_mtree f) f.
induction n as [|n IHn].
- simpl. intros f. generalize (f tt) as al.
  intros al. induction al as [|a ar IHar].
  + simpl. reflexivity.
  + simpl. unfold hashassetlist. simpl.
    change (match hashassetlist ar with
              | Some k => Some (hashpair (hashnat 4) (hashpair (hashasset a) k))
              | None => Some (hashpair (hashnat 3) (hashasset a))
            end =
            match hlist_hashroot (assets_hlist ar) with
              | Some k => Some (hashpair (hashnat 4) (hashpair (hashasset a) k))
              | None => Some (hashpair (hashnat 3) (hashasset a))
            end).
    rewrite IHar. reflexivity.
- simpl. intros f.
  set (Tl := statefun_mtree (fun alpha : bitseq n => f (false, alpha))).
  set (Tr := statefun_mtree (fun alpha : bitseq n => f (true, alpha))).
  destruct (mtreeHinv Tl) as [[h|]|] eqn: Tlhe.
  + unfold mtreeB. split; apply IHn.
  + destruct (mtreeHinv Tr) as [[h|]|] eqn: Trhe.
    * unfold mtreeB. split; apply IHn.
    * { exists Tl. exists Tr. repeat split.
        - rewrite (mtreeHinv_hashroot _ _ Tlhe).
          rewrite (mtreeHinv_hashroot _ _ Trhe).
          reflexivity.
        - apply IHn.
        - apply IHn.
      }
    * unfold mtreeB. split; apply IHn.
  + unfold mtreeB. split; apply IHn.
Qed.

Lemma statefun_mtree_normal_p {n} :
  forall f:bitseq n -> list asset, mtree_normal_p (statefun_mtree f).
induction n as [|n IHn].
- simpl. intros _. tauto.
- simpl. intros f.
  set (Tl := statefun_mtree (fun alpha : bitseq n => f (false, alpha))).
  set (Tr := statefun_mtree (fun alpha : bitseq n => f (true, alpha))).
  destruct (mtreeHinv Tl) as [[h|]|] eqn: Tlhe.
  + unfold mtreeB. repeat split.
    * now apply IHn.
    * now apply IHn.
    * left. rewrite (mtreeHinv_hashroot _ _ Tlhe). congruence.
  + destruct (mtreeHinv Tr) as [[h|]|] eqn: Trhe.
    * { unfold mtreeB. repeat split.
        - now apply IHn.
        - now apply IHn.
        - right. rewrite (mtreeHinv_hashroot _ _ Trhe). congruence.
      }
    * tauto.
    * { unfold mtreeB. repeat split.
        - now apply IHn.
        - now apply IHn.
        - right. intros H1.
          assert (L1: mtreeHinv Tr = Some(None)).
          { apply mtree_normal_hashroot_None_mtreeHinv.
            - apply IHn.
            - assumption.
          }
          rewrite L1 in Trhe. discriminate Trhe.
      }
  +  unfold mtreeB. repeat split.
     * now apply IHn.
     * now apply IHn.
     * left. intros H1.
       assert (L1: mtreeHinv Tl = Some(None)).
       { apply mtree_normal_hashroot_None_mtreeHinv.
         - apply IHn.
         - assumption.
       }
       rewrite L1 in Tlhe. discriminate Tlhe.
Qed.

Lemma mtree_normal_L {n:nat} :
  forall Tl Tr:mtree n, @mtree_normal_p (S n) (inr (Tl,Tr)) -> mtree_normal_p Tl.
destruct n as [|n].
- simpl. tauto.
- simpl. destruct Tl as [hl|[Tll Tlr]].
  + tauto.
  + intros [hr|[Trl Trr]].
    * tauto.
    * tauto.
Qed.

Lemma mtree_normal_R {n:nat} :
  forall Tl Tr:mtree n, @mtree_normal_p (S n) (inr (Tl,Tr)) -> mtree_normal_p Tr.
destruct n as [|n].
- simpl. tauto.
- simpl. destruct Tl as [hl|[Tll Tlr]].
  + tauto.
  + intros [hr|[Trl Trr]].
    * tauto.
    * tauto.
Qed.

Lemma mtree_sf_rights_consumed b alpha T f inpl rtot :
  mtree_approx_fun_p T f ->
  mtree_rights_consumed b alpha T inpl rtot ->
  sf_rights_consumed b alpha f inpl rtot.
intros HTf H. induction H as [|beta h inpr r1 bday obl r2 H1 IH H2|beta h inpr r1 bday obl u H1 IH H2 H3].
- apply sf_rights_consumed_nil.
- apply sf_rights_consumed_cons with (bday := bday) (obl := obl).
  + exact IH.
  + revert HTf H2. apply mtree_supports_asset_In_statefun.
- apply sf_rights_consumed_skip with (bday := bday) (obl := obl) (u := u).
  + exact IH.
  + revert HTf H2. apply mtree_supports_asset_In_statefun.
  + exact H3.
Qed.

Lemma mtree_sf_asset_value_in (inpl : list addr_assetid) (T:mtree 162) (f:statefun) (utot:nat) :
  mtree_approx_fun_p T f ->
  mtree_asset_value_in T inpl utot ->
  statefun_asset_value_in f inpl utot.
intros H1 H.
induction H as [|h a u inpr alpha v H2 IH H3 H4 H5|h a inpr alpha v H2 IH H3 H4 H5].
- apply statefun_asset_value_in_nil.
- apply statefun_asset_value_in_cons with (a := a).
  + apply IH.
  + apply mtree_supports_asset_In_statefun with (T := T).
    * exact H1.
    * exact H3.
  + exact H4.
  + exact H5.
- apply statefun_asset_value_in_skip with (a := a).
  + apply IH.
  + apply mtree_supports_asset_In_statefun with (T := T).
    * exact H1.
    * exact H3.
  + exact H4.
  + exact H5.
Qed.

Lemma mtree_approx_fun_lookup_stp T f h a :
  mtree_approx_fun_p T f ->
  mtree_lookup_stp T h a ->
  sf_lookup_stp f h a.
unfold mtree_lookup_stp. intros H1 [k [bday [obl H2]]].
exists k. exists bday. exists obl. revert H2.
apply mtree_supports_asset_In_statefun. exact H1.
Qed.

Lemma mtree_approx_fun_lookup_known T f h :
  mtree_approx_fun_p T f ->
  mtree_lookup_known T h ->
  sf_lookup_known f h.
unfold mtree_lookup_stp. intros H1 [k [bday [obl H2]]].
exists k. exists bday. exists obl. revert H2.
apply mtree_supports_asset_In_statefun. exact H1.
Qed.

Lemma mtree_full_approx_fun_lookup_stp_conv T f h a :
  mtree_approx_fun_p T f ->
  mtree_full_approx_addr T (hashval_term_addr (hashpair h (hashstp a))) ->
  sf_lookup_stp f h a ->
  mtree_lookup_stp T h a.
unfold mtree_lookup_stp. intros H1 Ha [k [bday [obl H2]]].
exists k. exists bday. exists obl. revert H2.
apply mtree_supports_asset_In_statefun_conv.
- exact H1.
- exact Ha.
Qed.

Lemma mtree_full_approx_fun_lookup_known_conv T f h :
  mtree_approx_fun_p T f ->
  mtree_full_approx_addr T (hashval_term_addr h) ->
  sf_lookup_known f h ->
  mtree_lookup_known T h.
unfold mtree_lookup_stp. intros H1 Ha [k [bday [obl H2]]].
exists k. exists bday. exists obl. revert H2.
apply mtree_supports_asset_In_statefun_conv.
- exact H1.
- exact Ha.
Qed.

Theorem mtree_supports_tx_statefun tht sigt m tx (T:mtree 162) f fee rew :
  (forall h alpha u alpha' u', In (h,u) (f alpha) -> In (h,u') (f alpha') -> alpha = alpha' /\ u = u') ->
  mtree_approx_fun_p T f ->  
  mtree_supports_tx tht sigt m tx T fee rew ->
  statefun_supports_tx tht sigt m f tx fee rew.
intros Hf2 H1 Hs. generalize Hs. intros [Hs1 [[utot [Hs2 Hs3]] [[Hs4a Hs4b] [[Hs5a [Hs5b Hs5c]] [Hs6 [Hs7 Hs8]]]]]]. split.
- exists utot. split.
  + destruct tx as [inpl outpl]. simpl. simpl in Hs2.
    revert Hs2. 
    apply mtree_sf_asset_value_in.
    exact H1.
  + exact Hs3.
- split.
  + split.
    * { intros alpha b H2.
        destruct (Hs4a alpha b H2) as [H3 [H4 H5]].
        split.
        - intros [h' [bday' [obl' [beta' H6]]]]. apply H4.
          exists h'. exists bday'. exists obl'. exists beta'.
          revert H6.
          apply mtree_supports_asset_In_statefun_conv.
          + exact H1.
          + exact H3.
        - intros rtot1 rtot2 h bday obl beta u H6 H7 H8.
          assert (L2: mtree_supports_asset (h, (bday, (obl, owns b beta (Some u)))) T (termaddr_addr alpha)).
          { revert H7.
            apply mtree_supports_asset_In_statefun_conv.
            - exact H1.
            - exact H3.
          }
          destruct (H5 rtot1 rtot2 h bday obl beta u H6 L2 H8) as [rtot3 [rtot4 [H9 [H10 H11]]]].
          exists rtot3. exists rtot4. repeat split.
          + revert H9. simpl. apply mtree_sf_rights_consumed.
            exact H1.
          + exact H10.
          + exact H11.
      }
    * { intros alpha b beta h bday obl n H2 H3.
        assert (L1: mtree_supports_asset (h, (bday, (obl, rights b n alpha))) T beta).
        { generalize (mtree_supports_tx_can_support _ _ _ _ _ _ _ Hs).
          intros [Hc1 _].
          destruct (Hc1 _ _ H2) as [[obl' v] H4].
          generalize (mtree_supports_asset_In_statefun _ _ _ _ H1 H4).
          intros H5.
          generalize (Hf2 _ _ _ _ _ H5 H3). intros [_ H6].
          inversion H6. subst obl'. subst v.
          exact H4.
        }
        revert H2 L1. apply Hs4b.
      }
  + split.
    * { split; [|split].
        - intros obl gamma nonce d alpha H2.
          destruct (Hs5a obl gamma nonce d alpha H2) as [Hch [beta [h [bday' [obl' [H3 [H4 [H5 H6]]]]]]]].
          split.
          + exact Hch.
          + exists beta. exists h. exists bday'. exists obl'. repeat split.
            * exact H3.
            * exact H4.
            * exact H5.
            * revert H6. apply mtree_supports_asset_In_statefun. exact H1.
        - intros obl gamma nonce th d alpha H2.
          destruct (Hs5b obl gamma nonce th d alpha H2) as [Hch [beta [h [bday' [obl' [H3 [H4 [H5 H6]]]]]]]].
          split.
          + revert Hch. apply check_signaspec_p_subq.
            * intros k b. apply mtree_approx_fun_lookup_stp. exact H1.
            * intros k. apply mtree_approx_fun_lookup_known. exact H1.
          + exists beta. exists h. exists bday'. exists obl'. repeat split.
            * exact H3.
            * exact H4.
            * exact H5.
            * revert H6. apply mtree_supports_asset_In_statefun. exact H1.
        - intros obl gamma nonce th d alpha H2.
          destruct (Hs5c obl gamma nonce th d alpha H2) as [Hch [beta [h [bday' [obl' [H3 [H4 [H5 H6]]]]]]]].
          split.
          + revert Hch. apply check_doc_p_subq.
            * intros k b. apply mtree_approx_fun_lookup_stp. exact H1.
            * intros k. apply mtree_approx_fun_lookup_known. exact H1.
          + exists beta. exists h. exists bday'. exists obl'. repeat split.
            * exact H3.
            * exact H4.
            * exact H5.
            * revert H6. apply mtree_supports_asset_In_statefun. exact H1.
      } 
    * { split.
        - (*** 6 ***)
          intros alpha b obl beta r H2.
          destruct (Hs6 alpha b obl beta r H2) as [H3 [[h [beta' [bday' [obl' [r' [H4 H5]]]]]]|[H4 H5]]].
          + left. exists h. exists beta'. exists bday'. exists obl'. exists r'. split.
            * revert H4. apply mtree_supports_asset_In_statefun. exact H1.
            * exact H5.
          + right. split.
            * { intros [h [beta' [bday' [obl' [r' H6]]]]].
                apply H4. exists h. exists beta'. exists bday'. exists obl'. exists r'.
                revert H6. apply mtree_supports_asset_In_statefun_conv.
                - exact H1.
                - exact H3.
              }
            * exact H5.
        - split.
          + (*** 7 ***)
            intros k1 k2 b H2 H3.
            destruct (Hs7 k1 k2 b H2) as [H4 H5].
            apply H5.
            intros [h' [beta' [bday' [obl' [r' H6]]]]].
            apply H3. exists h'. exists beta'. exists bday'. exists obl'. exists r'.
            revert H6. apply mtree_supports_asset_In_statefun.
            exact H1.
          + (*** 8 ***)
            intros alpha h bday obl u H2 H3.
            assert (L1: mtree_supports_asset (h, (bday, (obl, bounty u))) T alpha).
            { generalize (mtree_supports_tx_can_support _ _ _ _ _ _ _ Hs).
              intros [Hc1 _].
              destruct (Hc1 _ _ H2) as [[obl' u'] H4].
              generalize (mtree_supports_asset_In_statefun _ _ _ _ H1 H4).
              intros H5.
              destruct (Hf2 h alpha (bday, (obl,bounty u)) alpha (obl',u') H3 H5) as [_ H6].
              inversion H6. subst obl'. subst u'.
              exact H4.
            }
            destruct (Hs8 alpha h bday obl u H2 L1) as [H4 [h' [bday' [obl' [beta [r [H5 [H6 H7]]]]]]]].
            exists h'. exists bday'. exists obl'. exists beta. exists r.
            repeat split.
            * exact H5.
            * revert H6. apply mtree_supports_asset_In_statefun. exact H1.
            * exact H7.
      }
Qed.

Lemma mtree_supports_asset_statefun_supports_asset a {n}
      (T:mtree n) (f:bitseq n -> list asset) (alpha:bitseq n) :
  mtree_approx_fun_p T f ->  
  mtree_supports_asset a T alpha -> In a (f alpha).
induction n as [|n IH].
- simpl. destruct alpha as []. generalize (f tt) as l. clear f.
  intros l H1 H2. simpl in T. change (In_hlist a T) in H2.
  revert l H1. induction H2 as [hl|b hl H1 IH'].
  + intros [|c l] H2.
    * simpl in H2. destruct (hlist_hashroot hl); discriminate H2.
    * { left.
        change (match hashassetlist l with
                  | Some k => Some (hashpair (hashnat 4) (hashpair (hashasset c) k))
                  | None => Some (hashpair (hashnat 3) (hashasset c))
                end =
                match hlist_hashroot hl with
                  | Some k => Some (hashpair (hashnat 4) (hashpair (hashasset a) k))
                  | None => Some (hashpair (hashnat 3) (hashasset a))
                end) in H2.
        destruct (hashassetlist l) as [lh|]; destruct (hlist_hashroot hl) as [hlh|].
        - inversion H2.
          apply hashpairinj in H0. destruct H0 as [_ H3].
          apply hashpairinj in H3. destruct H3 as [H3 _].
          apply hashassetinj in H3. exact H3.
        - inversion H2.
          apply hashpairinj in H0. destruct H0 as [H3 _].
          apply hashnatinj in H3. omega.
        - inversion H2.
          apply hashpairinj in H0. destruct H0 as [H3 _].
          apply hashnatinj in H3. omega.
        - inversion H2.
          apply hashpairinj in H0. destruct H0 as [_ H3].
          apply hashassetinj in H3. exact H3.
      }
  + intros [|c l] H2.
    * simpl in H2. destruct (hlist_hashroot hl); discriminate H2.
    * { right. apply IH'. simpl in H2.
        change (match hashassetlist l with
                  | Some k => Some (hashpair (hashnat 4) (hashpair (hashasset c) k))
                  | None => Some (hashpair (hashnat 3) (hashasset c))
                end =
                match hlist_hashroot hl with
                  | Some k => Some (hashpair (hashnat 4) (hashpair (hashasset b) k))
                  | None => Some (hashpair (hashnat 3) (hashasset b))
                end) in H2.
        destruct (hashassetlist l) as [lh|]; destruct (hlist_hashroot hl) as [hlh|].
        - inversion H2.
          apply hashpairinj in H0. destruct H0 as [_ H3].
          apply hashpairinj in H3. destruct H3 as [_ H3].
          congruence.
        - inversion H2.
          apply hashpairinj in H0. destruct H0 as [H3 _].
          apply hashnatinj in H3. omega.
        - inversion H2.
          apply hashpairinj in H0. destruct H0 as [H3 _].
          apply hashnatinj in H3. omega.
        - reflexivity.
      }
- destruct T as [h|[Tl Tr]].
  + intros _ [].
  + destruct alpha as [[|] alpha]; simpl.
    * intros [H1 H2]. 
      apply (IH Tr (fun gamma => f(true,gamma)) alpha).
      exact H2.
    * intros [H1 H2]. 
      apply (IH Tl (fun gamma => f(false,gamma)) alpha).
      exact H1.
Qed.

Lemma sf_mtree_asset_value_in (inpl : list addr_assetid) (T:mtree 162) (f:statefun) (utot:nat) :
  (forall h alpha u alpha' u', In (h,u) (f alpha) -> In (h,u') (f alpha') -> alpha = alpha' /\ u = u') ->
  mtree_approx_fun_p T f ->
  (forall (alpha : addr) (h : hashval),
     In (alpha, h) inpl ->
     exists bday:nat, exists obl:obligation, exists u:preasset, mtree_supports_asset (h, (bday,(obl,u))) T alpha) ->
  statefun_asset_value_in f inpl utot ->
  mtree_asset_value_in T inpl utot.
intros Hf2 H1 Hcs1 H.
induction H as [|h a u inpr alpha v H2 IH H3 H4 H5|h a inpr alpha v H2 IH H3 H4 H5].
- apply mtree_asset_value_in_nil.
- apply mtree_asset_value_in_cons with (a := a).
  + apply IH.
    intros beta k H6. apply Hcs1. now right.
  + assert (L1: exists (bday:nat) (obl : obligation) (u : preasset), mtree_supports_asset (h, (bday, (obl, u))) T alpha).
    { apply Hcs1. now left. }
    destruct L1 as [bday2 [obl2 [w H6]]].
    generalize (mtree_supports_asset_In_statefun _ _ _ _ H1 H6).
    intros H7.
    destruct a as [h' [bday' [obl' u']]].
    simpl in H5. subst h'.
    destruct (Hf2 h alpha (bday',(obl',u')) alpha (bday2,(obl2,w)) H3 H7) as [_ H8].
    inversion H8. subst obl2. subst w. exact H6.
  + exact H4.
  + exact H5.
- apply mtree_asset_value_in_skip with (a := a).
  + apply IH.
    intros beta k H6. apply Hcs1. now right.
  + assert (L1: exists (bday:nat) (obl : obligation) (u : preasset), mtree_supports_asset (h, (bday, (obl, u))) T alpha).
    { apply Hcs1. now left. }
    destruct L1 as [bday2 [obl2 [w H6]]].
    generalize (mtree_supports_asset_In_statefun _ _ _ _ H1 H6).
    intros H7.
    destruct a as [h' [bday' [obl' u']]].
    simpl in H5. subst h'.
    destruct (Hf2 h alpha (bday',(obl',u')) alpha (bday2,(obl2,w)) H3 H7) as [_ H8].
    inversion H8. subst obl2. subst w. exact H6.
  + exact H4.
  + exact H5.
Qed.

Lemma sf_mtree_rights_consumed (b:bool) (alpha:termaddr) (inpl : list addr_assetid) (T:mtree 162) (f:statefun) (utot:nat) :
  (forall h alpha u alpha' u', In (h,u) (f alpha) -> In (h,u') (f alpha') -> alpha = alpha' /\ u = u') ->
  mtree_approx_fun_p T f ->
  (forall (alpha : addr) (h : hashval),
     In (alpha, h) inpl ->
     exists bday:nat, exists obl:obligation, exists u:preasset, mtree_supports_asset (h, (bday,(obl,u))) T alpha) ->
  sf_rights_consumed b alpha f inpl utot ->
  mtree_rights_consumed b alpha T inpl utot.
intros Hf2 H1 Hcs1 H.
induction H as [|beta h inpr r1 bday obl r2 H2 IH H3|beta h inpr r1 bday obl u H2 IH H3 H4].
- apply mtree_rights_consumed_nil.
- apply mtree_rights_consumed_cons with (bday := bday) (obl := obl).
  + apply IH.
    intros beta' k H6. apply Hcs1. now right.
  + assert (L1: exists (bday:nat) (obl : obligation) (u : preasset), mtree_supports_asset (h, (bday,(obl, u))) T beta).
    { apply Hcs1. now left. }
    destruct L1 as [bday2 [obl2 [w H6]]].
    generalize (mtree_supports_asset_In_statefun _ _ _ _ H1 H6).
    intros H7.
    destruct (Hf2 h _ _ _ _ H3 H7) as [_ H8].
    inversion H8. subst bday2. subst obl2. subst w. exact H6.
- apply mtree_rights_consumed_skip with (bday := bday) (obl := obl) (u := u).
  + apply IH.
    intros beta' k H6. apply Hcs1. now right.
  + assert (L1: exists (bday : nat) (obl : obligation) (u : preasset), mtree_supports_asset (h, (bday, (obl, u))) T beta).
    { apply Hcs1. now left. }
    destruct L1 as [bday2 [obl2 [w H6]]].
    generalize (mtree_supports_asset_In_statefun _ _ _ _ H1 H6).
    intros H7.
    destruct (Hf2 h _ _ _ _ H3 H7) as [_ H8].
    inversion H8. subst bday2. subst obl2. subst w. exact H6.
  + exact H4.
Qed.

Opaque mtree_full_approx_addr.

Theorem mtree_supports_tx_statefun_conv tht sigt m tx (T:mtree 162) f fee rew :
  (forall h alpha u alpha' u', In (h,u) (f alpha) -> In (h,u') (f alpha') -> alpha = alpha' /\ u = u') ->
  mtree_approx_fun_p T f ->  
  tx_valid m tx ->
  mtree_can_support_tx tx T ->
  statefun_supports_tx tht sigt m f tx fee rew ->
  mtree_supports_tx tht sigt m tx T fee rew.
intros Hf2 H1 Ht Hcs Hxf. generalize Hcs Hxf. intros [Hcs1 [Hcs2 [Hcs3 [Hcs4 [Hcs5 [Hcs6 [Hcs7 Hcs8]]]]]]] [[utot [Hxf1 Hxf2]] [[Hxf3a Hxf3b] [[Hxf4a [Hxf4b Hxf4c]] [Hxf5 [Hxf6 Hxf7]]]]].
assert (Hcs1' : forall (alpha : addr) (h : hashval),
                  In (alpha, h) (tx_inputs tx) ->
                  exists (bday:nat) (obl:obligation) (u:preasset), mtree_supports_asset (h, (bday, (obl,u))) T alpha).
{ intros beta k H2. destruct (Hcs1 beta k H2) as [[bday' [obl' u']] H3].
  exists bday'. exists obl'. exists u'. exact H3. }
split.
- exact Hcs2.
- split.
  + exists utot. split.
    * { revert Hxf1. 
        apply (sf_mtree_asset_value_in (tx_inputs tx) T f utot).
        - exact Hf2.
        - exact H1.
        - exact Hcs1'.
      }
    * exact Hxf2.
  + split.
    * { split.
        - intros alpha b H2.
          destruct (Hxf3a alpha b H2) as [H3 H4].
          split.
          + revert Hcs3 Hcs4 H2. clear.
            intros Hcs3 Hcs4 H2.
            destruct H2 as [H2|[beta [obl [n H2]]]].
            * revert H2. apply Hcs4.
            * revert H2. apply Hcs3.
          + split.
            * intros [h' [bday' [obl' [beta' H5]]]]. apply H3.
              exists h'. exists bday'. exists obl'. exists beta'.
              revert H1 H5. apply mtree_supports_asset_In_statefun.
            * { intros rtot1 rtot2 h bday obl beta u H5 H6 H7.
                assert (L1: In (h, (bday, (obl, owns b beta (Some u)))) (f (termaddr_addr alpha))).
                { revert H1 H6. apply mtree_supports_asset_In_statefun. }
                destruct (H4 rtot1 rtot2 h bday obl beta u H5 L1 H7) as [rtot3 [rtot4 [H8 [H9 H10]]]].
                exists rtot3. exists rtot4. repeat split.
                - revert H8. apply sf_mtree_rights_consumed.
                  + exact Hf2.
                  + exact H1.
                  + exact Hcs1'.
                - exact H9.
                - exact H10.
              }
        - intros alpha b beta h bday obl n H2 H3.
          assert (L3: In (h, (bday, (obl, rights b n alpha))) (f beta)).
          { revert H1 H3. apply mtree_supports_asset_In_statefun. }
          revert H2 L3. apply Hxf3b.
      }
    * { split; [split; [|split]|].
        - intros obl gamma nonce d alpha H2.
          destruct (Hxf4a obl gamma nonce d alpha H2) as [Hch [beta [h [bday' [obl' [H3 [H4 [H5 H6]]]]]]]].
          split.
          + exact Hch.
          + exists beta. exists h. exists bday'. exists obl'. repeat split.
            * exact H3.
            * exact H4.
            * exact H5.
            * destruct (Hcs1 _ _ H4) as [[bday2 [obl2 w]] H7].
              generalize (mtree_supports_asset_In_statefun _ _ _ _ H1 H7).
              intros H8.
              destruct (Hf2 h _ _ _ _ H6 H8) as [_ H9].
              inversion H9. subst bday2. subst obl2. subst w. exact H7.
        - intros obl gamma nonce th d alpha H2.
          destruct (Hxf4b obl gamma nonce th d alpha H2) as [Hch [beta [h [bday' [obl' [H3 [H4 [H5 H6]]]]]]]].
          split.
          + revert Hch. apply check_signaspec_p_markers.
            * intros k b H7 H8.
              apply (Hcs7 obl gamma nonce th d alpha (hashpair k (hashstp b)) H2).
              left. exact H7.
            * intros k H7 H8.
              apply (Hcs7 obl gamma nonce th d alpha k H2).
              right. exact H7.
          + exists beta. exists h. exists bday'. exists obl'. repeat split.
            * exact H3.
            * exact H4.
            * exact H5.
            * destruct (Hcs1 _ _ H4) as [[bday2 [obl2 w]] H7].
              generalize (mtree_supports_asset_In_statefun _ _ _ _ H1 H7).
              intros H8.
              destruct (Hf2 h _ _ _ _ H6 H8) as [_ H9].
              inversion H9. subst bday2. subst obl2. subst w. exact H7.
        - intros obl gamma nonce th d alpha H2.
          destruct (Hxf4c obl gamma nonce th d alpha H2) as [Hch [beta [h [bday' [obl' [H3 [H4 [H5 H6]]]]]]]].
          split.
          + revert Hch. apply check_doc_p_markers.
            * intros k b H7 H8.
              apply (Hcs8 obl gamma nonce th d alpha (hashpair k (hashstp b)) H2).
              left. exact H7.
            * intros k H7 H8.
              apply (Hcs8 obl gamma nonce th d alpha k H2).
              right. exact H7.
          + exists beta. exists h. exists bday'. exists obl'. repeat split.
            * exact H3.
            * exact H4.
            * exact H5.
            * destruct (Hcs1 _ _ H4) as [[bday2 [obl2 w]] H7].
              generalize (mtree_supports_asset_In_statefun _ _ _ _ H1 H7).
              intros H8.
              destruct (Hf2 h _ _ _ _ H6 H8) as [_ H9].
              inversion H9. subst bday2. subst obl2. subst w. exact H7.
        - split.
          + intros alpha b obl beta r H2.
            destruct (Hxf5 alpha b obl beta r H2) as [[h [beta' [bday' [obl' [r' [H3 H4]]]]]]|[H3 H4]]; split.
            * revert H2. apply Hcs6.
            * { left. exists h. exists beta'. exists bday'. exists obl'. exists r'. split.
                - destruct (Hcs1 _ _ H4) as [[obl2 w] H6].
                  generalize (mtree_supports_asset_In_statefun _ _ _ _ H1 H6).
                  intros H7.
                  destruct (Hf2 h _ _ _ _ H3 H7) as [_ H8].
                  inversion H8. subst obl2. subst w. exact H6.
                - exact H4.
              }
            * revert H2. apply Hcs6.
            * { right. split.
                - intros [h [beta' [bday' [obl' [r' H5]]]]]. apply H3.
                  exists h. exists beta'. exists bday'. exists obl'. exists r'.
                  revert H5. apply mtree_supports_asset_In_statefun.
                  exact H1.
                - exact H4.
              }
          + split.
            * { intros k1 k2 b H2. split.
                - revert H2. apply Hcs5.
                - intros H3. 
                  assert (L1: ~ exists (h' : hashval) (beta' : payaddr) (bday':nat) (obl' : obligation) (r' : option nat), In (h', (bday',(obl', owns b beta' r'))) (f (hashval_term_addr k1))).
                    { intros [h' [beta' [bday' [obl' [r' H4]]]]].
                      apply H3. exists h'. exists beta'. exists bday'. exists obl'. exists r'.
                      revert H4. 
                      apply mtree_supports_asset_In_statefun_conv.
                      - exact H1.
                      - revert H2. apply Hcs5.
                    }
                    exact (Hxf6 k1 k2 b H2 L1).
              }
            * { intros alpha h bday obl u H2 H3.
                assert (L1: In (h, (bday, (obl, bounty u))) (f alpha)).
                { revert H3. apply mtree_supports_asset_In_statefun. exact H1. }
                destruct (Hxf7 alpha h bday obl u H2 L1) as [h' [bday' [obl' [beta [r [H4 [H5 H6]]]]]]].
                destruct Ht as [_ [_ [Hto2 _]]].
                generalize (Hto2 alpha obl' true beta r H6). intros H7.
                destruct alpha as [[|] [[|] alpha]]; try contradiction H7.
                split.
                - revert H6. apply Hcs6.
                - exists h'. exists bday'. exists obl'. exists beta. exists r. repeat split.
                  + exact H4.
                  + revert H5. apply mtree_supports_asset_In_statefun_conv.
                    * exact H1.
                    * revert H6. apply Hcs6.
                  + exact H6.
              }
      }
Qed.

Lemma remove_assets_hlist_nil (hl:hlist) :
  remove_assets_hlist hl nil = hl.
induction hl as [h| |[h u] hr IH].
- simpl. reflexivity.
- simpl. reflexivity.
- simpl. rewrite IH. reflexivity.
Qed.

Lemma remove_assets_hlist_nIn_cons (l:hlist) (h:hashval) (rem:list hashval) :
  (~exists u, In_hlist (h,u) l) ->
  remove_assets_hlist l (h::rem) = remove_assets_hlist l rem.
induction l as [k| |[k v] l IH]; intros H1.
- reflexivity.
- reflexivity.
- simpl. destruct (hashval_eq_dec h k) as [D1|D1].
  + exfalso. apply H1. exists v. subst k. apply In_hlist_H.
  + destruct (in_dec hashval_eq_dec k rem) as [D2|D2].
    * apply IH. intros [u H2]. apply H1. exists u. now apply In_hlist_C.
    * f_equal. apply IH. intros [u H2]. apply H1. exists u. now apply In_hlist_C.
Qed.

Lemma remove_assets_hlist_app2 (l:hlist) (rem1 rem2:list hashval) :
  remove_assets_hlist l (rem1 ++ rem2) = remove_assets_hlist (remove_assets_hlist l rem1) rem2.
induction l as [k| |[k v] l IH].
- reflexivity.
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

Lemma hashassetlist_app al1 al2 hl2 :
  hashassetlist al2 = hlist_hashroot hl2 ->
  hashassetlist (al1 ++ al2) = hlist_hashroot (hlist_new_assets al1 hl2).
induction al1 as [|a ar1 IH].
- simpl. tauto.
- simpl. intros H1. unfold hashassetlist. simpl.
  change (match hashassetlist (ar1 ++ al2) with
            | Some k => Some (hashpair (hashnat 4) (hashpair (hashasset a) k))
            | None => Some (hashpair (hashnat 3) (hashasset a))
          end =
          match hlist_hashroot (hlist_new_assets ar1 hl2) with
            | Some k => Some (hashpair (hashnat 4) (hashpair (hashasset a) k))
            | None => Some (hashpair (hashnat 3) (hashasset a))
          end).
  rewrite IH.
  + reflexivity.
  + exact H1.
Qed.

(*** only includes those explicitly listed in the hlist ***)
Fixpoint hlist_to_assetlist (hl:hlist) : list asset :=
match hl with
  | hlistC a hr => a::hlist_to_assetlist hr
  | _ => nil
end.

Lemma In_hlist_In_hlist_to_assetlist a hl :
  In_hlist a hl -> In a (hlist_to_assetlist hl).
intros H. induction H as [hl|b hl H IH].
- now left.
- now right.
Qed.

Lemma remove_assets_hlist_noint_eq (hl:hlist) (rem:list hashval) :
  (forall k, In k rem -> ~exists u, In_hlist (k,u) hl) ->
  remove_assets_hlist hl rem = hl.
induction hl as [h| |[h u] hr IH].
- intros _. reflexivity.
- intros _. reflexivity.
- intros H1. simpl. destruct (in_dec hashval_eq_dec h rem) as [D1|D1].
  + exfalso. apply (H1 h D1). exists u. now left.
  + f_equal. apply IH. intros k H2 [v H3]. apply (H1 k H2). exists v. now right.
Qed.

Lemma remove_assets_hashassetlist_hlist_hashroot_eq (al:list asset) (hl:hlist) (rem:list hashval) :
  fnl al ->
  (forall k, In k rem -> In_dom k al -> exists u, In_hlist (k,u) hl) ->
  hashassetlist al = hlist_hashroot hl ->
  hashassetlist (remove_assets al rem) = hlist_hashroot (remove_assets_hlist hl rem).
revert al. induction hl as [h| |[h [bday [obl u]]] hr IH]; intros al H0 H1 H2.
- assert (L1: forall k, In k rem -> ~In_dom k al).
  { intros k H3 H4. destruct (H1 k H3 H4) as [u H5]. inversion H5. }
  rewrite (remove_assets_noint_eq al rem L1).
  rewrite remove_assets_hlist_noint_eq.
  + exact H2.
  + intros k H3 [v H4]. inversion H4.
- assert (L1: forall k, In k rem -> ~In_dom k al).
  { intros k H3 H4. destruct (H1 k H3 H4) as [u H5]. inversion H5. }
  rewrite (remove_assets_noint_eq al rem L1).
  rewrite remove_assets_hlist_noint_eq.
  + exact H2.
  + intros k H3 [v H4]. inversion H4.
- destruct al as [|[h' [bday' [obl' u']]] ar].
  + simpl in H2. destruct (hlist_hashroot hr); discriminate H2.
  + assert (L1: h' = h /\ bday' = bday /\ obl' = obl /\ u' = u /\ hashassetlist ar = hlist_hashroot hr).
    { change (match hashassetlist ar with
                | Some k =>
                  Some
                    (hashpair (hashnat 4)
                              (hashpair (hashpair h' (hashpair (hashnat bday') (hashpair (hashobligation obl') (hashpreasset u')))) k))
                | None => Some (hashpair (hashnat 3) (hashpair h' (hashpair (hashnat bday') (hashpair (hashobligation obl') (hashpreasset u')))))
              end =
              match hlist_hashroot hr with
                | Some k =>
                  Some
                    (hashpair (hashnat 4) (hashpair (hashpair h (hashpair (hashnat bday) (hashpair (hashobligation obl) (hashpreasset u)))) k))
                | None => Some (hashpair (hashnat 3) (hashpair h (hashpair (hashnat bday) (hashpair (hashobligation obl) (hashpreasset u)))))
              end) in H2.
      destruct (hlist_hashroot hr) as [k|].
      - destruct (hashassetlist ar) as [k'|].
        + injection H2. intros H3.
          apply hashpairinj in H3. destruct H3 as [_ H3].
          apply hashpairinj in H3. destruct H3 as [H3 H4].
          apply hashpairinj in H3. destruct H3 as [H5 H6].
          apply hashpairinj in H6. destruct H6 as [H7 H8].
          apply hashpairinj in H8. destruct H8 as [H9 H10].
          apply hashnatinj in H7.
          apply hashobligationinj in H9.
          apply hashpreassetinj in H10.
          repeat split; congruence.
        + exfalso. injection H2. intros H3.
          apply hashpairinj in H3. destruct H3 as [H3 _].
          apply hashnatinj in H3. omega.
      - destruct (hashassetlist ar) as [k'|].
        + exfalso. injection H2. intros H3.
          apply hashpairinj in H3. destruct H3 as [H3 _].
          apply hashnatinj in H3. omega.
        + injection H2. intros H3.
          apply hashpairinj in H3. destruct H3 as [_ H3].
          apply hashpairinj in H3. destruct H3 as [H3 H4].
          apply hashpairinj in H4. destruct H4 as [H5 H6].
          apply hashpairinj in H6. destruct H6 as [H7 H8].
          apply hashnatinj in H5.
          apply hashobligationinj in H7.
          apply hashpreassetinj in H8.
          tauto.
    }
    destruct L1 as [L1a [L1b [L1c [L1d L1e]]]]. subst h'. subst obl'. subst u'.
    assert (L2: hashassetlist (remove_assets ar rem) =
                hlist_hashroot (remove_assets_hlist hr rem)).
    { apply IH.
      - inversion H0. assumption.
      - intros k H3 H4.
        assert (L2a: In_dom k ((h,(bday,(obl,u)))::ar)) by now right.
        destruct (H1 k H3 L2a) as [v H5].
        inversion H5.
        + inversion H0. exfalso. apply H10. congruence.
        + exists v. assumption.
      - exact L1e.
    }
    simpl. destruct (in_dec hashval_eq_dec h rem) as [D1|D1].
    * exact L2.
    * change (match hashassetlist (remove_assets ar rem) with
                | Some k =>
                  Some (hashpair (hashnat 4) (hashpair (hashpair h (hashpair (hashnat bday') (hashpair (hashobligation obl) (hashpreasset u)))) k))
                | None => Some (hashpair (hashnat 3) (hashpair h (hashpair (hashnat bday') (hashpair (hashobligation obl) (hashpreasset u)))))
              end =
              match hlist_hashroot (remove_assets_hlist hr rem) with
                | Some k =>
                  Some (hashpair (hashnat 4) (hashpair (hashpair h (hashpair (hashnat bday) (hashpair (hashobligation obl) (hashpreasset u)))) k))
                | None => Some (hashpair (hashnat 3) (hashpair h (hashpair (hashnat bday) (hashpair (hashobligation obl) (hashpreasset u)))))
              end).
      rewrite L2. rewrite L1b. reflexivity.
Qed.

Lemma inpl_reln_remove_assets_eq1 (fullinpl : list addr_assetid) (inpl : list (unit * hashval)) (alphapre : unit -> addr) :
  (forall gamma delta, alphapre gamma = alphapre delta -> gamma = delta) ->
  @inpl_reln 0 alphapre fullinpl inpl ->
  forall hl al,
    fnl al ->
    (forall gamma a, In (gamma,assetid a) inpl -> In a al -> In_hlist a hl) ->
    hashassetlist al = hlist_hashroot hl ->
    hashassetlist (remove_assets al (get_spent (alphapre tt) fullinpl)) =
    hlist_hashroot (remove_assets_hlist hl (map (snd (B:=hashval)) inpl)).
intros H0 H1. induction H1 as [|fullinpl inpl alpha k H1 H2 IH|fullinpl inpl [] k H1 IH].
- intros hl al _ _ H1. rewrite remove_assets_nil. rewrite remove_assets_hlist_nil. exact H1.
- intros hl al H3 H4 H5. simpl. destruct (addr_eq_dec (alphapre tt) alpha) as [H6|H6].
  + exfalso. apply (H1 tt). exact H6.
  + apply IH.
    * assumption.
    * assumption.
    * assumption.
- intros hl al H3 H4 H5. simpl.  destruct (addr_eq_dec (alphapre tt) (alphapre tt)) as [H6|H6].
  + (*** This is the main case. ***)
    change (hashassetlist (remove_assets al ((k :: nil) ++ get_spent (alphapre tt) fullinpl)) =
            hlist_hashroot (remove_assets_hlist hl ((k :: nil) ++ map (snd (B:=hashval)) inpl))).
    rewrite remove_assets_app2. rewrite remove_assets_hlist_app2.
    apply IH.
    * apply fnl_remove_assets. assumption.
    * { intros [] [k' v'] H7 H8.
        apply remove_assets_iff in H8.
        destruct H8 as [H9 H10].
        apply remove_assets_hlist_iff. split.
        - apply (H4 tt (k',v')).
          + now right.
          + assumption.
        - assumption.
      }
    * { apply remove_assets_hashassetlist_hlist_hashroot_eq.
        - assumption.
        - intros k' [H7|[]] H8.
          subst k'. apply In_In_dom_lem in H8.
          destruct H8 as [v H9]. exists v.
          apply (H4 tt (k,v)).
          + now left.
          + assumption.
        - assumption.
      }
  + exfalso. apply H6. reflexivity.
Qed.

Lemma outpl_reln_new_assets_eq1 m (fulloutpl:list addr_preasset) (txh:hashval) :
  forall j, forall (outpl:list (bitseq 0 * asset)%type),
  forall (alphapre:bitseq 0 -> addr),
    outpl_reln m txh alphapre j fulloutpl outpl ->
    new_assets m (alphapre tt) fulloutpl txh j = map (snd (B:=asset)) outpl.
intros j outpl alphapre H.
induction H as [j|j fulloutpl outpl alpha [obl u] H1 H2 IH|j fulloutpl outpl [] [obl u] H1 IH].
- simpl. reflexivity.
- simpl. destruct (addr_eq_dec (alphapre tt) alpha) as [H3|H3].
  + exfalso. apply (H1 tt). exact H3.
  + exact IH.
- simpl. destruct (addr_eq_dec (alphapre tt) (alphapre tt)) as [H3|H3].
  + rewrite IH. reflexivity.
  + exfalso. apply H3. reflexivity.
Qed.

Lemma mtree_approx_fun_p_ext {n} :
  forall T:mtree n, forall f g:bitseq n -> list asset,
    (forall alpha, f alpha = g alpha) ->
    mtree_approx_fun_p T f -> mtree_approx_fun_p T g.
induction n as [|n IH].
- intros hl f g H1. simpl. rewrite (H1 tt). tauto.
- intros [h|[Tl Tr]] f g H1.
  + intros [Tl [Tr [H2 [H3 H4]]]]. exists Tl. exists Tr. repeat split.
    * assumption.
    * revert H3. apply IH. intros alpha. apply H1.
    * revert H4. apply IH. intros alpha. apply H1.
  + intros [H2 H3]. split.
    * revert H2. apply IH. intros alpha. apply H1.
    * revert H3. apply IH. intros alpha. apply H1.
Qed.

Lemma inpl_reln_strip_bitseq_false {n:nat} 
      (alphapre:bitseq (S n) -> addr) (fullinpl:list addr_assetid) (inpl:list (bitseq (S n) * hashval)%type) :
  (forall gamma delta, alphapre gamma = alphapre delta -> gamma = delta) ->
  inpl_reln alphapre fullinpl inpl ->
  inpl_reln (fun gamma => alphapre (false,gamma)) fullinpl (strip_bitseq_false inpl).
intros Hapi H. induction H as [|fullinpl inpl alpha h H1 H2 IH|fullinpl inpl [[|] gamma] h H1 IH].
- simpl. apply inpl_reln_nil.
- simpl. apply inpl_reln_skip.
  + intros gamma. apply H1.
  + exact IH.
- simpl. apply inpl_reln_skip.
  + intros gamma' H2. apply Hapi in H2. inversion H2.
  + exact IH.
- simpl.
  apply (inpl_reln_cons (fun gamma => alphapre (false,gamma)) fullinpl (strip_bitseq_false inpl) gamma h).
  exact IH.
Qed.


Lemma empty_approx_empty_fun {n:nat} :
  forall f:bitseq n -> list asset,
    (forall gamma, f gamma = nil) ->
    mtree_approx_fun_p (empty_mtree n) f.
induction n as [|n IH].
- intros f; simpl. intros H1. rewrite (H1 tt). reflexivity.
- intros f H1. simpl. exists (empty_mtree n). exists (empty_mtree n). repeat split.
  + rewrite mtree_hashroot_empty. reflexivity.
  + apply IH. intros gamma. apply H1.
  + apply IH. intros gamma. apply H1.
Qed.

Lemma mtree_hashroot_None_approx_empty_fun {n:nat} :
              forall T:mtree n, forall f:bitseq n -> list asset,
                mtree_hashroot T = None ->
                (forall gamma, f gamma = nil) ->
                mtree_approx_fun_p T f.
induction n as [|n IH].
- intros [h| |h hl] f; simpl.
  + simpl; discriminate.
  + intros _ H1. rewrite (H1 tt). reflexivity.
  + simpl; destruct (hlist_hashroot hl); discriminate.
- intros [[h|]|[Tl Tr]] f.
  + simpl. discriminate.
  + intros _ H1. exists (empty_mtree n). exists (empty_mtree n). repeat split.
    * rewrite mtree_hashroot_empty. reflexivity.
    * now apply empty_approx_empty_fun.
    * now apply empty_approx_empty_fun.
  + simpl. intros H1 H2. split.
    * { apply IH.
        - destruct (mtree_hashroot Tl) as [h|].
          + destruct (mtree_hashroot Tr); discriminate.
          + reflexivity.
        - intros gamma. apply H2.
      }
    * { apply IH.
        - destruct (mtree_hashroot Tr) as [h|].
          + destruct (mtree_hashroot Tl); discriminate.
          + reflexivity.
        - intros gamma. apply H2.
      }
Qed.

Lemma mtree_hashroot_None_approx_empty_fun_conv {n:nat} :
              forall T:mtree n, forall f:bitseq n -> list asset,
                mtree_hashroot T = None ->
                mtree_approx_fun_p T f ->
                (forall gamma, f gamma = nil).
induction n as [|n IH].
- intros [h| |h hl] f; simpl.
  + discriminate.
  + intros _ H1 []. simpl in H1. destruct (f tt) as [|a al].
    * reflexivity.
    * unfold hashassetlist in H1. simpl in H1.
      destruct (ohashlist (map hashasset al)); discriminate H1.
  + destruct (hlist_hashroot hl); discriminate.
- intros [[h|]|[Tl Tr]]; simpl.
  + discriminate.
  + intros f _ [Tl [Tr [H1 [H2 H3]]]] [[|] gamma].
    * { apply (IH Tr (fun gamma => f(true,gamma))).
        - symmetry in H1. revert H1. apply hashopair_None_2.
        - exact H3.
      }
    * { apply (IH Tl (fun gamma => f(false,gamma))).
        - symmetry in H1. revert H1. apply hashopair_None_1.
        - exact H2.
      }
  + intros f H1 [H2 H3] [[|] gamma].
    * { apply (IH Tr (fun gamma => f(true,gamma))).
        - revert H1. apply hashopair_None_2.
        - exact H3.
      }
    * { apply (IH Tl (fun gamma => f(false,gamma))).
        - revert H1. apply hashopair_None_1.
        - exact H2.
      }
Qed.

Lemma hashassetlist_hlist_hashroot_In_hlist_In al hl a :      
  hashassetlist al = hlist_hashroot hl ->
  In_hlist a hl ->
  In a al.
revert al. induction hl as [h| |b hr IH].
- intros al H1 H2. inversion H2.
- intros al H1 H2. inversion H2.
- intros [|c ar] H1 H2.
  + simpl in H1. destruct (hlist_hashroot hr); discriminate H1.
  + inversion H2.
    * { subst b. left.
        change (match hashassetlist ar with
                  | Some k => Some (hashpair (hashnat 4) (hashpair (hashasset c) k))
                  | None => Some (hashpair (hashnat 3) (hashasset c))
                end =
                match hlist_hashroot hr with
                  | Some k => Some (hashpair (hashnat 4) (hashpair (hashasset a) k))
                  | None => Some (hashpair (hashnat 3) (hashasset a))
                end) in H1.
        destruct (hashassetlist ar) as [arh|]; destruct (hlist_hashroot hr) as [hrh|].
        - inversion H1.
          apply hashpairinj in H0. destruct H0 as [_ H4].
          apply hashpairinj in H4. destruct H4 as [H4 _].
          apply hashassetinj in H4. exact H4.
        - inversion H1.
          apply hashpairinj in H0. destruct H0 as [H4 _].
          apply hashnatinj in H4. omega.
        - inversion H1.
          apply hashpairinj in H0. destruct H0 as [H4 _].
          apply hashnatinj in H4. omega.
        - inversion H1.
          apply hashpairinj in H0. destruct H0 as [_ H4].
          apply hashassetinj in H4. exact H4.
      }
    * { right. apply IH.
        - change (match hashassetlist ar with
                  | Some k => Some (hashpair (hashnat 4) (hashpair (hashasset c) k))
                  | None => Some (hashpair (hashnat 3) (hashasset c))
                end =
                match hlist_hashroot hr with
                  | Some k => Some (hashpair (hashnat 4) (hashpair (hashasset b) k))
                  | None => Some (hashpair (hashnat 3) (hashasset b))
                end) in H1.
          destruct (hashassetlist ar) as [arh|]; destruct (hlist_hashroot hr) as [hrh|].
          + inversion H1.
            apply hashpairinj in H5. destruct H5 as [_ H5].
            apply hashpairinj in H5. destruct H5 as [_ H5].
            congruence.
          + inversion H1.
            apply hashpairinj in H5. destruct H5 as [H5 _].
            apply hashnatinj in H5. omega.
          + inversion H1.
            apply hashpairinj in H5. destruct H5 as [H5 _].
            apply hashnatinj in H5. omega.
          + reflexivity.
        - exact H0.
      }
Qed.

Lemma approx_trans_lem {n:nat} m (fullinpl:list addr_assetid) (fulloutpl:list addr_preasset) (txh:hashval) :
  forall (inpl:list (bitseq n * hashval)%type) (outpl:list (bitseq n * asset)%type),
  forall (alphapre:bitseq n -> addr),
    (forall gamma delta, alphapre gamma = alphapre delta -> gamma = delta)
    ->
  forall (T:mtree n) (f:bitseq n -> list asset),
    inpl_reln alphapre fullinpl inpl
    ->
    outpl_reln m txh alphapre 0 fulloutpl outpl
    ->
    (forall gamma, fnl (f gamma))
    ->
    ((forall alpha h, In (alpha,h) inpl -> exists u, mtree_supports_asset (h,u) T alpha)
     /\
     (forall alpha u, In (alpha,u) outpl -> mtree_supports_addr T alpha)) ->
    mtree_approx_fun_p T f ->
    mtree_approx_fun_p (tx_mtree_trans_ inpl outpl T)
                       (fun alpha:bitseq n =>
                          (new_assets m (alphapre alpha) fulloutpl txh 0)
                            ++
                            (remove_assets (f alpha)
                                           (get_spent (alphapre alpha) fullinpl))).
induction n as [|n IH].
- simpl. intros inpl outpl alphapre Hapi hl f H1 H3 H4 [H5 H6] H7.
  destruct inpl as [|[[] h] inpl]; simpl.
  + assert (L1: (get_spent (alphapre tt) fullinpl) = nil).
    { destruct (get_spent (alphapre tt) fullinpl) as [|k kl] eqn:Hgs1.
      - reflexivity.
      - exfalso.
        assert (L1a: In k (get_spent (alphapre tt) fullinpl)).
        { rewrite Hgs1. now left. }
        apply get_spent_iff in L1a.
        apply (@inpl_reln_In_iff 0 alphapre fullinpl nil Hapi H1) in L1a.
        contradiction L1a.
    }
    rewrite L1. rewrite remove_assets_nil.
    destruct outpl as [|[[] [k v]] outpr].
    * rewrite (outpl_reln_new_assets_eq1 m fulloutpl txh 0 nil alphapre H3).
      simpl. exact H7.
    * rewrite (hashassetlist_app (new_assets m (alphapre tt) fulloutpl txh 0) (f tt) hl H7).
      rewrite (outpl_reln_new_assets_eq1 m fulloutpl txh 0 _ alphapre H3).
      rewrite remove_assets_hlist_nil.
      reflexivity.
  + rewrite (outpl_reln_new_assets_eq1 m fulloutpl txh 0 _ alphapre H3).
    apply hashassetlist_app.
    rewrite (inpl_reln_remove_assets_eq1 fullinpl ((tt,h)::inpl) alphapre Hapi H1 hl (f tt) (H4 tt)).
    * reflexivity.
    * intros [] [k u] H8 H9.
      destruct (H5 tt k H8) as [v H10].
      change (In_hlist (k,v) hl) in H10.
      generalize (hashassetlist_hlist_hashroot_In_hlist_In _ _ _ H7 H10).
      intros H11.
      generalize (fnl_lem (f tt) (H4 tt) k u v H9 H11).
      intros H12. subst v. exact H10.
    * exact H7.
- intros inpl outpl alphapre Hapi [[h|]|[Tl Tr]] f H1 H2 H3 [H4a H4b] H5.
  + destruct H5 as [Tl [Tr [H6 [H7 H8]]]].
    assert (L1: inpl = nil).
    { destruct inpl as [|[alpha k] inpl].
      - reflexivity.
      - assert (L1a: exists u, mtree_supports_asset (k, u) (mtreeH n (Some h)) alpha).
        { apply (H4a alpha k). now left. }
        destruct L1a as [u L1a].
        inversion L1a.
    }
    assert (L2: outpl = nil).
    { destruct outpl as [|[alpha [k u]] outpl].
      - reflexivity.
      - assert (L2a: mtree_supports_addr (mtreeH n (Some h)) alpha).
        { apply (H4b alpha (k,u)). now left. }
        inversion L2a.
    }
    subst inpl. subst outpl.
    exists Tl. exists Tr. repeat split.
    * exact H6.
    * { revert H7. apply mtree_approx_fun_p_ext.
        intros gamma.
        rewrite (inpl_reln_nil_no_spent_lem fullinpl alphapre H1).
        rewrite remove_assets_nil.
        rewrite (outpl_reln_nil_no_new_assets_lem m fulloutpl txh alphapre 0 H2).
        reflexivity.
      }
    * { revert H8. apply mtree_approx_fun_p_ext.
        intros gamma.
        rewrite (inpl_reln_nil_no_spent_lem fullinpl alphapre H1).
        rewrite remove_assets_nil.
        rewrite (outpl_reln_nil_no_new_assets_lem m fulloutpl txh alphapre 0 H2).
        reflexivity.
      }
  + destruct H5 as [Tl [Tr [H6 [H7 H8]]]].
    assert (L1: inpl = nil).
    { destruct inpl as [|[alpha k] inpl].
      - reflexivity.
      - assert (L1a: exists u, mtree_supports_asset (k, u) (mtreeH n None) alpha).
        { apply (H4a alpha k). now left. }
        destruct L1a as [u L1a].
        inversion L1a.
    }
    subst inpl. destruct outpl as [|[alpha [k v]] outpl].
    * { simpl. exists Tl. exists Tr. repeat split.
        - assumption.
        - revert H7. apply mtree_approx_fun_p_ext.
          intros gamma.
          rewrite (inpl_reln_nil_no_spent_lem fullinpl alphapre H1).
          rewrite remove_assets_nil.
          rewrite (outpl_reln_nil_no_new_assets_lem m fulloutpl txh alphapre 0 H2).
          reflexivity.
        - revert H8. apply mtree_approx_fun_p_ext.
          intros gamma.
          rewrite (inpl_reln_nil_no_spent_lem fullinpl alphapre H1).
          rewrite remove_assets_nil.
          rewrite (outpl_reln_nil_no_new_assets_lem m fulloutpl txh alphapre 0 H2).
          reflexivity.
      }
    * { split.
        - apply IH.
          + intros gamma delta H9. apply Hapi in H9. injection H9. tauto.
          + exact (inpl_reln_strip_bitseq_false alphapre fullinpl nil Hapi H1).
          + exact (outpl_reln_strip_bitseq_false m txh alphapre fulloutpl ((alpha, (k, v)) :: outpl) Hapi 0 H2).
          + intros gamma. apply H3.
          + split.
            * intros gamma a [].
            * intros gamma a H9. apply empty_supports_addr_lem.
              apply mtree_hashroot_empty.
          + apply empty_approx_empty_fun.
            apply mtree_hashroot_None_approx_empty_fun_conv with (T := Tl).
            * symmetry in H6. revert H6. apply hashopair_None_1.
            * exact H7.
        - apply IH.
          + intros gamma delta H9. apply Hapi in H9. injection H9. tauto.
          + exact (inpl_reln_strip_bitseq_true alphapre fullinpl nil Hapi H1).
          + exact (outpl_reln_strip_bitseq_true m txh alphapre fulloutpl ((alpha, (k, v)) :: outpl) Hapi 0 H2).
          + intros gamma. apply H3.
          + split.
            * intros gamma a [].
            * intros gamma a H9. apply empty_supports_addr_lem.
              apply mtree_hashroot_empty.
          + apply empty_approx_empty_fun.
            apply mtree_hashroot_None_approx_empty_fun_conv with (T := Tr).
            * symmetry in H6. revert H6. apply hashopair_None_2.
            * exact H8.
      }
  + destruct H5 as [H5a H5b]. destruct inpl as [|[alpha k] inpl].
    * { destruct outpl as [|[alpha [k v]] outpl].
        - simpl. split.
          + revert H5a. apply mtree_approx_fun_p_ext.
            intros gamma.
            rewrite (inpl_reln_nil_no_spent_lem fullinpl alphapre H1).
            rewrite remove_assets_nil.
            rewrite (outpl_reln_nil_no_new_assets_lem m fulloutpl txh alphapre 0 H2).
            reflexivity.
          + revert H5b. apply mtree_approx_fun_p_ext.
            intros gamma.
            rewrite (inpl_reln_nil_no_spent_lem fullinpl alphapre H1).
            rewrite remove_assets_nil.
            rewrite (outpl_reln_nil_no_new_assets_lem m fulloutpl txh alphapre 0 H2).
            reflexivity.
        - simpl. split.
          + change (mtree_approx_fun_p
                      (tx_mtree_trans_ nil (strip_bitseq_false ((alpha,(k,v))::outpl)) Tl)
                      (fun alpha0 : bitseq n =>
                         new_assets m (alphapre (false, alpha0)) fulloutpl txh 0 ++
                                    remove_assets (f (false, alpha0))
                                    (get_spent (alphapre (false, alpha0)) fullinpl))).
            apply IH.
            * intros gamma delta H6. apply Hapi in H6. injection H6. tauto.
            * exact (inpl_reln_strip_bitseq_false alphapre fullinpl nil Hapi H1).
            * exact (outpl_reln_strip_bitseq_false m txh alphapre fulloutpl ((alpha, (k, v)) :: outpl) Hapi 0 H2).
            * intros gamma. apply H3.
            * { split.
                - intros beta a [].
                - intros beta a H6.
                  assert (L1: In ((false,beta), a) ((alpha, (k, v)) :: outpl)).
                  { apply strip_bitseq_false_iff. exact H6. }
                  exact (H4b (false,beta) a L1).
              }
            * assumption.
          + change (mtree_approx_fun_p
                      (tx_mtree_trans_ nil (strip_bitseq_true ((alpha,(k,v))::outpl)) Tr)
                      (fun alpha0 : bitseq n =>
                         new_assets m (alphapre (true, alpha0)) fulloutpl txh 0 ++
                                    remove_assets (f (true, alpha0))
                                    (get_spent (alphapre (true, alpha0)) fullinpl))).
            apply IH.
            * intros gamma delta H6. apply Hapi in H6. injection H6. tauto.
            * exact (inpl_reln_strip_bitseq_true alphapre fullinpl nil Hapi H1).
            * exact (outpl_reln_strip_bitseq_true m txh alphapre fulloutpl ((alpha, (k, v)) :: outpl) Hapi 0 H2).
            * intros gamma. apply H3.
            * { split.
                - intros beta a [].
                - intros beta a H6.
                  assert (L1: In ((true,beta), a) ((alpha, (k, v)) :: outpl)).
                  { apply strip_bitseq_true_iff. exact H6. }
                  exact (H4b (true,beta) a L1).
              }
            * assumption.
      }
    * { simpl. split.
        - change (mtree_approx_fun_p
                      (tx_mtree_trans_ (strip_bitseq_false ((alpha, k) :: inpl)) (strip_bitseq_false outpl) Tl)
                      (fun alpha0 : bitseq n =>
                         new_assets m (alphapre (false, alpha0)) fulloutpl txh 0 ++
                                    remove_assets (f (false, alpha0))
                                    (get_spent (alphapre (false, alpha0)) fullinpl))).
          apply IH.
          + intros gamma delta H6. apply Hapi in H6. injection H6. tauto.
          + exact (inpl_reln_strip_bitseq_false alphapre fullinpl ((alpha,k)::inpl) Hapi H1).
          + exact (outpl_reln_strip_bitseq_false m txh alphapre fulloutpl outpl Hapi 0 H2).
          + intros gamma. apply H3.
          + split.
            * intros beta a H6.
              apply strip_bitseq_false_iff in H6.
              exact (H4a (false,beta) a H6).
            * intros beta a H6.
              apply strip_bitseq_false_iff in H6.
              exact (H4b (false,beta) a H6).
          + assumption.
        - change (mtree_approx_fun_p
                      (tx_mtree_trans_ (strip_bitseq_true ((alpha, k) :: inpl)) (strip_bitseq_true outpl) Tr)
                      (fun alpha0 : bitseq n =>
                         new_assets m (alphapre (true, alpha0)) fulloutpl txh 0 ++
                                    remove_assets (f (true, alpha0))
                                    (get_spent (alphapre (true, alpha0)) fullinpl))).
          apply IH.
          + intros gamma delta H6. apply Hapi in H6. injection H6. tauto.
          + exact (inpl_reln_strip_bitseq_true alphapre fullinpl ((alpha,k)::inpl) Hapi H1).
          + exact (outpl_reln_strip_bitseq_true m txh alphapre fulloutpl outpl Hapi 0 H2).
          + intros gamma. apply H3.
          + split.
            * intros beta a H6.
              apply strip_bitseq_true_iff in H6.
              exact (H4a (true,beta) a H6).
            * intros beta a H6.
              apply strip_bitseq_true_iff in H6.
              exact (H4b (true,beta) a H6).
          + assumption.
      }
Qed.

Opaque mtree_approx_fun_p.

Opaque mtree_supports_addr.

Theorem mtree_approx_trans tht sigt m (tx:Tx) T f fee rew :
  sf_valid f ->
  mtree_supports_tx tht sigt m tx T fee rew ->
  mtree_approx_fun_p T f ->
  mtree_approx_fun_p (tx_mtree_trans m tx T) (tx_statefun_trans m tx f).
intros Hf H1 H2. destruct tx as [fullinpl fulloutpl].
set (txh := hashtx(fullinpl,fulloutpl)).
assert (L1:forall (gamma : addr) (h : hashval) (bday:nat) (obl:obligation) (u : preasset),
   In (gamma, (h, (bday, (obl, u)))) (add_vout m txh fulloutpl 0) ->
   bday = m /\
   exists i : nat,
     nth_error fulloutpl i = value (gamma, (obl,u)) /\
     h = hashpair txh (hashnat i)).
{ intros gamma h bday obl u H3. apply add_vout_lem in H3. exact H3. }
assert (L2: forall gamma delta:addr, gamma = delta -> gamma = delta) by tauto.
apply (@approx_trans_lem 162 m fullinpl fulloutpl txh fullinpl (add_vout m txh fulloutpl 0) (fun alpha => alpha) L2 T f).
- apply inpl_reln_start.
- apply outpl_reln_start.
- now apply sf_valid_fnl.
- generalize (mtree_supports_tx_can_support _ _ _ _ _ _ _ H1).
  intros [H3 H4].
  apply mtree_supports_tx_can_support in H1.
  destruct H1 as [H1a [H1b _]]. split.
  + exact H1a.
  + intros alpha [h [bday [obl u]]] H5. apply L1 in H5. destruct H5 as [Hb [i [H6 H7]]].
    apply (H1b alpha (obl,u)). apply (nth_error_In _ i).
    exact H6.
- exact H2.
Qed.

Theorem mtree_normal_approx_trans tht sigt m (tx:Tx) T f fee rew :
  sf_valid f ->
  mtree_supports_tx tht sigt m tx T fee rew ->
  mtree_approx_fun_p T f ->
  mtree_approx_fun_p (normalize_mtree (tx_mtree_trans m tx T)) (tx_statefun_trans m tx f).
intros H1 H2 H3.
generalize (mtree_approx_trans tht sigt m tx T f fee rew H1 H2 H3).
apply normalize_mtree_approx_fun_p.
Qed.

Lemma approx_assetlist_lem hl al :
  hlist_hashroot hl = hashassetlist al <-> approx_assetlist hl al.
split.
- revert al. induction hl as [h| |b hr IH].
  + intros al H1. apply approx_assetlist_H. exact H1.
  + intros [|a ar].
    * intros _. apply approx_assetlist_N.
    * intros H1. unfold hashassetlist in H1. simpl in H1.
      destruct (ohashlist (map hashasset ar)); discriminate H1.
  + intros [|a ar].
    * intros H1. simpl in H1. destruct (hlist_hashroot hr); discriminate H1.
    * { intros H1. simpl in H1. unfold hashassetlist in H1. simpl in H1.
        destruct (hlist_hashroot hr) as [h|] eqn:E1; destruct (ohashlist (map hashasset ar)) as [k|] eqn:E2.
        - inversion H1.
          apply hashpairinj in H0. destruct H0 as [_ H0].
          apply hashpairinj in H0. destruct H0 as [H0 H2].
          apply hashassetinj in H0. subst b.
          apply approx_assetlist_C. apply IH.
          change (hashassetlist ar = Some k) in E2.
          congruence.
        - inversion H1.
          apply hashpairinj in H0. destruct H0 as [H0 _].
          apply hashnatinj in H0. omega.
        - inversion H1.
          apply hashpairinj in H0. destruct H0 as [H0 _].
          apply hashnatinj in H0. omega.
        - inversion H1.
          apply hashpairinj in H0. destruct H0 as [_ H0].
          apply hashassetinj in H0. subst b.
          apply approx_assetlist_C.
          destruct hr as [h| |b hr'].
          + discriminate E1.
          + destruct ar as [|c ar'].
            * apply approx_assetlist_N.
            * simpl in E2. destruct (ohashlist (map hashasset ar')); discriminate E2.
          + simpl in E1. destruct (hlist_hashroot hr'); discriminate E1.
     }
- intros H. induction H as [h al H1| |a hl al H1 IH].
  + exact H1.
  + reflexivity.
  + simpl. rewrite IH. reflexivity.
Qed.

Fixpoint mtree_totalassets {n:nat} : mtree n -> list asset -> Prop :=
match n with
| O => fun (hl:mtree 0) al => approx_assetlist hl al
| S n =>
  fun (T:mtree (S n)) al =>
    match T with
      | inl h =>
        exists Tl Tr:mtree n,
          exists all alr,
            hashopair (mtree_hashroot Tl) (mtree_hashroot Tr) = h /\
            mtree_totalassets Tl all /\
            mtree_totalassets Tr alr /\
            al = all ++ alr
      | inr (Tl,Tr) =>
        exists all alr,
          mtree_totalassets Tl all /\
          mtree_totalassets Tr alr /\
          al = all ++ alr
    end
end.
                                
Transparent mtree_approx_fun_p.

Lemma mtree_approx_fun_p_totalassets {n} (T:mtree n) (f:bitseq n -> list asset) (al:list asset) :
  mtree_approx_fun_p T f ->
  (mtree_totalassets T al <-> totalassets_ f = al).
revert al. induction n as [|n IH]; intros al.
- simpl. intros H1. split.
  + intros H2. apply (approx_assetlist_lem T al) in H2.
    assert (L2: hashassetlist (f tt) = hashassetlist al) by congruence.
    now apply hashassetlistinj.
  + intros H2. rewrite H2 in H1. apply approx_assetlist_lem. congruence.
- destruct T as [h|[Tl Tr]].
  + intros [Tl [Tr [H1 [H2 H3]]]]. split.
    * { intros [Tl' [Tr' [all [alr [H4 [H5 [H6 H7]]]]]]].
        assert (L1: mtree_hashroot Tl = mtree_hashroot Tl' /\ mtree_hashroot Tr = mtree_hashroot Tr').
        { rewrite H1 in H4. now apply hashopairinj. }
        destruct L1 as [L1a L1b].
        rewrite H7.
        change (totalassets_ (fun alpha => f (false,alpha)) ++ totalassets_ (fun alpha => f (true,alpha)) = all ++ alr).
        f_equal.
        - apply (IH Tl' (fun alpha => f (false,alpha))).
          + revert H2. now apply mtree_hashroot_mtree_approx_fun_p.
          + assumption.
        - apply (IH Tr' (fun alpha => f (true,alpha))).
          + revert H3. now apply mtree_hashroot_mtree_approx_fun_p.
          + assumption.
      }
    * { intros H4.
        change (totalassets_ (fun alpha => f (false,alpha)) ++ totalassets_ (fun alpha => f (true,alpha)) = al) in H4.
        simpl. exists Tl. exists Tr.
        exists (totalassets_ (fun alpha => f (false,alpha))).
        exists (totalassets_ (fun alpha => f (true,alpha))).
        repeat split.
        - congruence.
        - now apply (IH Tl (fun alpha => f (false,alpha))).
        - now apply (IH Tr (fun alpha => f (true,alpha))).
        - congruence.
      }
  + intros [H1 H2]. split.
    * { intros [all [alr [H3 [H4 H5]]]].
        rewrite H5.
        change (totalassets_ (fun alpha => f (false,alpha)) ++ totalassets_ (fun alpha => f (true,alpha)) = all ++ alr).
        f_equal.
        - now apply (IH Tl (fun alpha => f (false,alpha)) all).
        - now apply (IH Tr (fun alpha => f (true,alpha)) alr).
      }
    * { intros H3.
        change (totalassets_ (fun alpha => f (false,alpha)) ++ totalassets_ (fun alpha => f (true,alpha)) = al) in H3.
        simpl.
        exists (totalassets_ (fun alpha => f (false,alpha))).
        exists (totalassets_ (fun alpha => f (true,alpha))).
        repeat split.
        - now apply (IH Tl (fun alpha => f (false,alpha))).
        - now apply (IH Tr (fun alpha => f (true,alpha))).
        - congruence.
      }
Qed.

Opaque mtree_approx_fun_p.

Lemma mtree_totalunits_lem (T:mtree 162) (f:statefun) (al:list asset) :
  mtree_approx_fun_p T f ->
  mtree_totalassets T al ->
  asset_value_sum al = statefun_totalunits f.
intros H1 H2.
unfold statefun_totalunits. f_equal.
symmetry.
destruct (mtree_approx_fun_p_totalassets T f al H1) as [H3 _].
exact (H3 H2).
Qed.

Theorem mtree_normalize_tx_asset_value_sum tht sigt (blockheight:nat) (T:mtree 162) (tx:Tx) (fee rew:nat) (al bl:list asset) :
  mtree_valid T ->
  tx_valid blockheight tx ->
  mtree_supports_tx tht sigt blockheight tx T fee rew ->
  mtree_totalassets T al ->
  mtree_totalassets (normalize_mtree (tx_mtree_trans blockheight tx T)) bl ->
  asset_value_sum bl + fee + out_burncost (tx_outputs tx) = asset_value_sum al + rew.
intros [f [H1 H2]] [H3a H3b] H4 H5 H6.
assert (L1: asset_value_sum al = statefun_totalunits f).
{ exact (mtree_totalunits_lem T f al H2 H5). }
assert (L2: mtree_approx_fun_p (normalize_mtree (tx_mtree_trans blockheight tx T)) (tx_statefun_trans blockheight tx f)).
{ exact (mtree_normal_approx_trans tht sigt blockheight tx T f fee rew H1 H4 H2). }
assert (L3: asset_value_sum bl = statefun_totalunits (tx_statefun_trans blockheight tx f)).
{ exact (mtree_totalunits_lem (normalize_mtree (tx_mtree_trans blockheight tx T)) (tx_statefun_trans blockheight tx f) bl L2 H6). }
rewrite L1. rewrite L3.
apply (totalunits_bdd tht sigt blockheight f tx fee rew H1).
- destruct tx as [inpl outpl]. split.
  + exact H3a.
  + exact H3b.
- destruct H1 as [_ [Hf2 _]].
  exact (mtree_supports_tx_statefun tht sigt blockheight tx T f fee rew Hf2 H2 H4).
Qed.

Theorem mtree_valid_tx_mtree_trans tht sigt m tx T fee rew :
  tx_valid m tx ->
  mtree_supports_tx tht sigt m tx T fee rew ->
  mtree_valid T ->
  mtree_valid (tx_mtree_trans m tx T).
intros H0 H1 [f [H2 H3]].
exists (tx_statefun_trans m tx f).
split.
- apply sf_tx_valid_thm with (tht := tht) (sigt := sigt) (bday := m) (fee := fee) (rew := rew).
  + exact H2.
  + exact H0.
  + apply (mtree_supports_tx_statefun tht sigt m tx T f fee rew).
    * destruct H2 as [_ [Hf2 _]]. exact Hf2.
    * exact H3.
    * exact H1.
- apply mtree_approx_trans with (tht := tht) (sigt := sigt) (fee := fee) (rew := rew).
  + exact H2.
  + exact H1.
  + exact H3.
Qed.
