(** Copyright (c) 2015 Bill White **)
(** Distributed under the MIT/X11 software license **)
(** See http://www.opensource.org/licenses/mit-license.php **)

(** Transactions: Transactions are represented as pairs of input and output lists.
    An input list contains pairs of addresses and hashvals referring to an asset by
    it's id and the address where the asset is held.
    An output list contains addresses associated with pairs of use requirements and preassets.
    An asset id h is constructed for each output by hashing the transaction along with the index
    of the output (vout). Then the corresponding asset will be constructed by
    combining the asset id with the use requirement and preasset.
    A transaction is considered valid if it has at least one input and no duplicate inputs.
    This should not be confused with the transaction being supported, a notion
    that depends on the ledger.
 **)

Require Export Assets.

(***
 Basic unsigned Tx consisting of inputs and outputs
 where the input assets are only referred by address and hashval (assetid)
 ***)
Definition Tx : Type := prod (list addr_assetid) (list addr_preasset).

Definition hashtx (tx : Tx) : hashval :=
match tx with
| (inpl,outpl) =>
  hashpair (hashlist (map hash_addr_assetid inpl))
           (hashlist (map hash_addr_preasset outpl))
end.

Definition tx_inputs (tx:Tx) : list addr_assetid :=
match tx with
| (inpl,outpl) => inpl
end.

Definition tx_outputs (tx:Tx) : list addr_preasset :=
match tx with
| (inpl,outpl) => outpl
end.

Lemma hashtxioinj inpl outpl inpl' outpl' :
hashtx (inpl,outpl) = hashtx (inpl',outpl')
-> inpl = inpl' /\ outpl = outpl'.
unfold hashtx. intros H1. 
apply hashpairinj in H1. destruct H1 as [H2 H3]. split.
- apply hashlistinj in H2. now apply map_hash_addr_assetidinj.
- apply hashlistinj in H3. now apply map_hash_addr_preassetinj.
Qed.

Lemma hashtx_notin_inpl_lem alpha inpl inpl' outpl i :
  (forall z, In z inpl' -> In z inpl) ->
  ~In (alpha,hashpair (hashtx (inpl,outpl)) (hashnat i)) inpl'.
induction inpl'.
- simpl; tauto.
- intros H1 [H2|H2].
  + destruct a as [gamma hc].
    inversion H2.
    apply (subh_irrefl hc).
    rewrite H3 at 2.
    apply subh_PL. apply subh_PL.
    apply subh_tra with (h2 := (hash_addr_assetid (gamma,hc))).
    * simpl. apply subh_R.
    * apply subh_hashlist. apply in_map. apply H1. now left.
  + revert H2. apply IHinpl'.
    intros z H3. apply H1. now right.
Qed.

Lemma hashtx_notin_inpl alpha inpl outpl i :
  ~In (alpha,hashpair (hashtx (inpl,outpl)) (hashnat i)) inpl.
apply hashtx_notin_inpl_lem.
tauto.
Qed.

Inductive inpl_reln {n:nat} (alphapre:bitseq n -> addr) : list addr_assetid -> list (bitseq n * hashval) -> Prop :=
| inpl_reln_nil : inpl_reln alphapre nil nil
| inpl_reln_skip fullinpl inpl alpha h :
    (forall gamma:bitseq n, alphapre gamma <> alpha)
    -> inpl_reln alphapre fullinpl inpl
    -> inpl_reln alphapre ((alpha,h)::fullinpl) inpl
| inpl_reln_cons fullinpl inpl gamma h :
    inpl_reln alphapre fullinpl inpl
    -> inpl_reln alphapre ((alphapre gamma,h)::fullinpl) ((gamma,h)::inpl)
.

Inductive outpl_reln (bday:nat) (txh:hashval) {n:nat} (alphapre:bitseq n -> addr) : nat -> list addr_preasset -> list (bitseq n * asset) -> Prop :=
| outpl_reln_nil i : outpl_reln bday txh alphapre i nil nil
| outpl_reln_skip i fulloutpl outpl alpha u :
    (forall gamma:bitseq n, alphapre gamma <> alpha)
    -> outpl_reln bday txh alphapre (S i) fulloutpl outpl
    -> outpl_reln bday txh alphapre i ((alpha,u)::fulloutpl) outpl
| outpl_reln_cons i fulloutpl outpl gamma u :
    outpl_reln bday txh alphapre (S i) fulloutpl outpl
    -> outpl_reln bday txh alphapre i ((alphapre gamma,u)::fulloutpl) ((gamma,(hashpair txh (hashnat i),(bday,u)))::outpl)
.

Lemma inpl_reln_start fullinpl :
  inpl_reln (fun alpha : addr => alpha) fullinpl fullinpl.
induction fullinpl as [|[alpha h] fullinpl IH].
- simpl. apply inpl_reln_nil.
- simpl. 
  apply (inpl_reln_cons (fun alpha:addr => alpha) fullinpl fullinpl).
  apply IH.
Qed.

Lemma outpl_reln_start bday txh fulloutpl j :
  outpl_reln bday txh (fun alpha : addr => alpha) j fulloutpl (add_vout bday txh fulloutpl j).
revert j. induction fulloutpl as [|[alpha [obl u]] fulloutpl IH].
- simpl. apply outpl_reln_nil.
- simpl. intros j.
  apply (outpl_reln_cons bday txh (fun alpha:addr => alpha) j fulloutpl (add_vout bday txh fulloutpl (S j)) alpha (obl,u)).
  apply IH.
Qed.

Lemma inpl_reln_In_iff {n:nat} (alphapre:bitseq n -> addr) fullinpl inpl :
  (forall gamma delta, alphapre gamma = alphapre delta -> gamma = delta) ->
  inpl_reln alphapre fullinpl inpl ->
  forall gamma h, In (gamma,h) inpl <-> In (alphapre gamma,h) fullinpl.
intros H0 H. induction H as [|fullinpl inpl alpha k H1 H2 IH|fullinpl inpl delta k H1 IH].
- simpl. tauto.
- simpl. intros gamma h. split.
  + intros H3. right. now apply IH.
  + intros [H3|H3].
    * exfalso. inversion H3. symmetry in H4. revert H4. apply H1.
    * now apply IH.
- intros gamma h. split.
  + intros [H3|H3].
    * inversion H3. now left.
    * right. now apply IH.
  + intros [H3|H3].
    * inversion H3. apply H0 in H2. left. congruence.
    * right. now apply IH.
Qed.

Lemma outpl_reln_new_assets_eq1 (bday:nat) (fulloutpl:list addr_preasset) (txh:hashval) :
  forall j, forall (outpl:list (bitseq 0 * asset)%type),
  forall (alphapre:bitseq 0 -> addr),
    outpl_reln bday txh alphapre j fulloutpl outpl ->
    new_assets bday (alphapre tt) fulloutpl txh j = map (snd (B:=asset)) outpl.
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

Lemma inpl_reln_strip_bitseq_true {n:nat} 
      (alphapre:bitseq (S n) -> addr) (fullinpl:list addr_assetid) (inpl:list (bitseq (S n) * hashval)%type) :
  (forall gamma delta, alphapre gamma = alphapre delta -> gamma = delta) ->
  inpl_reln alphapre fullinpl inpl ->
  inpl_reln (fun gamma => alphapre (true,gamma)) fullinpl (strip_bitseq_true inpl).
intros Hapi H. induction H as [|fullinpl inpl alpha h H1 H2 IH|fullinpl inpl [[|] gamma] h H1 IH].
- simpl. apply inpl_reln_nil.
- simpl. apply inpl_reln_skip.
  + intros gamma. apply H1.
  + exact IH.
- simpl.
  apply (inpl_reln_cons (fun gamma => alphapre (true,gamma)) fullinpl (strip_bitseq_true inpl) gamma h).
  exact IH.
- simpl. apply inpl_reln_skip.
  + intros gamma' H2. apply Hapi in H2. inversion H2.
  + exact IH.
Qed.

Lemma outpl_reln_strip_bitseq_false bday (txh:hashval) {n:nat} 
      (alphapre:bitseq (S n) -> addr) (fulloutpl:list addr_preasset) (outpl:list (bitseq (S n) * asset)%type) :
  (forall gamma delta, alphapre gamma = alphapre delta -> gamma = delta) ->
  forall j,
  outpl_reln bday txh alphapre j fulloutpl outpl ->
  outpl_reln bday txh (fun gamma => alphapre (false,gamma)) j fulloutpl (strip_bitseq_false outpl).
intros Hapi j H. induction H as [j|j fulloutpl outpl alpha u H1 H2 IH|j fulloutpl outpl [[|] gamma] u H1 IH].
- simpl. apply outpl_reln_nil.
- simpl. apply outpl_reln_skip.
  + intros gamma. apply H1.
  + exact IH.
- simpl. apply outpl_reln_skip.
  + intros gamma' H2. apply Hapi in H2. inversion H2.
  + exact IH.
- simpl.
  apply (outpl_reln_cons bday txh (fun gamma => alphapre (false,gamma)) j fulloutpl (strip_bitseq_false outpl) gamma u).
  exact IH.
Qed.

Lemma outpl_reln_strip_bitseq_true bday (txh:hashval) {n:nat} 
      (alphapre:bitseq (S n) -> addr) (fulloutpl:list addr_preasset) (outpl:list (bitseq (S n) * asset)%type) :
  (forall gamma delta, alphapre gamma = alphapre delta -> gamma = delta) ->
  forall j,
  outpl_reln bday txh alphapre j fulloutpl outpl ->
  outpl_reln bday txh (fun gamma => alphapre (true,gamma)) j fulloutpl (strip_bitseq_true outpl).
intros Hapi j H. induction H as [j|j fulloutpl outpl alpha u H1 H2 IH|j fulloutpl outpl [[|] gamma] u H1 IH].
- simpl. apply outpl_reln_nil.
- simpl. apply outpl_reln_skip.
  + intros gamma. apply H1.
  + exact IH.
- simpl.
  apply (outpl_reln_cons bday txh (fun gamma => alphapre (true,gamma)) j fulloutpl (strip_bitseq_true outpl) gamma u).
  exact IH.
- simpl. apply outpl_reln_skip.
  + intros gamma' H2. apply Hapi in H2. inversion H2.
  + exact IH.
Qed.

Lemma inpl_reln_nil_no_spent_lem {n:nat} (fullinpl:list addr_assetid) (alphapre:bitseq n -> addr) :
    inpl_reln alphapre fullinpl nil
    ->
    forall gamma:bitseq n,
      get_spent (alphapre gamma) fullinpl = nil.
induction fullinpl as [|[alpha k] fullinpl IH].
- intros _ gamma. reflexivity.
- intros H1 gamma. inversion H1.
  simpl. destruct (addr_eq_dec (alphapre gamma) alpha) as [D1|D1].
  + exfalso. revert D1. apply H4.
  + now apply IH.
Qed.

Lemma outpl_reln_nil_no_new_assets_lem {n:nat} bday (fulloutpl:list addr_preasset) (txh:hashval) (alphapre:bitseq n -> addr) :
    forall j,
    outpl_reln bday txh alphapre j fulloutpl nil
    ->
    forall gamma:bitseq n,
      new_assets bday (alphapre gamma) fulloutpl txh j = nil.
induction fulloutpl as [|[alpha [obl u]] fulloutpl IH].
- intros j _ gamma. reflexivity.
- intros j H1 gamma. inversion H1. simpl.
  destruct (addr_eq_dec (alphapre gamma) alpha) as [D1|D1].
  + exfalso. revert D1. apply H5.
  + now apply IH.
Qed.

Definition tx_inputs_valid (inpl:list addr_assetid) : Prop :=
inpl <> nil (*** without this, two tx can have the same hashes. ***)
/\
no_dups inpl (*** inputs cannot be listed more than once. ***)
.

Definition tx_outputs_valid (outpl:list addr_preasset) : Prop :=
(*** Can't declare 2 owners (exception: owns false vs. owns true; can have one owner as an object [the one who defined it] and another as a prop [the one who proved it]) ***)
(forall alpha i obl beta u i' obl' beta' u' b,
  nth_error outpl i = value(alpha,(obl,owns b beta u))
  ->
  nth_error outpl i' = value(alpha,(obl',owns b beta' u'))
  ->
  i = i' /\ obl = obl' /\ beta = beta' /\ u = u')
/\
(*** Ownership deeds must sent to term addresses (the address of the owned term). ***)
(forall alpha obl b beta u,
   In (alpha,(obl,owns b beta u)) outpl -> term_addr_p alpha)
/\
(*** Publications must be sent to publication addresses. This is to make it easy for nodes to abstract away all of this part of the tree. ***)
(forall alpha obl beta nonce thy,
   In (alpha,(obl,theorypublication beta nonce thy)) outpl -> exists h, theoryspec_hashroot thy = Some h /\ pubaddr_addr (hashval_pubaddr h) = alpha)
/\
(forall alpha obl beta nonce th s,
   In (alpha,(obl,signapublication beta nonce th s)) outpl -> pubaddr_addr (hashval_pubaddr (signaspec_hashroot th s)) = alpha)
/\
(forall alpha obl beta nonce th d,
   In (alpha,(obl,docpublication beta nonce th d)) outpl -> pubaddr_addr (hashval_pubaddr (doc_hashroot th d)) = alpha)
.

Definition tx_valid (tx:Tx) : Prop :=
tx_inputs_valid (tx_inputs tx) /\ tx_outputs_valid (tx_outputs tx).

(*** Signed Transactions ***)
Inductive gensignat : Type :=
| ordinarysignat : signat -> gensignat
| endorsedsignat : signat -> payaddr -> signat -> gensignat.

Definition sTx : Type := prod Tx (prod (list gensignat) (list gensignat)).

Definition check_spend_obligation (alpha:addr) (blockheight:nat) (h:hashval) (s:gensignat) (obl:obligation) : Prop :=
match s,obl with
| ordinarysignat s0,None =>
  match alpha with
    | (false,alpha0) => check_signat h s0 alpha0 (*** only for payaddrs ***)
    | (true,_) => False
  end
| endorsedsignat s0 alpha1 s1,None =>
  match alpha with
    | (false,alpha0) => check_signat (hashaddr (payaddr_addr alpha1)) s0 alpha0 /\ check_signat h s1 alpha1
    | (true,_) => False
  end
| ordinarysignat s0,Some(gamma,b) =>
  (*** block height has been reached ***)
  b >= blockheight
  /\
  check_signat h s0 gamma
| endorsedsignat s0 alpha1 s1,Some(gamma,b) =>
  (*** block height has been reached ***)
  b >= blockheight
  /\
  check_signat (hashaddr (payaddr_addr alpha1)) s0 gamma /\ check_signat h s1 alpha1
end.

Definition check_move_obligation (alpha:addr) (h:hashval) (s:gensignat) : Prop :=
match s,alpha with
| ordinarysignat s0,(false,alpha0) => check_signat h s0 alpha0
| _,_ => False
end.

Fixpoint check_tx_in_signatures (blockheight:nat) (h:hashval) (outpl:list addr_preasset)
         (inpl:list addr_assetid) (al:list asset) (sl:list gensignat) : Prop :=
match inpl,al,sl with
| nil,nil,nil => True
| (alpha,k)::inpr,(a::ar),(s::sr) =>
  check_tx_in_signatures blockheight h outpl inpr ar sr /\
  assetid a = k /\
  (check_spend_obligation alpha blockheight h s (assetobl a)
   \/
   exists beta, In (beta,(assetobl a,assetpre a)) outpl
                /\
                check_move_obligation alpha h s)
| _,_,_ => False
end.

Fixpoint check_tx_out_signatures (blockheight:nat) (h:hashval) (outpl:list addr_preasset) (sl:list gensignat) : Prop :=
match outpl,sl with
| nil,nil => True
| (_,(_,theorypublication alpha n thy))::outpr,ordinarysignat s::sr =>
  check_tx_out_signatures blockheight h outpr sr /\
  check_signat h s alpha
| (_,(_,signapublication alpha n th si))::outpr,ordinarysignat s::sr =>
  check_tx_out_signatures blockheight h outpr sr /\
  check_signat h s alpha
| (_,(_,docpublication alpha n th d))::outpr,ordinarysignat s::sr =>
  check_tx_out_signatures blockheight h outpr sr /\
  check_signat h s alpha
| _::outpr,_ =>
  check_tx_out_signatures blockheight h outpr sl
| _,_ => False
end.

Definition tx_signatures_valid (blockheight : nat) (al:list asset) (stx:sTx) : Prop :=
match stx with
| (tx,(sli,slo)) =>
  check_tx_in_signatures blockheight (hashtx tx) (tx_outputs tx) (tx_inputs tx) al sli
  /\
  check_tx_out_signatures blockheight (hashtx tx) (tx_outputs tx) slo
end.

(*** Transform the theory tree and signature tree based on the specs in the output of the tx ***)
Fixpoint txout_update_ottree (outpl:list addr_preasset) (tht:option (ttree 160)) : option (ttree 160) :=
match outpl with
| nil => tht
| (alpha,(obl,theorypublication gamma nonce d))::outpr =>
  txout_update_ottree outpr (Some(ottree_insert tht (hashval_bit160 (hashtheoryspec d)) (theoryspec_theory d)))
| _::outpr => txout_update_ottree outpr tht
end.

Definition tx_update_ottree (tx:Tx) (tht:option (ttree 160)) : option (ttree 160) :=
txout_update_ottree (tx_outputs tx) tht.

Fixpoint txout_update_ostree (outpl:list addr_preasset) (sigt:option (stree 160)) : option (stree 160) :=
match outpl with
| nil => sigt
| (alpha,(obl,signapublication gamma nonce th d))::outpr =>
  txout_update_ostree outpr (Some(ostree_insert sigt (hashval_bit160 (hashsignaspec d)) th (signaspec_signa th d)))
| _::outpr => txout_update_ostree outpr sigt
end.

Definition tx_update_ostree (tx:Tx) (sigt:option (stree 160)) : option (stree 160) :=
txout_update_ostree (tx_outputs tx) sigt.
