(** Copyright (c) 2015 Bill White **)
(** Distributed under the MIT/X11 software license **)
(** See http://www.opensource.org/licenses/mit-license.php **)

(** CryptoHashes : Idealized representation of cryptographic hashing
    using inductive types enclosed in a module. The module 
    simulates the 'trapdoor' property by disallowing writing a destructor
    function via a match. **)

Require Export Addrs.

Module Type HashValsType.

  Parameter hashval : Type.
  Parameter hashnat : nat -> hashval.
  Parameter hashaddr : addr -> hashval.
  Parameter hashpair : hashval -> hashval -> hashval.

  Parameter hashval_eq_dec : forall (h1 h2:hashval), { h1 = h2 } + { h1 <> h2 }.

  Axiom hashnatinj : forall m n, hashnat m = hashnat n -> m = n.
  Axiom hashaddrinj : forall alpha beta, hashaddr alpha = hashaddr beta -> alpha = beta.
  Axiom hashpairinj : forall h1a h1b h2a h2b, hashpair h1a h1b = hashpair h2a h2b -> h1a = h2a /\ h1b = h2b.

  Axiom hashnataddrdiscr : forall m alpha, hashnat m <> hashaddr alpha.
  Axiom hashnatpairdiscr : forall m h1 h2, hashnat m <> hashpair h1 h2.
  Axiom hashaddrpairdiscr : forall alpha h1 h2, hashaddr alpha <> hashpair h1 h2.

  Axiom hashval_ind : forall p:hashval -> Prop,
                        (forall n, p (hashnat n)) ->
                        (forall alpha, p (hashaddr alpha)) ->
                        (forall h1, p h1 -> forall h2, p h2 -> p (hashpair h1 h2)) ->
                        forall h, p h.

End HashValsType.

Module HashVals : HashValsType.

  Inductive hashval' : Type :=
  | hashnat' : nat -> hashval'
  | hashaddr' : addr -> hashval'
  | hashpair' : hashval' -> hashval' -> hashval'.

  Definition hashval := hashval'.
  Definition hashnat := hashnat'.
  Definition hashaddr := hashaddr'.
  Definition hashpair := hashpair'.

  Fixpoint hashval_eq_dec (h1 h2:hashval) : { h1 = h2 } + { h1 <> h2 }.
  destruct h1 as [n1|alpha1|h1a h1b]; destruct h2 as [n2|alpha2|h2a h2b]; try (right; discriminate).
  - destruct (eq_nat_dec n1 n2).
    + left. congruence.
    + right. congruence.
  - destruct (addr_eq_dec alpha1 alpha2).
    + left. congruence.
    + right. congruence.
  - destruct (hashval_eq_dec h1a h2a).
    + destruct (hashval_eq_dec h1b h2b).
      * left. congruence.
      * right. congruence.
    + right. congruence.
  Defined.

  Lemma hashnatinj : forall m n, hashnat m = hashnat n -> m = n.
    intros m n H. inversion H. reflexivity.
  Qed.

  Lemma hashaddrinj : forall alpha beta, hashaddr alpha = hashaddr beta -> alpha = beta.
    intros alpha beta H. inversion H. reflexivity.
  Qed.

  Lemma hashpairinj : forall h1a h1b h2a h2b, hashpair h1a h1b = hashpair h2a h2b -> h1a = h2a /\ h1b = h2b.
    intros h1a h1b h2a h2b H1. inversion H1. tauto.
  Qed.

  Lemma hashnataddrdiscr : forall m alpha, hashnat m <> hashaddr alpha.
    discriminate.
  Qed.

  Lemma hashnatpairdiscr : forall m h1 h2, hashnat m <> hashpair h1 h2.
    discriminate.
  Qed.

  Lemma hashaddrpairdiscr : forall alpha h1 h2, hashaddr alpha <> hashpair h1 h2.
    discriminate.
  Qed.

  Lemma hashval_ind : forall p:hashval -> Prop,
                         (forall n, p (hashnat n)) ->
                         (forall alpha, p (hashaddr alpha)) ->
                         (forall h1, p h1 -> forall h2, p h2 -> p (hashpair h1 h2)) ->
                         forall h, p h.
    exact hashval'_ind.
  Qed.

End HashVals.

Export HashVals.

Lemma hashpair_neq_L h1 h2 : hashpair h1 h2 <> h1.
  revert h1 h2. apply (hashval_ind (fun h1 => forall h2, hashpair h1 h2 <> h1)).
  - intros n h2 H. symmetry in H. revert H. apply hashnatpairdiscr.
  - intros alpha h2 H. symmetry in H. revert H. apply hashaddrpairdiscr.
  - intros h1a IHa h1b IHb h2 H. apply hashpairinj in H. destruct H as [H _].
    revert H. apply IHa.
Qed.

Lemma hashpair_neq_R h1 h2 : hashpair h1 h2 <> h2.
  revert h2 h1. apply (hashval_ind (fun h2 => forall h1, hashpair h1 h2 <> h2)).
  - intros n h1 H. symmetry in H. revert H. apply hashnatpairdiscr.
  - intros alpha h1 H. symmetry in H. revert H. apply hashaddrpairdiscr.
  - intros h2a IHa h2b IHb h1 H. apply hashpairinj in H. destruct H as [_ H].
    revert H. apply IHb.
Qed.

Definition hashval_In_dec (h:hashval) (hl:list hashval) : { In h hl } + { ~ In h hl }.
induction hl as [|k hr IH].
- right. simpl. tauto.
- destruct IH as [H1|H1].
  + left. right. exact H1.
  + destruct (hashval_eq_dec k h) as [H2|H2].
    * subst k. left. left. reflexivity.
    * { right. intros [H3|H3].
        - exact (H2 H3).
        - exact (H1 H3).
      }
Defined.

Fixpoint hashlist (hl:list hashval) : hashval :=
match hl with
| h::hr => hashpair h (hashlist hr)
| nil => hashnat 0
end.

Lemma hashlistinj : forall hl1 hl2, hashlist hl1 = hashlist hl2 -> hl1 = hl2.
intros hl1. induction hl1 as [|h1 hr1 IH]; intros [|h2 hr2].
- reflexivity.
- simpl. intros H. exfalso. revert H. apply hashnatpairdiscr.
- simpl. intros H. exfalso. symmetry in H. revert H. apply hashnatpairdiscr.
- simpl. intros H3. apply hashpairinj in H3. destruct H3 as [H4 H5].
  subst h2. f_equal.
  apply IH. exact H5.
Qed.

Lemma hashmapinj {X} (f : X -> hashval) (l l': list X) :
  (forall x y, f x = f y -> x = y) ->
  map f l = map f l' -> l = l'.
intros H1. revert l'. induction l as [|x l IH]; intros [|y l'].
- tauto.
- discriminate.
- discriminate.
- intros H2. inversion H2. f_equal.
  + revert H0. apply H1.
  + revert H3. apply IH.
Qed.

Definition hashopair (h1 h2:option hashval) : option hashval :=
match h1,h2 with
| None,None => None
| Some h1,None => Some (hashpair (hashnat 0) h1)
| None,Some h2 => Some (hashpair (hashnat 1) h2)
| Some h1,Some h2 => Some (hashlist (hashnat 2::h1::h2::nil))
end.

Lemma hashopairinj h1a h1b h2a h2b : hashopair h1a h1b = hashopair h2a h2b -> h1a = h2a /\ h1b = h2b.
destruct h1a as [h1a|]; destruct h2a as [h2a|];
destruct h1b as [h1b|]; destruct h2b as [h2b|]; simpl; intros H; try (discriminate H).
- inversion H. apply hashpairinj in H1. destruct H1 as [H2 H3]. apply hashpairinj in H3.
  destruct H3 as [H4 H5]. apply hashpairinj in H5. destruct H5 as [H6 H7].
  split; congruence.
- inversion H. apply hashpairinj in H1. destruct H1 as [H2 H3]. apply hashnatinj in H2. discriminate H2.
- inversion H. apply hashpairinj in H1. destruct H1 as [H2 H3]. apply hashnatinj in H2. discriminate H2.
- inversion H. apply hashpairinj in H1. destruct H1 as [H2 H3].
  split; congruence.
- inversion H. apply hashpairinj in H1. destruct H1 as [H2 H3]. apply hashnatinj in H2. discriminate H2.
- inversion H. apply hashpairinj in H1. destruct H1 as [H2 H3]. apply hashnatinj in H2. discriminate H2.
- inversion H. apply hashpairinj in H1. destruct H1 as [H2 H3]. apply hashnatinj in H2. discriminate H2.
- inversion H. apply hashpairinj in H1. destruct H1 as [H2 H3]. apply hashnatinj in H2. discriminate H2.
- inversion H. apply hashpairinj in H1. destruct H1 as [H2 H3].
  split; congruence.
- split; reflexivity.
Qed.

Lemma hashopair_None_1 (h1 h2:option hashval) : hashopair h1 h2 = None -> h1 = None.
  destruct h1 as [h1|].
  - simpl. destruct h2; discriminate.
  - tauto.
Qed.

Lemma hashopair_None_2 (h1 h2:option hashval) : hashopair h1 h2 = None -> h2 = None.
  destruct h2 as [h2|].
  - destruct h1; discriminate.
  - tauto.
Qed.

Definition hashopair1 (h1:hashval) (h2:option hashval) : hashval :=
match h2 with
  | Some h2 => hashlist (hashnat 2::h1::h2::nil)
  | None => hashpair (hashnat 0) h1
end.

Definition hashopair2 (h1:option hashval) (h2:hashval) : hashval :=
match h1 with
  | Some h1 => hashlist (hashnat 2::h1::h2::nil)
  | None => hashpair (hashnat 1) h2
end.

Lemma hashopair1inj h1 h2 h1' h2' : hashopair1 h1 h2 = hashopair1 h1' h2' -> h1 = h1' /\ h2 = h2'.
destruct h2 as [h2|]; destruct h2' as [h2'|]; simpl; intros H; try discriminate H.
- inversion H. apply hashpairinj in H1. destruct H1 as [H2 H3]. apply hashpairinj in H3.
  destruct H3 as [H4 H5]. apply hashpairinj in H5. destruct H5 as [H6 H7].
  split; congruence.
- inversion H. apply hashpairinj in H1. destruct H1 as [H2 H3]. apply hashnatinj in H2. discriminate H2.
- inversion H. apply hashpairinj in H1. destruct H1 as [H2 H3]. apply hashnatinj in H2. discriminate H2.
- inversion H. apply hashpairinj in H1. destruct H1 as [H2 H3].
  split; congruence.
Qed.

Lemma hashopair2inj h1 h2 h1' h2' : hashopair2 h1 h2 = hashopair2 h1' h2' -> h1 = h1' /\ h2 = h2'.
destruct h1 as [h1|]; destruct h1' as [h1'|]; simpl; intros H; try discriminate H.
- inversion H. apply hashpairinj in H1. destruct H1 as [H2 H3]. apply hashpairinj in H3.
  destruct H3 as [H4 H5]. apply hashpairinj in H5. destruct H5 as [H6 H7].
  split; congruence.
- inversion H. apply hashpairinj in H1. destruct H1 as [H2 H3]. apply hashnatinj in H2. discriminate H2.
- inversion H. apply hashpairinj in H1. destruct H1 as [H2 H3]. apply hashnatinj in H2. discriminate H2.
- inversion H. apply hashpairinj in H1. destruct H1 as [H2 H3].
  split; congruence.
Qed.

Fixpoint ohashlist (hl:list hashval) : option hashval :=
match hl with
| nil => None
| h::hr =>
  match ohashlist hr with
    | None => Some(hashpair (hashnat 3) h)
    | Some k => Some(hashpair (hashnat 4) (hashpair h k))
  end
end.

Lemma ohashlistinj : forall hl1 hl2, ohashlist hl1 = ohashlist hl2 -> hl1 = hl2.
intros hl1. induction hl1 as [|h1 hr1 IH]; intros [|h2 hr2] H1.
- reflexivity.
- exfalso. simpl in H1. destruct (ohashlist hr2); discriminate H1.
- exfalso. simpl in H1. destruct (ohashlist hr1); discriminate H1.
- simpl in H1.
  destruct (ohashlist hr1) as [k1|] eqn:E1; destruct (ohashlist hr2) as [k2|] eqn:E2.
  + inversion H1.
    apply hashpairinj in H0. destruct H0 as [_ H0].
    apply hashpairinj in H0. destruct H0 as [H0 H2].
    subst h2. f_equal. apply IH. congruence.
  + exfalso. inversion H1.
    apply hashpairinj in H0. destruct H0 as [H0 _].
    apply hashnatinj in H0. omega.
  + exfalso. inversion H1.
    apply hashpairinj in H0. destruct H0 as [H0 _].
    apply hashnatinj in H0. omega.
  + inversion H1.
    apply hashpairinj in H0. destruct H0 as [_ H0].
    subst h2. f_equal. apply IH. congruence.
Qed.

Inductive subh (h:hashval) : hashval -> Prop :=
| subh_L h' : subh h (hashpair h h')
| subh_R h' : subh h (hashpair h' h)
| subh_PL h1 h2 : subh h h1 -> subh h (hashpair h1 h2)
| subh_PR h1 h2 : subh h h2 -> subh h (hashpair h1 h2)
.

Lemma subh_hashlist h hl : In h hl -> subh h (hashlist hl).
induction hl.
- simpl; tauto.
- intros [H1|H1]; simpl.
  + subst a. apply subh_L.
  + apply subh_PR. now apply IHhl.
Qed.

Lemma subh_tra h1 h2 h3 : subh h1 h2 -> subh h2 h3 -> subh h1 h3.
intros H. revert h3. induction H as [h2|h2|h2 h3 H1 IH1|h2 h3 H1 IH1].
- intros h3 H. induction H as [h3|h3|h3 h4 H2 IH2|h3 h4 H2 IH2].
  + apply subh_PL. apply subh_L.
  + apply subh_PR. apply subh_L.
  + now apply subh_PL.
  + now apply subh_PR.
- intros h3 H. induction H as [h3|h3|h3 h4 H2 IH2|h3 h4 H2 IH2].
  + apply subh_PL. apply subh_R.
  + apply subh_PR. apply subh_R.
  + now apply subh_PL.
  + now apply subh_PR.
- intros h4 H. induction H as [h4|h4|h4 h5 H2 IH2|h4 h5 H2 IH2].
  + apply IH1. apply subh_PL. apply subh_L.
  + apply IH1. apply subh_PR. apply subh_L.
  + now apply subh_PL.
  + now apply subh_PR.
- intros h4 H. induction H as [h4|h4|h4 h5 H2 IH2|h4 h5 H2 IH2].
  + apply IH1. apply subh_PL. apply subh_R.
  + apply IH1. apply subh_PR. apply subh_R.
  + now apply subh_PL.
  + now apply subh_PR.
Qed.

Lemma subh_irrefl h : ~ subh h h.
  revert h. apply hashval_ind.
  - intros n H. inversion H.
    + symmetry in H1. revert H1. apply hashnatpairdiscr.
    + symmetry in H1. revert H1. apply hashnatpairdiscr.
    + symmetry in H0. revert H0. apply hashnatpairdiscr.
    + symmetry in H0. revert H0. apply hashnatpairdiscr.
  - intros alpha H. inversion H.
    + symmetry in H1. revert H1. apply hashaddrpairdiscr.
    + symmetry in H1. revert H1. apply hashaddrpairdiscr.
    + symmetry in H0. revert H0. apply hashaddrpairdiscr.
    + symmetry in H0. revert H0. apply hashaddrpairdiscr.
  - intros h1 IH1 h2 IH2 H. inversion H.
    + revert H1. apply hashpair_neq_L.
    + revert H1. apply hashpair_neq_R.
    + apply IH1. apply subh_tra with (h2 := (hashpair h1 h2)).
      * apply subh_L.
      * apply hashpairinj in H0. destruct H0 as [H0a H0b]. congruence.
    + apply IH2. apply subh_tra with (h2 := (hashpair h1 h2)).
      * apply subh_R.
      * apply hashpairinj in H0. destruct H0 as [H0a H0b]. congruence.
Qed.

Lemma subh_asym h h' : subh h h' -> ~ subh h' h.
intros H1 H2. apply (subh_irrefl h).
now apply subh_tra with (h2 := h').
Qed.

Definition ohashval_eq_dec (h h':option hashval) : {h = h'} + {h <> h'}.
destruct h as [h|]; destruct h' as [h'|].
- destruct (hashval_eq_dec h h') as [H|H].
  + left. congruence.
  + right. intros H'. inversion H'. contradiction (H H1).
- right. discriminate.
- right. discriminate.
- left. reflexivity.
Defined.

(***
 Finally assume a parameter for turning hashvals into an 160 bit sequences.
 (In the implementation hashvals are represented by 160 bit sequences.)
 These can be used to give different kinds of addresses (162 bites).
 ***)
Parameter hashval_bit160 : hashval -> bitseq 160.

Definition hashval_termaddr (h:hashval) : termaddr :=
hashval_bit160 h.

Definition hashval_pubaddr (h:hashval) : pubaddr :=
hashval_bit160 h.

Definition hashval_p2pkh_payaddr (h:hashval) : payaddr :=
(false,hashval_bit160 h).

Definition hashval_p2sh_payaddr (h:hashval) : payaddr :=
(true,hashval_bit160 h).

Definition hashval_p2pkh_addr (h:hashval) : addr :=
(false,(false,hashval_bit160 h)).

Definition hashval_p2sh_addr (h:hashval) : addr :=
(false,(true,hashval_bit160 h)).

Definition hashval_term_addr (h:hashval) : addr :=
(true,(false,hashval_bit160 h)).

Definition hashval_publication_addr (h:hashval) : addr :=
(true,(true,hashval_bit160 h)).

(***
 Also assume a way of serializing hashes.
 ***)
Parameter ser_hashval : hashval -> list nat.
Axiom ser_hashval_inj : forall h h' l l', ser_hashval h ++ l = ser_hashval h' ++ l' -> l = l' /\ h = h'.

