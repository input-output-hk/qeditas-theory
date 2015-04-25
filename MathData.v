(** Copyright (c) 2015 Bill White **)
(** Distributed under the MIT/X11 software license **)
(** See http://www.opensource.org/licenses/mit-license.php **)

(** MathDoc: Representation of the doc part of higher-order logic
    (simple types, typed terms, proof terms) without the checking.
    This is following Egal by representing 'global definitions' by hash values.
    There are functions computing when a term or proof uses a global definition,
    and functions computing when a proof uses a "known" (a hash of a proposition
    which is either an axiom or previously proven proposition).
 **)

Require Export ETrees.

Inductive stp : Type :=
| prop : stp
| ind : stp
| tvar : nat -> stp
| sar : stp -> stp -> stp.

Inductive trm : Type :=
| Db : nat -> trm
| Gn : hashval -> list stp -> trm
| Ap : trm -> trm -> trm
| La : stp -> trm -> trm
| Imp : trm -> trm -> trm
| All : stp -> trm -> trm.

Inductive pf : Type :=
| PDb : nat -> pf
| Gpn : hashval -> list stp -> pf
| PAp : pf -> pf -> pf
| TAp : pf -> trm -> pf
| PLa : trm -> pf -> pf
| TLa : stp -> pf -> pf.

Fixpoint ser_stp (a:stp) :=
match a with
| prop => (0::nil)
| ind => (1::nil)
| tvar n => (2::n::nil)
| sar a1 a2 => (3::ser_stp a1) ++ ser_stp a2
end.

Definition hashstp (a:stp) : hashval := hashwordlist (0::ser_stp a).

Fixpoint ser_stp_l al : list nat :=
match al with
| nil => (0::nil)
| (a::ar) => (1::ser_stp a) ++ ser_stp_l ar
end.

Fixpoint ser_trm (m:trm) : list nat :=
match m with
| Db n => 0::n::nil
| Gn h al => 1::ser_hashval h ++ ser_stp_l al
| Ap m n => 2::(ser_trm m) ++ (ser_trm n)
| La a m => 3::(ser_stp a) ++ (ser_trm m)
| Imp m n => 4::(ser_trm m) ++ (ser_trm n)
| All a m => 5::(ser_stp a) ++ (ser_trm m)
end.

Definition hashtrm (m:trm) : hashval := hashwordlist (1::ser_trm m).

(*** This hashes a trm with a theory. We need to have separate identifiers for the same term in different theories, especially for conjectures with bounties. ***)
Definition hashthtrm (th:option hashval) (m:trm) : hashval := hashopair2 th (hashtrm m).

Fixpoint ser_pf (d:pf) : list nat :=
match d with
| PDb n => 0::n::nil
| Gpn h al => 1::(ser_hashval h) ++ ser_stp_l al
| PAp d e => 2::(ser_pf d) ++ (ser_pf e)
| TAp d n => 3::(ser_pf d) ++ (ser_trm n)
| PLa p d => 4::(ser_trm p) ++ (ser_pf d)
| TLa a d => 5::(ser_stp a) ++ (ser_pf d)
end.

Definition hashpf (d:pf) : hashval := hashwordlist (2::ser_pf d).

(*** Theory (primitives and axioms, possibly with some helper definitions.) ***)
Inductive theoryitem : Type :=
| thyprim : stp -> theoryitem
| thydef : stp -> trm -> theoryitem
| thyaxiom : trm -> theoryitem
.

Definition theory : Type := list theoryitem.

Definition ser_theoryitem (d : theoryitem) : list nat :=
match d with
| thyprim a => 1::ser_stp a
| thydef a m => 2::ser_stp a ++ ser_trm m
| thyaxiom p => 3::ser_trm p
end.

Definition hashtheoryitem (d : theoryitem) : hashval := hashwordlist (3::ser_theoryitem d).

Fixpoint ser_theory (dl : theory) : list nat :=
match dl with
| nil => 0::nil
| (d::dr) => 1::ser_theoryitem d ++ ser_theory dr
end.

Definition hashtheory (dl : theory) : hashval := hashwordlist (ser_theory dl).

(*** Signatures (parameters, definitions and knowns that can be imported into a document) ***)
Inductive signaitem : Type :=
| signasigna : hashval -> signaitem
| signaparam : hashval -> stp -> signaitem
| signadef : stp -> trm -> signaitem
| signaknown : trm -> signaitem
.

Definition signa : Type := list signaitem.

Definition ser_signaitem (d : signaitem) : list nat :=
match d with
| signasigna h => 0::ser_hashval h
| signaparam h a => 1::ser_hashval h ++ ser_stp a
| signadef a m => 2::ser_stp a ++ ser_trm m
| signaknown p => 3::ser_trm p
end.

Definition hashsignaitem (d : signaitem) : hashval := hashwordlist (4::ser_signaitem d).

Fixpoint ser_signa (dl : signa) : list nat :=
match dl with
| nil => 0::nil
| (d::dr) => 1::ser_signaitem d ++ ser_signa dr
end.

Definition hashsigna (dl : signa) : hashval := hashwordlist (ser_signa dl).

(*** Documents ***)
Inductive docitem : Type :=
| docsign : hashval -> docitem
| docparam : hashval -> stp -> docitem
| docdef : stp -> trm -> docitem
| docknown : trm -> docitem
| docpfof : trm -> pf -> docitem
.

Definition doc : Type := list docitem.

Definition ser_docitem (d : docitem) : list nat :=
match d with
| docsign h => 0::ser_hashval h
| docparam h a => 1::ser_hashval h ++ ser_stp a
| docdef a m => 2::ser_stp a ++ ser_trm m
| docknown p => 3::ser_trm p
| docpfof p d => 4::ser_trm p ++ ser_pf d
end.

Definition hashdocitem (d : docitem) : hashval := hashwordlist (5::ser_docitem d).

Fixpoint ser_doc (dl : doc) : list nat :=
match dl with
| nil => 0::nil
| (d::dr) => 1::ser_docitem d ++ ser_doc dr
end.

Definition hashdoc (dl : doc) : hashval := hashwordlist (ser_doc dl).

Lemma ser_stp_inj_lem a a' l l' : ser_stp a ++ l = ser_stp a' ++ l' -> l = l' /\ a = a'.
revert a' l l'. induction a as [| |n|a IHa b IHb]; intros [| |n'|a' b'] l l' H1; simpl in H1;
           try now (exfalso; inversion H1).
- inversion H1. tauto.
- inversion H1. tauto.
- inversion H1. tauto.
- rewrite <- app_assoc in H1. rewrite <- app_assoc in H1.
  inversion H1.
  destruct (IHa a' _ _ H0) as [H2 H3].
  destruct (IHb b' _ _ H2) as [H4 H5].
  subst l'. subst a'. subst b'. tauto.
Qed.

Lemma ser_stp_inj a a' : ser_stp a = ser_stp a' -> a = a'.
intros H1.
assert (L1: ser_stp a ++ nil = ser_stp a' ++ nil) by congruence.
generalize (ser_stp_inj_lem a a' nil nil L1). tauto.
Qed.

Lemma hashstpinj a a' : hashstp a = hashstp a' -> a = a'.
unfold hashstp. intros H1. apply hashwordlistinj in H1.
- inversion H1.
  exact (ser_stp_inj a a' H0).
- discriminate.
- discriminate.
Qed.

Lemma ser_stp_l_inj_lem al al' l l' : ser_stp_l al ++ l = ser_stp_l al' ++ l' -> l = l' /\ al = al'.
revert al' l l'. induction al as [|a al IH]; intros [|a' al'] l l' H1; simpl in H1;
                 try now (exfalso; inversion H1).
- inversion H1. split; congruence.
- inversion H1. rewrite <- app_assoc in H0. rewrite <- app_assoc in H0.
  destruct (ser_stp_inj_lem a a' _ _ H0) as [H2 H3].
  apply IH in H2. destruct H2 as [H4 H5].
  split; congruence.
Qed.

Lemma ser_trm_inj_lem m m' l l' : ser_trm m ++ l = ser_trm m' ++ l' -> l = l' /\ m = m'.
revert m' l l'. induction m as [n|h al|m IHm n IHn|a m IHm|m IHm n IHn|a m IHm]; intros [n'|h' al'|m' n'|a' m'|m' n'|a' m'] l l' H1; simpl in H1;
           try now (exfalso; inversion H1).
- inversion H1. tauto.
- rewrite <- app_assoc in H1. rewrite <- app_assoc in H1.
  inversion H1.
  destruct (ser_hashval_inj h h' _ _ H0) as [H2 H3].
  apply ser_stp_l_inj_lem in H2. destruct H2 as [H4 H5].
  split; congruence.
- inversion H1. rewrite <- app_assoc in H0. rewrite <- app_assoc in H0.
  destruct (IHm _ _ _ H0) as [H2 H3].
  destruct (IHn _ _ _ H2) as [H4 H5].
  split; congruence.
- inversion H1. rewrite <- app_assoc in H0. rewrite <- app_assoc in H0.
  destruct (ser_stp_inj_lem _ _ _ _ H0) as [H2 H3].
  destruct (IHm _ _ _ H2) as [H4 H5].
  split; congruence.
- inversion H1. rewrite <- app_assoc in H0. rewrite <- app_assoc in H0.
  destruct (IHm _ _ _ H0) as [H2 H3].
  destruct (IHn _ _ _ H2) as [H4 H5].
  split; congruence.
- inversion H1. rewrite <- app_assoc in H0. rewrite <- app_assoc in H0.
  destruct (ser_stp_inj_lem _ _ _ _ H0) as [H2 H3].
  destruct (IHm _ _ _ H2) as [H4 H5].
  split; congruence.
Qed.

Lemma ser_trm_inj m m' : ser_trm m = ser_trm m' -> m = m'.
intros H1.
assert (L1: ser_trm m ++ nil = ser_trm m' ++ nil) by congruence.
generalize (ser_trm_inj_lem m m' nil nil L1). tauto.
Qed.

Lemma hashtrminj m m' : hashtrm m = hashtrm m' -> m = m'.
unfold hashtrm. intros H1. apply hashwordlistinj in H1.
- inversion H1.
  exact (ser_trm_inj m m' H0).
- discriminate.
- discriminate.
Qed.

Lemma hashthtrminj th m th' m' : hashthtrm th m = hashthtrm th' m' -> th = th' /\ m = m'.
unfold hashthtrm. intros H. apply hashopair2inj in H. destruct H as [H1 H2].
apply hashtrminj in H2. split; congruence.
Qed.

Lemma ser_pf_inj_lem d d' l l' : ser_pf d ++ l = ser_pf d' ++ l' -> l = l' /\ d = d'.
revert d' l l'. induction d as [n|h al|d IHd e IHe|d IHd n|n d IHd|a d IHd]; intros [n'|h' al'|d' e'|d' n'|n' d'|a' d'] l l' H1; simpl in H1;
                try now (exfalso; inversion H1).
- inversion H1. tauto.
- rewrite <- app_assoc in H1. rewrite <- app_assoc in H1.
  inversion H1.
  destruct (ser_hashval_inj h h' _ _ H0) as [H2 H3].
  apply ser_stp_l_inj_lem in H2. destruct H2 as [H4 H5].
  split; congruence.
- inversion H1. rewrite <- app_assoc in H0. rewrite <- app_assoc in H0.
  destruct (IHd _ _ _ H0) as [H2 H3].
  destruct (IHe _ _ _ H2) as [H4 H5].
  split; congruence.
- inversion H1. rewrite <- app_assoc in H0. rewrite <- app_assoc in H0.
  destruct (IHd _ _ _ H0) as [H2 H3].
  destruct (ser_trm_inj_lem _ _ _ _ H2) as [H4 H5].
  split; congruence.
- inversion H1. rewrite <- app_assoc in H0. rewrite <- app_assoc in H0.
  destruct (ser_trm_inj_lem _ _ _ _ H0) as [H2 H3].
  destruct (IHd _ _ _ H2) as [H4 H5].
  split; congruence.
- inversion H1. rewrite <- app_assoc in H0. rewrite <- app_assoc in H0.
  destruct (ser_stp_inj_lem _ _ _ _ H0) as [H2 H3].
  destruct (IHd _ _ _ H2) as [H4 H5].
  split; congruence.
Qed.

Lemma ser_pf_inj d d' : ser_pf d = ser_pf d' -> d = d'.
intros H1.
assert (L1: ser_pf d ++ nil = ser_pf d' ++ nil) by congruence.
generalize (ser_pf_inj_lem d d' nil nil L1). tauto.
Qed.

Lemma hashpfinj d d' : hashpf d = hashpf d' -> d = d'.
unfold hashpf. intros H1. apply hashwordlistinj in H1.
- inversion H1.
  exact (ser_pf_inj d d' H0).
- discriminate.
- discriminate.
Qed.

Lemma ser_theoryitem_inj_lem d d' l l' : ser_theoryitem d ++ l = ser_theoryitem d' ++ l' -> l = l' /\ d = d'.
destruct d as [a|a m|p]; destruct d' as [a'|a' m'|p']; simpl; intros H1; try now (exfalso; inversion H1).
- inversion H1.
  destruct (ser_stp_inj_lem _ _ _ _ H0) as [H4 H5].
  split; congruence.
- inversion H1. rewrite <- app_assoc in H0. rewrite <- app_assoc in H0.
  destruct (ser_stp_inj_lem _ _ _ _ H0) as [H2 H3].
  destruct (ser_trm_inj_lem _ _ _ _ H2) as [H4 H5].
  split; congruence.
- inversion H1.
  destruct (ser_trm_inj_lem _ _ _ _ H0) as [H2 H3].
  split; congruence.
Qed.

Lemma ser_theoryitem_inj d d' : ser_theoryitem d = ser_theoryitem d' -> d = d'.
intros H1.
assert (L1: ser_theoryitem d ++ nil = ser_theoryitem d' ++ nil) by congruence.
generalize (ser_theoryitem_inj_lem d d' nil nil L1). tauto.
Qed.

Lemma hashtheoryiteminj d d' : hashtheoryitem d = hashtheoryitem d' -> d = d'.
unfold hashtheoryitem. intros H1. apply hashwordlistinj in H1.
- inversion H1.
  exact (ser_theoryitem_inj d d' H0).
- discriminate.
- discriminate.
Qed.

Lemma ser_theory_inj_lem dl dl' l l' : ser_theory dl ++ l = ser_theory dl' ++ l' -> l = l' /\ dl = dl'.
revert dl' l l'. induction dl as [|d dl IH]; intros [|d' dl'] l l' H1; simpl in H1;
                 try now (exfalso; inversion H1).
- inversion H1. split; congruence.
- inversion H1. rewrite <- app_assoc in H0. rewrite <- app_assoc in H0.
  destruct (ser_theoryitem_inj_lem d d' _ _ H0) as [H2 H3].
  apply IH in H2. destruct H2 as [H4 H5].
  split; congruence.
Qed.

Lemma ser_theory_inj dl dl' : ser_theory dl = ser_theory dl' -> dl = dl'.
intros H1.
assert (L1: ser_theory dl ++ nil = ser_theory dl' ++ nil) by congruence.
generalize (ser_theory_inj_lem dl dl' nil nil L1). tauto.
Qed.

Lemma hashtheoryinj dl dl' : hashtheory dl = hashtheory dl' -> dl = dl'.
unfold hashtheory. intros H1. apply hashwordlistinj in H1.
- inversion H1.
  exact (ser_theory_inj dl dl' H0).
- destruct dl; discriminate.
- destruct dl'; discriminate.
Qed.

Lemma ser_signaitem_inj_lem d d' l l' : ser_signaitem d ++ l = ser_signaitem d' ++ l' -> l = l' /\ d = d'.
destruct d as [h|h a|a m|p]; destruct d' as [h'|h' a'|a' m'|p']; simpl; intros H1; try now (exfalso; inversion H1).
- inversion H1.
  destruct (ser_hashval_inj _ _ _ _ H0) as [H2 H3].
  split; congruence.
- inversion H1. rewrite <- app_assoc in H0. rewrite <- app_assoc in H0.
  destruct (ser_hashval_inj _ _ _ _ H0) as [H2 H3].
  destruct (ser_stp_inj_lem _ _ _ _ H2) as [H4 H5].
  split; congruence.
- inversion H1. rewrite <- app_assoc in H0. rewrite <- app_assoc in H0.
  destruct (ser_stp_inj_lem _ _ _ _ H0) as [H2 H3].
  destruct (ser_trm_inj_lem _ _ _ _ H2) as [H4 H5].
  split; congruence.
- inversion H1.
  destruct (ser_trm_inj_lem _ _ _ _ H0) as [H2 H3].
  split; congruence.
Qed.

Lemma ser_signaitem_inj d d' : ser_signaitem d = ser_signaitem d' -> d = d'.
intros H1.
assert (L1: ser_signaitem d ++ nil = ser_signaitem d' ++ nil) by congruence.
generalize (ser_signaitem_inj_lem d d' nil nil L1). tauto.
Qed.

Lemma hashsignaiteminj d d' : hashsignaitem d = hashsignaitem d' -> d = d'.
unfold hashsignaitem. intros H1. apply hashwordlistinj in H1.
- inversion H1.
  exact (ser_signaitem_inj d d' H0).
- discriminate.
- discriminate.
Qed.

Lemma ser_signa_inj_lem dl dl' l l' : ser_signa dl ++ l = ser_signa dl' ++ l' -> l = l' /\ dl = dl'.
revert dl' l l'. induction dl as [|d dl IH]; intros [|d' dl'] l l' H1; simpl in H1;
                 try now (exfalso; inversion H1).
- inversion H1. split; congruence.
- inversion H1. rewrite <- app_assoc in H0. rewrite <- app_assoc in H0.
  destruct (ser_signaitem_inj_lem d d' _ _ H0) as [H2 H3].
  apply IH in H2. destruct H2 as [H4 H5].
  split; congruence.
Qed.

Lemma ser_signa_inj dl dl' : ser_signa dl = ser_signa dl' -> dl = dl'.
intros H1.
assert (L1: ser_signa dl ++ nil = ser_signa dl' ++ nil) by congruence.
generalize (ser_signa_inj_lem dl dl' nil nil L1). tauto.
Qed.

Lemma hashsignainj dl dl' : hashsigna dl = hashsigna dl' -> dl = dl'.
unfold hashsigna. intros H1. apply hashwordlistinj in H1.
- inversion H1.
  exact (ser_signa_inj dl dl' H0).
- destruct dl; discriminate.
- destruct dl'; discriminate.
Qed.

Lemma ser_docitem_inj_lem d d' l l' : ser_docitem d ++ l = ser_docitem d' ++ l' -> l = l' /\ d = d'.
destruct d as [h|h a|a m|p|p d]; destruct d' as [h'|h' a'|a' m'|p'|p' d']; simpl; intros H1; try now (exfalso; inversion H1).
- inversion H1.
  destruct (ser_hashval_inj _ _ _ _ H0) as [H2 H3].
  split; congruence.
- inversion H1. rewrite <- app_assoc in H0. rewrite <- app_assoc in H0.
  destruct (ser_hashval_inj _ _ _ _ H0) as [H2 H3].
  destruct (ser_stp_inj_lem _ _ _ _ H2) as [H4 H5].
  split; congruence.
- inversion H1. rewrite <- app_assoc in H0. rewrite <- app_assoc in H0.
  destruct (ser_stp_inj_lem _ _ _ _ H0) as [H2 H3].
  destruct (ser_trm_inj_lem _ _ _ _ H2) as [H4 H5].
  split; congruence.
- inversion H1.
  destruct (ser_trm_inj_lem _ _ _ _ H0) as [H2 H3].
  split; congruence.
- inversion H1. rewrite <- app_assoc in H0. rewrite <- app_assoc in H0.
  destruct (ser_trm_inj_lem _ _ _ _ H0) as [H2 H3].
  destruct (ser_pf_inj_lem _ _ _ _ H2) as [H4 H5].
  split; congruence.
Qed.

Lemma ser_docitem_inj d d' : ser_docitem d = ser_docitem d' -> d = d'.
intros H1.
assert (L1: ser_docitem d ++ nil = ser_docitem d' ++ nil) by congruence.
generalize (ser_docitem_inj_lem d d' nil nil L1). tauto.
Qed.

Lemma hashdociteminj d d' : hashdocitem d = hashdocitem d' -> d = d'.
unfold hashdocitem. intros H1. apply hashwordlistinj in H1.
- inversion H1.
  exact (ser_docitem_inj d d' H0).
- discriminate.
- discriminate.
Qed.

Lemma ser_doc_inj_lem dl dl' l l' : ser_doc dl ++ l = ser_doc dl' ++ l' -> l = l' /\ dl = dl'.
revert dl' l l'. induction dl as [|d dl IH]; intros [|d' dl'] l l' H1; simpl in H1;
                 try now (exfalso; inversion H1).
- inversion H1. split; congruence.
- inversion H1. rewrite <- app_assoc in H0. rewrite <- app_assoc in H0.
  destruct (ser_docitem_inj_lem d d' _ _ H0) as [H2 H3].
  apply IH in H2. destruct H2 as [H4 H5].
  split; congruence.
Qed.

Lemma ser_doc_inj dl dl' : ser_doc dl = ser_doc dl' -> dl = dl'.
intros H1.
assert (L1: ser_doc dl ++ nil = ser_doc dl' ++ nil) by congruence.
generalize (ser_doc_inj_lem dl dl' nil nil L1). tauto.
Qed.

Lemma hashdocinj dl dl' : hashdoc dl = hashdoc dl' -> dl = dl'.
unfold hashdoc. intros H1. apply hashwordlistinj in H1.
- inversion H1.
  exact (ser_doc_inj dl dl' H0).
- destruct dl; discriminate.
- destruct dl'; discriminate.
Qed.

Definition stp_eq_dec (a a' : stp) : {a = a'} + {a <> a'}.
repeat decide equality.
Defined.

Definition trm_eq_dec (m m' : trm) : {m = m'} + {m <> m'}.
repeat decide equality. apply hashval_eq_dec.
Defined.

Definition pf_eq_dec (d d' : pf) : {d = d'} + {d <> d'}.
repeat decide equality; apply hashval_eq_dec.
Defined.

Definition theoryitem_eq_dec (d d':theoryitem) : {d = d'} + {d <> d'}.
destruct d as [a|a m|p]; destruct d' as [a'|a' m'|p']; try (right; discriminate).
- repeat decide equality; try apply hashval_eq_dec.
- repeat decide equality; try apply hashval_eq_dec.
- repeat decide equality; try apply hashval_eq_dec.
Defined.

Definition theory_eq_dec (dl dl':theory) : {dl = dl'} + {dl <> dl'}.
revert dl'. induction dl as [|d dl IH]; intros [|d' dl']; try (right; discriminate).
- left. reflexivity.
- destruct (theoryitem_eq_dec d d') as [D1|D1].
  + destruct (IH dl') as [D2|D2].
    * left. congruence.
    * right. intros H1. inversion H1. tauto.
  + right. intros H1. inversion H1. tauto.
Defined.

Definition signaitem_eq_dec (d d':signaitem) : {d = d'} + {d <> d'}.
destruct d as [h|h a|a m|p]; destruct d' as [h'|h' a'|a' m'|p']; try (right; discriminate).
- repeat decide equality; try apply hashval_eq_dec.
- repeat decide equality; try apply hashval_eq_dec.
- repeat decide equality; try apply hashval_eq_dec.
- repeat decide equality; try apply hashval_eq_dec.
Defined.

Definition signa_eq_dec (dl dl':signa) : {dl = dl'} + {dl <> dl'}.
revert dl'. induction dl as [|d dl IH]; intros [|d' dl']; try (right; discriminate).
- left. reflexivity.
- destruct (signaitem_eq_dec d d') as [D1|D1].
  + destruct (IH dl') as [D2|D2].
    * left. congruence.
    * right. intros H1. inversion H1. tauto.
  + right. intros H1. inversion H1. tauto.
Defined.

Definition docitem_eq_dec (d d':docitem) : {d = d'} + {d <> d'}.
destruct d as [h|h a|a m|p|p d]; destruct d' as [h'|h' a'|a' m'|p'|p' d']; try (right; discriminate).
- repeat decide equality; try apply hashval_eq_dec.
- repeat decide equality; try apply hashval_eq_dec.
- repeat decide equality; try apply hashval_eq_dec.
- repeat decide equality; try apply hashval_eq_dec.
- repeat decide equality; try apply hashval_eq_dec.
Defined.

Definition doc_eq_dec (dl dl':doc) : {dl = dl'} + {dl <> dl'}.
revert dl'. induction dl as [|d dl IH]; intros [|d' dl']; try (right; discriminate).
- left. reflexivity.
- destruct (docitem_eq_dec d d') as [D1|D1].
  + destruct (IH dl') as [D2|D2].
    * left. congruence.
    * right. intros H1. inversion H1. tauto.
  + right. intros H1. inversion H1. tauto.
Defined.

Fixpoint signa_uses_objs (dl:signa) : list hashval :=
match dl with
| signaparam h _::dr => h::signa_uses_objs dr
| _::dr => signa_uses_objs dr
| nil => nil
end.

Fixpoint signa_uses_props (th:option hashval) (dl:signa) : list hashval :=
match dl with
| signaknown p::dr => hashthtrm th p::signa_uses_props th dr
| _::dr => signa_uses_props th dr
| nil => nil
end.

Fixpoint doc_uses_objs (dl:doc) : list hashval :=
match dl with
| docparam h _::dr => h::doc_uses_objs dr
| _::dr => doc_uses_objs dr
| nil => nil
end.

Fixpoint doc_uses_props (th:option hashval) (dl:doc) : list hashval :=
match dl with
| docknown p::dr => hashthtrm th p::doc_uses_props th dr
| _::dr => doc_uses_props th dr
| nil => nil
end.

(*** type checking and proof checking, left abstract here ***)
Parameter trm_tp_p : theory -> signa -> trm -> stp -> Prop.
Parameter pf_trm_p : theory -> signa -> pf -> trm -> Prop.

