(** Copyright (c) 2015 Bill White **)
(** Distributed under the MIT/X11 software license **)
(** See http://www.opensource.org/licenses/mit-license.php **)

(** MathData: Representation of the data part of higher-order logic
    (simple types, typed terms, proof terms) without the checking.
    This is following Egal by representing 'global definitions' by hash values.
    There are functions computing when a term or proof uses a global definition,
    and functions computing when a proof uses a "known" (a hash of a proposition
    which is either an axiom or previously proven proposition).
 **)

Require Export CryptoSignatures.

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

Fixpoint hashstp (a:stp) : hashval :=
match a with
| prop => hashnat 0
| ind => hashnat 1
| tvar n => hashpair (hashnat 0) (hashnat n)
| sar a1 a2 => hashpair (hashnat 1) (hashpair (hashstp a1) (hashstp a2))
end.

Fixpoint hashtrm (m:trm) : hashval :=
match m with
| Db n => hashpair (hashnat 0) (hashnat n)
| Gn h al => hashlist (hashnat 1::h::map hashstp al)
| Ap m n => hashpair (hashnat 2) (hashpair (hashtrm m) (hashtrm n))
| La a m => hashpair (hashnat 3) (hashpair (hashstp a) (hashtrm m))
| Imp m n => hashpair (hashnat 4) (hashpair (hashtrm m) (hashtrm n))
| All a m => hashpair (hashnat 5) (hashpair (hashstp a) (hashtrm m))
end.

Fixpoint hashpf (d:pf) : hashval :=
match d with
| PDb n => hashpair (hashnat 0) (hashnat n)
| Gpn h al => hashlist (hashnat 1::h::map hashstp al)
| PAp d e => hashpair (hashnat 2) (hashpair (hashpf d) (hashpf e))
| TAp d n => hashpair (hashnat 3) (hashpair (hashpf d) (hashtrm n))
| PLa p d => hashpair (hashnat 4) (hashpair (hashtrm p) (hashpf d))
| TLa a d => hashpair (hashnat 5) (hashpair (hashstp a) (hashpf d))
end.

Parameter trm_tp_p : trm -> stp -> Prop.
Parameter pf_trm_p : pf -> trm -> Prop.

Inductive dataitem : Type :=
| dataparam : hashval -> stp -> dataitem
| datadef : stp -> trm -> dataitem
| dataknown : trm -> dataitem
| datapfof : trm -> pf -> dataitem
.

Definition data : Type := list dataitem.

Definition hashdataitem (d : dataitem) : hashval :=
match d with
| dataparam h a => hashpair (hashnat 0) (hashpair h (hashstp a))
| datadef a m => hashpair (hashnat 1) (hashpair (hashstp a) (hashtrm m))
| dataknown p => hashpair (hashnat 2) (hashtrm p)
| datapfof p d => hashpair (hashnat 3) (hashpair (hashtrm p) (hashpf d))
end.

Definition hashdata (dl : data) : hashval := hashlist (map hashdataitem dl).

Lemma hashstpinj a a' : hashstp a = hashstp a' -> a = a'.
revert a'. induction a as [| |n|a IHa b IHb]; intros [| |n'|a' b'] H1; simpl in H1;
           try (exfalso; apply hashnatinj in H1; omega);
           try (exfalso; revert H1; apply hashnatpairdiscr);
           try (exfalso; symmetry in H1; revert H1; apply hashnatpairdiscr);
           try (exfalso; apply hashpairinj in H1; destruct H1 as [H1 _]; apply hashnatinj in H1; omega).
- reflexivity.
- reflexivity.
- apply hashpairinj in H1. destruct H1 as [_ H1]. apply hashnatinj in H1.
  congruence.
- apply hashpairinj in H1. destruct H1 as [_ H1].
  apply hashpairinj in H1. destruct H1 as [H2 H3].
  apply IHa in H2. apply IHb in H3.
  congruence.
Qed.

Lemma hashtrminj m m' : hashtrm m = hashtrm m' -> m = m'.
revert m'. induction m as [n|h al|m IHm n IHn|a m IHm|m IHm n IHn|a m IHm]; intros [n'|h' al'|m' n'|a' m'|m' n'|a' m'] H1; simpl in H1;
           try (exfalso; apply hashpairinj in H1; destruct H1 as [H1 _]; apply hashnatinj in H1; omega).
- apply hashpairinj in H1. destruct H1 as [_ H1]. apply hashnatinj in H1.
  congruence.
- apply hashpairinj in H1. destruct H1 as [_ H1].
  apply hashpairinj in H1. destruct H1 as [H2 H3].
  apply hashlistinj in H3. apply hashmapinj in H3.
  + congruence.
  + exact hashstpinj.
- apply hashpairinj in H1. destruct H1 as [_ H1].
  apply hashpairinj in H1. destruct H1 as [H2 H3].
  apply IHm in H2. apply IHn in H3.
  congruence.
- apply hashpairinj in H1. destruct H1 as [_ H1].
  apply hashpairinj in H1. destruct H1 as [H2 H3].
  apply hashstpinj in H2. apply IHm in H3.
  congruence.
- apply hashpairinj in H1. destruct H1 as [_ H1].
  apply hashpairinj in H1. destruct H1 as [H2 H3].
  apply IHm in H2. apply IHn in H3.
  congruence.
- apply hashpairinj in H1. destruct H1 as [_ H1].
  apply hashpairinj in H1. destruct H1 as [H2 H3].
  apply hashstpinj in H2. apply IHm in H3.
  congruence.
Qed.

Lemma hashpfinj d d' : hashpf d = hashpf d' -> d = d'.
revert d'. induction d as [n|h al|d IHd e IHe|d IHd n|n d IHd|a d IHd]; intros [n'|h' al'|d' e'|d' n'|n' d'|a' d'] H1; simpl in H1;
           try (exfalso; apply hashpairinj in H1; destruct H1 as [H1 _]; apply hashnatinj in H1; omega).
- apply hashpairinj in H1. destruct H1 as [_ H1]. apply hashnatinj in H1.
  congruence.
- apply hashpairinj in H1. destruct H1 as [_ H1].
  apply hashpairinj in H1. destruct H1 as [H2 H3].
  apply hashlistinj in H3. apply hashmapinj in H3.
  + congruence.
  + exact hashstpinj.
- apply hashpairinj in H1. destruct H1 as [_ H1].
  apply hashpairinj in H1. destruct H1 as [H2 H3].
  apply IHd in H2. apply IHe in H3.
  congruence.
- apply hashpairinj in H1. destruct H1 as [_ H1].
  apply hashpairinj in H1. destruct H1 as [H2 H3].
  apply IHd in H2. apply hashtrminj in H3.
  congruence.
- apply hashpairinj in H1. destruct H1 as [_ H1].
  apply hashpairinj in H1. destruct H1 as [H2 H3].
  apply hashtrminj in H2. apply IHd in H3.
  congruence.
- apply hashpairinj in H1. destruct H1 as [_ H1].
  apply hashpairinj in H1. destruct H1 as [H2 H3].
  apply hashstpinj in H2. apply IHd in H3.
  congruence.
Qed.

Lemma hashdataiteminj d d' : hashdataitem d = hashdataitem d' -> d = d'.
destruct d as [h a|a m|p|p d]; destruct d' as [h' a'|a' m'|p'|p' d']; simpl; intros H1; try (exfalso; apply hashpairinj in H1; destruct H1 as [H1 _]; apply hashnatinj in H1; omega).
- apply hashpairinj in H1. destruct H1 as [_ H1].
  apply hashpairinj in H1. destruct H1 as [H2 H3].
  apply hashstpinj in H3.
  congruence.
- apply hashpairinj in H1. destruct H1 as [_ H1].
  apply hashpairinj in H1. destruct H1 as [H2 H3].
  apply hashstpinj in H2.
  apply hashtrminj in H3.
  congruence.
- apply hashpairinj in H1. destruct H1 as [_ H1].
  apply hashtrminj in H1.
  congruence.
- apply hashpairinj in H1. destruct H1 as [_ H1].
  apply hashpairinj in H1. destruct H1 as [H2 H3].
  apply hashtrminj in H2.
  apply hashpfinj in H3.
  congruence.
Qed.

Lemma hashdatainj dl dl' : hashdata dl = hashdata dl' -> dl = dl'.
intros H1. apply hashlistinj in H1. apply hashmapinj in H1.
- exact H1.
- exact hashdataiteminj.
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

Definition dataitem_eq_dec (d d':dataitem) : {d = d'} + {d <> d'}.
destruct d as [h a|a m|p|p d]; destruct d' as [h' a'|a' m'|p'|p' d']; try (right; discriminate).
- repeat decide equality; try apply hashval_eq_dec.
- repeat decide equality; try apply hashval_eq_dec.
- repeat decide equality; try apply hashval_eq_dec.
- repeat decide equality; try apply hashval_eq_dec.
Defined.

Definition data_eq_dec (dl dl':data) : {dl = dl'} + {dl <> dl'}.
revert dl'. induction dl as [|d dl IH]; intros [|d' dl']; try (right; discriminate).
- left. reflexivity.
- destruct (dataitem_eq_dec d d') as [D1|D1].
  + destruct (IH dl') as [D2|D2].
    * left. congruence.
    * right. intros H1. inversion H1. tauto.
  + right. intros H1. inversion H1. tauto.
Defined.

Fixpoint data_uses_objs (dl:data) : list hashval :=
match dl with
| dataparam h _::dr => h::data_uses_objs dr
| _::dr => data_uses_objs dr
| nil => nil
end.

Fixpoint data_uses_props (dl:data) : list hashval :=
match dl with
| dataknown p::dr => hashtrm p::data_uses_props dr
| _::dr => data_uses_props dr
| nil => nil
end.

