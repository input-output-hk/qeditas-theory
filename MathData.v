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

Require Export CryptoSignatures.

Inductive stp : Type :=
| prop : stp
| base : nat -> stp
| tvar : nat -> stp
| sar : stp -> stp -> stp.

Inductive trm : Type :=
| Gn : hashval -> trm
| Prm : nat -> list stp -> trm
| Db : nat -> trm
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
| base n => (1::n::nil)
| tvar n => (2::n::nil)
| sar a1 a2 => (3::ser_stp a1) ++ ser_stp a2
end.

Fixpoint hashstp (a:stp) : hashval :=
  match a with
    | prop => hashpair (hashnat 0) (hashnat 0)
    | base n => hashpair (hashnat 1) (hashnat n)
    | tvar n => hashpair (hashnat 2) (hashnat n)
    | sar a1 a2 => hashpair (hashnat 3) (hashpair (hashstp a1) (hashstp a2))
  end.

Fixpoint ser_stp_l al : list nat :=
match al with
| nil => (0::nil)
| (a::ar) => (1::ser_stp a) ++ ser_stp_l ar
end.

Fixpoint hashstpl (al:list stp) : option hashval :=
  match al with
    | nil => None
    | a::ar => Some (hashopair1 (hashstp a) (hashstpl ar))
  end.

Fixpoint ser_trm (m:trm) : list nat :=
match m with
| Gn h => 0::ser_hashval h
| Prm n al => 1::n::ser_stp_l al
| Db n => 2::n::nil
| Ap m n => 3::(ser_trm m) ++ (ser_trm n)
| La a m => 4::(ser_stp a) ++ (ser_trm m)
| Imp m n => 5::(ser_trm m) ++ (ser_trm n)
| All a m => 6::(ser_stp a) ++ (ser_trm m)
end.

(*** hashtrm - injective function from trm into hashval.
 This should not be confused with trm_hashroot below.
 ***)
Fixpoint hashtrm (m:trm) : hashval :=
match m with
| Gn h => hashpair (hashnat 4) h
| Prm i al => hashpair (hashnat 5) (hashopair1 (hashnat i) (hashstpl al))
| Db n => hashpair (hashnat 6) (hashnat n)
| Ap m n => hashpair (hashnat 7) (hashpair (hashtrm m) (hashtrm n))
| La a m => hashpair (hashnat 8) (hashpair (hashstp a) (hashtrm m))
| Imp m n => hashpair (hashnat 9) (hashpair (hashtrm m) (hashtrm n))
| All a m => hashpair (hashnat 10) (hashpair (hashstp a) (hashtrm m))
end.

(***
 This computes a hashroot for a trm relative to a theory.
 We need to have separate identifiers for the same term in different theories, especially for conjectures with bounties.
 Note that this is by design not injective since Gn's may abbreviate terms by giving their hashroot explicitly.
 hashtrm should be used when injectivity is needed.
 trm_hashroot will determine addresses where information about the trm is stored, and for POR purposes.
 ***)
Fixpoint trm_hashroot (th:option hashval) (m:trm) : hashval :=
  match m with
    | Gn h => h
    | Prm i al => hashopair2 th (hashpair (hashnat 11) (hashopair1 (hashnat i) (hashstpl al)))
    | Db i => hashopair2 th (hashpair (hashnat 12) (hashnat i))
    | Ap m n => hashopair2 th (hashpair (hashnat 13) (hashpair (trm_hashroot th m) (trm_hashroot th n)))
    | La a m => hashopair2 th (hashpair (hashnat 14) (hashpair (hashstp a) (trm_hashroot th m)))
    | Imp m n => hashopair2 th (hashpair (hashnat 15) (hashpair (trm_hashroot th m) (trm_hashroot th n)))
    | All a m => hashopair2 th (hashpair (hashnat 16) (hashpair (hashstp a) (trm_hashroot th m)))
  end.

Fixpoint ser_pf (d:pf) : list nat :=
match d with
| PDb n => 0::n::nil
| Gpn h al => 1::(ser_hashval h) ++ ser_stp_l al
| PAp d e => 2::(ser_pf d) ++ (ser_pf e)
| TAp d n => 3::(ser_pf d) ++ (ser_trm n)
| PLa p d => 4::(ser_trm p) ++ (ser_pf d)
| TLa a d => 5::(ser_stp a) ++ (ser_pf d)
end.

(*** This hashes a proof term. ***)
Fixpoint hashpf (d:pf) : hashval :=
match d with
| PDb n => hashpair (hashnat 17) (hashnat n)
| Gpn h al => hashpair (hashnat 18) (hashopair1 h (hashstpl al))
| PAp d e => hashpair (hashnat 19) (hashpair (hashpf d) (hashpf e))
| TAp d n => hashpair (hashnat 20) (hashpair (hashpf d) (hashtrm n))
| PLa p d => hashpair (hashnat 21) (hashpair (hashtrm p) (hashpf d))
| TLa a d => hashpair (hashnat 22) (hashpair (hashstp a) (hashpf d))
end.

(*** This computes a hashroot for a proof term relative to a theory. ***)
Fixpoint pf_hashroot (th:option hashval) (d:pf) : hashval :=
  match d with
    | PDb i => hashopair2 th (hashpair (hashnat 23) (hashnat i))
    | Gpn h al => hashopair2 th (hashpair (hashnat 24) (hashopair1 h (hashstpl al)))
    | PAp d e => hashopair2 th (hashpair (hashnat 25) (hashpair (pf_hashroot th d) (pf_hashroot th e)))
    | TAp d n => hashopair2 th (hashpair (hashnat 26) (hashpair (pf_hashroot th d) (trm_hashroot th n)))
    | PLa p d => hashopair2 th (hashpair (hashnat 27) (hashpair (trm_hashroot th p) (pf_hashroot th d)))
    | TLa a d => hashopair2 th (hashpair (hashnat 28) (hashpair (hashstp a) (pf_hashroot th d)))
  end.

(*** Theory (primitives and axioms, possibly with some helper definitions. No Gn should be here.) ***)
Inductive theoryitem : Type :=
| thyprim : stp -> theoryitem
| thyaxiom : trm -> theoryitem
.

(*** A theory is given as a stack of declarations. The first to be checked is at the end of the list. ***)
Definition theoryspec : Type := list theoryitem.

(*** The essential information we need to retrain about a theory consists of two parts:
 1. A list giving the stp of each primitive (Prm).
 2. A list giving hashvals of axioms.
 ***)
Definition theory : Type := prod (list stp) (list hashval).

Fixpoint theoryspec_primtps (thy:theoryspec) : list stp :=
  match thy with
    | nil => nil
    | thyprim a::thy => theoryspec_primtps thy ++ (a::nil)
    | _::thy => theoryspec_primtps thy
  end.

Definition hashtheoryitem (d:theoryitem) : hashval :=
match d with
| thyprim a => hashpair (hashnat 29) (hashstp a)
| thyaxiom p => hashpair (hashnat 30) (hashtrm p)
end.

Definition hashtheoryspec (dl : theoryspec) : hashval := hashlist (map hashtheoryitem dl).

Fixpoint theoryspec_hashroot (thy:theoryspec) : option hashval :=
match thy with
| nil => None
| thyprim a::thy => Some(hashopair1 (hashpair (hashnat 31) (hashstp a)) (theoryspec_hashroot thy))
| thyaxiom p::thy => Some(hashopair1 (hashpair (hashnat 32) (trm_hashroot None p)) (theoryspec_hashroot thy))
end.

Definition hashtheory (thy:theory) : option hashval :=
  match thy with
    | (nil,nil) => None
    | (al,hl) => Some(hashpair (hashlist (map hashstp al)) (hashlist hl))
  end.

Fixpoint theoryspec_hashedaxioms (h:option hashval) (thy:theoryspec) : list hashval :=
  match thy with
    | nil => nil
    | thyaxiom p::thy => trm_hashroot h p::theoryspec_hashedaxioms h thy
    | _::thy => theoryspec_hashedaxioms h thy
  end.

Definition theoryspec_theory (thy:theoryspec) : theory :=
  (theoryspec_primtps thy,theoryspec_hashedaxioms (theoryspec_hashroot thy) thy).

Definition ser_theoryitem (d : theoryitem) : list nat :=
match d with
| thyprim a => 1::ser_stp a
| thyaxiom p => 2::ser_trm p
end.

Fixpoint ser_theoryspec (dl : theoryspec) : list nat :=
match dl with
| nil => 0::nil
| (d::dr) => 1::ser_theoryitem d ++ ser_theoryspec dr
end.

(*** Signatures (parameters, definitions and knowns that can be imported into a document) ***)
Inductive signaitem : Type :=
| signasigna : hashval -> signaitem
| signaparam : hashval -> stp -> signaitem
| signadef : stp -> trm -> signaitem
| signaknown : trm -> signaitem
.

(*** A signature is given as a stack of declarations. The first to be checked is at the end of the list. ***)
Definition signaspec : Type := list signaitem.

Definition gsigna : Type := prod (list (prod hashval (prod stp (option trm)))) (list hashval).

Definition signa : Type := prod (list hashval) gsigna.

Definition ser_signaitem (d : signaitem) : list nat :=
match d with
| signasigna h => 0::ser_hashval h
| signaparam h a => 1::ser_hashval h ++ ser_stp a
| signadef a m => 2::ser_stp a ++ ser_trm m
| signaknown p => 3::ser_trm p
end.

Fixpoint ser_signaspec (dl : signaspec) : list nat :=
match dl with
| nil => 0::nil
| (d::dr) => 1::ser_signaitem d ++ ser_signaspec dr
end.

Definition hashsignaitem (d:signaitem) : hashval :=
match d with
  | signasigna h => hashpair (hashnat 33) h
  | signaparam h a => hashpair (hashnat 34) (hashpair h (hashstp a))
  | signadef a m => hashpair (hashnat 35) (hashpair (hashstp a) (hashtrm m))
  | signaknown p => hashpair (hashnat 36) (hashtrm p)
end.

Definition hashsignaspec (dl : signaspec) : hashval := hashlist (map hashsignaitem dl).

Fixpoint signaspec_hashroot (th:option hashval) (dl : signaspec) : hashval :=
  match dl with
    | nil => hashpair (hashnat 37) (hashnat 0)
    | signasigna h::dr => hashpair (hashnat 38) (hashpair h (signaspec_hashroot th dr))
    | signaparam h a::dr => hashpair (hashnat 39) (hashpair h (hashpair (hashstp a) (signaspec_hashroot th dr)))
    | signadef a m::dr => hashpair (hashnat 40) (hashpair (hashstp a) (hashpair (trm_hashroot th m) (signaspec_hashroot th dr)))
    | signaknown p::dr => hashpair (hashnat 41) (hashpair (trm_hashroot th p) (signaspec_hashroot th dr))
  end.

Definition hashgsigna (th:option hashval) (s : gsigna) : hashval :=
  match s with
    | (tl',kl) => hashpair (hashlist (map (fun z =>
                                            match z with
                                              | (h,(a,None)) => hashpair (hashnat 42) (hashpair h (hashstp a))
                                              | (h,(a,Some(m))) => hashpair (hashnat 43) (hashpair h (hashpair (hashstp a) (trm_hashroot th m)))
                                            end)
                                         tl'))
                          (hashlist kl)
  end.

Definition hashsigna (th:option hashval) (s : signa) : hashval :=
  match s with
    | (sl,(tl',kl)) => hashpair (hashlist sl) (hashgsigna th (tl',kl))
  end.

Fixpoint signaspec_trms (th:option hashval) (s:signaspec) : list (prod hashval (prod stp (option trm))) :=
  match s with
    | nil => nil
    | signaparam h a::s => (h,(a,None))::signaspec_trms th s
    | signadef a m::s => (trm_hashroot th m,(a,Some(m)))::signaspec_trms th s
    | _::s => signaspec_trms th s
  end.

Fixpoint signaspec_knowns (th:option hashval) (s:signaspec) : list hashval :=
  match s with
    | nil => nil
    | signaknown p::s => trm_hashroot th p::signaspec_knowns th s
    | _::s => signaspec_knowns th s
  end.

Fixpoint signaspec_signas (s:signaspec) : list hashval :=
  match s with
    | nil => nil
    | signasigna h::s => h::signaspec_signas s
    | _::s => signaspec_signas s
  end.

Definition signaspec_signa (th:option hashval) (s:signaspec) : signa :=
(signaspec_signas s,(signaspec_trms th s,signaspec_knowns th s)).

(*** Documents ***)
Inductive docitem : Type :=
| docsigna : hashval -> docitem
| docparam : hashval -> stp -> docitem
| docdef : stp -> trm -> docitem
| docknown : trm -> docitem
| docpfof : trm -> pf -> docitem
.

(*** A doc is given as a stack of declarations. The first to be checked is at the end of the list. ***)
Definition doc : Type := list docitem.

Definition ser_docitem (d : docitem) : list nat :=
match d with
| docsigna h => 0::ser_hashval h
| docparam h a => 1::ser_hashval h ++ ser_stp a
| docdef a m => 2::ser_stp a ++ ser_trm m
| docknown p => 3::ser_trm p
| docpfof p d => 4::ser_trm p ++ ser_pf d
end.

Fixpoint ser_doc (dl : doc) : list nat :=
match dl with
| nil => 0::nil
| (d::dr) => 1::ser_docitem d ++ ser_doc dr
end.

Definition hashdocitem (d : docitem) : hashval :=
match d with
| docsigna h => hashpair (hashnat 44) h
| docparam h a => hashpair (hashnat 45) (hashpair h (hashstp a))
| docdef a m => hashpair (hashnat 46) (hashpair (hashstp a) (hashtrm m))
| docknown p => hashpair (hashnat 47) (hashtrm p)
| docpfof p d => hashpair (hashnat 48) (hashpair (hashtrm p) (hashpf d))
end.

Definition hashdoc (dl : doc) : hashval := hashlist (map hashdocitem dl).

Definition docitem_hashroot (th:option hashval) (d : docitem) : hashval :=
match d with
| docsigna h => hashpair (hashnat 49) h
| docparam h a => hashpair (hashnat 50) (hashpair h (hashstp a))
| docdef a m => hashpair (hashnat 51) (hashpair (hashstp a) (trm_hashroot th m))
| docknown p => hashpair (hashnat 52) (trm_hashroot th p)
| docpfof p d => hashpair (hashnat 53) (hashpair (trm_hashroot th p) (pf_hashroot th d))
end.

Definition doc_hashroot (th:option hashval) (dl : doc) : hashval := hashlist (map (docitem_hashroot th) dl).

Lemma doc_hashroot_nil_eq th :
  doc_hashroot th nil = hashnat 0.
reflexivity.
Qed.

Lemma doc_hashroot_cons_eq th d dl :
  doc_hashroot th (d::dl) = hashpair (docitem_hashroot th d) (doc_hashroot th dl).
reflexivity.
Qed.

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
revert a'. induction a as [|i|n|a IHa b IHb]; intros [|i'|n'|a' b'] H1; simpl in H1;
           try (exfalso; apply hashnatinj in H1; omega);
           try (exfalso; revert H1; apply hashnatpairdiscr);
           try (exfalso; symmetry in H1; revert H1; apply hashnatpairdiscr);
           try (exfalso; apply hashpairinj in H1; destruct H1 as [H1 _]; apply hashnatinj in H1; omega).
- reflexivity.
- apply hashpairinj in H1. destruct H1 as [_ H1]. apply hashnatinj in H1.
  congruence.
- apply hashpairinj in H1. destruct H1 as [_ H1]. apply hashnatinj in H1.
  congruence.
- apply hashpairinj in H1. destruct H1 as [_ H1].
  apply hashpairinj in H1. destruct H1 as [H2 H3].
  apply IHa in H2. apply IHb in H3.
  congruence.
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

Inductive partialdoc : Type :=
| pdoc_nil : partialdoc
| pdoc_hash : hashval -> partialdoc
| pdoc_signa : hashval -> partialdoc -> partialdoc
| pdoc_param : hashval -> stp -> partialdoc -> partialdoc
| pdoc_param_hash : hashval -> partialdoc -> partialdoc
| pdoc_def : stp -> trm -> partialdoc -> partialdoc
| pdoc_def_hash : hashval -> partialdoc -> partialdoc
| pdoc_known : trm -> partialdoc -> partialdoc
| pdoc_pfof : trm -> pf -> partialdoc -> partialdoc
| pdoc_pfof_hash : hashval -> partialdoc -> partialdoc
.

Fixpoint partialdoc_hashroot (th:option hashval) (d : partialdoc) : hashval :=
match d with
| pdoc_nil => hashnat 0
| pdoc_hash h => h
| pdoc_signa h dr => hashpair (hashpair (hashnat 49) h) (partialdoc_hashroot th dr)
| pdoc_param h a dr => hashpair (hashpair (hashnat 50) (hashpair h (hashstp a))) (partialdoc_hashroot th dr)
| pdoc_param_hash h dr => hashpair (hashpair (hashnat 50) h) (partialdoc_hashroot th dr)
| pdoc_def a m dr => hashpair (hashpair (hashnat 51) (hashpair (hashstp a) (trm_hashroot th m))) (partialdoc_hashroot th dr)
| pdoc_def_hash h dr => hashpair (hashpair (hashnat 51) h) (partialdoc_hashroot th dr)
| pdoc_known p dr => hashpair (hashpair (hashnat 52) (trm_hashroot th p)) (partialdoc_hashroot th dr)
| pdoc_pfof p d dr => hashpair (hashpair (hashnat 53) (hashpair (trm_hashroot th p) (pf_hashroot th d))) (partialdoc_hashroot th dr)
| pdoc_pfof_hash h dr => hashpair (hashpair (hashnat 53) h) (partialdoc_hashroot th dr)
end.

Inductive doc_approx (th:option hashval) : partialdoc -> doc -> Prop :=
| doc_approx_nil : doc_approx th pdoc_nil nil
| doc_approx_hash h d : doc_hashroot th d = h -> doc_approx th (pdoc_hash h) d
| doc_approx_signa h dr dr': doc_approx th dr dr' -> doc_approx th (pdoc_signa h dr) (docsigna h::dr')
| doc_approx_param h a dr dr' : doc_approx th dr dr' -> doc_approx th (pdoc_param h a dr) (docparam h a::dr')
| doc_approx_param_hash h a dr dr' : doc_approx th dr dr' -> doc_approx th (pdoc_param_hash (hashpair h (hashstp a)) dr) (docparam h a::dr')
| doc_approx_def a m m' dr dr' : trm_hashroot th m = trm_hashroot th m' -> doc_approx th dr dr' -> doc_approx th (pdoc_def a m dr) (docdef a m'::dr')
| doc_approx_def_hash a m dr dr' : doc_approx th dr dr' -> doc_approx th (pdoc_def_hash (hashpair (hashstp a) (trm_hashroot th m)) dr) (docdef a m::dr')
| doc_approx_known p p' dr dr' : trm_hashroot th p = trm_hashroot th p' -> doc_approx th dr dr' -> doc_approx th (pdoc_known p dr) (docknown p'::dr')
| doc_approx_pfof p d p' d' dr dr' : trm_hashroot th p = trm_hashroot th p' -> pf_hashroot th d = pf_hashroot th d' -> doc_approx th dr dr' -> doc_approx th (pdoc_pfof p d dr) (docpfof p' d'::dr')
| doc_approx_pfof_hash p d dr dr' : doc_approx th dr dr' -> doc_approx th (pdoc_pfof_hash (hashpair (trm_hashroot th p) (pf_hashroot th d)) dr) (docpfof p d::dr')
.

Lemma doc_approx_hashroot_eq th dl dl' :
  doc_approx th dl dl' <-> partialdoc_hashroot th dl = doc_hashroot th dl'.
split.
- intros H1. induction H1.
  + simpl. reflexivity.
  + simpl. congruence.
  + simpl. rewrite IHdoc_approx. reflexivity.
  + simpl. rewrite IHdoc_approx. reflexivity.
  + simpl. rewrite IHdoc_approx. reflexivity.
  + simpl. rewrite IHdoc_approx. rewrite doc_hashroot_cons_eq. simpl. congruence.
  + simpl. rewrite IHdoc_approx. rewrite doc_hashroot_cons_eq. simpl. congruence.
  + simpl. rewrite IHdoc_approx. rewrite doc_hashroot_cons_eq. simpl. congruence.
  + simpl. rewrite IHdoc_approx. rewrite doc_hashroot_cons_eq. simpl. congruence.
  + simpl. rewrite IHdoc_approx. rewrite doc_hashroot_cons_eq. simpl. congruence.
- revert dl'. induction dl; intros [|[h'|h' a'|a' m'|p'|p' d'] dr'];
              try now (simpl; intros H1; exfalso; revert H1; apply hashnatpairdiscr).
  + intros _. apply doc_approx_nil.
  + simpl. intros H1. apply doc_approx_hash. congruence.
  + simpl. intros H1. apply doc_approx_hash. congruence.
  + simpl. intros H1. apply doc_approx_hash. congruence.
  + simpl. intros H1. apply doc_approx_hash. congruence.
  + simpl. intros H1. apply doc_approx_hash. congruence.
  + simpl. intros H1. apply doc_approx_hash. congruence.
  + simpl. intros H1. exfalso. symmetry in H1. revert H1. apply hashnatpairdiscr.
  + simpl. intros H1. rewrite doc_hashroot_cons_eq in H1.
    apply hashpairinj in H1.
    destruct H1 as [H2 H3].
    simpl in H2. apply hashpairinj in H2. destruct H2 as [_ H2]. subst h'.
    apply doc_approx_signa. apply IHdl. exact H3.
  + simpl. intros H1. exfalso. rewrite doc_hashroot_cons_eq in H1.
    apply hashpairinj in H1.
    destruct H1 as [H2 H3].
    simpl in H2. apply hashpairinj in H2. destruct H2 as [H2 _].
    apply hashnatinj in H2. omega.
  + simpl. intros H1. exfalso. rewrite doc_hashroot_cons_eq in H1.
    apply hashpairinj in H1.
    destruct H1 as [H2 H3].
    simpl in H2. apply hashpairinj in H2. destruct H2 as [H2 _].
    apply hashnatinj in H2. omega.
  + simpl. intros H1. exfalso. rewrite doc_hashroot_cons_eq in H1.
    apply hashpairinj in H1.
    destruct H1 as [H2 H3].
    simpl in H2. apply hashpairinj in H2. destruct H2 as [H2 _].
    apply hashnatinj in H2. omega.
  + simpl. intros H1. exfalso. rewrite doc_hashroot_cons_eq in H1.
    apply hashpairinj in H1.
    destruct H1 as [H2 H3].
    simpl in H2. apply hashpairinj in H2. destruct H2 as [H2 _].
    apply hashnatinj in H2. omega.
  + simpl. intros H1. exfalso. rewrite doc_hashroot_nil_eq in H1.
    symmetry in H1. revert H1. apply hashnatpairdiscr.
  + simpl. intros H1. exfalso. rewrite doc_hashroot_cons_eq in H1.
    apply hashpairinj in H1.
    destruct H1 as [H2 H3].
    simpl in H2. apply hashpairinj in H2. destruct H2 as [H2 _].
    apply hashnatinj in H2. omega.
  + simpl. intros H1. rewrite doc_hashroot_cons_eq in H1.
    apply hashpairinj in H1.
    destruct H1 as [H2 H3].
    simpl in H2. apply hashpairinj in H2. destruct H2 as [_ H2].
    apply hashpairinj in H2. destruct H2 as [H4 H5].
    apply hashstpinj in H5. subst s. subst h.
    apply doc_approx_param. apply IHdl. exact H3.
  + simpl. intros H1. exfalso. rewrite doc_hashroot_cons_eq in H1.
    apply hashpairinj in H1.
    destruct H1 as [H2 H3].
    simpl in H2. apply hashpairinj in H2. destruct H2 as [H2 _].
    apply hashnatinj in H2. omega.
  + simpl. intros H1. exfalso. rewrite doc_hashroot_cons_eq in H1.
    apply hashpairinj in H1.
    destruct H1 as [H2 H3].
    simpl in H2. apply hashpairinj in H2. destruct H2 as [H2 _].
    apply hashnatinj in H2. omega.
  + simpl. intros H1. exfalso. rewrite doc_hashroot_cons_eq in H1.
    apply hashpairinj in H1.
    destruct H1 as [H2 H3].
    simpl in H2. apply hashpairinj in H2. destruct H2 as [H2 _].
    apply hashnatinj in H2. omega.
  + simpl. intros H1. exfalso. rewrite doc_hashroot_nil_eq in H1.
    symmetry in H1. revert H1. apply hashnatpairdiscr.
  + simpl. intros H1. exfalso. rewrite doc_hashroot_cons_eq in H1.
    apply hashpairinj in H1.
    destruct H1 as [H2 H3].
    simpl in H2. apply hashpairinj in H2. destruct H2 as [H2 _].
    apply hashnatinj in H2. omega.
  + simpl. intros H1. rewrite doc_hashroot_cons_eq in H1.
    apply hashpairinj in H1.
    destruct H1 as [H2 H3].
    simpl in H2. apply hashpairinj in H2. destruct H2 as [_ H2]. subst h.
    apply doc_approx_param_hash. apply IHdl. exact H3.
  + simpl. intros H1. exfalso. rewrite doc_hashroot_cons_eq in H1.
    apply hashpairinj in H1.
    destruct H1 as [H2 H3].
    simpl in H2. apply hashpairinj in H2. destruct H2 as [H2 _].
    apply hashnatinj in H2. omega.
  + simpl. intros H1. exfalso. rewrite doc_hashroot_cons_eq in H1.
    apply hashpairinj in H1.
    destruct H1 as [H2 H3].
    simpl in H2. apply hashpairinj in H2. destruct H2 as [H2 _].
    apply hashnatinj in H2. omega.
  + simpl. intros H1. exfalso. rewrite doc_hashroot_cons_eq in H1.
    apply hashpairinj in H1.
    destruct H1 as [H2 H3].
    simpl in H2. apply hashpairinj in H2. destruct H2 as [H2 _].
    apply hashnatinj in H2. omega.
  + simpl. intros H1. exfalso. rewrite doc_hashroot_nil_eq in H1.
    symmetry in H1. revert H1. apply hashnatpairdiscr.
  + simpl. intros H1. exfalso. rewrite doc_hashroot_cons_eq in H1.
    apply hashpairinj in H1.
    destruct H1 as [H2 H3].
    simpl in H2. apply hashpairinj in H2. destruct H2 as [H2 _].
    apply hashnatinj in H2. omega.
  + simpl. intros H1. exfalso. rewrite doc_hashroot_cons_eq in H1.
    apply hashpairinj in H1.
    destruct H1 as [H2 H3].
    simpl in H2. apply hashpairinj in H2. destruct H2 as [H2 _].
    apply hashnatinj in H2. omega.
  + simpl. intros H1. rewrite doc_hashroot_cons_eq in H1.
    apply hashpairinj in H1.
    destruct H1 as [H2 H3].
    simpl in H2. apply hashpairinj in H2. destruct H2 as [_ H2].
    apply hashpairinj in H2. destruct H2 as [H4 H5].
    apply hashstpinj in H4. subst s.
    apply doc_approx_def.
    * exact H5.
    * apply IHdl. exact H3.
  + simpl. intros H1. exfalso. rewrite doc_hashroot_cons_eq in H1.
    apply hashpairinj in H1.
    destruct H1 as [H2 H3].
    simpl in H2. apply hashpairinj in H2. destruct H2 as [H2 _].
    apply hashnatinj in H2. omega.
  + simpl. intros H1. exfalso. rewrite doc_hashroot_cons_eq in H1.
    apply hashpairinj in H1.
    destruct H1 as [H2 H3].
    simpl in H2. apply hashpairinj in H2. destruct H2 as [H2 _].
    apply hashnatinj in H2. omega.
  + simpl. intros H1. exfalso. rewrite doc_hashroot_nil_eq in H1.
    symmetry in H1. revert H1. apply hashnatpairdiscr.
  + simpl. intros H1. exfalso. rewrite doc_hashroot_cons_eq in H1.
    apply hashpairinj in H1.
    destruct H1 as [H2 H3].
    simpl in H2. apply hashpairinj in H2. destruct H2 as [H2 _].
    apply hashnatinj in H2. omega.
  + simpl. intros H1. exfalso. rewrite doc_hashroot_cons_eq in H1.
    apply hashpairinj in H1.
    destruct H1 as [H2 H3].
    simpl in H2. apply hashpairinj in H2. destruct H2 as [H2 _].
    apply hashnatinj in H2. omega.
  + simpl. intros H1. rewrite doc_hashroot_cons_eq in H1.
    apply hashpairinj in H1.
    destruct H1 as [H2 H3].
    simpl in H2. apply hashpairinj in H2. destruct H2 as [_ H2].
    subst h.
    apply doc_approx_def_hash.
    apply IHdl. exact H3.
  + simpl. intros H1. exfalso. rewrite doc_hashroot_cons_eq in H1.
    apply hashpairinj in H1.
    destruct H1 as [H2 H3].
    simpl in H2. apply hashpairinj in H2. destruct H2 as [H2 _].
    apply hashnatinj in H2. omega.
  + simpl. intros H1. exfalso. rewrite doc_hashroot_cons_eq in H1.
    apply hashpairinj in H1.
    destruct H1 as [H2 H3].
    simpl in H2. apply hashpairinj in H2. destruct H2 as [H2 _].
    apply hashnatinj in H2. omega.
  + simpl. intros H1. exfalso. rewrite doc_hashroot_nil_eq in H1.
    symmetry in H1. revert H1. apply hashnatpairdiscr.
  + simpl. intros H1. exfalso. rewrite doc_hashroot_cons_eq in H1.
    apply hashpairinj in H1.
    destruct H1 as [H2 H3].
    simpl in H2. apply hashpairinj in H2. destruct H2 as [H2 _].
    apply hashnatinj in H2. omega.
  + simpl. intros H1. exfalso. rewrite doc_hashroot_cons_eq in H1.
    apply hashpairinj in H1.
    destruct H1 as [H2 H3].
    simpl in H2. apply hashpairinj in H2. destruct H2 as [H2 _].
    apply hashnatinj in H2. omega.
  + simpl. intros H1. exfalso. rewrite doc_hashroot_cons_eq in H1.
    apply hashpairinj in H1.
    destruct H1 as [H2 H3].
    simpl in H2. apply hashpairinj in H2. destruct H2 as [H2 _].
    apply hashnatinj in H2. omega.
  + simpl. intros H1. rewrite doc_hashroot_cons_eq in H1.
    apply hashpairinj in H1.
    destruct H1 as [H2 H3].
    simpl in H2. apply hashpairinj in H2. destruct H2 as [_ H2].
    apply doc_approx_known.
    * assumption.
    * apply IHdl. exact H3.
  + simpl. intros H1. exfalso. rewrite doc_hashroot_cons_eq in H1.
    apply hashpairinj in H1.
    destruct H1 as [H2 H3].
    simpl in H2. apply hashpairinj in H2. destruct H2 as [H2 _].
    apply hashnatinj in H2. omega.
  + simpl. intros H1. exfalso. rewrite doc_hashroot_nil_eq in H1.
    symmetry in H1. revert H1. apply hashnatpairdiscr.
  + simpl. intros H1. exfalso. rewrite doc_hashroot_cons_eq in H1.
    apply hashpairinj in H1.
    destruct H1 as [H2 H3].
    simpl in H2. apply hashpairinj in H2. destruct H2 as [H2 _].
    apply hashnatinj in H2. omega.
  + simpl. intros H1. exfalso. rewrite doc_hashroot_cons_eq in H1.
    apply hashpairinj in H1.
    destruct H1 as [H2 H3].
    simpl in H2. apply hashpairinj in H2. destruct H2 as [H2 _].
    apply hashnatinj in H2. omega.
  + simpl. intros H1. exfalso. rewrite doc_hashroot_cons_eq in H1.
    apply hashpairinj in H1.
    destruct H1 as [H2 H3].
    simpl in H2. apply hashpairinj in H2. destruct H2 as [H2 _].
    apply hashnatinj in H2. omega.
  + simpl. intros H1. exfalso. rewrite doc_hashroot_cons_eq in H1.
    apply hashpairinj in H1.
    destruct H1 as [H2 H3].
    simpl in H2. apply hashpairinj in H2. destruct H2 as [H2 _].
    apply hashnatinj in H2. omega.
  + simpl. intros H1. rewrite doc_hashroot_cons_eq in H1.
    apply hashpairinj in H1.
    destruct H1 as [H2 H3].
    simpl in H2. apply hashpairinj in H2. destruct H2 as [_ H2].
    apply hashpairinj in H2. destruct H2 as [H4 H5].
    apply doc_approx_pfof.
    * exact H4.
    * exact H5.
    * apply IHdl. exact H3.
  + simpl. intros H1. exfalso. rewrite doc_hashroot_nil_eq in H1.
    symmetry in H1. revert H1. apply hashnatpairdiscr.
  + simpl. intros H1. exfalso. rewrite doc_hashroot_cons_eq in H1.
    apply hashpairinj in H1.
    destruct H1 as [H2 H3].
    simpl in H2. apply hashpairinj in H2. destruct H2 as [H2 _].
    apply hashnatinj in H2. omega.
  + simpl. intros H1. exfalso. rewrite doc_hashroot_cons_eq in H1.
    apply hashpairinj in H1.
    destruct H1 as [H2 H3].
    simpl in H2. apply hashpairinj in H2. destruct H2 as [H2 _].
    apply hashnatinj in H2. omega.
  + simpl. intros H1. exfalso. rewrite doc_hashroot_cons_eq in H1.
    apply hashpairinj in H1.
    destruct H1 as [H2 H3].
    simpl in H2. apply hashpairinj in H2. destruct H2 as [H2 _].
    apply hashnatinj in H2. omega.
  + simpl. intros H1. exfalso. rewrite doc_hashroot_cons_eq in H1.
    apply hashpairinj in H1.
    destruct H1 as [H2 H3].
    simpl in H2. apply hashpairinj in H2. destruct H2 as [H2 _].
    apply hashnatinj in H2. omega.
  + simpl. intros H1. rewrite doc_hashroot_cons_eq in H1.
    apply hashpairinj in H1.
    destruct H1 as [H2 H3].
    simpl in H2. apply hashpairinj in H2. destruct H2 as [_ H2].
    subst h.
    apply doc_approx_pfof_hash.
    apply IHdl. exact H3.
Qed.

Lemma ser_trm_inj_lem m m' l l' : ser_trm m ++ l = ser_trm m' ++ l' -> l = l' /\ m = m'.
revert m' l l'. induction m as [h|n al|n|m IHm n IHn|a m IHm|m IHm n IHn|a m IHm]; intros [h'|n' al'|n'|m' n'|a' m'|m' n'|a' m'] l l' H1; simpl in H1;
           try now (exfalso; inversion H1).
- inversion H1.
  destruct (ser_hashval_inj h h' _ _ H0) as [H2 H3].
  split; congruence.
- inversion H1.
  apply ser_stp_l_inj_lem in H2. destruct H2 as [H4 H5].
  split; congruence.
- inversion H1. tauto.
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

Lemma ser_theoryitem_inj_lem d d' l l' : ser_theoryitem d ++ l = ser_theoryitem d' ++ l' -> l = l' /\ d = d'.
destruct d as [a|p]; destruct d' as [a'|p']; simpl; intros H1; try now (exfalso; inversion H1).
- inversion H1.
  destruct (ser_stp_inj_lem _ _ _ _ H0) as [H4 H5].
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

Lemma ser_theoryspec_inj_lem dl dl' l l' : ser_theoryspec dl ++ l = ser_theoryspec dl' ++ l' -> l = l' /\ dl = dl'.
revert dl' l l'. induction dl as [|d dl IH]; intros [|d' dl'] l l' H1; simpl in H1;
                 try now (exfalso; inversion H1).
- inversion H1. split; congruence.
- inversion H1. rewrite <- app_assoc in H0. rewrite <- app_assoc in H0.
  destruct (ser_theoryitem_inj_lem d d' _ _ H0) as [H2 H3].
  apply IH in H2. destruct H2 as [H4 H5].
  split; congruence.
Qed.

Lemma ser_theoryspec_inj dl dl' : ser_theoryspec dl = ser_theoryspec dl' -> dl = dl'.
intros H1.
assert (L1: ser_theoryspec dl ++ nil = ser_theoryspec dl' ++ nil) by congruence.
generalize (ser_theoryspec_inj_lem dl dl' nil nil L1). tauto.
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

Lemma ser_signaspec_inj_lem dl dl' l l' : ser_signaspec dl ++ l = ser_signaspec dl' ++ l' -> l = l' /\ dl = dl'.
revert dl' l l'. induction dl as [|d dl IH]; intros [|d' dl'] l l' H1; simpl in H1;
                 try now (exfalso; inversion H1).
- inversion H1. split; congruence.
- inversion H1. rewrite <- app_assoc in H0. rewrite <- app_assoc in H0.
  destruct (ser_signaitem_inj_lem d d' _ _ H0) as [H2 H3].
  apply IH in H2. destruct H2 as [H4 H5].
  split; congruence.
Qed.

Lemma ser_signaspec_inj dl dl' : ser_signaspec dl = ser_signaspec dl' -> dl = dl'.
intros H1.
assert (L1: ser_signaspec dl ++ nil = ser_signaspec dl' ++ nil) by congruence.
generalize (ser_signaspec_inj_lem dl dl' nil nil L1). tauto.
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

Lemma hashstplinj al al' : hashstpl al = hashstpl al' -> al = al'.
revert al'. induction al as [|a ar IH]; intros [|a' ar'].
- intros _. reflexivity.
- simpl. intros H1. discriminate H1.
- simpl. intros H1. discriminate H1.
- simpl. intros H1. inversion H1.
  apply hashopair1inj in H0.
  destruct H0 as [H2 H3].
  apply hashstpinj in H2. apply IH in H3.
  congruence.
Qed.

Lemma hashtrminj m m' : hashtrm m = hashtrm m' -> m = m'.
revert m'. induction m as [h|i al|n|m IHm n IHn|a m IHm|m IHm n IHn|a m IHm]; intros [h'|i' al'|n'|m' n'|a' m'|m' n'|a' m'] H1; simpl in H1;
           try (exfalso; apply hashpairinj in H1; destruct H1 as [H1 _]; apply hashnatinj in H1; omega).
- apply hashpairinj in H1. destruct H1 as [_ H1]. congruence.
- apply hashpairinj in H1. destruct H1 as [_ H1].
  apply hashopair1inj in H1. destruct H1 as [H2 H3].
  apply hashnatinj in H2. apply hashstplinj in H3.
  congruence.
- apply hashpairinj in H1. destruct H1 as [_ H1]. apply hashnatinj in H1.
  congruence.
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
  apply hashopair1inj in H1. destruct H1 as [H2 H3].
  apply hashstplinj in H3.
  congruence.
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

Lemma hashtheoryiteminj d d' : hashtheoryitem d = hashtheoryitem d' -> d = d'.
destruct d as [a|p]; destruct d' as [a'|p']; simpl; intros H1; try (exfalso; apply hashpairinj in H1; destruct H1 as [H1 _]; apply hashnatinj in H1; omega).
- apply hashpairinj in H1. destruct H1 as [_ H1]. apply hashstpinj in H1. congruence.
- apply hashpairinj in H1. destruct H1 as [_ H1].
  apply hashtrminj in H1.
  congruence.
Qed.

Lemma hashtheoryspecinj dl dl' : hashtheoryspec dl = hashtheoryspec dl' -> dl = dl'.
intros H1. apply hashlistinj in H1. apply hashmapinj in H1.
- exact H1.
- exact hashtheoryiteminj.
Qed.

Lemma hashsignaiteminj d d' : hashsignaitem d = hashsignaitem d' -> d = d'.
destruct d as [h|a|a m|p]; destruct d' as [h'|a'|a' m'|p']; simpl; intros H1; try (exfalso; apply hashpairinj in H1; destruct H1 as [H1 _]; apply hashnatinj in H1; omega).
- apply hashpairinj in H1. destruct H1 as [_ H1]. congruence.
- apply hashpairinj in H1. destruct H1 as [_ H1].
  apply hashpairinj in H1. destruct H1 as [H2 H3].
  apply hashstpinj in H3. congruence.
- apply hashpairinj in H1. destruct H1 as [_ H1].
  apply hashpairinj in H1. destruct H1 as [H2 H3].
  apply hashstpinj in H2. apply hashtrminj in H3.
  congruence.
- apply hashpairinj in H1. destruct H1 as [_ H1].
  apply hashtrminj in H1.
  congruence.
Qed.

Lemma hashsignaspecinj dl dl' : hashsignaspec dl = hashsignaspec dl' -> dl = dl'.
intros H1. apply hashlistinj in H1. apply hashmapinj in H1.
- exact H1.
- exact hashsignaiteminj.
Qed.

Lemma hashdociteminj d d' : hashdocitem d = hashdocitem d' -> d = d'.
destruct d as [h|h a|a m|p|p d]; destruct d' as [h'|h' a'|a' m'|p'|p' d']; simpl; intros H1; try (exfalso; apply hashpairinj in H1; destruct H1 as [H1 _]; apply hashnatinj in H1; omega).
- apply hashpairinj in H1. destruct H1 as [_ H1]. congruence.
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

Lemma hashdocinj dl dl' : hashdoc dl = hashdoc dl' -> dl = dl'.
intros H1. apply hashlistinj in H1. apply hashmapinj in H1.
- exact H1.
- exact hashdociteminj.
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
destruct d as [a|p]; destruct d' as [a'|p']; try (right; discriminate).
- repeat decide equality; try apply hashval_eq_dec.
- repeat decide equality; try apply hashval_eq_dec.
Defined.

Definition theoryspec_eq_dec (dl dl':theoryspec) : {dl = dl'} + {dl <> dl'}.
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

Definition signaspec_eq_dec (dl dl':signaspec) : {dl = dl'} + {dl <> dl'}.
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

Fixpoint signaspec_uses_objs (dl:signaspec) : list hashval :=
match dl with
| signaparam h _::dr => h::signaspec_uses_objs dr
| _::dr => signaspec_uses_objs dr
| nil => nil
end.

Fixpoint signaspec_uses_props (th:option hashval) (dl:signaspec) : list hashval :=
match dl with
| signaknown p::dr => trm_hashroot th p::signaspec_uses_props th dr
| _::dr => signaspec_uses_props th dr
| nil => nil
end.

Fixpoint signaspec_stp_markers (dl:signaspec) : list hashval :=
match dl with
| signaparam h a::dr => hashpair h (hashstp a)::signaspec_stp_markers dr
| signaknown p::dr => signaspec_stp_markers dr
| _::dr => signaspec_stp_markers dr
| nil => nil
end.

Fixpoint signaspec_known_markers (th:option hashval) (dl:signaspec) : list hashval :=
match dl with
| signaparam h a::dr => signaspec_known_markers th dr
| signaknown p::dr => trm_hashroot th p::signaspec_known_markers th dr
| _::dr => signaspec_known_markers th dr
| nil => nil
end.

Fixpoint doc_stp_markers (dl:doc) : list hashval :=
match dl with
| docparam h a::dr => hashpair h (hashstp a)::doc_stp_markers dr
| docknown p::dr => doc_stp_markers dr
| _::dr => doc_stp_markers dr
| nil => nil
end.

Fixpoint doc_known_markers (th:option hashval) (dl:doc) : list hashval :=
match dl with
| docparam h a::dr => doc_known_markers th dr
| docknown p::dr => trm_hashroot th p::doc_known_markers th dr
| _::dr => doc_known_markers th dr
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
| docknown p::dr => trm_hashroot th p::doc_uses_props th dr
| _::dr => doc_uses_props th dr
| nil => nil
end.

Fixpoint doc_creates_objs (th:option hashval) (dl:doc) : list (prod hashval hashval) :=
match dl with
| docdef a m::dr => (trm_hashroot th m,hashstp a)::doc_creates_objs th dr
| _::dr => doc_creates_objs th dr
| nil => nil
end.

Fixpoint doc_creates_props (th:option hashval) (dl:doc) : list (prod hashval hashval) :=
match dl with
| docpfof p d::dr => (trm_hashroot th p,pf_hashroot th d)::doc_creates_props th dr
| _::dr => doc_creates_props th dr
| nil => nil
end.

Fixpoint htree (A:Type) (n:nat) : Type :=
  match n with
    | 0 => A
    | S n => prod (option (htree A n)) (option (htree A n))
  end.

Fixpoint htree_lookup {A:Type} {n:nat} : bitseq n -> htree A n -> option A :=
match n as n' return bitseq n' -> htree A n' -> option A with
| 0 => fun bs a => Some(a)
| S n => fun bs t =>
           match bs,t with
             | (false,br),(Some(t),_) => htree_lookup br t
             | (true,br),(_,Some(t)) => htree_lookup br t
             | _,_ => None
           end
end.

Fixpoint htree_create {A:Type} {n:nat} : bitseq n -> A -> htree A n :=
match n with
  | 0 => fun bs a => a
  | S n => fun bs a =>
             match bs with
               | (false,br) => (Some(htree_create br a),None)
               | (true,br) => (None,Some(htree_create br a))
             end
end.

Fixpoint htree_insert {A:Type} {n:nat} :  htree A n -> bitseq n -> A -> htree A n :=
match n with
  | 0 => fun t bs a => a
  | S n => fun t bs a =>
             match bs,t with
               | (false,br),(Some(t0),t1) => (Some(htree_insert t0 br a),t1)
               | (true,br),(t0,Some(t1)) => (t0,Some(htree_insert t1 br a))
               | (false,br),(None,t1) => (Some(htree_create br a),t1)
               | (true,br),(t0,None) => (t0,Some(htree_create br a))
             end
end.

Fixpoint ohtree_hashroot {A:Type} {n:nat} (f:A -> option hashval) : option (htree A n) -> option hashval :=
  match n with
    | 0 => fun a =>
             match a with
               | Some(a) => f a
               | None => None
             end
    | S n => fun t =>
               match t with
                 | Some(t0,t1) => hashopair (ohtree_hashroot f t0) (ohtree_hashroot f t1)
                 | None => None
               end
  end.

Definition ttree (n:nat) := htree theory n.

Definition stree (n:nat) := htree (option hashval * signa) n.

Definition theory_lookup {n} (h:bitseq n) (t:ttree n) : theory :=
  match htree_lookup h t with
    | Some(thy) => thy
    | None => (nil,nil)
  end.

Definition signa_lookup {n} (bs:bitseq n) (t:stree n) : option hashval * signa :=
  match htree_lookup bs t with
    | Some(th,s) => (th,s)
    | None => (None,(nil,(nil,nil)))
  end.

Definition ottree_insert {n} (t:option (ttree n)) (bs:bitseq n) (thy:theory) : ttree n :=
  match t with
    | Some(t) => htree_insert t bs thy
    | None => htree_create bs thy
  end.

Definition ostree_insert {n} (t:option (stree n)) (bs:bitseq n) (th:option hashval) (s:signa) : stree n :=
  match t with
    | Some(t) => htree_insert t bs (th,s)
    | None => htree_create bs (th,s)
  end.

Definition ottree_hashroot {n} (t:option (ttree n)) : option hashval :=
  ohtree_hashroot hashtheory t.

Definition ostree_hashroot {n} (t:option (stree n)) : option hashval :=
  ohtree_hashroot (fun ths: option hashval * signa =>
                     let (th,s) := ths in
                     Some(hashopair2 th (hashsigna th s)))
                  t.

(*** type checking and proof checking, left abstract here ***)

(*** Check if a trm (with no Gn's) has an stp under a certain (partial) theory. ***)
Parameter check_thy_trm_tp_p : theory -> trm -> stp -> Prop.

Fixpoint check_theoryspec_p (thy:theoryspec) : Prop :=
   match thy with
     | nil => True
     | thyprim a::thy => check_theoryspec_p thy
     | thyaxiom p::thy => check_theoryspec_p thy /\ check_thy_trm_tp_p (theoryspec_theory thy) p prop
   end.

(*** Check if a [trm has an stp|pf is of a prop] under a certain theory and signature.
 The theory hash is also given since it would be needed to hash.
 It could be recomputed from the theory, but there is no need for this.
 The trm should not contain any closed terms except Gn's.
 ***)
Parameter check_trm_tp_p : option hashval -> theory -> signa -> trm -> stp -> Prop.

Parameter check_pf_prop_p : option hashval -> theory -> signa -> pf -> trm -> Prop.

(***
 gvtp is a generic way of verifying the term with a certain hashval has a certain stp
 and gvkn is a generic way of verifying the prop with a certain hashval is known.
 In practice this will be computed using a compact tree (CTree) approximating the state.
 st is the stree for looking up signatures (signa). Each node will keep up with this.
 Using signatures reduces the need to repeat objects/knowns that are often used.
 th is the hashval of the theory (None is the empty theory).
 thy is the theory whose theoryspec has hash th.
 ***)
Fixpoint check_signaspec_r (gvtp : hashval -> stp -> Prop) (gvkn : hashval -> Prop)
         (st:option (stree 160)) (th:option hashval) (thy:theory) (s:signaspec) : Prop :=
   match s with
     | nil => True
     | signasigna h::s =>
       match st with
         | None => False
         | Some(st1) =>
           match signa_lookup (hashval_bit160 h) st1 with
             | (sth,(al,kl)) => check_signaspec_r gvtp gvkn st th thy s /\ sth = th
           end
       end
     | signaparam h a::s => check_signaspec_r gvtp gvkn st th thy s /\ gvtp h a
     | signadef a m::s => check_signaspec_r gvtp gvkn st th thy s /\ check_trm_tp_p th thy (signaspec_signa th s) m a
     | signaknown p::s => check_signaspec_r gvtp gvkn st th thy s /\ gvkn (trm_hashroot th p)
   end.

Definition check_signaspec_p (gvtp : hashval -> stp -> Prop) (gvkn : hashval -> Prop)
           (t:option (ttree 160)) (st:option (stree 160)) (th:option hashval) (s:signaspec) : Prop :=
  match th with
    | None => check_signaspec_r gvtp gvkn st th (nil,nil) s
    | Some(h) =>
      match t with
        | None => False
        | Some(t) => check_signaspec_r gvtp gvkn st th (theory_lookup (hashval_bit160 h) t) s
      end
  end.

Fixpoint doc_signas (dl:doc) : list hashval :=
  match dl with
    | nil => nil
    | docsigna h::dr => h::doc_signas dr
    | _::dr => doc_signas dr
  end.

Fixpoint doc_trms (th:option hashval) (dl:doc) : list (prod hashval (prod stp (option trm))) :=
  match dl with
    | nil => nil
    | docparam h a::dr => (h,(a,None))::doc_trms th dr
    | docdef a m::dr => (trm_hashroot th m,(a,Some(m)))::doc_trms th dr
    | _::dr => doc_trms th dr
  end.

Fixpoint doc_knowns (th:option hashval) (dl:doc) : list hashval :=
  match dl with
    | nil => nil
    | docknown p::dr => trm_hashroot th p::doc_knowns th dr
    | docpfof p _::dr => trm_hashroot th p::doc_knowns th dr
    | _::dr => doc_knowns th dr
  end.

Definition doc_signa (th:option hashval) (dl:doc) : signa :=
(doc_signas dl,(doc_trms th dl,doc_knowns th dl)).

Fixpoint check_doc_r (gvtp : hashval -> stp -> Prop) (gvkn : hashval -> Prop)
         (st:option (stree 160)) (th:option hashval) (thy:theory) (dl:doc) : Prop :=
   match dl with
     | nil => True
     | docsigna h::dr =>
       match st with
         | None => False
         | Some(st1) =>
           match signa_lookup (hashval_bit160 h) st1 with
             | (sth,(al,kl)) => check_doc_r gvtp gvkn st th thy dr /\ sth = th
           end
       end
     | docparam h a::dr => check_doc_r gvtp gvkn st th thy dr /\ gvtp h a
     | docdef a m::dr => check_doc_r gvtp gvkn st th thy dr /\ check_trm_tp_p th thy (doc_signa th dr) m a
     | docknown p::dr => check_doc_r gvtp gvkn st th thy dr /\ gvkn (trm_hashroot th p)
     | docpfof p d::dr => check_doc_r gvtp gvkn st th thy dr /\ check_pf_prop_p th thy (doc_signa th dr) d p
   end.

Definition check_doc_p (gvtp : hashval -> stp -> Prop) (gvkn : hashval -> Prop)
           (t:option (ttree 160)) (st:option (stree 160)) (th:option hashval) (dl:doc) : Prop :=
  match th with
    | None => check_doc_r gvtp gvkn st th (nil,nil) dl
    | Some(h) =>
      match t with
        | None => False
        | Some(t) => check_doc_r gvtp gvkn st th (theory_lookup (hashval_bit160 h) t) dl
      end
  end.

Lemma check_signaspec_r_markers (gvtp gvtp':hashval -> stp -> Prop) (gvkn gvkn':hashval -> Prop) st th thy s :
  (forall h a, In (hashpair h (hashstp a)) (signaspec_stp_markers s) -> gvtp h a -> gvtp' h a)
  -> (forall h, In h (signaspec_known_markers th s) -> gvkn h -> gvkn' h)
  -> check_signaspec_r gvtp gvkn st th thy s
  -> check_signaspec_r gvtp' gvkn' st th thy s.
intros H1 H2. induction s as [|[h|h a|a m|p] s IH]; simpl.
- tauto.
- destruct st as [st1|]; try tauto.
  destruct (signa_lookup (hashval_bit160 h) st1) as [sth [y z]] eqn:E1.
  intros [H3 H4].
  split.
  + revert H3. apply IH.
    * intros k b H5. apply H1. exact H5.
    * intros k H5. apply H2. exact H5.
  + exact H4.
- intros [H3 H4].
  split.
  + revert H3. apply IH.
    * intros k b H5. apply H1. right. exact H5.
    * intros k H5. apply H2. exact H5.
  + apply H1.
    * left. reflexivity.
    * exact H4.
- intros [H3 H4].
  split.
  + revert H3. apply IH.
    * intros k b H5. apply H1. exact H5.
    * intros k H5. apply H2. exact H5.
  + exact H4.
- intros [H3 H4].
  split.
  + revert H3. apply IH.
    * intros k b H5. apply H1. exact H5.
    * intros k H5. apply H2. right. exact H5.
  + apply H2.
    * left. reflexivity.
    * exact H4.
Qed.

Lemma check_signaspec_p_markers (gvtp gvtp':hashval -> stp -> Prop) (gvkn gvkn':hashval -> Prop) t st th s :
  (forall h a, In (hashpair h (hashstp a)) (signaspec_stp_markers s) -> gvtp h a -> gvtp' h a)
  -> (forall h, In h (signaspec_known_markers th s) -> gvkn h -> gvkn' h)
  -> check_signaspec_p gvtp gvkn t st th s
  -> check_signaspec_p gvtp' gvkn' t st th s.
intros H1 H2. destruct th as [h|]; simpl.
- destruct t as [t|]; simpl.
  + now apply check_signaspec_r_markers.
  + tauto.
- now apply check_signaspec_r_markers.
Qed.

Lemma check_doc_r_markers (gvtp gvtp':hashval -> stp -> Prop) (gvkn gvkn':hashval -> Prop) st th thy dl :
  (forall h a, In (hashpair h (hashstp a)) (doc_stp_markers dl) -> gvtp h a -> gvtp' h a)
  -> (forall h, In h (doc_known_markers th dl) -> gvkn h -> gvkn' h)
  -> check_doc_r gvtp gvkn st th thy dl
  -> check_doc_r gvtp' gvkn' st th thy dl.
intros H1 H2. induction dl as [|[h|h a|a m|p|p d] dr IH]; simpl.
- tauto.
- destruct st as [st1|]; try tauto.
  destruct (signa_lookup (hashval_bit160 h) st1) as [sth [y z]] eqn:E1.
  intros [H3 H4].
  split.
  + revert H3. apply IH.
    * intros k b H5. apply H1. exact H5.
    * intros k H5. apply H2. exact H5.
  + exact H4.
- intros [H3 H4].
  split.
  + revert H3. apply IH.
    * intros k b H5. apply H1. right. exact H5.
    * intros k H5. apply H2. exact H5.
  + apply H1.
    * left. reflexivity.
    * exact H4.
- intros [H3 H4].
  split.
  + revert H3. apply IH.
    * intros k b H5. apply H1. exact H5.
    * intros k H5. apply H2. exact H5.
  + exact H4.
- intros [H3 H4].
  split.
  + revert H3. apply IH.
    * intros k b H5. apply H1. exact H5.
    * intros k H5. apply H2. right. exact H5.
  + apply H2.
    * left. reflexivity.
    * exact H4.
- intros [H3 H4].
  split.
  + revert H3. apply IH.
    * intros k b H5. apply H1. exact H5.
    * intros k H5. apply H2. exact H5.
  + exact H4.
Qed.

Lemma check_doc_p_markers (gvtp gvtp':hashval -> stp -> Prop) (gvkn gvkn':hashval -> Prop) t st th dl :
  (forall h a, In (hashpair h (hashstp a)) (doc_stp_markers dl) -> gvtp h a -> gvtp' h a)
  -> (forall h, In h (doc_known_markers th dl) -> gvkn h -> gvkn' h)
  -> check_doc_p gvtp gvkn t st th dl
  -> check_doc_p gvtp' gvkn' t st th dl.
intros H1 H2. destruct th as [h|]; simpl.
- destruct t as [t|]; simpl.
  + now apply check_doc_r_markers.
  + tauto.
- now apply check_doc_r_markers.
Qed.

Lemma check_signaspec_r_uses (gvtp gvtp':hashval -> stp -> Prop) (gvkn gvkn':hashval -> Prop) st th thy s :
  (forall h a, In h (signaspec_uses_objs s) -> gvtp h a -> gvtp' h a)
  -> (forall h, In h (signaspec_uses_props th s) -> gvkn h -> gvkn' h)
  -> check_signaspec_r gvtp gvkn st th thy s
  -> check_signaspec_r gvtp' gvkn' st th thy s.
intros H1 H2. induction s as [|[h|h a|a m|p] s IH]; simpl.
- tauto.
- destruct st as [st1|]; try tauto.
  destruct (signa_lookup (hashval_bit160 h) st1) as [sth [y z]] eqn:E1.
  intros [H3 H4].
  split.
  + revert H3. apply IH.
    * intros k b H5. apply H1. exact H5.
    * intros k H5. apply H2. exact H5.
  + exact H4.
- intros [H3 H4].
  split.
  + revert H3. apply IH.
    * intros k b H5. apply H1. right. exact H5.
    * intros k H5. apply H2. exact H5.
  + apply H1.
    * left. reflexivity.
    * exact H4.
- intros [H3 H4].
  split.
  + revert H3. apply IH.
    * intros k b H5. apply H1. exact H5.
    * intros k H5. apply H2. exact H5.
  + exact H4.
- intros [H3 H4].
  split.
  + revert H3. apply IH.
    * intros k b H5. apply H1. exact H5.
    * intros k H5. apply H2. right. exact H5.
  + apply H2.
    * left. reflexivity.
    * exact H4.
Qed.

Lemma check_signaspec_p_uses (gvtp gvtp':hashval -> stp -> Prop) (gvkn gvkn':hashval -> Prop) t st th s :
  (forall h a, In h (signaspec_uses_objs s) -> gvtp h a -> gvtp' h a)
  -> (forall h, In h (signaspec_uses_props th s) -> gvkn h -> gvkn' h)
  -> check_signaspec_p gvtp gvkn t st th s
  -> check_signaspec_p gvtp' gvkn' t st th s.
intros H1 H2. destruct th as [h|]; simpl.
- destruct t as [t|]; simpl.
  + now apply check_signaspec_r_uses.
  + tauto.
- now apply check_signaspec_r_uses.
Qed.

Lemma check_doc_r_uses (gvtp gvtp':hashval -> stp -> Prop) (gvkn gvkn':hashval -> Prop) st th thy dl :
  (forall h a, In h (doc_uses_objs dl) -> gvtp h a -> gvtp' h a)
  -> (forall h, In h (doc_uses_props th dl) -> gvkn h -> gvkn' h)
  -> check_doc_r gvtp gvkn st th thy dl
  -> check_doc_r gvtp' gvkn' st th thy dl.
intros H1 H2. induction dl as [|[h|h a|a m|p|p d] dr IH]; simpl.
- tauto.
- destruct st as [st1|]; try tauto.
  destruct (signa_lookup (hashval_bit160 h) st1) as [sth [y z]] eqn:E1.
  intros [H3 H4].
  split.
  + revert H3. apply IH.
    * intros k b H5. apply H1. exact H5.
    * intros k H5. apply H2. exact H5.
  + exact H4.
- intros [H3 H4].
  split.
  + revert H3. apply IH.
    * intros k b H5. apply H1. right. exact H5.
    * intros k H5. apply H2. exact H5.
  + apply H1.
    * left. reflexivity.
    * exact H4.
- intros [H3 H4].
  split.
  + revert H3. apply IH.
    * intros k b H5. apply H1. exact H5.
    * intros k H5. apply H2. exact H5.
  + exact H4.
- intros [H3 H4].
  split.
  + revert H3. apply IH.
    * intros k b H5. apply H1. exact H5.
    * intros k H5. apply H2. right. exact H5.
  + apply H2.
    * left. reflexivity.
    * exact H4.
- intros [H3 H4].
  split.
  + revert H3. apply IH.
    * intros k b H5. apply H1. exact H5.
    * intros k H5. apply H2. exact H5.
  + exact H4.
Qed.

Lemma check_doc_p_uses (gvtp gvtp':hashval -> stp -> Prop) (gvkn gvkn':hashval -> Prop) t st th dl :
  (forall h a, In h (doc_uses_objs dl) -> gvtp h a -> gvtp' h a)
  -> (forall h, In h (doc_uses_props th dl) -> gvkn h -> gvkn' h)
  -> check_doc_p gvtp gvkn t st th dl
  -> check_doc_p gvtp' gvkn' t st th dl.
intros H1 H2. destruct th as [h|]; simpl.
- destruct t as [t|]; simpl.
  + now apply check_doc_r_uses.
  + tauto.
- now apply check_doc_r_uses.
Qed.

Lemma check_signaspec_p_subq (gvtp gvtp':hashval -> stp -> Prop) (gvkn gvkn':hashval -> Prop) t st th s :
  (forall h a, gvtp h a -> gvtp' h a)
  -> (forall h, gvkn h -> gvkn' h)
  -> check_signaspec_p gvtp gvkn t st th s
  -> check_signaspec_p gvtp' gvkn' t st th s.
intros H1 H2. apply check_signaspec_p_uses.
- intros h a _. apply H1.
- intros h _. apply H2.
Qed.

Lemma check_doc_p_subq (gvtp gvtp':hashval -> stp -> Prop) (gvkn gvkn':hashval -> Prop) t st th dl :
  (forall h a, gvtp h a -> gvtp' h a)
  -> (forall h, gvkn h -> gvkn' h)
  -> check_doc_p gvtp gvkn t st th dl
  -> check_doc_p gvtp' gvkn' t st th dl.
intros H1 H2. apply check_doc_p_uses.
- intros h a _. apply H1.
- intros h _. apply H2.
Qed.

(***
 The next functions give the burncost for theories and signatures.
 Creating theories and signatures should be done sparingly since they must be kept on every node to check future documents.
 The real functions will give the number of cants based on the number of bytes required to serialize.
 The current idea is that it will be such that 21 million fraenks must be burned to create 1GB of theories and signatures, and so there will be a hard upper bound of 1GB of theories and 1GB of signatures (just counting what is stored at the leaves).
***)
(*** 21 zerms per byte = 21 billion cants per byte ***)
Parameter cants_per_byte : nat. (*** := 21000000000. Leave abstract here to avoid Coq trying to compute with it. The value doesn't matter here. ***)

(***
 These are simply estimates of the number of bytes required to represent the data serialized.
 The way it's implemented in the real code will require more care.
 ***)
Definition stp_numbytes (a:stp) : nat := length (ser_stp a).

Fixpoint stpl_numbytes (al:list stp) : nat :=
  match al with
    | nil => 0
    | a::ar => stp_numbytes a + stpl_numbytes ar
  end.

Fixpoint trm_numbytes (m:trm) : nat :=
  match m with
    | Gn _ => 21
    | Prm _ al => 1 + stpl_numbytes al
    | Db _ => 1
    | Ap m n => 1 + trm_numbytes m + trm_numbytes n
    | La a m => 1 + stp_numbytes a + trm_numbytes m
    | Imp m n => 1 + trm_numbytes m + trm_numbytes n
    | All a m => 1 + stp_numbytes a + trm_numbytes m
  end.

Fixpoint odefl_numbytes (dl: list (prod hashval (prod stp (option trm)))) : nat :=
  match dl with
    | nil => 0
    | (h,(a,None))::dr => stp_numbytes a + 21 + odefl_numbytes dr
    | (h,(a,Some(m)))::dr => stp_numbytes a + trm_numbytes m + 21 + odefl_numbytes dr
  end.

Definition theory_burncost (thy:theory) : nat :=
  let (al,kl) := thy in
  cants_per_byte * stpl_numbytes al
  +
  cants_per_byte * 21 * length kl.

Definition theoryspec_burncost (s:theoryspec) : nat := theory_burncost (theoryspec_theory s).

Fixpoint signaspec_burncost (s:signaspec) : nat :=
  match s with
    | signasigna h::s => cants_per_byte * 21 + signaspec_burncost s
    | signaparam h a::s => cants_per_byte * (stp_numbytes a + 21) + signaspec_burncost s
    | signadef a m::s => cants_per_byte * (trm_numbytes m + stp_numbytes a + 21) + signaspec_burncost s
    | signaknown p::s => cants_per_byte * 21 + signaspec_burncost s
    | nil => 0
  end.

Definition signa_burncost (s:signa) : nat :=
  match s with
    | (sl,(dl,kl)) =>
      length sl * cants_per_byte * 21
      + 
      odefl_numbytes dl * cants_per_byte
      +
      length kl * cants_per_byte * 21
  end.

Lemma signaspec_signa_burncost_eq (th:option hashval) (s:signaspec) :
  signaspec_burncost s = signa_burncost (signaspec_signa th s).
induction s as [|[h|h a|a m|p] sr IH].
- simpl. omega.
- simpl. rewrite IH. simpl. omega.
- simpl. rewrite IH. simpl.
  assert (L1: (stp_numbytes a + 21 + odefl_numbytes (signaspec_trms th sr)) * cants_per_byte = (stp_numbytes a + 21) * cants_per_byte + odefl_numbytes (signaspec_trms th sr) * cants_per_byte).
  { apply mult_plus_distr_r. }
  rewrite L1.
  rewrite mult_comm.
  omega.
- simpl. rewrite IH. simpl. repeat rewrite mult_plus_distr_l. repeat rewrite mult_plus_distr_r.
  rewrite (mult_comm 21). 
  repeat rewrite (mult_comm cants_per_byte).
  rewrite (mult_comm 21). 
  omega.
- simpl. rewrite IH. simpl. omega.
Qed.

Fixpoint htree_sum (A:Type) (f:A -> nat) (n:nat) : htree A n -> nat :=
  match n with
    | 0 => fun x:htree A 0 => f x
    | S n => fun t:htree A (S n) => match t with
                                      | (None,None) => 0
                                      | (Some l,None) => htree_sum A f n l
                                      | (None,Some r) => htree_sum A f n r
                                      | (Some l,Some r) => htree_sum A f n l + htree_sum A f n r
                                    end
  end.

Definition ottree_burncost {n} (tht:option (ttree n)) : nat :=
  match tht with
    | None => 0
    | Some(tht) => htree_sum theory theory_burncost n tht
  end.

Definition ostree_burncost {n} (sigt:option (stree n)) : nat :=
  match sigt with
    | None => 0
    | Some(sigt) => htree_sum (option hashval * signa) (fun z => let (x,y) := z in signa_burncost y) n sigt
  end.
