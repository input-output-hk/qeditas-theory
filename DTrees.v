(** Copyright (c) 2015 Bill White **)
(** Distributed under the MIT/X11 software license **)
(** See http://www.opensource.org/licenses/mit-license.php **)

(** DTrees: Merkle tree representations of data.
 **)

Require Export CryptoSignatures.

Fixpoint dtree (n:nat) : Type :=
  match n with
    | 0 => nat (*** word/int32 in the real implementation ***)
    | S n => sum (dtree n)
                 (prod (dtree n) (dtree n))
  end.

Fixpoint dtree_hashroot {n} : dtree n -> hashval :=
match n with
| O => fun d:dtree 0 => hashnat d
| S n => fun T : dtree (S n) =>
           match T with
             | inl Tl => hashopair1 (dtree_hashroot Tl) None
             | inr (Tl,Tr) => hashopair1 (dtree_hashroot Tl) (Some (dtree_hashroot Tr))
           end
end.

(*** ceiling of half ***)
Fixpoint half n : nat :=
match n with
| O => 0
| S O => 1
| S (S n) => S (half n)
end.

Fixpoint exp2 (n:nat) : nat :=
match n with
| O => 1
| S n => 2 * exp2 n
end.

Definition tmin (n m:nat) : nat := minus n (minus n m).

Lemma tmin_2 m n : n >= m -> tmin n m = m.
revert m. induction n as [|n IH]; intros [|m] H1.
- reflexivity.
- exfalso. omega.
- unfold tmin. simpl. omega.
- assert (L1: n >= m) by omega.
  generalize (IH m L1).
  unfold tmin. simpl.
  destruct (n - m) as [|k] eqn:E1.
  + omega.
  + omega.
Qed.  

Lemma half_geq m n : n > 1 -> S m >= n -> m >= half n.
revert n. induction m as [|m IH]; intros [|[|n]]; simpl; try omega.
intros H1 H2.
assert (L1: n = 0 \/ n = 1 \/ n > 1) by omega.
destruct L1 as [H3|[H3|H3]].
- subst n. simpl. omega.
- subst n. simpl. omega.
- assert (L1: S m >= n) by omega.
  generalize (IH n H3 L1). omega.
Qed.

Lemma tmin_half_S_eq n : n > 0 -> tmin n (half (S n)) = half (S n).
intros H1. apply tmin_2. apply half_geq; omega.
Qed.

(*** ceiling log2 ***)
Fixpoint log2 (n:nat) : nat :=
match n with
| O => 0
| S O => 0
| S n => S (log2 (tmin n (half (S n))))
end.

Lemma log2_eq n : n = 0 \/ n = 1 \/ log2 n = S (log2 (half n)).
revert n. fix IH 1. intros [|[|n]].
- simpl. omega.
- simpl. omega.
- right. right. simpl. rewrite tmin_half_S_eq.
  + reflexivity.
  + omega.
Qed.

Lemma exp2_pos n : exp2 n > 0.
induction n as [|n IH].
- simpl. omega.
- simpl. omega.
Qed.

Lemma half_double_leq m n : half m <= n -> m <= 2 * n.
revert m. induction n as [|n IH]; intros [|[|m]]; simpl; try omega.
intros H1.
assert (L1: half m <= n) by omega.
apply IH in L1. omega.
Qed.

Lemma exp2_log2_le m n : log2 m <= n -> m <= exp2 n.
revert m. induction n as [|n IH]; intros m H1.
- destruct m as [|[|m]]; simpl in H1; simpl; omega.
- destruct (log2_eq m) as [H2|[H2|H2]].
  + omega.
  + subst m. generalize (exp2_pos (S n)). omega.
  + assert (L1: log2 (half m) <= n) by omega.
    apply IH in L1. simpl.
    apply half_double_leq in L1.
    omega.
Qed.

Fixpoint wordlist_to_dtree_rec (n:nat) (l:list nat) : dtree n * list nat :=
match n as n' return dtree n' * list nat with
| O =>
  match l with
    | (x::r) => (x,r)
    | nil => (0,nil)
  end
| S n =>
  let (d,r) := wordlist_to_dtree_rec n l in
  match r with
    | nil => (inl d,nil)
    | _ =>
      let (e,s) := wordlist_to_dtree_rec n r in
      (inr (d,e),s)
  end
end.

Definition wordlist_to_dtree (l:list nat) : dtree (log2 (length l)) :=
let (d,_) := wordlist_to_dtree_rec (log2 (length l)) l in d.

Lemma wordlist_to_dtree_lem_1 n l d r : wordlist_to_dtree_rec n l = (d,r) -> length r <= length l - exp2 n.
revert l d r. induction n as [|n IH]; intros [|x l] d r.
- simpl. intros H1.
  assert (L: r = nil) by congruence.
  rewrite L. simpl. omega.
- simpl. intros H1.
  assert (L: l = r) by congruence.
  rewrite L. omega.
- simpl. destruct (wordlist_to_dtree_rec n nil) as [d1 r1] eqn:E1.
  apply IH in E1. simpl in E1. destruct r1 as [|x1 r1].
  + intros H1.
    assert (L: r = nil) by congruence.
    rewrite L. simpl. omega.
  + exfalso. simpl in E1. omega.
- simpl. destruct (wordlist_to_dtree_rec n (x::l)) as [d1 r1] eqn:E1.
  apply IH in E1. simpl in E1. destruct r1 as [|x1 r1].
  + intros H1.
    assert (L: r = nil) by congruence.
    rewrite L. simpl. omega.
  + destruct (wordlist_to_dtree_rec n (x1::r1)) as [d2 r2] eqn:E2.
    apply IH in E2.
    intros H1.
    assert (L: r2 = r) by congruence.
    subst r2.
    assert (L2: length (x1 :: r1) - exp2 n <= match exp2 n + (exp2 n + 0) with
                                                | 0 => S (length l)
                                                | S l0 => length l - l0
                                              end).
    { simpl. destruct (exp2 n) as [|e] eqn:E3.
      - simpl. exact E1.
      - simpl. simpl in E1. omega.
    }
    omega.
Qed.

Lemma wordlist_to_dtree_lem_2 n l d r : n >= log2 (length l) -> wordlist_to_dtree_rec n l = (d,r) -> r = nil.
intros H1 H2.
apply wordlist_to_dtree_lem_1 in H2.
assert (L1: length l <= exp2 n).
{ apply exp2_log2_le. omega. }
assert (L2: length r <= 0) by omega.
destruct r as [|r].
- reflexivity.
- simpl in L2. omega.
Qed.

Fixpoint dtree_to_wordlist {n} : dtree n -> list nat :=
match n with
| O => fun d:dtree 0 => cons d nil
| S n => fun T:dtree (S n) =>
           match T with
             | inl Tl => dtree_to_wordlist Tl
             | inr (Tl,Tr) => dtree_to_wordlist Tl ++ dtree_to_wordlist Tr
           end
end.

Lemma wordlist_to_dtree_rec_eq n l d r : wordlist_to_dtree_rec n l = (d,r) -> l = nil \/ l = dtree_to_wordlist d ++ r.
revert l d r. induction n as [|n IH]; intros [|x l] d r H1.
- now left.
- right. simpl in H1. inversion H1. simpl. reflexivity.
- now left.
- right. simpl in H1.
  destruct (wordlist_to_dtree_rec n (x :: l)) as [e s] eqn:E1.
  destruct (IH (x::l) e s E1) as [H2|H2].
  + discriminate H2.
  + destruct s as [|y s].
    * inversion H1. exact H2.
    * { destruct (wordlist_to_dtree_rec n (y :: s)) as [e2 s2] eqn:E2.
        destruct (IH (y :: s) e2 s2 E2) as [H3|H3].
        - discriminate H3.
        - inversion H1. simpl. subst s2. rewrite H3 in H2. rewrite <- app_assoc. exact H2.
      }
Qed.

Lemma wordlist_to_dtree_eq l : l = nil \/ dtree_to_wordlist (wordlist_to_dtree l) = l.
unfold wordlist_to_dtree.
destruct (wordlist_to_dtree_rec (log2 (length l)) l) as [d r] eqn:E1.
assert (L1: r = nil).
{ revert E1. apply wordlist_to_dtree_lem_2. omega. }
subst r.
apply wordlist_to_dtree_rec_eq in E1.
destruct E1 as [H1|H1].
- now left.
- right. rewrite <- app_nil_end in H1. now symmetry.
Qed.

Lemma dtree_hashroot_leveq {m n} (d:dtree m) (d':dtree n) : dtree_hashroot d = dtree_hashroot d' -> m = n.
revert n d d'. induction m as [|m IH]; intros [|n].
- tauto.
- intros d [T'|[Tl' Tr']]; simpl.
  + intros H1. exfalso. revert H1. apply hashnatpairdiscr.
  + intros H1. exfalso. revert H1. apply hashnatpairdiscr.
- intros [T|[Tl Tr]] h; simpl.
  + intros H1. exfalso. symmetry in H1. revert H1. apply hashnatpairdiscr.
  + intros H1. exfalso. symmetry in H1. revert H1. apply hashnatpairdiscr.
- intros [T|[Tl Tr]] [T'|[Tl' Tr']]; simpl; try tauto.
  + intros H1. f_equal. apply hashpairinj in H1. destruct H1 as [_ H1].
    revert H1. apply IH.
  + intros H1. exfalso. apply hashpairinj in H1. destruct H1 as [H1 _]. apply hashnatinj in H1. omega.
  + intros H1. exfalso. apply hashpairinj in H1. destruct H1 as [H1 _]. apply hashnatinj in H1. omega.
  + intros H1. f_equal. apply hashpairinj in H1. destruct H1 as [_ H1]. apply hashpairinj in H1. destruct H1 as [H1 _].
    revert H1. apply IH.
Qed.

Lemma dtree_hashroot_inj {m n} (d:dtree m) (d':dtree n) : dtree_hashroot d = dtree_hashroot d' -> existT dtree m d = existT dtree n d'.
intros H1.
assert (L: m = n).
{ exact (dtree_hashroot_leveq d d' H1). }
subst m. f_equal.
revert d d' H1. induction n as [|n IH]; intros d d'.
- simpl. apply hashnatinj.
- destruct d as [T|[Tl Tr]]; destruct d' as [T'|[Tl' Tr']].
  + simpl. intros H1. apply hashpairinj in H1.
    destruct H1 as [_ H1]. f_equal. f_equal. revert H1. simpl. apply IH.
  + simpl. intros H1. apply hashpairinj in H1.
    destruct H1 as [H1 _]. apply hashnatinj in H1. omega.
  + simpl. intros H1. apply hashpairinj in H1.
    destruct H1 as [H1 _]. apply hashnatinj in H1. omega.
  + simpl. intros H1. apply hashpairinj in H1. destruct H1 as [_ H1].
    apply hashpairinj in H1. destruct H1 as [H2 H3].
    apply hashpairinj in H3. destruct H3 as [H3 _].
    f_equal. f_equal. f_equal.
    * revert H2. simpl. apply IH.
    * revert H3. simpl. apply IH.
Qed.

Definition hashwordlist (l:list nat) : hashval := dtree_hashroot (wordlist_to_dtree l).

Lemma hashwordlistinj_lem (m n:nat) (d:dtree m) (d':dtree n) (l l':list nat) (r r':list nat) :
  l <> nil -> l' <> nil ->
  wordlist_to_dtree_rec m l = (d,r) ->
  wordlist_to_dtree_rec n l' = (d',r') ->
  dtree_hashroot d = dtree_hashroot d' ->
  r = r' ->
  l = l'.
revert n d d' l l' r r'. induction m as [|m IH]; intros [|n].
- simpl. intros d d' [|x l] [|x' l'] r r'; try tauto.
  intros _ _ H1 H2 H3 H4.
  inversion H1. inversion H2.
  apply hashnatinj in H3.
  congruence.
- intros d d' l l' r r' Hl Hl' H1 H2 H3 H4.
  exfalso.
  assert (L1: 0 = S n).
  { exact (dtree_hashroot_leveq d d' H3). }
  discriminate L1.
- intros d d' l l' r r' Hl Hl' H1 H2 H3 H4.
  exfalso.
  assert (L1: S m = 0).
  { exact (dtree_hashroot_leveq d d' H3). }
  discriminate L1.
- simpl. intros d d' l l' r r' Hl Hl' H1 H2 H3 H4.
  destruct (wordlist_to_dtree_rec m l) as [e s] eqn:E.
  destruct (wordlist_to_dtree_rec n l') as [e' s'] eqn:E'.
  destruct (wordlist_to_dtree_rec m s) as [f q] eqn:F.
  destruct (wordlist_to_dtree_rec n s') as [f' q'] eqn:F'.
  apply (IH n e e' l l' s s' Hl Hl' E E').
  + destruct s as [|y s]; destruct s' as [|y' s'].
    * inversion H1. inversion H2. subst d. subst d'. apply hashpairinj in H3. tauto.
    * exfalso. inversion H1. inversion H2. subst d. subst d'. apply hashpairinj in H3.
      destruct H3 as [H3 _]. apply hashnatinj in H3. omega.
    * exfalso. inversion H1. inversion H2. subst d. subst d'. apply hashpairinj in H3.
      destruct H3 as [H3 _]. apply hashnatinj in H3. omega.
    * inversion H1. inversion H2. subst d. subst d'. apply hashpairinj in H3.
      destruct H3 as [_ H3]. apply hashpairinj in H3. tauto.
  + destruct s as [|y s]; destruct s' as [|y' s'].
    * reflexivity.
    * exfalso. inversion H1. inversion H2. subst d. subst d'. apply hashpairinj in H3.
      destruct H3 as [H3 _]. apply hashnatinj in H3. omega.
    * exfalso. inversion H1. inversion H2. subst d. subst d'. apply hashpairinj in H3.
      destruct H3 as [H3 _]. apply hashnatinj in H3. omega.
    * { assert (L1: y::s <> nil) by discriminate.
        assert (L2: y'::s' <> nil) by discriminate.
        apply (IH n f f' (y::s) (y'::s') q q' L1 L2 F F').
        - inversion H1. inversion H2. subst d. subst d'. apply hashpairinj in H3.
          destruct H3 as [_ H3]. apply hashpairinj in H3.
          destruct H3 as [_ H3]. apply hashpairinj in H3.
          tauto.
        - inversion H1. inversion H2. assumption.
      }
Qed.

Lemma hashwordlistinj (l l':list nat) : l <> nil -> l' <> nil -> hashwordlist l = hashwordlist l' -> l = l'.
unfold hashwordlist. unfold wordlist_to_dtree.
destruct (wordlist_to_dtree_rec (log2 (length l)) l) as [d r] eqn:E.
destruct (wordlist_to_dtree_rec (log2 (length l')) l') as [d' r'] eqn:E'.
intros Hl Hl' H1.
apply (hashwordlistinj_lem _ _ d d' l l' r r' Hl Hl' E E' H1).
assert (L1: r = nil).
{ revert E. apply wordlist_to_dtree_lem_2. omega. }
assert (L2: r' = nil).
{ revert E'. apply wordlist_to_dtree_lem_2. omega. }
congruence.
Qed.

