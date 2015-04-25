(** Copyright (c) 2015 Bill White **)
(** Distributed under the MIT/X11 software license **)
(** See http://www.opensource.org/licenses/mit-license.php **)

(** DTrees: Merkle tree representations of data.
 **)

Require Export DTrees.

Fixpoint etree (n:nat) : Type :=
  match n with
    | 0 => nat (*** word/int32 in the real implementation ***)
    | S n => sum hashval
                 (sum (etree n)
                      (prod (etree n) (etree n)))
  end.

Fixpoint etree_hashroot {n} : etree n -> hashval :=
match n with
| O => fun d:etree 0 => hashnat d
| S n => fun T : etree (S n) =>
           match T with
             | inl h => h
             | inr (inl Tl) => hashopair1 (etree_hashroot Tl) None
             | inr (inr (Tl,Tr)) => hashopair1 (etree_hashroot Tl) (Some (etree_hashroot Tr))
           end
end.

Fixpoint approx_edtree {m n:nat} : etree m -> dtree n -> Prop :=
match m as m' return forall n:nat, etree m' -> dtree n -> Prop with
| O => fun n x => match n as n' return dtree n' -> Prop with O => fun y => x = y | _ => fun y => False end
| S m => fun n e =>
           match n as n' return dtree n' -> Prop with
             | O => fun d => False
             | S n =>
               match e with
                 | inl h => fun d => h = dtree_hashroot d
                 | inr (inl Te) => fun d =>
                   match d with
                     | inl Td => approx_edtree Te Td
                     | _ => False
                   end
                 | inr (inr (Tel,Ter)) => fun d =>
                   match d with
                     | inr (Tdl,Tdr) => approx_edtree Tel Tdl /\  approx_edtree Ter Tdr
                     | _ => False
                   end
               end
           end
end n.

Lemma approx_edtree_hashroot_eq {m n} (e:etree m) (d:dtree n) :
  approx_edtree e d -> etree_hashroot e = dtree_hashroot d.
revert n e d. induction m as [|m IH]; intros [|n] e d.
- simpl. congruence.
- simpl. tauto.
- simpl. tauto.
- destruct e as [h|[Te|[Tel Ter]]].
  + simpl. tauto.
  + destruct d as [Td|[Tdl Tdr]].
    * simpl. intros H1. apply IH in H1. congruence.
    * simpl. tauto.
  + destruct d as [Td|[Tdl Tdr]].
    * simpl. tauto.
    * simpl. intros [H1 H2]. apply IH in H1. apply IH in H2. congruence.
Qed.

Lemma hashroot_eq_approx_edtree {n} (e:etree n) (d:dtree n) :
  approx_edtree e d <-> etree_hashroot e = dtree_hashroot d.
split.
- apply approx_edtree_hashroot_eq.
- revert e d. induction n as [|n IH]; intros e d.
  + simpl. apply hashnatinj.
  + simpl. destruct e as [h|[T|[Tl Tr]]].
    * tauto.
    * { destruct d as [Td|[Tdl Tdr]].
        - intros H1. apply hashpairinj in H1. destruct H1 as [_ H1].
          revert H1. apply IH.
        - intros H1. exfalso. apply hashpairinj in H1. destruct H1 as [H1 _].
          apply hashnatinj in H1. omega.
      }
    * { destruct d as [Td|[Tdl Tdr]].
        - intros H1. exfalso. apply hashpairinj in H1. destruct H1 as [H1 _].
          apply hashnatinj in H1. omega.
        - intros H1. apply hashpairinj in H1. destruct H1 as [_ H1].
          apply hashpairinj in H1. destruct H1 as [H2 H3].
          apply hashpairinj in H3. destruct H3 as [H3 _].
          split.
          + revert H2. apply IH.
          + revert H3. apply IH.
      }
Qed.
