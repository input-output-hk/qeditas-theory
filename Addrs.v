(** Copyright (c) 2015 Bill White **)
(** Distributed under the MIT/X11 software license **)
(** See http://www.opensource.org/licenses/mit-license.php **)

(** Addrs : Representation of addresses as 160 bit sequences. **)

Require Export Prelude.

Fixpoint bitseq (n:nat) : Type :=
match n with
| 0 => unit
| S n' => (bool * bitseq n')%type
end.

Definition bitseq_eq_dec {n} (bs1 bs2:bitseq n) : { bs1 = bs2 } + { bs1 <> bs2 }.
induction n as [|n IHn].
- destruct bs1, bs2. decide equality.
- destruct bs1 as [b1 bs1], bs2 as [b2 bs2]. repeat decide equality.
Defined.

Fixpoint listbool_bitseq (bl:list bool) : bitseq (length bl) :=
match bl with
| nil => tt
| b::br => (b,listbool_bitseq br)
end.

Fixpoint bitseq_listbool {n} (bs:bitseq n) : list bool :=
match n as n' return bitseq n' -> list bool with
| O => fun _ => nil
| S n => fun bs => let (b,br) := bs in (b::bitseq_listbool br)
end bs.

Lemma listbool_bitseq_listbool bl : bitseq_listbool (listbool_bitseq bl) = bl.
induction bl as [|b bl IH].
- reflexivity.
- simpl. congruence.
Qed.

Lemma bitseq_listbool_length {n} (bs:bitseq n) : length (bitseq_listbool bs) = n.
induction n as [|n IH].
- reflexivity.
- destruct bs as [b bs]. simpl. rewrite IH. reflexivity.
Qed.

Fixpoint strip_bitseq_false {n:nat} {X:Type} (l:list (bitseq (S n) * X)%type) : list (bitseq n * X)%type :=
match l with
| nil => nil
| cons ((false,bs),x) l' => cons (bs,x) (strip_bitseq_false l')
| cons ((true,bs),x) l' => strip_bitseq_false l'
end.

Fixpoint strip_bitseq_true {n:nat} {X:Type} (l:list (bitseq (S n) * X)%type) : list (bitseq n * X)%type :=
match l with
| nil => nil
| cons ((true,bs),x) l' => cons (bs,x) (strip_bitseq_true l')
| cons ((false,bs),x) l' => strip_bitseq_true l'
end.

Lemma strip_bitseq_false_iff {n} {X} (alpha:bitseq n) (x:X) (l:list (bitseq (S n) * X)%type) :
  In (alpha,x) (strip_bitseq_false l) <-> In ((false,alpha),x) l.
induction l as [|[[[|] beta] y] l IH].
- simpl. tauto.
- simpl. split.
  + intros H1. right. now apply IH.
  + intros [H1|H1].
    * inversion H1.
    * now apply IH.
- simpl. split.
  + intros [H1|H1].
    * left. inversion H1. reflexivity.
    * right. now apply IH.
  + intros [H1|H1].
    * inversion H1. now left.
    * right. now apply IH.
Qed.

Lemma strip_bitseq_true_iff {n} {X} (alpha:bitseq n) (x:X) (l:list (bitseq (S n) * X)%type) :
  In (alpha,x) (strip_bitseq_true l) <-> In ((true,alpha),x) l.
induction l as [|[[[|] beta] y] l IH].
- simpl. tauto.
- simpl. split.
  + intros [H1|H1].
    * left. inversion H1. reflexivity.
    * right. now apply IH.
  + intros [H1|H1].
    * inversion H1. now left.
    * right. now apply IH.
- simpl. split.
  + intros H1. right. now apply IH.
  + intros [H1|H1].
    * inversion H1.
    * now apply IH.
Qed.

Fixpoint bitseq_concat {n} (bs:bitseq n) {m} (br:bitseq m) : bitseq (n+m) :=
match n as n' return bitseq n' -> bitseq (n'+m) with
| O => fun _ => br
| S n => fun bs => let (b,bs') := bs in (b,bitseq_concat bs' br)
end bs.

Definition termaddr := bitseq 160.

Definition termaddr_eq_dec (a1 a2: termaddr) : { a1 = a2 } + { a1 <> a2 }.
apply bitseq_eq_dec.
Defined.

Definition pubaddr := bitseq 160.

Definition pubaddr_eq_dec (a1 a2: pubaddr) : { a1 = a2 } + { a1 <> a2 }.
apply bitseq_eq_dec.
Defined.

Definition payaddr := bitseq 161.

Definition payaddr_eq_dec (a1 a2: payaddr) : { a1 = a2 } + { a1 <> a2 }.
apply bitseq_eq_dec.
Defined.

Definition addr := bitseq 162.

Definition addr_eq_dec (a1 a2: addr) : { a1 = a2 } + { a1 <> a2 }.
apply bitseq_eq_dec.
Defined.

Definition payaddr_addr (alpha:payaddr) : addr := (false,alpha).

Definition termaddr_addr (a:termaddr) : addr := (true,(false,a)).

Definition pubaddr_addr (a:termaddr) : addr := (true,(true,a)).

Lemma payaddr_addr_inj a b : payaddr_addr a = payaddr_addr b -> a = b.
intros H1. destruct a as [[|] a]; destruct b as [[|] b]; try discriminate H1.
- inversion H1. congruence.
- inversion H1. congruence.
Qed.

Lemma termaddr_addr_inj a b : termaddr_addr a = termaddr_addr b -> a = b.
intros H1. destruct a as [[|] [[|] a]]; destruct b as [[|] [[|] b]]; try discriminate H1.
- inversion H1. congruence.
- inversion H1. congruence.
- inversion H1. congruence.
- inversion H1. congruence.
Qed.

Lemma pubaddr_addr_inj a b : pubaddr_addr a = pubaddr_addr b -> a = b.
intros H1. destruct a as [[|] [[|] a]]; destruct b as [[|] [[|] b]]; try discriminate H1.
- inversion H1. congruence.
- inversion H1. congruence.
- inversion H1. congruence.
- inversion H1. congruence.
Qed.

Definition p2pkh_payaddr_p (alpha:payaddr) : Prop :=
  match alpha with
    | (false,_) => True
    | _ => False
  end.

Definition p2sh_payaddr_p (alpha:payaddr) : Prop :=
  match alpha with
    | (true,_) => True
    | _ => False
  end.

Definition p2pkh_addr_p (alpha:addr) : Prop :=
  match alpha with
    | (false,(false,_)) => True
    | _ => False
  end.

Definition p2sh_addr_p (alpha:addr) : Prop :=
  match alpha with
    | (false,(true,_)) => True
    | _ => False
  end.

Definition pay_addr_p (alpha:addr) : Prop :=
  match alpha with
    | (false,_) => True
    | _ => False
  end.

Definition term_addr_p (alpha:addr) : Prop :=
  match alpha with
    | (true,(false,_)) => True
    | _ => False
  end.

Definition publication_addr_p (alpha:addr) : Prop :=
  match alpha with
    | (true,(true,_)) => True
    | _ => False
  end.


