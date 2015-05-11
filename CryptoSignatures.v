(** Copyright (c) 2015 Bill White **)
(** Distributed under the MIT/X11 software license **)
(** See http://www.opensource.org/licenses/mit-license.php **)

(** CryptoSignatures: The trivial code here simulates cryptographic signatures
    using a module that exports a type of signatures and a relation check_signat.
    There are some additional functions and properties exported that are not used
    in the rest of the development.
 **)

Require Export CryptoHashes.

Module Type SignatType.

  Parameter signat : Type.
  Parameter privkey : Type.
  Parameter privkey_payaddr : privkey -> payaddr.
  Parameter sign : privkey -> hashval -> nat -> signat.
  Parameter check_signat : hashval -> signat -> payaddr -> Prop.

  Axiom privkey_payaddr_inj : forall key key', privkey_payaddr key = privkey_payaddr key' -> key = key'.
  Axiom signat_prop : forall r key alpha h, privkey_payaddr key = alpha -> check_signat h (sign key h r) alpha.

End SignatType.

Module Signat : SignatType.

  Definition signat := unit.
  Definition privkey := payaddr.
  Definition privkey_payaddr : privkey -> payaddr := fun alpha => alpha.
  Definition sign : privkey -> hashval -> nat -> signat := fun _ _ _ => tt.
  Definition check_signat : hashval -> signat -> payaddr -> Prop := fun _ _ _ => True.

  Theorem privkey_payaddr_inj (key key':privkey) : privkey_payaddr key = privkey_payaddr key' -> key = key'.
    intros H. exact H.
  Qed.

  Theorem signat_prop r key alpha h : privkey_payaddr key = alpha -> check_signat h (sign key h r) alpha.
    intros _. unfold check_signat. tauto.
  Qed.

End Signat.

Export Signat.

