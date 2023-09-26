From Coq Require Import ZArith.
Require Import Lia.

Open Scope Z_scope.

Lemma example : forall x: Z, forall y: Z, 3 <= 11*x+13*y /\ 11*x+13*y <= 21 /\ -8 <= 7*x-9*y /\ 7*x-9*y <= 6 -> False.
Proof.
  lia.
Qed.
