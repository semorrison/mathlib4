From Coq Require Import ZArith.
Require Import Lia.

Open Scope Z_scope.

Require Import Lia.

Ltac fail_if_success T :=
  try (first [ T; fail 1 | idtac ]).

Example ex1 : True.
Proof. do 1000000 fail_if_success lia; trivial. Qed.
