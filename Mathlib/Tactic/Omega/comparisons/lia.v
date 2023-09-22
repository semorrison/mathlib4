From Coq Require Import ZArith.
Require Import Lia.

Open Scope Z_scope.

(*
This does not actually disable the cache within this file,
just prevents it persisting to the disk.
*)
Unset Lia Cache.

Lemma example : forall x: Z, 2*x + 1 >= 0 /\ 2*x + 1 <= 0 -> False.
  lia.
Qed.
