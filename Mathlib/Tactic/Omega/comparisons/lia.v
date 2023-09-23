From Coq Require Import ZArith.
Require Import Lia.

Open Scope Z_scope.

(*
This does not actually disable the cache within this file,
just prevents it persisting to the disk.

Asked about disabling the cache at
https://coq.zulipchat.com/#narrow/stream/237977-Coq-users/topic/clearing.20the.20.60lia.60.20cache/near/392433497
*)
Unset Lia Cache.

Lemma example : forall x: Z, 2*x + 1 >= 0 /\ 2*x + 1 <= 0 -> False.
  lia.
Qed.
