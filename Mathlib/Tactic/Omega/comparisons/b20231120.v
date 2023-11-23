From Coq Require Import ZArith.
Require Import Lia.

Open Scope Z_scope.

Require Import Lia.

Ltac fail_if_success T :=
  try (first [ T; fail 1 | idtac ]).

Example ex1 : True.
Proof. fail_if_success lia; trivial. Qed.

Example ex2 : forall (_ : (1 < 0)%Z), False.
Proof. lia. Qed.

Example ex3 : forall (_ : (0 < 0)%Z), False.
Proof. lia. Qed.
Example ex4 : forall (_ : (0 < 1)%Z), True.
Proof. fail_if_success lia; trivial. Qed.

(* Example ex5 : forall x : Z, (x mod 2 < x - 2 * (x / 2))%Z -> False.
Proof. lia. Qed. *)
(* Example ex6 : forall x : Z, (x mod 2 > 5)%Z -> False.
Proof. lia. Qed. *)

(*Example ex7 : forall x : Z, (2 * (x / 2) > x)%Z -> False.
Proof. lia. Qed.*)
(*Example ex8 : forall x : Z, (2 * (x / 2) <= x - 2)%Z -> False.
Proof. lia. Qed.*)

Example ex9 : (7 < 3)%Z -> False.
Proof. lia. Qed.
Example ex10 : (0 < 0)%Z -> False.
Proof. lia. Qed.

Example ex11 : forall x : nat, (x > 7)%nat -> (x < 3)%nat -> False.
Proof. lia. Qed.
Example ex12 : forall x : nat, (x >= 7)%nat -> (x <= 3)%nat -> False.
Proof. lia. Qed.
Example ex13 : forall x y : nat, (x + y > 10)%nat -> (x < 5)%nat -> (y < 5)%nat -> False.
Proof. lia. Qed.

Example ex14 : forall x y : Z, (x + y > 10)%Z -> (2 * x < 5)%Z -> (y < 5)%Z -> False.
Proof. lia. Qed.
Example ex15 : forall x y : nat, (x + y > 10)%nat -> (2 * x < 5)%nat -> (y < 5)%nat -> False.
Proof. lia. Qed.

Example ex16 : forall x y : Z, (2 * x + 4 * y = 5)%Z -> False.
Proof. lia. Qed.
Example ex17 : forall x y : nat, (2 * x + 4 * y = 5)%nat -> False.
Proof. lia. Qed.

Example ex18 : forall x y : Z, (6 * x + 7 * y = 5)%Z -> True.
Proof. fail_if_success lia; trivial. Qed.
Example ex19 : forall x y : nat, (6 * x + 7 * y = 5)%nat -> False.
Proof. lia. Qed.

Example ex20 : forall x : nat, (x < 0)%nat -> False.
Proof. lia. Qed.

Example ex21 : forall x y z : Z, (x + y > z)%Z -> (x < 0)%Z -> (y < 0)%Z -> (z > 0)%Z -> False.
Proof. lia. Qed.

Example ex22 : forall x y : nat, (x - y = 0)%nat -> (x > y)%nat -> False.
Proof. lia. Qed.

Example ex23 : forall x y z : Z, (x - y - z = 0)%Z -> (x > y + z)%Z -> False.
Proof. lia. Qed.

Example ex24 : forall x y z : nat, (x - y - z = 0)%nat -> (x > y + z)%nat -> False.
Proof. lia. Qed.

Example ex25 : forall a b c d e f : nat, (a - b - c - d - e - f = 0)%nat -> (a > b + c + d + e + f)%nat -> False.
Proof. lia. Qed.

Example ex26 : forall x y : nat, (x - y <= 0)%nat -> (y < x)%nat -> False.
Proof. lia. Qed.

(*Example ex27 : forall x y : Z, (x / 2 - y / 3 < 1)%Z -> (3 * x >= 2 * y + 6)%Z -> False.
Proof. lia. Qed.*)

(*Example ex28 : forall x y : nat, (x / 2 - y / 3 < 1)%nat -> (3 * x >= 2 * y + 6)%nat -> False.
Proof. lia. Qed.*)

(*Example ex29 : forall x y : nat, (x / 2 - y / 3 < 1)%nat -> (3 * x >= 2 * y + 4)%nat -> False.
Proof. lia. Qed.*)

(*Example ex30 : forall x y : nat, (x / 2 - y / 3 < x mod 2)%nat -> (3 * x >= 2 * y + 4)%nat -> False.
Proof. lia. Qed.*)

Example ex31 : forall x : Z, (5 <= x)%Z -> (x <= 4)%Z -> False.
Proof. lia. Qed.

Example ex32 : forall x : nat, (5 <= x)%nat -> (x <= 4)%nat -> False.
Proof. lia. Qed.

(*Example ex33 : forall x : nat, (x / 3 >= 2)%nat -> (x < 6)%nat -> False.
Proof. lia. Qed.*)

Example ex34 : forall x : Z, forall y : nat, (0 < x)%Z -> (x + Z.of_nat y <= 0)%Z -> False.
Proof. lia. Qed.

Example ex35 : forall a b c : nat, (a - (b - c) <= 5)%nat -> (b >= c + 3)%nat -> (a + c >= b + 6)%nat -> False.
Proof. lia. Qed.

(*Example ex36 : forall x y : nat, (x / 2 - y / 3 < x mod 2)%nat -> (3 * x >= 2 * y + 4)%nat -> False.
Proof. lia. Qed.*)

(*Example ex37 : forall x : nat, (1 < (1 + (Z.of_nat (x + 1)) + 2) / 2)%Z.
Proof. lia. Qed.*)

(*Example ex38 : forall x : nat, ((x + 4) / 2 <= x + 2)%nat.
Proof. lia. Qed.*)

(*Example ex39 : forall x : Z, forall m : nat, (0 < m)%nat -> (~ (x mod Z.of_nat m < (Z.of_nat m + 1) / 2))%Z -> (-Z.of_nat m / 2 <= x mod Z.of_nat m - Z.of_nat m)%Z.
Proof. lia. Qed.*)
