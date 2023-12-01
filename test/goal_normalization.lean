import Mathlib.Tactic.GoalNormalization.NormalizeHyps

set_option linter.unusedVariables false
set_option pp.sanitizeNames false

/--
error: unsolved goals
b : Int
a : Nat
⊢ True
-/
#guard_msgs in
example (a : Nat) (b : Int) : True := by
  reorder_hyps

/--
error: unsolved goals
a : Int
b : Nat
⊢ True
-/
#guard_msgs in
example (a : Int) (b : Nat) : True := by
  reorder_hyps

/--
error: unsolved goals
a : Int
w : a = 0
⊢ True
-/
#guard_msgs in
example (a : Int) (w : a = 0) : True := by
  reorder_hyps

/--
error: unsolved goals
A : Int
w : A = 0
⊢ True
-/
#guard_msgs in
example (A : Int) (w : A = 0) : True := by
  reorder_hyps


/--
error: unsolved goals
h1 : Nat
h2 : Int
⊢ True
-/
#guard_msgs in
example (a : Nat) (b : Int) : True := by
  normalize_names

/--
error: unsolved goals
h1 : Int
h2 : Nat
⊢ True
-/
#guard_msgs in
example (a : Int) (b : Nat) : True := by
  normalize_names

/--
error: unsolved goals
h1 : Int
h2 : h1 = 0
⊢ True
-/
#guard_msgs in
example (a : Int) (w : a = 0) : True := by
  normalize_names

/--
error: unsolved goals
h0 : Int
h1 : Nat
h2 : h0 = 0
h3 : h1 = 0
⊢ True
-/
#guard_msgs in
example (a : Int) (w : a = 0) (b : Nat) (h : b = 0) : True := by
  reorder_hyps
  normalize_names

/--
error: unsolved goals
h0 : Int
h1 : Nat
h2 : h0 = 0
h3 : h1 = 0
⊢ True
-/
#guard_msgs in
example (y : Int) (x : Nat)  (_ : x = 0) (_ : y = 0) : True := by
  -- Because the names appear in the types, `reorder_hyps; normalize_names` is not idempotent!
  reorder_hyps
  normalize_names
  reorder_hyps
  normalize_names

/--
error: unsolved goals
h0 : Int
h1 : Nat
h2 : h0 = 0
h3 : h1 = 0
⊢ True
-/
#guard_msgs in
example (a : Int) (w : a = 0) (b : Nat) (h : b = 0) : True := by
  normalize_hyps

/--
error: unsolved goals
h0 : Int
h1 : Nat
h2 : h0 = 0
h3 : h1 = 0
⊢ True
-/
#guard_msgs in
example (y : Int) (x : Nat)  (_ : x = 0) (_ : y = 0) : True := by
  normalize_hyps
