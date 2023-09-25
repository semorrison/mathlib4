import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.RunCmd

set_option autoImplicit true

@[macro_inline] def ite' {α : Sort u} (c : Prop) [h : Decidable c] (t e : α) : α :=
  (match h with
  | isTrue _ => fun _ => t
  | isFalse _ => fun _ => e) ()

def yum (P : Prop) [i : Decidable P] {C : α → Sort _} (x : C a) (y : C b) :
    C (if P then a else b) :=
  match i with
  | isTrue _ => x
  | isFalse _ => y

-- def mmmm (P : Prop) [Decidable P] {C : α → Sort _} (x : C a) (y : C b) :
--     C (if P then a else b) :=
--   if P then x else y

def yuck (P : Prop) [Decidable P] {C : α → Sort _} (x : C a) (y : C b) :
    C (if P then a else b) := by
  split_ifs
  · exact x
  · exact y

#print yuck


def mmmm! (P : Prop) [Decidable P] {C : α → Sort _} (x : C a) (y : C b) :
    C (match decide P with | true => a | false => b) :=
  match decide P with | true => x | false => y

run_cmd do if false then pure 3 else pure 7

macro_rules
  | `(if $c then $t else $e) => do
    let mvar ← Lean.withRef c `(?m)
    `(let_mvar% ?m := $c; wait_if_type_mvar% ?m; match decide $mvar with | true => $t | false => $e)


def mmmm!! (P : Prop) [Decidable P] {C : α → Sort _} (x : C a) (y : C b) :
    C (if P then a else b) :=
  if P then x else y


#print mmmm!!

-- run_cmd do if false then pure 3 else pure 7


def foo := do if true then return (← IO.println "true") else return (← IO.println "false")

#eval foo
