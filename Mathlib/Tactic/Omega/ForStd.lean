import Std
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.LibrarySearch

set_option autoImplicit true
set_option relaxedAutoImplicit true

@[simp]
theorem List.map_id''' (l : List α) : l.map (fun a => a) = l := l.map_id

theorem List.mem_of_mem_filter' {a : α} {l} (h : a ∈ filter p l) : a ∈ l :=
  (mem_filter.mp h).1

theorem List.mem_iff_mem_erase_or_eq [DecidableEq α] (l : List α) (a b : α) :
    a ∈ l ↔ a ∈ l.erase b ∨ (a = b ∧ b ∈ l) := by
  by_cases h : a = b
  · subst h
    simp [or_iff_right_of_imp List.mem_of_mem_erase]
  · simp_all

def List.zipWithAll (f : Option α → Option β → γ) : List α → List β → List γ
  | [], bs => bs.map fun b => f none (some b)
  | a :: as, [] => (a :: as).map fun a => f (some a) none
  | a :: as, b :: bs => f a b :: zipWithAll f as bs

@[simp] theorem List.zipWithAll_nil_right :
    List.zipWithAll f as [] = as.map fun a => f (some a) none := by
  cases as <;> rfl

@[simp] theorem List.zipWithAll_nil_left :
    List.zipWithAll f [] bs = bs.map fun b => f none (some b) := by
  rw [List.zipWithAll]

@[simp] theorem List.zipWithAll_cons_cons :
    List.zipWithAll f (a :: as) (b :: bs) = f (some a) (some b) :: zipWithAll f as bs := rfl

theorem Int.div_nonneg_iff_of_pos {a b : Int} (h : 0 < b) : a / b ≥ 0 ↔ a ≥ 0 := by
  rw [Int.div_def]
  match b, h with
  | Int.ofNat (b+1), _ =>
    rcases a with ⟨a⟩ <;> simp [Int.ediv]
    exact decide_eq_decide.mp rfl

attribute [simp] Int.zero_ediv Int.ediv_zero

theorem Int.mul_eq_mul_right_iff {a b c : Int} (h : c ≠ 0) : a * c = b * c ↔ a = b :=
  ⟨Int.eq_of_mul_eq_mul_right h, fun w => congrArg (fun x => x * c) w⟩

attribute [simp] Int.add_zero Int.zero_add Int.sub_zero Int.zero_sub Int.neg_zero

@[simp] theorem ite_some_none_eq_none [Decidable P] :
    (if P then some x else none) = none ↔ ¬ P := by
  split_ifs <;> simp_all

@[simp] theorem ite_some_none_eq_some [Decidable P] :
    (if P then some x else none) = some y ↔ P ∧ x = y := by
  split_ifs <;> simp_all

namespace List

theorem dropWhile_cons :
    (x :: xs : List α).dropWhile p = if p x then xs.dropWhile p else x :: xs := by
  split_ifs <;> simp_all [dropWhile]

@[simp] theorem findIdx?_nil : ([] : List α).findIdx? p i = none := rfl
@[simp] theorem findIdx?_cons :
    (x :: xs).findIdx? p i = if p x then some i else findIdx? p xs (i + 1) := rfl
@[simp] theorem findIdx?_succ :
    (xs : List α).findIdx? p (i+1) = (xs.findIdx? p i).map fun i => i + 1 := by
  induction xs generalizing i with
  | nil => simp
  | cons x xs ih =>
    simp only [findIdx?_cons]
    split_ifs <;> simp_all

theorem findIdx?_eq_some_iff (xs : List α) (p : α → Bool) :
    xs.findIdx? p = some i ↔ (xs.take (i + 1)).map p = List.replicate i false ++ [true] := by
  induction xs generalizing i with
  | nil => simp
  | cons x xs ih =>
    simp only [findIdx?_cons, Nat.zero_add, findIdx?_succ, take_succ_cons, map_cons]
    split_ifs with h
    · cases i <;> simp_all
    · cases i <;> simp_all

theorem findIdx?_of_eq_some {xs : List α} {p : α → Bool} (w : xs.findIdx? p = some i) :
    match xs.get? i with | some a => p a | none => false := by
  induction xs generalizing i with
  | nil => simp_all
  | cons x xs ih =>
    simp_all only [findIdx?_cons, Nat.zero_add, findIdx?_succ]
    split_ifs at w with h
    · cases i <;> simp_all
    · cases i <;> simp_all

theorem findIdx?_of_eq_none {xs : List α} {p : α → Bool} (w : xs.findIdx? p = none) :
    ∀ i, match xs.get? i with | some a => ¬ p a | none => true := by
  intro i
  induction xs generalizing i with
  | nil => simp_all
  | cons x xs ih =>
    simp_all only [Bool.not_eq_true, findIdx?_cons, Nat.zero_add, findIdx?_succ]
    cases i with
    | zero =>
      split_ifs at w
      simp_all
    | succ i =>
      simp only [get?_cons_succ]
      apply ih
      split_ifs at w
      simp_all

@[simp] theorem findIdx?_append :
    (xs ++ ys : List α).findIdx? p =
      (xs.findIdx? p <|> (ys.findIdx? p).map fun i => i + xs.length) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [cons_append, findIdx?_cons, Nat.zero_add, findIdx?_succ]
    split_ifs
    · simp
    · simp_all only [Bool.not_eq_true, Option.map_orElse, Option.map_map, length_cons]
      rfl

@[simp] theorem findIdx?_replicate :
    (List.replicate n a).findIdx? p = if 0 < n ∧ p a then some 0 else none := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [replicate, findIdx?_cons, Nat.zero_add, findIdx?_succ, Nat.zero_lt_succ, true_and]
    split_ifs <;> simp_all

end List

namespace List

theorem exists_of_findSome?_eq_some {l : List α} {f : α → Option β} (w : l.findSome? f = some b) :
    ∃ a, a ∈ l ∧ f a = b := by
  induction l with
  | nil => simp_all
  | cons h l ih =>
    simp_all only [findSome?_cons, mem_cons, exists_eq_or_imp]
    split at w <;> simp_all

end List
