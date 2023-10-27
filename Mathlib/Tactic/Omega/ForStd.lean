import Std
import Mathlib.Tactic.LibrarySearch

set_option autoImplicit true
set_option relaxedAutoImplicit true

/-- A type synonym to equip a type with its lexicographic order. -/
def Lex (α : Type _) := α

@[inherit_doc] notation:35 α " ×ₗ " β:34 => Lex (Prod α β)

instance Prod.Lex.instLT (α β : Type _) [LT α] [LT β] : LT (α ×ₗ β) where
  lt := Prod.Lex (· < ·) (· < ·)

namespace Option

theorem getD_eq_iff {o : Option α} {a b} : o.getD a = b ↔ (o = some b ∨ o = none ∧ a = b) := by
  cases o <;> simp

end Option

namespace List

theorem filter_cons :
    (x :: xs : List α).filter p = if p x then x :: (xs.filter p) else xs.filter p := by
  split <;> rename_i h
  · rw [filter_cons_of_pos _ h]
  · rw [filter_cons_of_neg _ h]

@[simp]
theorem get?_coe {xs : List α} {i : Fin xs.length} : xs.get? i = some (xs.get i) :=
   get?_eq_some.mpr ⟨i.2, rfl⟩

/--
Return an index for an element in a list, given that the element is a member of the list.
This function is `O(xs.length)`, as it just traverses the list looking the element.
-/
def idx_of_mem [DecidableEq α] {xs : List α} (h : y ∈ xs) : Fin xs.length :=
  ⟨xs.findIdx (· = y), xs.findIdx_lt_length_of_exists ⟨y, h, by simp⟩⟩

theorem idx_of_mem_spec [DecidableEq α] {xs : List α} (w : y ∈ xs) :
    xs.get (xs.idx_of_mem w) = y :=
  decide_eq_true_eq.mp (List.findIdx_get (p := (· = y)) (xs := xs))

end List

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

-- The next two lemmas are in https://github.com/leanprover/std4/pull/325

theorem List.zipWith_get? {f : α → β → γ} :
    (List.zipWith f as bs).get? i = match as.get? i, bs.get? i with
      | some a, some b => some (f a b) | _, _ => none := by
  induction as generalizing bs i with
  | nil => cases bs with
    | nil => simp
    | cons b bs => simp
  | cons a as aih => cases bs with
    | nil => simp
    | cons b bs => cases i <;> simp_all

theorem List.zipWithAll_get? {f : Option α → Option β → γ} :
    (List.zipWithAll f as bs).get? i = match as.get? i, bs.get? i with
      | none, none => .none | a?, b? => some (f a? b?) := by
  induction as generalizing bs i with
  | nil => induction bs generalizing i with
    | nil => simp
    | cons b bs bih => cases i <;> simp_all
  | cons a as aih => cases bs with
    | nil =>
      specialize @aih []
      cases i <;> simp_all
    | cons b bs => cases i <;> simp_all

-- These attributes are all added in https://github.com/leanprover/std4/pull/291
attribute [simp] Int.zero_ediv Int.ediv_zero
attribute [simp] Int.add_zero Int.zero_add Int.sub_zero Int.zero_sub Int.neg_zero

theorem Int.div_nonneg_iff_of_pos {a b : Int} (h : 0 < b) : a / b ≥ 0 ↔ a ≥ 0 := by
  rw [Int.div_def]
  match b, h with
  | Int.ofNat (b+1), _ =>
    rcases a with ⟨a⟩ <;> simp [Int.ediv]
    exact decide_eq_decide.mp rfl

-- The next two are in https://github.com/leanprover/std4/pull/326

theorem Int.mul_eq_mul_left_iff {a b c : Int} (h : c ≠ 0) : c * a = c * b ↔ a = b :=
  ⟨Int.eq_of_mul_eq_mul_left h, fun w => congrArg (fun x => c * x) w⟩

theorem Int.mul_eq_mul_right_iff {a b c : Int} (h : c ≠ 0) : a * c = b * c ↔ a = b :=
  ⟨Int.eq_of_mul_eq_mul_right h, fun w => congrArg (fun x => x * c) w⟩

@[simp] theorem ite_some_none_eq_none [Decidable P] :
    (if P then some x else none) = none ↔ ¬ P := by
  split <;> simp_all

@[simp] theorem ite_some_none_eq_some [Decidable P] :
    (if P then some x else none) = some y ↔ P ∧ x = y := by
  split <;> simp_all

namespace List

theorem dropWhile_cons :
    (x :: xs : List α).dropWhile p = if p x then xs.dropWhile p else x :: xs := by
  split <;> simp_all [dropWhile]

-- These `findIdx?` lemmas are in https://github.com/leanprover/std4/pull/293

@[simp] theorem findIdx?_nil : ([] : List α).findIdx? p i = none := rfl
@[simp] theorem findIdx?_cons :
    (x :: xs).findIdx? p i = if p x then some i else findIdx? p xs (i + 1) := rfl
@[simp] theorem findIdx?_succ :
    (xs : List α).findIdx? p (i+1) = (xs.findIdx? p i).map fun i => i + 1 := by
  induction xs generalizing i with
  | nil => simp
  | cons x xs ih =>
    simp only [findIdx?_cons]
    split <;> simp_all

theorem findIdx?_eq_some_iff (xs : List α) (p : α → Bool) :
    xs.findIdx? p = some i ↔ (xs.take (i + 1)).map p = List.replicate i false ++ [true] := by
  induction xs generalizing i with
  | nil => simp
  | cons x xs ih =>
    simp only [findIdx?_cons, Nat.zero_add, findIdx?_succ, take_succ_cons, map_cons]
    split
    · cases i <;> simp_all
    · cases i <;> simp_all

theorem findIdx?_of_eq_some {xs : List α} {p : α → Bool} (w : xs.findIdx? p = some i) :
    match xs.get? i with | some a => p a | none => false := by
  induction xs generalizing i with
  | nil => simp_all
  | cons x xs ih =>
    simp_all only [findIdx?_cons, Nat.zero_add, findIdx?_succ]
    split at w
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
      split at w <;>
      simp_all
    | succ i =>
      simp only [get?_cons_succ]
      apply ih
      split at w <;>
      simp_all

@[simp] theorem findIdx?_append :
    (xs ++ ys : List α).findIdx? p =
      (xs.findIdx? p <|> (ys.findIdx? p).map fun i => i + xs.length) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [cons_append, findIdx?_cons, Nat.zero_add, findIdx?_succ]
    split
    · simp
    · simp_all only [Bool.not_eq_true, Option.map_orElse, Option.map_map, length_cons]
      rfl

@[simp] theorem findIdx?_replicate :
    (List.replicate n a).findIdx? p = if 0 < n ∧ p a then some 0 else none := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [replicate, findIdx?_cons, Nat.zero_add, findIdx?_succ, Nat.zero_lt_succ, true_and]
    split <;> simp_all

end List

namespace List

-- https://github.com/leanprover/std4/pull/327

theorem exists_of_findSome?_eq_some {l : List α} {f : α → Option β} (w : l.findSome? f = some b) :
    ∃ a, a ∈ l ∧ f a = b := by
  induction l with
  | nil => simp_all
  | cons h l ih =>
    simp_all only [findSome?_cons, mem_cons, exists_eq_or_imp]
    split at w <;> simp_all

end List
