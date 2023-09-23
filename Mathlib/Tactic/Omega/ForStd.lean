import Std
import Mathlib.Tactic.SplitIfs

set_option autoImplicit true
set_option relaxedAutoImplicit true

@[simp]
theorem List.map_id''' (l : List α) : l.map (fun a => a) = l := l.map_id

theorem List.zip_map_left' (l₁ : List α) (l₂ : List β) (f : α → γ) :
    List.zip (l₁.map f) l₂ = (List.zip l₁ l₂).map fun p => (f p.1, p.2) := by
  induction l₁ generalizing l₂ <;> cases l₂ <;> simp_all

theorem List.zip_map_right' (l₁ : List α) (l₂ : List β) (f : β → γ) :
    List.zip l₁ (l₂.map f) = (List.zip l₁ l₂).map fun p => (p.1, f p.2) := by
  induction l₁ generalizing l₂ <;> cases l₂ <;> simp_all

theorem List.zipWith_map_left' (l₁ : List α) (l₂ : List β) (f : α → α') (g : α' → β → γ) :
    List.zipWith g (l₁.map f) l₂ = List.zipWith (fun a b => g (f a) b) l₁ l₂ := by
  induction l₁ generalizing l₂ <;> cases l₂ <;> simp_all

theorem List.zipWith_map_right' (l₁ : List α) (l₂ : List β) (f : β → β') (g : α → β' → γ) :
    List.zipWith g l₁ (l₂.map f) = List.zipWith (fun a b => g a (f b)) l₁ l₂ := by
  induction l₁ generalizing l₂ <;> cases l₂ <;> simp_all

theorem List.zipWith_foldr_eq_zip_foldr {f : α → β → γ} (i : δ):
    (List.zipWith f l₁ l₂).foldr g i = (List.zip l₁ l₂).foldr (fun p r => g (f p.1 p.2) r) i := by
  induction l₁ generalizing l₂ <;> cases l₂ <;> simp_all

theorem List.zipWith_foldl_eq_zip_foldl {f : α → β → γ} (i : δ):
    (List.zipWith f l₁ l₂).foldl g i = (List.zip l₁ l₂).foldl (fun r p => g r (f p.1 p.2)) i := by
  induction l₁ generalizing i l₂ <;> cases l₂ <;> simp_all

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

theorem Nat.gcd_eq_iff (a b : Nat) :
    gcd a b = g ↔ g ∣ a ∧ g ∣ b ∧ (∀ c, c ∣ a → c ∣ b → c ∣ g) := by
  constructor
  · rintro rfl
    exact ⟨gcd_dvd_left _ _, gcd_dvd_right _ _, fun _ => Nat.dvd_gcd⟩
  · rintro ⟨ha, hb, hc⟩
    apply Nat.dvd_antisymm
    · apply hc
      · exact gcd_dvd_left a b
      · exact gcd_dvd_right a b
    · exact Nat.dvd_gcd ha hb

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

@[simp] theorem List.findIdx?_nil : ([] : List α).findIdx? p i = none := rfl
@[simp] theorem List.findIdx?_cons :
    (x :: xs).findIdx? p i = if p x then some i else findIdx? p xs (i + 1) := rfl
@[simp] theorem List.findIdx?_succ :
    (xs : List α).findIdx? p (i+1) = (xs.findIdx? p i).map fun i => i + 1 := by
  induction xs generalizing i with
  | nil => simp
  | cons x xs ih =>
    simp only [findIdx?_cons]
    split_ifs <;> simp_all

theorem List.findIdx?_eq_some_iff (xs : List α) (p : α → Bool) :
    xs.findIdx? p = some i ↔ (xs.take (i + 1)).map p = List.replicate i false ++ [true] := by
  induction xs generalizing i with
  | nil => simp
  | cons x xs ih =>
    simp
    split_ifs with h
    · cases i <;> simp_all
    · cases i <;> simp_all
