import Std
import Mathlib.Tactic.Simps.Basic
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.Rewrites
import Mathlib.Tactic.Have
import Mathlib.Tactic.SplitIfs
import Mathlib.Logic.Basic -- yuck!
import Mathlib.Tactic.NthRewrite

set_option autoImplicit true
set_option relaxedAutoImplicit true

/-!
# Abstract description of integer linear programming problems.

We define `LinearCombo`, `Problem`, and `DisjunctiveProblem`.
These are abstract descriptions of integer linear programming problems.

In particular, they are intended to be easy to reason about,
but need not be fast to compute with.

Later we will define variants carrying additional data required to run Omega efficiently,
and transfer the proofs from these simpler versions.
-/

@[simp]
theorem List.map_id' (l : List α) : l.map (fun a => a) = l := l.map_id

theorem List.zip_map_left (l₁ : List α) (l₂ : List β) (f : α → γ) :
    List.zip (l₁.map f) l₂ = (List.zip l₁ l₂).map fun p => (f p.1, p.2) := by
  induction l₁ generalizing l₂ <;> cases l₂ <;> simp_all

theorem List.zip_map_right (l₁ : List α) (l₂ : List β) (f : β → γ) :
    List.zip l₁ (l₂.map f) = (List.zip l₁ l₂).map fun p => (p.1, f p.2) := by
  induction l₁ generalizing l₂ <;> cases l₂ <;> simp_all

theorem List.zipWith_map_left (l₁ : List α) (l₂ : List β) (f : α → α') (g : α' → β → γ) :
    List.zipWith g (l₁.map f) l₂ = List.zipWith (fun a b => g (f a) b) l₁ l₂ := by
  induction l₁ generalizing l₂ <;> cases l₂ <;> simp_all

theorem List.zipWith_map_right (l₁ : List α) (l₂ : List β) (f : β → β') (g : α → β' → γ) :
    List.zipWith g l₁ (l₂.map f) = List.zipWith (fun a b => g a (f b)) l₁ l₂ := by
  induction l₁ generalizing l₂ <;> cases l₂ <;> simp_all

theorem List.zipWith_foldr_eq_zip_foldr {f : α → β → γ} (i : δ):
    (List.zipWith f l₁ l₂).foldr g i = (List.zip l₁ l₂).foldr (fun p r => g (f p.1 p.2) r) i := by
  induction l₁ generalizing l₂ <;> cases l₂ <;> simp_all

theorem List.zipWith_foldl_eq_zip_foldl {f : α → β → γ} (i : δ):
    (List.zipWith f l₁ l₂).foldl g i = (List.zip l₁ l₂).foldl (fun r p => g r (f p.1 p.2)) i := by
  induction l₁ generalizing i l₂ <;> cases l₂ <;> simp_all

-- This is in Mathlib.Data.List.Basic but I need it earlier.
theorem List.mem_of_mem_filter {a : α} {l} (h : a ∈ filter p l) : a ∈ l :=
  sorry

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

attribute [simp] Int.add_zero Int.zero_add Int.sub_zero Int.zero_sub Int.neg_zero

abbrev IntList := List Int

namespace IntList

def add (xs ys : IntList) : IntList :=
  List.zipWithAll (fun x y => x.getD 0 + y.getD 0) xs ys

instance : Add IntList := ⟨add⟩

theorem add_def (xs ys : IntList) :
    xs + ys = List.zipWithAll (fun x y => x.getD 0 + y.getD 0) xs ys :=
  rfl

def mul (xs ys : IntList) : IntList := List.zipWith (· * ·) xs ys

instance : Mul IntList := ⟨mul⟩

theorem mul_def (xs ys : IntList) : xs * ys = List.zipWith (· * ·) xs ys :=
  rfl

@[simp] theorem mul_nil_left : ([] : IntList) * ys = [] := rfl
@[simp] theorem mul_nil_right : xs * ([] : IntList) = [] := List.zipWith_nil_right
@[simp] theorem mul_cons₂ : (x::xs : IntList) * (y::ys) = (x * y) :: (xs * ys) := rfl

def neg (xs : IntList) : IntList := xs.map fun x => -x

instance : Neg IntList := ⟨neg⟩

theorem neg_def (xs : IntList) : - xs = xs.map fun x => -x := rfl

@[simp] theorem neg_nil : (- ([] : IntList)) = [] := rfl
@[simp] theorem neg_cons : (- (x::xs : IntList)) = -x :: -xs := rfl

def sub (xs ys : IntList) : IntList :=
  List.zipWithAll (fun x y => x.getD 0 - y.getD 0) xs ys

instance : Sub IntList := ⟨sub⟩

theorem sub_def (xs ys : IntList) :
    xs - ys = List.zipWithAll (fun x y => x.getD 0 - y.getD 0) xs ys :=
  rfl

attribute [local simp] add_def mul_def in
theorem mul_distrib_left (xs ys zs : IntList) : (xs + ys) * zs = xs * zs + ys * zs := by
  induction xs generalizing ys zs with
  | nil =>
    cases ys with
    | nil => simp
    | cons _ _ =>
      cases zs with
      | nil => simp
      | cons _ _ => simp_all [Int.add_mul]
  | cons x xs ih₁ =>
    cases ys with
    | nil => simp_all
    | cons _ _ =>
      cases zs with
      | nil => simp
      | cons _ _ => simp_all [Int.add_mul]

theorem mul_neg_left (xs ys : IntList) : (-xs) * ys = -(xs * ys) := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    cases ys with
    | nil => simp
    | cons y ys => simp_all [Int.neg_mul]

attribute [local simp] add_def neg_def sub_def in
theorem sub_eq_add_neg (xs ys : IntList) : xs - ys = xs + (-ys) := by
  induction xs generalizing ys with
  | nil => simp; rfl
  | cons x xs ih =>
    cases ys with
    | nil => simp
    | cons y ys => simp_all [Int.sub_eq_add_neg]

def sum (xs : IntList) : Int := xs.foldr (· + ·) 0

@[simp] theorem sum_nil : sum ([] : IntList) = 0 := rfl
@[simp] theorem sum_cons : sum (x::xs : IntList) = x + sum xs := rfl

attribute [local simp] sum add_def in
theorem sum_add (xs ys : IntList) : (xs + ys).sum = xs.sum + ys.sum := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    cases ys with
    | nil => simp
    | cons y ys => simp_all [Int.add_assoc, Int.add_left_comm]

@[simp]
theorem sum_neg (xs : IntList) : (-xs).sum = -(xs.sum) := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp_all [Int.neg_add]

def dot (xs ys : IntList) : Int := (xs * ys).sum

@[simp] theorem dot_nil_left : dot ([] : IntList) ys = 0 := rfl
@[simp] theorem dot_nil_right : dot xs ([] : IntList) = 0 := by simp [dot]
@[simp] theorem dot_cons₂ : dot (x::xs) (y::ys) = x * y + dot xs ys := rfl

theorem dot_distrib_left (xs ys zs : IntList) : (xs + ys).dot zs = xs.dot zs + ys.dot zs := by
  simp [dot, mul_distrib_left, sum_add]

@[simp] theorem dot_neg_left (xs ys : IntList) : (-xs).dot ys = -(xs.dot ys) := by
  simp [dot, mul_neg_left]

def sdiv (xs : IntList) (g : Nat) : IntList := xs.map fun x => x / g

def gcd (xs : IntList) : Nat := xs.foldr (fun x g => Nat.gcd x.natAbs g) 0

@[simp] theorem gcd_nil : gcd [] = 0 := rfl
@[simp] theorem gcd_cons : gcd (x :: xs) = Nat.gcd x.natAbs (gcd xs) := rfl

theorem gcd_cons_div_left : (gcd (x::xs) : Int) ∣ x := by
  simp only [gcd, List.foldr_cons, Int.ofNat_dvd_left]
  apply Nat.gcd_dvd_left

theorem gcd_cons_div_right : gcd (x::xs) ∣ gcd xs := by
  simp only [gcd, List.foldr_cons]
  apply Nat.gcd_dvd_right

theorem gcd_dvd (xs : IntList) {a : Int} (m : a ∈ xs) : (xs.gcd : Int) ∣ a := by
  rw [Int.ofNat_dvd_left]
  induction m with
  | head =>
    simp only [gcd_cons]
    apply Nat.gcd_dvd_left
  | tail b m ih =>   -- FIXME: why is the argument of tail implicit?
    simp only [gcd_cons]
    exact Nat.dvd_trans (Nat.gcd_dvd_right _ _) ih

theorem dvd_gcd (xs : IntList) (c : Nat) (w : ∀ {a : Int}, a ∈ xs → (c : Int) ∣ a) :
    c ∣ xs.gcd := by
  simp only [Int.ofNat_dvd_left] at w
  induction xs with
  | nil => simpa using Nat.dvd_zero c
  | cons x xs ih =>
    simp
    apply Nat.dvd_gcd
    · apply w
      simp
    · apply ih
      intro b m
      apply w
      exact List.mem_cons_of_mem x m

theorem gcd_eq_iff (xs : IntList) (g : Nat) :
    xs.gcd = g ↔ (∀ {a : Int}, a ∈ xs → (g : Int) ∣ a) ∧ (∀ (c : Nat), (∀ {a : Int}, a ∈ xs → (c : Int) ∣ a) → c ∣ g) := by
  constructor
  · rintro rfl
    exact ⟨gcd_dvd _, dvd_gcd _⟩
  · rintro ⟨hi, hg⟩
    apply Nat.dvd_antisymm
    · apply hg
      intro i m
      exact gcd_dvd xs m
    · exact dvd_gcd xs g hi

attribute [simp] Int.zero_dvd

@[simp] theorem gcd_eq_zero (xs : IntList) : xs.gcd = 0 ↔ ∀ x ∈ xs, x = 0 := by
  simp [gcd_eq_iff, Nat.dvd_zero]

@[simp] theorem dot_mod_gcd_left (xs ys : IntList) : dot xs ys % xs.gcd = 0 := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    cases ys with
    | nil => simp
    | cons y ys =>
      rw [dot_cons₂, Int.add_emod,
        ← Int.emod_emod_of_dvd (x * y) (gcd_cons_div_left),
        ← Int.emod_emod_of_dvd (dot xs ys) (Int.ofNat_dvd.mpr gcd_cons_div_right)]
      simp_all

end IntList

@[ext]
structure LinearCombo where
  const : Int
  coeffs : IntList
deriving DecidableEq, Inhabited, Repr

namespace LinearCombo

/--
Evaluate a linear combination `⟨r, [c_1, …, c_k]⟩` at values `[v_1, …, v_k]` to obtain
`r + (c_1 * x_1 + (c_2 * x_2 + ... (c_k * x_k + 0))))`.
-/
def eval (lc : LinearCombo) (values : IntList) : Int :=
  lc.const + lc.coeffs.dot values

-- -- Prove some alternative formulas for `eval`? Which to use?
-- theorem eval_eq (lc : LinearCombo) (values : List Int) :
--     lc.eval values = lc.const + (List.zipWith (· * ·) lc.coeffs values).foldr (· + ·) 0 := by
--   simp [eval, List.zipWith_foldr_eq_zip_foldr]

def add (l₁ l₂ : LinearCombo) : LinearCombo where
  const := l₁.const + l₂.const
  coeffs := l₁.coeffs + l₂.coeffs

instance : Add LinearCombo := ⟨add⟩

@[simp] lemma add_const {l₁ l₂ : LinearCombo} : (l₁ + l₂).const = l₁.const + l₂.const := rfl
@[simp] lemma add_coeffs {l₁ l₂ : LinearCombo} : (l₁ + l₂).coeffs = l₁.coeffs + l₂.coeffs := rfl

def sub (l₁ l₂ : LinearCombo) : LinearCombo where
  const := l₁.const - l₂.const
  coeffs := l₁.coeffs - l₂.coeffs

instance : Sub LinearCombo := ⟨sub⟩

@[simp] lemma sub_const {l₁ l₂ : LinearCombo} : (l₁ - l₂).const = l₁.const - l₂.const := rfl
@[simp] lemma sub_coeffs {l₁ l₂ : LinearCombo} : (l₁ - l₂).coeffs = l₁.coeffs - l₂.coeffs := rfl

/-- Negating a linear combination means negating the constant term and the coefficients. -/
def neg (lc : LinearCombo) : LinearCombo where
  const := -lc.const
  coeffs := -lc.coeffs

instance : Neg LinearCombo := ⟨neg⟩

@[simp] lemma neg_const {l : LinearCombo} : (-l).const = -l.const := rfl
@[simp] lemma neg_coeffs {l : LinearCombo} : (-l).coeffs = -l.coeffs  := rfl

theorem sub_eq_add_neg (l₁ l₂ : LinearCombo) : l₁ - l₂ = l₁ + -l₂ := by
  rcases l₁ with ⟨a₁, c₁⟩; rcases l₂ with ⟨a₂, c₂⟩
  ext1
  · simp [Int.sub_eq_add_neg]
  · simp [IntList.sub_eq_add_neg]

@[simp]
theorem add_eval (l₁ l₂ : LinearCombo) (v : List Int) : (l₁ + l₂).eval v = l₁.eval v + l₂.eval v := by
  rcases l₁ with ⟨r₁, c₁⟩; rcases l₂ with ⟨r₂, c₂⟩
  simp only [eval, add_const, add_coeffs, Int.add_assoc, Int.add_left_comm]
  congr
  exact IntList.dot_distrib_left c₁ c₂ v

@[simp]
theorem neg_eval (lc : LinearCombo) (v : List Int) : (-lc).eval v = - lc.eval v := by
  rcases lc with ⟨a, coeffs⟩
  simp [eval, Int.neg_add]

@[simp]
theorem sub_eval (l₁ l₂ : LinearCombo) (v : List Int) :
    (l₁ - l₂).eval v = l₁.eval v - l₂.eval v := by
  simp [sub_eq_add_neg, Int.sub_eq_add_neg]

end LinearCombo

structure Problem where
  possible : Bool := true
  equalities : List LinearCombo := []
  inequalities : List LinearCombo := []
deriving Repr

namespace Problem

structure sat (p : Problem) (values : List Int) : Prop where
  possible : p.possible = true := by rfl
  equalities : lc ∈ p.equalities → lc.eval values = 0
  inequalities : lc ∈ p.inequalities → lc.eval values ≥ 0

@[simps]
def trivial : Problem where

theorem trivial_sat (values : List Int) : trivial.sat values where
  equalities := by simp
  inequalities := by simp

@[simps]
def and (p q : Problem) : Problem where
  possible := p.possible && q.possible
  equalities := p.equalities ++ q.equalities
  inequalities := p.inequalities ++ q.inequalities

theorem and_sat {p q : Problem} (hp : p.sat values) (hq : q.sat values) : (p.and q).sat values where
  possible := by simp [hp.possible, hq.possible]
  equalities := by
    intros lc m
    simp only [and_equalities, List.mem_append] at m
    rcases m with pm | qm <;>
    simp_all [hp.equalities, hq.equalities]
  inequalities := by
    intros lc m
    simp only [and_inequalities, List.mem_append] at m
    rcases m with pm | qm <;>
    simp_all [hp.inequalities, hq.inequalities]

def solutions (p : Problem) : Type :=
  { values // p.sat values }

instance : CoeSort Problem Type where
  coe := solutions

def unsat (p : Problem) : Prop := p → False

theorem unsat_of_impossible {p : Problem} (h : p.possible = false) : p.unsat :=
  fun ⟨v, s⟩ => by
    rw [s.possible] at h
    simp at h

@[simps]
def impossible : Problem where
  possible := false

theorem impossible_unsat : impossible.unsat := unsat_of_impossible rfl

/-- A solution to a problem consists either of a witness, or a proof of unsatisfiability. -/
inductive Solution (p : Problem)
| sat : p → Solution p
| unsat : p.unsat → Solution p

/--
Two problems are equivalent if a solution to one gives an solution to the other.
We don't care that this is bijective,
just that the solution sets are either both empty or both non-empty.
-/
structure equiv (p q : Problem) where
  mp : p → q
  mpr : q → p

end Problem

structure DisjunctiveProblem where
  problems : List Problem

namespace DisjunctiveProblem

def sat (d : DisjunctiveProblem) (values : List Int) : Prop :=
  ∃ p ∈ d.problems, p.sat values

def solutions (p : DisjunctiveProblem) : Type :=
  { values // p.sat values }

instance : CoeSort DisjunctiveProblem Type where
  coe := solutions

def unsat (p : DisjunctiveProblem) : Prop := p → False

inductive Solution (d : DisjunctiveProblem)
| sat : d.sat values → Solution d
| unsat : d.unsat → Solution d

end DisjunctiveProblem

/-!
Erasing an inequality results in a larger solution space.
-/
namespace Problem

/-- Erase an inequality from a problem. -/
@[simps]
def eraseInequality (p : Problem) (lc : LinearCombo) : Problem :=
  { p with inequalities := p.inequalities.erase lc }

/-- Any solution gives a solution after erasing an inequality. -/
def eraseInequality_map (p : Problem) (lc : LinearCombo) : p → p.eraseInequality lc :=
  fun ⟨v, s⟩ => ⟨v, { s with
    inequalities := fun m => s.inequalities (by simp at m; apply List.mem_of_mem_erase m) }⟩

def filterEqualities_map (p : Problem) : p → { p with equalities := p.equalities.filter f } :=
  fun ⟨v, s⟩ => ⟨v, { s with
    equalities := fun m  => s.equalities (by simp at m; exact List.mem_of_mem_filter m) }⟩

def filterInequalities_map (p : Problem) : p → { p with inequalities := p.inequalities.filter f } :=
  fun ⟨v, s⟩ => ⟨v, { s with
    inequalities := fun m  => s.inequalities (by simp at m; exact List.mem_of_mem_filter m) }⟩

end Problem

/-!
Define `a ≤ b` on linear combinations to mean that the coefficients are identical,
and the constant terms satisfy `≤`.

If `a ≤ b`, then the non-negative set for `a` is a subset of the non-negative set for `b`.

(Note this is only a preorder, not even a partial order,
as we don't allow for rescaling when comparing coefficients.)

We show:
```
a < b → a ∈ p.inequalities → p.eraseInequality b → p
```
-/

namespace LinearCombo

/--
Define `a ≤ b` on linear combinations to mean that the coefficients are identical,
and the constant terms satisfy `≤`.

If `a ≤ b`, then the non-negative set for `a` is a subset of the non-negative set for `b`.

(Note this is only a preorder, not even a partial order,
as we don't allow for rescaling when comparing coefficients.)
-/
def le (a b : LinearCombo) : Prop :=
  a.coeffs = b.coeffs ∧ a.const ≤ b.const

instance : LE LinearCombo := ⟨le⟩

@[simp]
theorem le_def (a b : LinearCombo) : a ≤ b ↔ a.coeffs = b.coeffs ∧ a.const ≤ b.const := Iff.rfl

theorem eval_le_of_le {a b : LinearCombo} (h : a ≤ b) (v : List Int) : a.eval v ≤ b.eval v := by
  simp [LinearCombo.eval]
  rcases a with ⟨a, coeffs⟩; rcases b with ⟨b, bcoeffs⟩
  rcases h with ⟨rfl, h⟩
  apply Int.add_le_add_right h

theorem evalNonneg_of_le {a b : LinearCombo} (h : a ≤ b) : a.eval v ≥ 0 → b.eval v ≥ 0 :=
  fun w => Int.le_trans w (eval_le_of_le h v)

/--
Define `a < b` on linear combinations to mean that the coefficients are identical,
and the constant terms satisfy `<`.

If `a < b`, then the non-negative set for `a` is a strict subset of the non-negative set for `b`.
-/
def lt (a b : LinearCombo) : Prop :=
  a ≤ b ∧ a ≠ b

instance instLinearComboLT : LT LinearCombo := ⟨lt⟩

@[simp]
theorem lt_def (a b : LinearCombo) : a < b ↔ a.coeffs = b.coeffs ∧ a.const < b.const := by
  dsimp [instLinearComboLT, lt]
  rw [le_def]
  rcases a with ⟨a, as⟩; rcases b with ⟨b, bs⟩
  simp only [mk.injEq]
  constructor
  · rintro ⟨⟨rfl, le⟩, h⟩
    simp_all only [and_true, true_and]
    exact Int.lt_iff_le_and_ne.mpr ⟨le, h⟩
  · rintro ⟨rfl, lt⟩
    simp only [true_and, and_true]
    exact ⟨Int.le_of_lt lt, Int.ne_of_lt lt⟩

theorem eval_lt_of_lt {a b : LinearCombo} (h : a < b) (v : List Int) : a.eval v < b.eval v := by
  simp [LinearCombo.eval]
  rcases a with ⟨a, coeffs⟩; rcases b with ⟨b, bcoeffs⟩
  rw [lt_def] at h
  rcases h with ⟨rfl, h⟩
  apply Int.add_lt_add_right h

end LinearCombo

namespace Problem

/--
If `a < b` is a strict comparison between inequality constraints,
in any problems containing `a`, we can discard `b`.
-/
def eraseRedundantInequality_map
    (p : Problem) {a b : LinearCombo} (lt : a < b) (m : a ∈ p.inequalities) :
    p.eraseInequality b → p :=
  fun ⟨v, s⟩ => ⟨v, { s with
    inequalities := fun m' => by
      rw [List.mem_iff_mem_erase_or_eq _ _ b] at m'
      rcases m' with m' | ⟨rfl, m'⟩
      · apply s.inequalities
        exact m'
      · rcases lt with ⟨le, ne⟩
        apply LinearCombo.evalNonneg_of_le le
        apply s.inequalities
        simpa using (List.mem_erase_of_ne ne).mpr m }⟩

/--
If `a < b` is a strict comparison between inequality constraints,
in any problems containing `a`, we can discard `b` to obtain an equivalent problem.
-/
def eraseRedundantInequality_equiv
    (p : Problem) {a b : LinearCombo} (lt : a < b) (m : a ∈ p.inequalities) :
    p.equiv (p.eraseInequality b) where
  mp := p.eraseInequality_map b
  mpr := p.eraseRedundantInequality_map lt m

end Problem

/-!
We define negation of a linear combination,
and show that `a < b.neg` gives a contradition.
-/
namespace LinearCombo

theorem contradiction_of_neg_lt (p : Problem) {a b : LinearCombo}
    (ma : a ∈ p.inequalities) (mb : b ∈ p.inequalities) (w : a < -b) : p.unsat := by
  rintro ⟨v, s⟩
  have := LinearCombo.eval_lt_of_lt w v
  simp only [neg_eval] at this
  apply Int.lt_irrefl 0 (Int.lt_of_lt_of_le (Int.lt_of_le_of_lt (s.inequalities ma) this)
    (Int.neg_le_neg (s.inequalities mb)))

/--
We verify that `x - 1 ≥ 0` and `-x ≥ 0` have no solutions.
-/
example : let p : Problem := { inequalities := [⟨-1, [1]⟩, ⟨0, [-1]⟩] }; p.unsat := by
  apply contradiction_of_neg_lt (a := ⟨-1, [1]⟩) (b := ⟨0, [-1]⟩) <;> simp

end LinearCombo


@[simp] theorem ite_some_none_eq_none [Decidable P] :
    (if P then some x else none) = none ↔ ¬ P := by
  split_ifs <;> simp_all

@[simp] theorem ite_some_none_eq_some [Decidable P] :
    (if P then some x else none) = some y ↔ P ∧ x = y := by
  split_ifs <;> simp_all

namespace LinearCombo

def constant? (lc : LinearCombo) : Option Int :=
  if lc.coeffs.all (· = 0) then
    some lc.const
  else
    none

theorem eval_eq_of_constant (lc : LinearCombo) (h : lc.constant? = some c) : lc.eval v = c := by
  simp [constant?] at h
  rcases h with ⟨h, rfl⟩
  rcases lc with ⟨c, coeffs⟩
  simp [eval]
  nth_rewrite 2 [← Int.add_zero c]
  congr
  induction coeffs generalizing v with
  | nil => simp
  | cons x coeffs ih =>
    cases v with
    | nil => simp
    | cons v vs =>
      simp_all [ih]

end LinearCombo

namespace Problem

def processConstants (p : Problem) : Problem :=
  let equalityConstants := p.equalities.filterMap LinearCombo.constant?
  let inequalityConstants := p.inequalities.filterMap LinearCombo.constant?
  if equalityConstants.all (· = 0) ∧ inequalityConstants.all (· ≥ 0) then
    { possible := p.possible
      equalities := p.equalities.filter fun lc => lc.constant?.isNone
      inequalities := p.inequalities.filter fun lc => lc.constant?.isNone }
  else
    impossible

def processConstants_map (p : Problem) : p → p.processConstants := by
  dsimp [processConstants]
  split_ifs with w
  · exact (filterEqualities_map _) ∘ (filterInequalities_map _)
  · simp only [not_and_or] at w
    simp only [List.all_eq_true, List.mem_filterMap, decide_eq_true_eq, forall_exists_index,
      and_imp, not_forall, exists_prop, exists_and_left] at w
    intro ⟨v, s⟩
    exfalso
    rcases w with (⟨c, eq, w, m, ne⟩ | ⟨c, eq, w, m, ne⟩)
    · have := s.equalities w
      simp [eq.eval_eq_of_constant m] at this
      exact ne this
    · have := s.inequalities w
      simp [eq.eval_eq_of_constant m] at this
      exact ne this

example : processConstants { equalities := [⟨1, []⟩] } = impossible := rfl
example : processConstants { equalities := [⟨1, []⟩] } |>.unsat := impossible_unsat
example : Problem.unsat { equalities := [⟨1, []⟩] } := impossible_unsat ∘ processConstants_map _
example : Problem.unsat { inequalities := [⟨-1, []⟩] } := impossible_unsat ∘ processConstants_map _

def processConstants_inv (p : Problem) : p.processConstants → p := sorry

def processConstants_equiv (p : Problem) : p.equiv p.processConstants where
  mp := p.processConstants_map
  mpr := p.processConstants_inv

end Problem

namespace LinearCombo

def normalizeInequality (lc : LinearCombo) : LinearCombo :=
  let gcd := lc.coeffs.gcd
  { coeffs := lc.coeffs.sdiv gcd
    -- Recall `Int.fdiv` is division with floor rounding.
    const := Int.fdiv lc.const gcd }

def normalizeEquality (lc : LinearCombo) : LinearCombo :=
  let gcd := lc.coeffs.gcd
  if (gcd : Int) ∣ lc.const then
    { coeffs := lc.coeffs.sdiv gcd
      const := lc.const / gcd }
  else
    { coeffs := []
      const := 1 }

theorem normalizeInequality_eval {lc : LinearCombo} :
    lc.normalizeInequality.eval v ≥ 0 ↔ lc.eval v ≥ 0 := by
  sorry

attribute [simp] Int.zero_ediv Int.ediv_zero

theorem normalizeEquality_eval {lc : LinearCombo} :
    lc.normalizeEquality.eval v = 0 ↔ lc.eval v = 0 := by
  rcases lc with ⟨const, coeffs⟩
  dsimp [normalizeEquality]
  split_ifs with h
  · simp [eval]
    by_cases w : coeffs.gcd = 0
    · simp [w] at h ⊢
      simp [h]
      simp at w
      sorry -- easy from here?
    · -- not terrible from here?
      sorry
  · simp only [eval, IntList.dot_nil_left, Int.add_zero, false_iff]
    intro w
    apply h
    replace w := congr_arg (fun x : Int => x % coeffs.gcd) w
    simp [Int.add_emod] at w
    exact Int.dvd_of_emod_eq_zero w

end LinearCombo
namespace Problem

def normalize (p : Problem) : Problem where
  possible := p.possible
  equalities := p.equalities.map LinearCombo.normalizeEquality
  inequalities := p.equalities.map LinearCombo.normalizeInequality

def normalize_map (p : Problem) : p → p.normalize := sorry

def normalize_inv (p : Problem) : p.normalize → p := sorry

def normalize_equiv (p : Problem) : p.equiv p.normalize where
  mp := p.normalize_map
  mpr := p.normalize_inv

end Problem
