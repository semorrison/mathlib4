import Mathlib.Tactic.Simps.Basic
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.Rewrites
import Mathlib.Tactic.Have
import Mathlib.Tactic.SplitIfs
import Mathlib.Logic.Basic -- yuck!
import Mathlib.Tactic.NthRewrite
import Mathlib.Tactic.Omega.IntList
import Std.Data.Option.Lemmas
import Mathlib.Tactic.Omega.Problem

set_option autoImplicit true
set_option relaxedAutoImplicit true

/-- A type synonym to equip a type with its lexicographic order. -/
def Lex (α : Type _) := α

@[inherit_doc] notation:35 α " ×ₗ " β:34 => Lex (Prod α β)

instance Prod.Lex.instLT (α β : Type _) [LT α] [LT β] : LT (α ×ₗ β) where
  lt := Prod.Lex (· < ·) (· < ·)


namespace UInt64

attribute [ext] UInt64

protected theorem min_def {a b : UInt64} : min a b = if a ≤ b then a else b := rfl
protected theorem le_def {a b : UInt64} : a ≤ b ↔ a.val.val ≤ b.val.val := Iff.rfl
protected theorem lt_def {a b : UInt64} : a < b ↔ a.val.val < b.val.val := Iff.rfl

protected theorem min_val_val {a b : UInt64} : (min a b).val.val = min a.val.val b.val.val := by
  simp only [UInt64.min_def, UInt64.le_def, Nat.min_def]
  split_ifs <;> rfl

@[simp] protected theorem not_le {a b : UInt64} : ¬ (a ≤ b) ↔ b < a := by
  rw [UInt64.le_def, UInt64.lt_def]
  exact Fin.not_le

protected theorem min_comm {a b : UInt64} : min a b = min b a := by
  ext
  simp [UInt64.min_val_val, Nat.min_comm]

protected theorem min_eq_left {a b : UInt64} (h : a ≤ b) : min a b = a := by
  simp [UInt64.min_def, h]

protected theorem min_eq_right {a b : UInt64} (h : b ≤ a) : min a b = b := by
  rw [UInt64.min_comm]; exact UInt64.min_eq_left h

end UInt64

namespace IntList

/--
We need two properties of this hash:
1. It is stable under adding trailing zeroes.
2. `(-xs).hash = xs.hash`
-/
def hash (xs : IntList) : UInt64 :=
  min (Hashable.hash xs.trim) (Hashable.hash (-xs).trim)

/-- We override the default `Hashable` instance. -/
instance : Hashable IntList := ⟨hash⟩

theorem hash_append_zero : hash (xs ++ [0]) = hash xs := by
  simp [hash]

theorem hash_neg : hash (-xs) = hash xs := by
  simp [hash, UInt64.min_comm]

end IntList

namespace Omega.Impl

structure LinearCombo where
  const : Int := 0
  coeffs : IntList := []
  -- smallCoeff : Option Nat := coeffs.findIdx? fun i => i.natAbs = 1
  -- smallCoeff_eq : smallCoeff = coeffs.findIdx? fun i => i.natAbs = 1 := by rfl
deriving DecidableEq, Repr

instance : ToString LinearCombo where
  toString lc := s!"{lc.const}{String.join <| lc.coeffs.enum.map fun ⟨i, c⟩ => s!" + {c} * x{i+1}"}"

example : toString (⟨7, [3, 5]/-, none, rfl-/⟩ : LinearCombo) = "7 + 3 * x1 + 5 * x2" := rfl

namespace LinearCombo

@[simps]
def of (a : Omega.LinearCombo) : LinearCombo := { a with }

@[simps]
def to (a : LinearCombo) : Omega.LinearCombo := { a with }

instance : Inhabited LinearCombo := ⟨{const := 1}⟩

@[ext] theorem ext {a b : LinearCombo} (w₁ : a.const = b.const) (w₂ : a.coeffs = b.coeffs) :
    a = b := by
  cases a; cases b
  subst w₁; subst w₂
  congr
  -- simp_all

theorem ext_iff {a b : LinearCombo} : a = b ↔ a.const = b.const ∧ a.coeffs = b.coeffs :=
  ⟨by rintro rfl; simp, fun ⟨w₁, w₂⟩ => ext w₁ w₂⟩

def sign (a : LinearCombo) : Int :=
  IntList.leadingSign a.coeffs

def coordinate (i : Nat) : LinearCombo where
  const := 0
  coeffs := List.replicate i 0 ++ [1]
  -- smallCoeff := i
  -- smallCoeff_eq := by simp

/--
Evaluate a linear combination `⟨r, [c_1, …, c_k]⟩` at values `[v_1, …, v_k]` to obtain
`r + (c_1 * x_1 + (c_2 * x_2 + ... (c_k * x_k + 0))))`.
-/
def eval (lc : LinearCombo) (values : IntList) : Int :=
  lc.const + lc.coeffs.dot values

@[simp] theorem eval_nil : (lc : LinearCombo).eval [] = lc.const := by
  simp [eval]

@[simp] theorem of_eval (a : Omega.LinearCombo) : (of a).eval v = a.eval v := rfl
@[simp] theorem to_eval (a : LinearCombo) : (to a).eval v = a.eval v := rfl

@[simp] theorem coordinate_eval (i : Nat) (v : IntList) :
    (coordinate i).eval v = (v.get? i).getD 0 := by
  simp [eval, coordinate]
  induction v generalizing i with
  | nil => simp
  | cons x v ih =>
    cases i with
    | zero => simp
    | succ i => simp_all

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

def smul (lc : LinearCombo) (i : Int) : LinearCombo where
  const := i * lc.const
  coeffs := lc.coeffs.smul i

instance : HMul Int LinearCombo LinearCombo := ⟨fun i lc => lc.smul i⟩

@[simp] lemma smul_const {lc : LinearCombo} {i : Int} : (i * lc).const = i * lc.const := rfl
@[simp] lemma smul_coeffs {lc : LinearCombo} {i : Int} : (i * lc).coeffs = i * lc.coeffs := rfl

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

@[simp]
theorem smul_eval (lc : LinearCombo) (i : Int) (v : List Int) :
    (i * lc).eval v = i * lc.eval v := by
  rcases lc with ⟨a, coeffs⟩
  simp [eval, Int.mul_add]

def coeff (lc : LinearCombo) (i : Nat) : Int := lc.coeffs.get i

@[simps]
def setCoeff (lc : LinearCombo) (i : Nat) (x : Int) : LinearCombo :=
  { lc with
    coeffs := lc.coeffs.set i x }

@[simp] theorem setCoeff_eval {lc : LinearCombo} :
    (lc.setCoeff i x).eval v = lc.eval v + (x - lc.coeff i) * v.get i := by
  simp [eval, Int.add_assoc, Int.sub_mul]
  rfl

@[simp]
theorem eval_set {lc : LinearCombo} :
    lc.eval (v.set i x) = lc.eval v + lc.coeff i * (x - v.get i) := by
  simp [eval, Int.add_assoc]
  rfl

end LinearCombo

structure Equality where
  linearCombo : LinearCombo
  minCoeff? : Option Nat := none
  minCoeffIdx? : Option Nat := none
  minCoeff?_spec : SatisfiesM (fun min => ∀ x ∈ linearCombo.coeffs, x = 0 ∨ min ≤ x.natAbs) minCoeff? := by simp
  minCoeffIdx?_spec : SatisfiesM (fun idx => (linearCombo.coeff idx).natAbs = minCoeff?) minCoeffIdx? := by simp
deriving DecidableEq

theorem List.filter_cons :
    (x :: xs : List α).filter p = if p x then x :: (xs.filter p) else xs.filter p := by
  split_ifs with h
  · rw [List.filter_cons_of_pos _ h]
  · rw [List.filter_cons_of_neg _ h]
namespace Equality

def minCoeff (e : Equality) : Nat :=
  match e.minCoeff? with
  | some min => min
  | none => e.linearCombo.coeffs.filter (· ≠ 0) |>.map Int.natAbs |>.foldr aux none |>.getD 0
where
  aux : Nat → Option Nat → Option Nat
  | x, none => some x
  | x, some y => some (min x y)

theorem minCoeff_spec (e : Equality) :
    ∀ x ∈ e.linearCombo.coeffs, x = 0 ∨ e.minCoeff ≤ x.natAbs := by
  intro x m
  rcases e with ⟨lc, ⟨⟩|⟨n⟩, _, spec, _⟩
  · dsimp [minCoeff]
    by_cases h : x = 0
    · left
      exact h
    · right
      dsimp at m
      dsimp
      rcases lc with ⟨const, coeffs⟩
      dsimp at m ⊢
      clear spec
      rename_i spec'
      clear spec'
      induction coeffs with
      | nil => simp
      | cons y ys ih =>
        simp at m
        cases m with
        | inl m =>
          subst m
          rw [List.filter_cons_of_pos _ (by simpa using h)]
          simp only [List.map_cons, List.foldr_cons]
          revert ih
          generalize List.foldr _ _ _ = z
          intro ih
          cases z with
          | none => simp [minCoeff.aux]
          | some z =>
            simp_all only [Option.getD_some, minCoeff.aux]
            apply Nat.min_le_left
        | inr m =>
          specialize ih m
          rw [List.filter_cons]
          split_ifs
          · simp only [List.map_cons, List.foldr_cons]
            revert ih
            generalize w : List.foldr _ _ _ = z
            intro ih
            cases z with
            | none =>
              -- We can get a contradiction from `h`, `m`, and `w`, but it is tedious.
              sorry
            | some z =>
              simp_all only [Option.getD_some, minCoeff.aux]
              exact Nat.le_trans (Nat.min_le_right _ _) ih
          · exact ih
  · dsimp [minCoeff]
    dsimp at m
    rw [SatisfiesM_Option_eq] at spec
    exact spec n rfl _ m

def minCoeffIdx (e : Equality) : Nat :=
  let m := e.minCoeff
  e.linearCombo.coeffs.findIdx fun x => x.natAbs = m

theorem minCoeffIdx_spec (e : Equality) :
    (e.linearCombo.coeff e.minCoeffIdx).natAbs = e.minCoeff := by
  simp [minCoeffIdx, IntList.get]
  sorry

def calculateMinCoeff (e : Equality) : Equality :=
  match e.minCoeff? with
  | some _ => e
  | none =>
    { linearCombo := e.linearCombo
      minCoeff? := e.minCoeff
      minCoeff?_spec := by
        rw [SatisfiesM_Option_eq]
        rintro a ⟨⟩
        apply minCoeff_spec }

def calculateMinCoeffIdx (e : Equality) : Equality :=
  match e.minCoeffIdx? with
  | some _ => e
  | none =>
    let e' := calculateMinCoeff e
    { e' with
      minCoeffIdx? := e'.minCoeffIdx
      minCoeffIdx?_spec := by
        rw [SatisfiesM_Option_eq]
        rintro a ⟨⟩
        rw [e'.minCoeffIdx_spec]
        simp only [calculateMinCoeff]
        split <;> simp_all [minCoeff] }

instance : ToString Equality where
  toString eq := s!"{eq.linearCombo} = 0"

-- TODO: make sure this is only called on `Equality`s with precomputed `minCoeff` and `minCoeffIdx`.
def smallCoeff (a : Equality) : Option Nat :=
  if a.minCoeff = 1 then
    a.minCoeffIdx
  else
    none

theorem smallCoeff_natAbs {a : Equality} (w : a.smallCoeff = some i) :
    (a.linearCombo.coeff i).natAbs = 1 := by
  dsimp [smallCoeff] at w
  simp at w
  rcases w with ⟨w, rfl⟩
  rw [a.minCoeffIdx_spec, w]

end Equality

structure Problem where
  possible : Bool := true
  equalities : List Equality := []
  inequalities : List LinearCombo := []
  -- inequalities' : Lean.HashMap Nat (Option Int × Option Int) := {}
  -- constraintKeys : Lean.HashMap IntList Nat := {}
  -- constraintKeys' : Array IntList := #[]

namespace Problem

instance : ToString Problem where
  toString p :=
    if p.possible then
      if p.equalities = [] ∧ p.inequalities = [] then
        "trivial"
      else
        "\n".intercalate <|
          (p.equalities.map fun e => s!"{e}") ++(p.inequalities.map fun e => s!"{e} ≥ 0")
    else
      "impossible"

-- def addEquality (p : Problem) (a : LinearCombo) : Problem :=
--   { p with
--     equalities := a :: p.equalities }


@[simps]
def of (p : Omega.Problem) : Problem where
  possible := p.possible
  equalities := p.equalities.map fun lc => { linearCombo := .of lc }
  inequalities := p.inequalities.map .of

@[simps]
def to (p : Problem) : Omega.Problem where
  possible := p.possible
  equalities := p.equalities.map fun eq => LinearCombo.to eq.linearCombo
  inequalities := p.inequalities.map LinearCombo.to

structure sat (p : Problem) (values : List Int) : Prop where
  possible : p.possible = true := by trivial
  equalities : eq ∈ p.equalities → eq.linearCombo.eval values = 0
  inequalities : lc ∈ p.inequalities → lc.eval values ≥ 0

@[simps]
def trivial : Problem where

theorem trivial_sat (values : List Int) : trivial.sat values where
  equalities := by simp
  inequalities := by simp

theorem of_sat (p : Omega.Problem) : (of p).sat v ↔ p.sat v := by
  constructor
  · intro ⟨_, _, _⟩
    constructor <;> simp_all
  · intro ⟨_, _, _⟩
    constructor <;> simp_all

theorem to_sat (p : Problem) : (to p).sat v ↔ p.sat v := by
  constructor
  · intro ⟨_, _, _⟩
    constructor <;> simp_all
  · intro ⟨_, _, _⟩
    constructor <;> simp_all

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

def map_of (p : Omega.Problem) : p → of p := fun ⟨v, s⟩ => ⟨v, (of_sat p).mpr s⟩
def map_to (p : Problem) : p → to p := fun ⟨v, s⟩ => ⟨v, (to_sat p).mpr s⟩

def map_of_sat {p q : Problem} (h : ∀ v, p.sat v → q.sat v) : p → q :=
  fun ⟨v, s⟩ => ⟨v, h v s⟩

def unsat (p : Problem) : Prop := p → False

theorem unsat_of_impossible {p : Problem} (h : p.possible = false) : p.unsat :=
  fun ⟨v, s⟩ => by
    rw [s.possible] at h
    simp at h

@[simps]
def impossible : Problem where
  possible := false

theorem impossible_unsat : impossible.unsat := unsat_of_impossible rfl

@[simp] theorem not_sat_impossible : sat impossible v ↔ False :=
  ⟨fun h => impossible_unsat ⟨_, h⟩, False.elim⟩

/-- A solution to a problem consists either of a witness, or a proof of unsatisfiability. -/
inductive Solution (p : Problem)
| sat : p → Solution p
| unsat : p.unsat → Solution p


instance : ToString (Solution p) where
  toString s := match s with
  | .sat ⟨v, _⟩ => s!"satisfied at {v}"
  | .unsat _ => "unsat"

/--
Two problems are equivalent if a solution to one gives an solution to the other.
We don't care that this is bijective,
just that the solution sets are either both empty or both non-empty.
-/
structure equiv (p q : Problem) where
  mp : p → q
  mpr : q → p

def equiv_of_sat_iff {p q : Problem} (h : ∀ v, p.sat v ↔ q.sat v) : p.equiv q where
  mp := fun ⟨v, s⟩ => ⟨v, (h v).mp s⟩
  mpr := fun ⟨v, s⟩ => ⟨v, (h v).mpr s⟩

namespace equiv

def refl (p : Problem) : p.equiv p where
  mp := id
  mpr := id

def trans {p q r : Problem} (e : p.equiv q) (f : q.equiv r) : p.equiv r where
  mp := f.mp ∘ e.mp
  mpr := e.mpr ∘ f.mpr

end equiv

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

theorem eraseEquality_sat (p : Problem) (eq : Equality) (v : List Int) (s : p.sat v) :
    { p with equalities := p.equalities.erase eq }.sat v :=
  { s with
    equalities := fun m => s.equalities (by simp at m; apply List.mem_of_mem_erase m) }

theorem eraseInequality_sat (p : Problem) (lc : LinearCombo) (v : List Int) (s : p.sat v) :
    { p with inequalities := p.inequalities.erase lc }.sat v :=
  { s with
    inequalities := fun m => s.inequalities (by simp at m; apply List.mem_of_mem_erase m) }

/-- Any solution gives a solution after erasing an equality. -/
def eraseEquality_map (p : Problem) (eq : Equality) :
    p → { p with equalities := p.equalities.erase eq } :=
  map_of_sat (p.eraseEquality_sat eq)

/-- Any solution gives a solution after erasing an inequality. -/
def eraseInequality_map (p : Problem) (lc : LinearCombo) :
    p → { p with inequalities := p.inequalities.erase lc } :=
  map_of_sat (p.eraseInequality_sat lc)

theorem filterEqualities_sat (p : Problem) (f) (v : List Int) (s : p.sat v) :
    { p with equalities := p.equalities.filter f }.sat v :=
  { s with
    equalities := fun m => s.equalities (by simp at m; exact List.mem_of_mem_filter' m) }

theorem filterInequalities_sat (p : Problem) (f) (v : List Int) (s : p.sat v) :
    { p with inequalities := p.inequalities.filter f }.sat v :=
  { s with
    inequalities := fun m => s.inequalities (by simp at m; exact List.mem_of_mem_filter' m) }

def filterEqualities_map (p : Problem) (f) :
    p → { p with equalities := p.equalities.filter f } :=
  map_of_sat (p.filterEqualities_sat f)

def filterInequalities_map (p : Problem) (f) :
    p → { p with inequalities := p.inequalities.filter f } :=
  map_of_sat (p.filterInequalities_sat f)

end Problem

/-!
Define `a ≤ b` on linear combinations to mean that the coefficients are identical,
and the constant terms satisfy `≤`.

If `a ≤ b`, then the non-negative set for `a` is a subset of the non-negative set for `b`.

(Note this is only a preorder, not even a partial order,
as we don't allow for rescaling when comparing coefficients.)

We show:
```
a < b → a ∈ p.inequalities → { p with equalities := p.equalities.erase b } → p
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

instance : DecidableRel ((· : LinearCombo) ≤ ·) :=
  fun a b => decidable_of_iff' _ (le_def a b)

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

instance : LT LinearCombo := ⟨lt⟩

@[simp]
theorem lt_def (a b : LinearCombo) : a < b ↔ a.coeffs = b.coeffs ∧ a.const < b.const := by
  change a ≤ b ∧ ¬a = b ↔ _
  rw [le_def]
  rcases a with ⟨a, as⟩; rcases b with ⟨b, bs⟩
  simp only [ext_iff]
  constructor
  · rintro ⟨⟨rfl, le⟩, h⟩
    simp_all only [and_true, true_and]
    exact Int.lt_iff_le_and_ne.mpr ⟨le, h⟩
  · rintro ⟨rfl, lt⟩
    simp only [true_and, and_true]
    exact ⟨Int.le_of_lt lt, Int.ne_of_lt lt⟩

instance : DecidableRel ((· : LinearCombo) < ·) :=
  fun a b => decidable_of_iff' _ (lt_def a b)

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
theorem sat_of_eraseRedundantInequality_sat
    (p : Problem) {a b : LinearCombo} (lt : a < b) (m : a ∈ p.inequalities) (v)
    (s : { p with inequalities := p.inequalities.erase b }.sat v) : p.sat v :=
  { s with
    inequalities := fun m' => by
      rw [List.mem_iff_mem_erase_or_eq _ _ b] at m'
      rcases m' with m' | ⟨rfl, m'⟩
      · apply s.inequalities
        exact m'
      · rcases lt with ⟨le, ne⟩
        apply LinearCombo.evalNonneg_of_le le
        apply s.inequalities
        simpa using (List.mem_erase_of_ne ne).mpr m }

/--
If `a < b` is a strict comparison between inequality constraints,
in any problems containing `a`, we can discard `b` to obtain an equivalent problem.
-/
def eraseRedundantInequality_equiv
    (p : Problem) {a b : LinearCombo} (lt : a < b) (m : a ∈ p.inequalities) :
    { p with inequalities := p.inequalities.erase b }.equiv p :=
  equiv_of_sat_iff
    fun v => ⟨p.sat_of_eraseRedundantInequality_sat lt m v, p.eraseInequality_sat b v⟩

end Problem

/-!
We define negation of a linear combination,
and show that `a < b.neg` gives a contradition.
-/
namespace Problem

theorem contradiction_of_neg_lt (p : Problem) {a b : LinearCombo}
    (ma : a ∈ p.inequalities) (mb : b ∈ p.inequalities) (w : a < -b) : p.unsat := by
  rintro ⟨v, s⟩
  have := LinearCombo.eval_lt_of_lt w v
  simp only [LinearCombo.neg_eval] at this
  apply Int.lt_irrefl 0 (Int.lt_of_lt_of_le (Int.lt_of_le_of_lt (s.inequalities ma) this)
    (Int.neg_le_neg (s.inequalities mb)))

/--
We verify that `x - 1 ≥ 0` and `-x ≥ 0` have no solutions.
-/
example :
    let p : Problem := { inequalities := [{const:=-1, coeffs:=[1]}, {const:=0, coeffs:=[-1]}] };
    p.unsat := by
  apply contradiction_of_neg_lt (a := {const:=-1, coeffs:=[1]}) (b := {const:=0, coeffs:=[-1]}) <;>
  simp

instance {α : Type _} [DecidableEq α] {l : List α} (p : α → Prop) [∀ a, Decidable (p a)] :
    Decidable (∃ (a : α) (_ : a ∈ l), p a) :=
  decidable_of_iff (∃ (a : α), a ∈ l ∧ p a) (exists_congr (fun _ => exists_prop.symm))

def checkContradictions (p : Problem) : Problem :=
  if ∃ (a : LinearCombo) (_ : a ∈ p.inequalities) (b : LinearCombo) (_ : b ∈ p.inequalities), a < -b then
    impossible
  else p

theorem checkContradictions_sat_iff (p : Problem) (v) : p.checkContradictions.sat v ↔ p.sat v := by
  dsimp [checkContradictions]
  split_ifs with h
  · constructor
    · intro s
      simp_all
    · intro s
      simp only [not_sat_impossible]
      obtain ⟨a, ma, b, mb, w⟩ := h
      exact p.contradiction_of_neg_lt ma mb w ⟨v, s⟩
  · rfl

def checkContradictions_equiv (p : Problem) : p.checkContradictions.equiv p :=
  Problem.equiv_of_sat_iff p.checkContradictions_sat_iff

end Problem

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
  simp at h
  simp [eval]
  nth_rewrite 2 [← Int.add_zero c]
  congr
  exact IntList.dot_of_left_zero h

end LinearCombo

namespace Problem

/--
We look for any constant equalities with nonzero constant,
or for any constant inequalities with negative constant.

If we find any, the problem is impossible.
Otherwise, we can discard all constants.
-/
def processConstants (p : Problem) : Problem :=
  let equalityConstants := p.equalities.filterMap fun eq => eq.linearCombo.constant?
  let inequalityConstants := p.inequalities.filterMap LinearCombo.constant?
  if equalityConstants.all (· = 0) ∧ inequalityConstants.all (· ≥ 0) then
    { p with
      equalities := p.equalities.filter fun eq => eq.linearCombo.constant? = none
      inequalities := p.inequalities.filter fun lc => lc.constant? = none }
  else
    impossible

theorem processConstants_sat (p : Problem) (v) (s : p.sat v) : p.processConstants.sat v := by
  dsimp [processConstants]
  split_ifs with w
  · exact Problem.filterEqualities_sat _ _ _ (Problem.filterInequalities_sat _ _ _ s)
  · exfalso
    simp only [not_and_or] at w
    simp only [List.all_eq_true, List.mem_filterMap, decide_eq_true_eq, forall_exists_index,
      and_imp, not_forall, exists_prop, exists_and_left] at w
    rcases w with (⟨c, eq, w, m, ne⟩ | ⟨c, eq, w, m, ne⟩)
    · have := s.equalities w
      simp [eq.linearCombo.eval_eq_of_constant m] at this
      exact ne this
    · have := s.inequalities w
      simp [eq.eval_eq_of_constant m] at this
      exact ne this

theorem sat_of_processConstants_sat (p : Problem) (v) (s : p.processConstants.sat v) : p.sat v := by
  dsimp [processConstants] at s
  split_ifs at s with w
  · simp at w
    rcases w with ⟨eqs, ineqs⟩
    constructor
    · exact s.possible
    · intro eq mem
      match h : eq.linearCombo.constant? with
      | some c =>
        rw [eq.linearCombo.eval_eq_of_constant h]
        exact eqs _ eq mem h
      | none =>
        apply s.equalities
        simp
        rw [List.mem_filter]
        exact ⟨mem, decide_eq_true h⟩
    · intro lc mem
      match h : lc.constant? with
      | some c =>
        rw [lc.eval_eq_of_constant h]
        exact ineqs _ lc mem h
      | none =>
        apply s.inequalities
        simp
        rw [List.mem_filter]
        exact ⟨mem, decide_eq_true h⟩
  · replace s := s.possible
    simp at s

/-- A problem is equivalent to the problem after processing constants. -/
def processConstants_equiv (p : Problem) : p.processConstants.equiv p :=
  equiv_of_sat_iff fun v => ⟨p.sat_of_processConstants_sat v, p.processConstants_sat v⟩

example : processConstants { equalities := [{linearCombo := {const := 1}}] } = impossible := rfl
example : processConstants { equalities := [{linearCombo := {const := 1}}] } |>.unsat := impossible_unsat
example : Problem.unsat { equalities := [{linearCombo := {const := 1}}] } :=
  impossible_unsat ∘ (processConstants_equiv _).mpr
example : Problem.unsat { inequalities := [{const := -1}] } :=
  impossible_unsat ∘ (processConstants_equiv _).mpr

end Problem

namespace LinearCombo

/--
To normalize an inequality, we divide through by the gcd of the coefficients,
using floor rounding when we divide the constant term.
-/
def normalizeInequality (lc : LinearCombo) : LinearCombo :=
  let gcd := lc.coeffs.gcd
  if gcd = 0 then
    { const := lc.const
      coeffs := [] }
  else
    { coeffs := lc.coeffs.sdiv gcd
      -- Since `gcd ≥ 0`, `ediv` and `fdiv` coincide: this is floor rounding.
      const := lc.const / gcd }

example : ({const := 1, coeffs := [2]} : LinearCombo).normalizeInequality =
    {const := 0, coeffs := [1]} := rfl
example : ({const := 5, coeffs := [6, 15]} : LinearCombo).normalizeInequality =
    {const := 1, coeffs := [2, 5]} := rfl
example : ({const := -5, coeffs := [6, 15]} : LinearCombo).normalizeInequality =
    {const := -2, coeffs := [2, 5]} := rfl
example : ({const := 10, coeffs := [6, 8]} : LinearCombo).normalizeInequality =
    {const := 5, coeffs := [3, 4]} := rfl

/--
To normalize an equality, we check if the constant term is divisible by the gcd of the coefficients.
If it is, we divide through by the gcd. Otherwise, the equality is unsatisfiable.
-/
def normalizeEquality (lc : LinearCombo) : LinearCombo :=
  let gcd := lc.coeffs.gcd
  if (gcd : Int) ∣ lc.const then
    { coeffs := lc.coeffs.sdiv gcd
      const := lc.const / gcd }
  else
    { coeffs := []
      const := 1 }

example : ({const := 1, coeffs := [2]} : LinearCombo).normalizeEquality = {const := 1} := rfl
example : ({const := -1, coeffs := [-2]} : LinearCombo).normalizeEquality = {const := 1} := rfl
example : ({const := 1, coeffs := [6, 9]} : LinearCombo).normalizeEquality = {const := 1} := rfl
example : ({const := 3, coeffs := [6, 9]} : LinearCombo).normalizeEquality =
    {const := 1, coeffs := [2, 3]} := rfl

@[simp] theorem normalizeInequality_eval {lc : LinearCombo} :
    lc.normalizeInequality.eval v ≥ 0 ↔ lc.eval v ≥ 0 := by
  rcases lc with ⟨const, coeffs⟩
  dsimp [normalizeInequality, eval]
  split_ifs with h
  · rw [IntList.gcd_eq_zero] at h
    simp [IntList.dot_of_left_zero h]
  · rw [IntList.dot_sdiv_gcd_left, ← Int.add_ediv_of_dvd_right (IntList.gcd_dvd_dot_left coeffs v),
      Int.div_nonneg_iff_of_pos]
    match coeffs.gcd, h with
    | (n+1), _ => exact Int.ofNat_succ_pos n

@[simp] theorem normalizeEquality_eval {lc : LinearCombo} :
    lc.normalizeEquality.eval v = 0 ↔ lc.eval v = 0 := by
  rcases lc with ⟨const, coeffs⟩
  dsimp [normalizeEquality, eval]
  split_ifs with h
  · simp only [IntList.dot_sdiv_gcd_left]
    by_cases w : coeffs.gcd = 0
    · simp only [w, Int.ofNat_zero, Int.zero_dvd, Int.ediv_zero, Int.add_zero, true_iff] at h ⊢
      simp only [h, Int.zero_add]
      simp at w
      rw [IntList.dot_of_left_zero w]
    · replace w : (coeffs.gcd : Int) ≠ 0 := Int.ofNat_ne_zero.mpr w
      rw [← Int.mul_eq_mul_right_iff w]
      have : (coeffs.gcd : Int) ∣ IntList.dot coeffs v := IntList.gcd_dvd_dot_left _ _
      simp_all [Int.add_mul, Int.ediv_mul_cancel]
  · simp only [IntList.dot_nil_left, Int.add_zero, false_iff]
    intro w
    apply h
    replace w := congr_arg (fun x : Int => x % coeffs.gcd) w
    simp [Int.add_emod] at w
    exact Int.dvd_of_emod_eq_zero w

end LinearCombo

namespace Equality

@[simps]
def normalize (eq : Equality) : Equality :=
  { linearCombo := eq.linearCombo.normalizeEquality }
  -- TODO copy other fields?

theorem normalize_eval {eq : Equality} :
  eq.normalize.linearCombo.eval v = 0 ↔ eq.linearCombo.eval v = 0 := by simp

end Equality
namespace Problem

/-- To normalize a problem we normalize each equality and inequality. -/
def normalize (p : Problem) : Problem where
  possible := p.possible
  equalities := p.equalities.map Equality.normalize
  inequalities := p.inequalities.map LinearCombo.normalizeInequality

theorem normalize_sat (p : Problem) (h : p.sat v) : p.normalize.sat v where
  possible := h.possible
  equalities m := by
    simp [normalize] at m
    obtain ⟨a, m, rfl⟩ := m
    simpa using h.equalities m
  inequalities m := by
    simp [normalize] at m
    obtain ⟨a, m, rfl⟩ := m
    simpa using h.inequalities m

theorem sat_of_normalize_sat (p : Problem) (h : p.normalize.sat v) : p.sat v where
  possible := h.possible
  equalities m := by
    rw [← Equality.normalize_eval]
    apply h.equalities
    simp [normalize]
    refine ⟨_, m, rfl⟩
  inequalities m := by
    rw [← LinearCombo.normalizeInequality_eval]
    apply h.inequalities
    simp [normalize]
    refine ⟨_, m, rfl⟩

/-- The normalization of a problem is equivalent to the problem. -/
def normalize_equiv (p : Problem) : p.normalize.equiv p :=
  equiv_of_sat_iff fun _ => ⟨p.sat_of_normalize_sat, p.normalize_sat⟩

end Problem

namespace LinearCombo

/-- Replace `xᵢ` in `b` with `r`. -/
def substitute (b : LinearCombo) (i : Nat) (r : LinearCombo) : LinearCombo :=
  if b.coeff i = 0 then
    b
  else
    b.setCoeff i 0 + (b.coeff i * r)

@[simp] theorem substitute_eval :
    (substitute b i r).eval v = b.eval v + b.coeff i * (r.eval v - v.get i) := by
  rw [substitute]
  split_ifs
  · simp_all
  · simp only [add_eval, setCoeff_eval, Int.zero_sub, Int.neg_mul, smul_eval, Int.add_assoc,
      Int.mul_sub]
    simp only [Int.sub_eq_add_neg, Int.add_comm (_ * _)]

end LinearCombo

namespace Equality

/--
Assuming `a = 0`, solve for the variable `xᵢ`, as a `LinearCombo`.

The result is only valid if `(a.coeff i).natAbs = 1`.
-/
def solveFor (a : Equality) (i : Nat) : LinearCombo :=
  (- (a.linearCombo.coeff i)) * a.linearCombo.setCoeff i 0

end Equality

theorem Int.mul_self_eq_one_of_natAbs_eq_one {x : Int} (h : x.natAbs = 1) : x * x = 1 := by
  match x, h with
  | 1,            _ => simp
  | Int.negSucc 0, _ => simp

namespace LinearCombo

theorem substitute_solveFor_eval (w : (a.linearCombo.coeff i).natAbs = 1) (h : a.linearCombo.eval v = 0) :
    (LinearCombo.substitute b i (Equality.solveFor a i)).eval v = b.eval v := by
  simp only [Equality.solveFor, substitute_eval, smul_eval, setCoeff_eval, h, Int.zero_sub, Int.neg_mul,
    Int.zero_add, Int.mul_neg, Int.neg_neg]
  rw [← Int.mul_assoc (a.linearCombo.coeff i), Int.mul_self_eq_one_of_natAbs_eq_one w, Int.one_mul,
    Int.sub_self, Int.mul_zero, Int.add_zero]

end LinearCombo

namespace Equality

-- Are we going to regret not storing matrices? Or row operations??
def backSubstitution (a : Equality) (i : Nat) (w : IntList) : IntList :=
  w.set i ((a.solveFor i).eval w)

attribute [simp] Int.sub_self

theorem eval_backSubstitution (a : Equality) (b : LinearCombo) (i : Nat) (w : IntList) :
    b.eval (a.backSubstitution i w) = (b.substitute i (solveFor a i)).eval w := by
  simp [backSubstitution]

open LinearCombo

theorem eval_backSubstitution_self (a : Equality) (w : (a.linearCombo.coeff i).natAbs = 1) :
    a.linearCombo.eval (a.backSubstitution i v) = 0 := by
  simp only [backSubstitution, solveFor, smul_eval, setCoeff_eval, Int.zero_sub, Int.neg_mul,
    eval_set, Int.mul_sub, Int.mul_neg]
  rw [← Int.mul_assoc]
  rw [Int.mul_self_eq_one_of_natAbs_eq_one w]
  simp only [Int.one_mul, Int.neg_add, Int.neg_neg, Int.add_sub_cancel]
  simp only [← Int.sub_eq_add_neg, Int.sub_self]

@[simps]
def substitute (a : Equality) (i : Nat) (r : LinearCombo) : Equality :=
  { linearCombo := a.linearCombo.substitute i r }
  -- TODO: Other fields?

end Equality

namespace Problem

-- This only makes sense when `a ∈ p.equalities` and `(a.linearCombo.coeff i).natAbs = 1`.
@[simps]
def eliminateEquality (p : Problem) (a : Equality) (i : Nat) : Problem :=
  let r := a.solveFor i
  { possible := p.possible
    equalities := (p.equalities.erase a).map fun eq => eq.substitute i r
    inequalities := p.inequalities.map fun ineq => ineq.substitute i r }

theorem eliminateEquality_equalities_length (p : Problem) {a : Equality} (i : Nat)
    (ma : a ∈ p.equalities) :
    (p.eliminateEquality a i).equalities.length + 1 = p.equalities.length := by
  simp only [eliminateEquality_equalities, List.length_map, ma, List.length_erase_of_mem]
  rw [Nat.add_one, Nat.succ_pred]
  rw [← @Nat.pos_iff_ne_zero]
  exact List.length_pos_of_mem ma

theorem eliminateEquality_sat (p : Problem) {a : Equality} {i : Nat} (ma : a ∈ p.equalities)
    (w : (a.linearCombo.coeff i).natAbs = 1) (v) (s : p.sat v) : (p.eliminateEquality a i).sat v where
  possible := s.possible
  equalities mb := by
    simp only [eliminateEquality_equalities, List.mem_map, ne_eq] at mb
    obtain ⟨b, mb, rfl⟩ := mb
    have mb' : b ∈ p.equalities := List.mem_of_mem_erase mb
    rw [Equality.substitute_linearCombo, LinearCombo.substitute_solveFor_eval w (s.equalities ma),
      s.equalities mb']
  inequalities mb := by
    simp only [eliminateEquality_inequalities, List.mem_map, ne_eq] at mb
    obtain ⟨b, mb, rfl⟩ := mb
    rw [LinearCombo.substitute_solveFor_eval w (s.equalities ma)]
    exact s.inequalities mb

theorem sat_of_eliminateEquality_sat (p : Problem) {a : Equality} {i : Nat}
    (m : a ∈ p.equalities) (w : (a.linearCombo.coeff i).natAbs = 1) (v)
    (s : (p.eliminateEquality a i).sat v) : p.sat (a.backSubstitution i v) where
  possible := s.possible
  equalities := by
    intro eq mb
    by_cases h : eq = a
    · subst h
      rw [Equality.eval_backSubstitution_self _ w]
    · rw [Equality.eval_backSubstitution, ← Equality.substitute_linearCombo]
      apply s.equalities
      simp only [eliminateEquality_equalities, List.mem_map, ne_eq]
      refine ⟨eq, ?_, rfl⟩
      exact (List.mem_erase_of_ne h).mpr mb
  inequalities mb := by
    rw [Equality.eval_backSubstitution]
    apply s.inequalities
    simp only [eliminateEquality_inequalities, List.mem_map]
    exact ⟨_, mb, rfl⟩

/-- The normalization of a problem is equivalent to the problem. -/
def eliminateEquality_equiv (p : Problem) {a : Equality} {i : Nat} (m : a ∈ p.equalities)
    (w : (a.linearCombo.coeff i).natAbs = 1) : (p.eliminateEquality a i).equiv p where
  mp := fun ⟨v, s⟩ => ⟨a.backSubstitution i v, p.sat_of_eliminateEquality_sat m w v s⟩
  mpr := fun ⟨v, s⟩ => ⟨v, p.eliminateEquality_sat m w v s⟩

end Problem



namespace Problem

def smallCoeffEquality (p : Problem) : Option (Equality × Nat) :=
  p.equalities.findSome? fun e => match e.smallCoeff with | some i => some (e, i) | none => none

theorem smallCoeffEquality_mem {p : Problem} (w : p.smallCoeffEquality = some (e, i)) :
    e ∈ p.equalities := by
  obtain ⟨e', m, h⟩ := List.exists_of_findSome?_eq_some w
  split at h <;> simp_all

theorem smallCoeffEquality_natAbs_Eq {p : Problem} (w : p.smallCoeffEquality = some (e, i)) :
    (e.linearCombo.coeff i).natAbs = 1 := by
  obtain ⟨e', m, h⟩ := List.exists_of_findSome?_eq_some w
  split at h <;> simp_all
  exact e.smallCoeff_natAbs ‹_›

def eliminateEasyEqualities_aux (n : Nat) (p : Problem) (w : p.equalities.length ≤ n) : Problem :=
  match n with
  | 0 => p
  | n+1 =>
    match h : p.smallCoeffEquality with
    | some (e, i) =>
      have m : e ∈ p.equalities := smallCoeffEquality_mem h
      have : (p.equalities.erase e).length < p.equalities.length := by
        rw [← p.eliminateEquality_equalities_length i m]
        simp
      have : (p.eliminateEquality e i).equalities.length ≤ n := by
        simpa using Nat.lt_succ.mp (Nat.lt_of_lt_of_le this w)
      eliminateEasyEqualities_aux n (p.eliminateEquality e i) this
    | none => p

def eliminateEasyEqualities (p : Problem) : Problem :=
  match p.equalities with
  | [] => p
  | _ => p.eliminateEasyEqualities_aux _ (Nat.le_refl _)

def eliminateEasyEqualities_equiv_aux (n : Nat) (p : Problem) (w : p.equalities.length ≤ n) :
    (p.eliminateEasyEqualities_aux n w).equiv p :=
  match n with
  | 0 => equiv.refl p
  | n+1 => by
    dsimp [eliminateEasyEqualities_aux]
    -- TODO I'm unhappy to have to use `split` here.
    -- Just using `match h : p.smallCoeffEquality with` results in `tag not found`.
    split
    · rename_i e i h
      have m : e ∈ p.equalities := smallCoeffEquality_mem h
      have : (p.equalities.erase e).length < p.equalities.length := by
        rw [← p.eliminateEquality_equalities_length i m]
        simp
      have : (p.eliminateEquality e i).equalities.length ≤ n := by
        simpa using Nat.lt_succ.mp (Nat.lt_of_lt_of_le this w)
      exact (eliminateEasyEqualities_equiv_aux n (p.eliminateEquality e i) this).trans
        (p.eliminateEquality_equiv m (smallCoeffEquality_natAbs_Eq h))
    · exact equiv.refl p

def eliminateEasyEqualities_equiv (p : Problem) : p.eliminateEasyEqualities.equiv p := by
  dsimp [eliminateEasyEqualities]
  split
  · exact equiv.refl p
  · exact p.eliminateEasyEqualities_equiv_aux _ (Nat.le_refl _)

end Problem

/-- Balanced mod, taking values in the range [- m/2, (m - 1)/2]. -/
def Int.bmod (x : Int) (m : Nat) : Int :=
  let r := x % m
  if r < (m + 1) / 2 then
    r
  else
    r - m

example : Int.bmod 3 7 = 3 := rfl
example : Int.bmod 4 7 = -3 := rfl
example : Int.bmod 3 8 = 3 := rfl
example : Int.bmod 4 8 = -4 := rfl

theorem Int.dvd_emod_sub_self {x : Int} {m : Nat} : (m : Int) ∣ x % m - x := by
  apply Int.dvd_of_emod_eq_zero
  simp [Int.sub_emod]

theorem Int.dvd_bmod_sub_self {x : Int} {m : Nat} : (m : Int) ∣ Int.bmod x m - x := by
  dsimp [Int.bmod]
  split_ifs
  · exact Int.dvd_emod_sub_self
  · rw [Int.sub_sub, Int.add_comm, ← Int.sub_sub]
    exact Int.dvd_sub Int.dvd_emod_sub_self (Int.dvd_refl _)

theorem Int.le_bmod {x : Int} {m : Nat} : - m/2 ≤ Int.bmod x m := sorry
theorem Int.bmod_lt {x : Int} {m : Nat} : Int.bmod x m < (m + 1) / 2 := sorry
theorem Int.bmod_le {x : Int} {m : Nat} : Int.bmod x m ≤ (m - 1) / 2 := sorry


@[simp] theorem Int.emod_self_add_one {x : Int} (h : 0 ≤ x) : x % (x + 1) = x :=
  Int.emod_eq_of_lt h (Int.lt_succ x)

@[simp] theorem Int.sign_ofNat_add_one {x : Nat} : Int.sign (x + 1) = 1 := rfl
@[simp] theorem Int.sign_negSucc {x : Nat} : Int.sign (Int.negSucc x) = -1 := rfl

example (a b : Nat) (w : a ≤ 2 * b) : a / 2 ≤ b :=
  Nat.div_le_of_le_mul w

theorem Int.ofNat_two : ((2 : Nat) : Int) = 2 := rfl

theorem Int.bmod_abs_plus_one (x : Int) : Int.bmod x (x.natAbs + 1) = - x.sign := by
  cases x with
  | ofNat x =>
    simp_all only [bmod, Int.ofNat_eq_coe, Int.natAbs_ofNat, Int.natCast_add, Int.ofNat_one,
      emod_self_add_one (Int.ofNat_nonneg x)]
    match x with
    | 0 => rw [if_pos] <;> simp
    | (x+1) =>
      rw [if_neg]
      · simp [← Int.sub_sub]
      · refine Int.not_lt.mpr ?_
        simp only [← Int.natCast_add, ← Int.ofNat_one, ← Int.ofNat_two, ← Int.ofNat_ediv]
        refine Int.ofNat_le.mpr ?hnc.a --
        apply Nat.div_le_of_le_mul
        sorry -- okay, doable from here.
  | negSucc x =>
    simp [Int.bmod]
    rw [if_neg]
    · sorry
    · sorry

namespace LinearCombo

def shrinkingConstraint (eq : LinearCombo) (i : Nat) (n : Nat) : LinearCombo :=
  sorry

def shrinkingConstraint_solution {eq : LinearCombo} (i : Nat) (n : Nat) (v : IntList) : IntList :=
  v.set n sorry

theorem shrinkingConstraint_eval {eq : LinearCombo} (w : eq.eval v = 0) :
    (eq.shrinkingConstraint i n).eval (eq.shrinkingConstraint_solution i n v) = 0 :=
  sorry

theorem shrinkingConstraint_coeff_natAbs {eq : LinearCombo} :
    ((eq.shrinkingConstraint i n).coeff i).natAbs = 1 :=
  sorry

end LinearCombo


namespace Problem

def addEquality (p : Problem) (eq : Equality) : Problem where
  possible := p.possible
  equalities := eq :: p.equalities
  inequalities := p.inequalities

-- TODO The maps connecting `p` and `p.addEquality eq`.

def shrinkEqualityCoeffs (p : Problem) (eq : Equality) (i : Nat) : Problem :=
  (p.addEquality eq).eliminateEquality eq i

-- This will require additional hypotheses?
def shrinkEqualityCoeffs_equiv (p : Problem) (eq : Equality) (i : Nat) (w : (sorry : Prop)) :
    (p.shrinkEqualityCoeffs eq i).equiv p :=
  sorry

/-- The minimal absolute value of a nonzero coefficient appearing in an equality. -/
def minEqualityCoeff (p : Problem) : Nat :=
  p.equalities.map (Equality.minCoeff) |>.minimum? |>.getD 0

/--
The maximal absolute value of a coefficient appearing in an equality which
also contains a coefficient with absolute value `p.minEqualityCoeff`.
-/
def maxEqualityCoeff (p : Problem) : Nat := sorry

def equalityCoeffPair (p : Problem) : Nat ×ₗ Nat :=
  (p.minEqualityCoeff, p.maxEqualityCoeff)

theorem shrinkTermination (p : Problem) (eq) (i) :
    (p.shrinkEqualityCoeffs eq i).equalityCoeffPair < p.equalityCoeffPair :=
  sorry

def eliminateEqualities_of_minEqualityCoeff_le_one (p : Problem) (h : p.minEqualityCoeff ≤ 1) : Problem := sorry

theorem _root_.Prod.Lex.right'' [LT α] [LT β] {a₁ a₂ : α} {b₁ b₂ : β} (ha : a₁ = a₂) (hb : b₁ < b₂) :
    Prod.Lex (· < ·) (· < · ) (a₁, b₁) (a₂, b₂) :=
  ha ▸ Prod.Lex.right a₁ hb

def eliminateEqualities (p : Problem) : Problem :=
  if h₁ : p.equalities.length = 0 then
    p
  else if h₂ : p.minEqualityCoeff = 0 then
    p
  else if h₃ : p.minEqualityCoeff = 1 then
    sorry
  else
    let eq := sorry
    let i := sorry
    let p' := p.shrinkEqualityCoeffs eq i
    if h₄ : p'.minEqualityCoeff < p.minEqualityCoeff then
      p'.eliminateEqualities
    else
      have h₅ : p'.minEqualityCoeff = p.minEqualityCoeff := sorry
      have h₆ : p'.maxEqualityCoeff < p.maxEqualityCoeff := sorry
      have h₇ := Prod.Lex.right'' h₅ h₆
      p'.eliminateEqualities
termination_by eliminateEqualities p => (p.minEqualityCoeff, p.maxEqualityCoeff)
decreasing_by
  first | assumption | (constructor; assumption)

theorem eliminateEqualities_equalities_length {p : Problem} :
    p.eliminateEqualities.equalities.length = 0 :=
  sorry

def eliminateEqualities_equiv (p : Problem) : p.eliminateEqualities.equiv p := by
  rw [eliminateEqualities]
  split_ifs with h₁ h₂ h₃
  · exact equiv.refl p
  · exact equiv.refl p
  · sorry
  · dsimp
    split_ifs with h₄
    · exact equiv.trans (p.shrinkEqualityCoeffs sorry sorry).eliminateEqualities_equiv (p.shrinkEqualityCoeffs_equiv sorry sorry sorry)
    · let p' := p.shrinkEqualityCoeffs sorry sorry
      have h₅ : p'.minEqualityCoeff = p.minEqualityCoeff := sorry
      have h₆ : p'.maxEqualityCoeff < p.maxEqualityCoeff := sorry
      have h₇ := Prod.Lex.right'' h₅ h₆
      exact equiv.trans (p.shrinkEqualityCoeffs sorry sorry).eliminateEqualities_equiv (p.shrinkEqualityCoeffs_equiv sorry sorry sorry)
termination_by eliminateEqualities_equiv p => (p.minEqualityCoeff, p.maxEqualityCoeff)
decreasing_by
  first | assumption | (constructor; assumption)

end Problem

end Omega.Impl
