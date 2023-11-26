
import Std
import Mathlib.Tactic.Omega.IntList
import Mathlib.Tactic.Omega.Impl.MinNatAbs
import Mathlib.Tactic.Omega.Impl.bmod
import Qq
import Mathlib.Tactic.LibrarySearch
import Mathlib.Util.Time

set_option autoImplicit true
set_option relaxedAutoImplicit true

open Std (HashMap RBSet RBMap AssocList)

namespace List

@[inline] protected def insert' [BEq α] (a : α) (l : List α) : List α :=
  if l.elem a then l else a :: l

end List

namespace Std.HashMap

def all [BEq α] [Hashable α] (m : HashMap α β) (f : α → β → Bool) : Bool :=
  m.fold (init := true) fun r a b => r && f a b

end Std.HashMap
namespace Std.AssocList

def insert [BEq α] (a : α) (b : β) : AssocList α β → AssocList α β
  | .nil => .cons a b .nil
  | .cons x y t => if x == a then .cons x b t else .cons x y (insert a b t)

end Std.AssocList

inductive Bound
| lowerBound (x : Int)
| upperBound (x : Int)

namespace Bound

def sat : Bound → Int → Bool
| .lowerBound x, y => x ≤ y
| .upperBound x, y => y ≤ x

end Bound

inductive Constraint
| impossible
| lowerBound (x : Int)
| upperBound (x : Int)
| between (x y : Int)
| exact (x : Int)
| trivial
deriving BEq, Repr

namespace Constraint

instance : ToString Constraint where
  toString := fun
  | impossible => "∅"
  | .lowerBound x => s!"[{x}, ∞)"
  | .upperBound y => s!"(-∞, {y}]"
  | .between x y => s!"[{x}, {y}]"
  | .exact x => s!"\{{x}}"
  | .trivial => s!"(-∞, ∞)"

def sat : Constraint → Int → Bool
| .impossible, _ => false
| .lowerBound x, y => x ≤ y
| .upperBound x, y => y ≤ x
| .between x y, z => x ≤ z ∧ z ≤ y
| .exact x, z => x = z
| .trivial, _ => true

def translate : Constraint → Int → Constraint
| .impossible, _ => .impossible
| .lowerBound x, t => .lowerBound (x + t)
| .upperBound y, t => .upperBound (y + t)
| .between x y, t => .between (x + t) (y + t)
| .exact x, t => .exact (x + t)
| .trivial, _ => .trivial

def neg : Constraint → Constraint
| .impossible => .impossible
| .lowerBound x => .upperBound (-x)
| .upperBound y => .lowerBound (-y)
| .between x y => .between (-y) (-x)
| .exact x => .exact (-x)
| .trivial => .trivial

theorem translate_sat : sat c v → sat (c.translate t) (v + t) := sorry

def interval (x y : Int) : Constraint :=
  if y < x then
    .impossible
  else if x = y then
    .exact x
  else
    .between x y

def combine_bound : Constraint → Bound → Constraint
| .impossible, .lowerBound _ => .impossible
| .impossible, .upperBound _ => .impossible
| .lowerBound x, .lowerBound w => if x < w then .lowerBound w else .lowerBound x
| .lowerBound x, .upperBound z => interval x z
| .upperBound y, .lowerBound w => interval w y
| .upperBound y, .upperBound z => if y < z then .upperBound y else .upperBound y
| .between x y, .lowerBound w =>
  if x ≤ w then interval w y else .between x y
| .between x y, .upperBound z =>
  if z ≤ y then interval x z else .between x y
| .exact x, .lowerBound w => if w ≤ x then .exact x else .impossible
| .exact x, .upperBound z => if x ≤ z then .exact x else .impossible
| .trivial, .lowerBound w => .lowerBound w
| .trivial, .upperBound z => .upperBound z

def combine : Constraint → Constraint → Constraint
| _, .impossible => .impossible
| c, .lowerBound w => combine_bound c (.lowerBound w)
| c, .upperBound z => combine_bound c (.upperBound z)
| c, .between x y => combine_bound (combine_bound c (.lowerBound x)) (.upperBound y)
| c, .exact x => combine_bound (combine_bound c (.lowerBound x)) (.upperBound x)
| c, .trivial => c

theorem combine_bound_sat :
    (c : Constraint) → (i : Bound) → (t : Int) → (c.combine_bound i).sat t = (c.sat t ∧ i.sat t)
| .impossible, .lowerBound _, t => by simp [sat, combine_bound]
| .impossible, .upperBound _, t => by simp [sat, combine_bound]
| .lowerBound x, .lowerBound w, t => by
  simp [combine_bound]
  split <;> rename_i h <;> simp [sat, Bound.sat]
  · sorry
  · sorry
| .lowerBound x, .upperBound z, t => sorry
| .upperBound y, .lowerBound w, t => sorry
| .upperBound y, .upperBound z, t => sorry
| .between x y, .lowerBound w, t => sorry
| .between x y, .upperBound z, t => sorry
| .exact x, .lowerBound w, t => sorry
| .exact x, .upperBound z, t => sorry
| .trivial, .lowerBound w, t => sorry
| .trivial, .upperBound z, t => sorry

def div : Constraint → Nat → Constraint
| .impossible, _ => .impossible
| .lowerBound x, k => .lowerBound (- ((- x) / k))
| .upperBound y, k => .upperBound (y / k)
| .between x y, k =>
  let x' := - ((- x) / k)
  let y' := y / k
  if x'  = y' then .exact x' else .between x' y'
| .exact x, k => if (k : Int) ∣ x then .exact (x / k) else .impossible
| .trivial, _ => .trivial

end Constraint

def hashIntList (v : List Int) : UInt64 :=
  v.foldl (init := 37) fun r x => 7 * r + Hashable.hash (73 * (x + 17))

structure Coefficients where
  coeffs : List Int
  -- spec: first nonzero entry is nonnegative, and no trailing zeroes?
  gcd : Nat := IntList.gcd coeffs
  -- gcd_spec

  -- TODO cache the hash
  hash : UInt64 := hashIntList coeffs

  minNatAbs : Nat := coeffs.minNatAbs
  -- minNatAbs_spec

  maxNatAbs : Nat := coeffs.map Int.natAbs |>.maximum? |>.getD 0
  -- maxNatAbs_spec
deriving Repr

namespace Coefficients

instance : Ord Coefficients where
  compare x y := compareOfLessAndEq x.coeffs y.coeffs

instance : BEq Coefficients where
  beq x y := x.hash == y.hash && x.coeffs == y.coeffs

-- TODO remove the `DecidableEq` instance, which compares determined fields,
-- in favour of a `LawfulBEq` instance.

instance : ToString Coefficients where
  toString c := " + ".intercalate <| c.coeffs.enum.map fun ⟨i, c⟩ => s!"{c} * x{i+1}"

def eval (c : Coefficients) (v : List Int) : Int := IntList.dot c.coeffs v

instance : Hashable Coefficients := ⟨hash⟩

-- It is essential that the kernel can compute our hash function.
example : hash ({ coeffs := [1, 2] } : Coefficients) = 22983 := rfl

def div_gcd (c : Coefficients) : Coefficients :=
  { coeffs := IntList.sdiv c.coeffs c.gcd |>.trim
    gcd := 1
    minNatAbs := c.minNatAbs / c.gcd }

end Coefficients

-- instance : LawfulBEq Coefficients := sorry

-- structure Indexer (α : Type _) [BEq α] [Hashable α] where
--   keys : HashMap α Nat := ∅
--   values : Array α := #[]
--   spec : ∀ c i, keys.find? c = some i ↔ values.get? i = some c := by intros; simp

-- @[simp] theorem Array.nil_getElem? {i : Nat} : (#[] : Array α)[i]?  = none := rfl

-- @[simp] theorem Std.HashMap.empty_find? {α : Type _} [BEq α] [Hashable α] {a : α} :
--     (∅ : HashMap α β).find? a = none := by
--   sorry

-- theorem Std.HashMap.insert_find? {α : Type _} [BEq α] [LawfulBEq α] [Hashable α]
--     (m : HashMap α β) (a a' : α) (b : β) :
--     (m.insert a b).find? a' = if a' == a then some b else m.find? a' :=
--   sorry

-- theorem Array.push_getElem? {a : Array α} : (a.push x)[i]? = if i = a.size then some x else a[i]? :=
--   sorry
-- @[simp] theorem Array.getElem?_size {a : Array α} : a[a.size]? = none :=
--   sorry

-- def Indexer.empty (α : Type _) [BEq α] [Hashable α] : Indexer α where

-- def Indexer.insert {α : Type _} [BEq α] [LawfulBEq α] [Hashable α] (m : Indexer α) (a : α) : Nat × Indexer α :=
--   match h : m.keys.find? a with
--   | some i => (i, m)
--   | none =>
--     (m.values.size,
--       { keys := m.keys.insert a m.values.size
--         values := m.values.push a
--         spec := fun c i => by
--           simp only [Array.get?_eq_getElem?, HashMap.insert_find?, Array.push_getElem?]
--           have s := m.spec c i
--           split <;> rename_i h <;> simp only [beq_iff_eq] at h <;> split <;> rename_i h'
--           · simp_all
--           · replace h' := Ne.symm h'
--             simp_all
--           · replace h := Ne.symm h
--             simp_all
--           · simp_all })

-- def Indexer.lookup {α : Type _} [BEq α] [Hashable α] (m : Indexer α) (i : Nat) : Option α :=
--   m.values[i]?

structure Problem where
  constraints : AssocList Coefficients Constraint := ∅

  possible : Bool := true
  -- possible_spec : ¬ ∃ c, contraints.find? c matches some (.impossible)

  equalities : List Coefficients := ∅
  -- equalities_spec : ∀ i, equalities.contains i ↔ constraints.find? i matches some (.exact _)

  -- lowerBounds : Array (HashSet Nat)
  -- lowerBounds_spec :
  -- upperBounds : Array (HashSet Nat)


instance : ToString Problem where
  toString p :=
    if p.possible then
      if p.constraints.isEmpty then
        "trivial"
      else
        "\n".intercalate <|
          (p.constraints.toList.map fun ⟨coeffs, cst⟩ => s!"{coeffs} ∈ {cst}")
    else
      "impossible"

structure Inequality where
  coeffs : Coefficients
  cst : Constraint

namespace Inequality

def sat (i : Inequality) (v : List Int) : Bool :=
  i.cst.sat (i.coeffs.eval v)

def normalize (i : Inequality) : Inequality :=
  if i.coeffs.gcd = 0 then
    match i.cst with
    | .lowerBound x => if 0 < x then { i with cst := .impossible } else { i with cst := .trivial }
    | .upperBound y => if y < 0 then { i with cst := .impossible } else { i with cst := .trivial }
    | .between x y => if 0 < x || y < 0 then { i with cst := .impossible } else { i with cst := .trivial }
    | .exact x => if x = 0 then { i with cst := .trivial } else { i with cst := .impossible }
    | _ => i
  else if i.coeffs.gcd = 1 then
    i
  else
    { coeffs := i.coeffs.div_gcd
      cst := i.cst.div i.coeffs.gcd }

theorem normalize_sat {i : Inequality} : i.normalize.sat v = i.sat v :=
  sorry

def of (coeffs : List Int) (cst : Constraint) : Inequality :=
  let coeffs := IntList.trim coeffs
  normalize <|
  if 0 ≤ (coeffs.find? (! · == 0) |>.getD 0) then
    { coeffs := { coeffs }
      cst := cst }
  else
    { coeffs := { coeffs := IntList.smul coeffs (-1) }
      cst := cst.neg }

/-- Convert `const + ∑ coeffs[i] * xᵢ ≥ 0` into an `Inequality`. -/
def of_le (coeffs : List Int) (const : Int) : Inequality :=
  of coeffs (.lowerBound (-const))

/-- Convert `const + ∑ coeffs[i] * xᵢ = 0` into an `Inequality`. -/
def of_eq (coeffs : List Int) (const : Int) : Inequality :=
  of coeffs (.exact (-const))

theorem of_le_sat {coeffs const} : (of_le coeffs const).sat v = (0 ≤ (IntList.dot coeffs v) + const) :=
  sorry

end Inequality

namespace Problem

instance : Inhabited Problem := ⟨{}⟩

def sat (p : Problem) (v : List Int) : Bool :=
  p.constraints.all fun coeffs cst => cst.sat (coeffs.eval v)

def addInequality (p : Problem) (ineq : Inequality) : Problem :=
  if p.possible then
    let cst := (p.constraints.find? ineq.coeffs).getD .trivial
    match cst.combine ineq.cst with
    | .trivial => p
    | .impossible => { possible := false }
    | cst' =>
      let constraints := p.constraints.insert ineq.coeffs cst'
      { constraints
        possible := p.possible
        -- possible_spec := sorry
        equalities :=
        if cst' matches .exact _ then
          p.equalities.insert' ineq.coeffs
        else
          p.equalities
        -- equalities_spec := sorry
        }
  else
    p

theorem addInequality_sat : (addInequality p ineq).sat v = p.sat v && ineq.sat v :=
  sorry

def addInequalities (p : Problem) (ineqs : List Inequality) : Problem :=
  ineqs.foldl addInequality p

example : (Problem.addInequalities {}
    [Inequality.of_le [1, 1] (-1), Inequality.of_le [-1, -1] (-1)] |>.possible) = false := rfl

example : (Problem.addInequalities {}
    [Inequality.of_le [2] 2, Inequality.of_le [-2] (-2)] |>.possible) = true := rfl

example : (Problem.addInequalities {}
    [Inequality.of_le [2] 1, Inequality.of_le [-2] (-1)] |>.possible) = false := rfl

example : (Problem.addInequalities {}
    [Inequality.of_eq [2] 2] |>.possible) = true := rfl

example : (Problem.addInequalities {}
    [Inequality.of_eq [2] 1] |>.possible) = false := rfl

def selectEquality (p : Problem) : Option Coefficients :=
  p.equalities.foldl (init := none) fun
  | none, c => c
  | some r, c => if 2 ≤ r.minNatAbs && (c.minNatAbs < r.minNatAbs || c.minNatAbs = r.minNatAbs && c.maxNatAbs < r.maxNatAbs) then c else r

def solveEasyEquality (p : Problem) (c : Coefficients) : Problem :=
  let i := c.coeffs.findIdx? (·.natAbs = 1) |>.getD 0 -- findIdx? is always some
  let sign := c.coeffs.get? i |>.getD 0 |> Int.sign
  match p.constraints.find? c with
  | some (.exact r) =>
    p.constraints.foldl (init := {}) fun p' coeffs cst =>
      match coeffs.coeffs.get? i |>.getD 0 with
      | 0 =>
        p'.addInequality ⟨coeffs, cst⟩
      | ci =>
        let k := -1 * sign * ci
        p'.addInequality <| .of
          (coeffs.coeffs + IntList.smul c.coeffs k)
          (cst.translate (k * r))
  | _ => unreachable!

def freshVar (p : Problem) : Nat := p.constraints.foldl (init := 0) fun l c _ => max l c.coeffs.length

/--
We deal with a hard equality by introducing a new easy equality.

After solving the easy equality,
the minimum lexicographic value of `(c.minNatAbs, c.maxNatAbs)` will have been reduced.
-/
def dealWithHardEquality (p : Problem) (c : Coefficients) : Problem :=
  let m := c.minNatAbs + 1
  let j := p.freshVar
  match p.constraints.find? c with
  | some (.exact r) =>
    p.addInequality
      { coeffs :=
        { coeffs := IntList.add (c.coeffs.map fun x => Int.bmod x m)
            (List.replicate j 0 ++ [- (m : Int)]) }
        cst := .exact (Int.bmod r m) }
  | cst =>
    dbgTrace (toString cst)
      fun _ => unreachable!

def solveEquality (p : Problem) (c : Coefficients) : Problem :=
  if c.minNatAbs = 1 then
    p.solveEasyEquality c
  else
    p.dealWithHardEquality c

def solveEqualities (p : Problem) (fuel : Nat := 100) : Problem :=
  match fuel with
  | 0 => p
  | f + 1 =>
  -- dbgTrace ("---\n" ++ toString p) fun _ =>
  match p.selectEquality with
  | some c => (p.solveEquality c).solveEqualities f
  | none => p
