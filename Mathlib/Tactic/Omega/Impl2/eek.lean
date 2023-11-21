
import Std

import Mathlib.Tactic.LibrarySearch

set_option autoImplicit true

open Std (HashMap RBSet RBMap)

inductive Inequality
| lowerBound (x : Int)
| upperBound (x : Int)

namespace Inequality

def sat : Inequality → Int → Prop
| .lowerBound x, y => x ≤ y
| .upperBound x, y => y ≤ x

end Inequality

inductive Constraint
| impossible
| lowerBound (x : Int)
| upperBound (x : Int)
| between (x y : Int)
| exact (x : Int)
| trivial

namespace Constraint

def sat : Constraint → Int → Prop
| .impossible, _ => False
| .lowerBound x, y => x ≤ y
| .upperBound x, y => y ≤ x
| .between x y, z => x ≤ z ∧ z ≤ y
| .exact x, z => x = z
| .trivial, _ => True

def combine : Constraint → Inequality → Constraint
| .impossible, .lowerBound _ => .impossible
| .impossible, .upperBound _ => .impossible
| .lowerBound x, .lowerBound w => if x < w then .lowerBound w else .lowerBound x
| .lowerBound x, .upperBound z => if z < x then .impossible else .between x z
| .upperBound y, .lowerBound w => if y < w then .impossible else .between w y
| .upperBound y, .upperBound z => if y < z then .upperBound y else .upperBound y
| .between x y, .lowerBound w =>
  if y < w then .impossible else if x ≤ w then .between w y else .between x y
| .between x y, .upperBound z =>
  if z < x then .impossible else if z ≤ y then .between x z else .between x y
| .exact x, .lowerBound w => if w ≤ x then .exact x else .impossible
| .exact x, .upperBound z => if x ≤ z then .exact x else .impossible
| .trivial, .lowerBound w => .lowerBound w
| .trivial, .upperBound z => .upperBound z

theorem combine_sat :
    (c : Constraint) → (i : Inequality) → (t : Int) → (c.combine i).sat t = (c.sat t ∧ i.sat t)
| .impossible, .lowerBound _, t => by simp [sat, combine]
| .impossible, .upperBound _, t => by simp [sat, combine]
| .lowerBound x, .lowerBound w, t => by
  simp [combine]
  split <;> rename_i h <;> simp [sat, Inequality.sat]
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


end Constraint

structure Coefficients where
  coeffs : List Int
  -- TODO cache the hash
deriving BEq, Hashable -- TODO we need a custom hash function that is invariant under negatino

instance : LawfulBEq Coefficients := sorry

structure Indexer (α : Type _) [BEq α] [Hashable α] where
  keys : HashMap α Nat := ∅
  values : Array α := #[]
  spec : ∀ c i, keys.find? c = some i ↔ values.get? i = some c := by intros; simp

@[simp] theorem Array.nil_getElem? {i : Nat} : (#[] : Array α)[i]?  = none := rfl

@[simp] theorem Std.HashMap.empty_find? {α : Type _} [BEq α] [Hashable α] {a : α} :
    (∅ : HashMap α β).find? a = none := by
  sorry

theorem Std.HashMap.insert_find? {α : Type _} [BEq α] [LawfulBEq α] [Hashable α]
    (m : HashMap α β) (a a' : α) (b : β) :
    (m.insert a b).find? a' = if a' == a then some b else m.find? a' :=
  sorry

theorem Array.push_getElem? {a : Array α} : (a.push x)[i]? = if i = a.size then some x else a[i]? :=
  sorry
@[simp] theorem Array.getElem?_size {a : Array α} : a[a.size]? = none :=
  sorry

def Indexer.empty (α : Type _) [BEq α] [Hashable α] : Indexer α where

def Indexer.insert {α : Type _} [BEq α] [LawfulBEq α] [Hashable α] (m : Indexer α) (a : α) : Nat × Indexer α :=
  match h : m.keys.find? a with
  | some i => (i, m)
  | none =>
    (m.values.size,
      { keys := m.keys.insert a m.values.size
        values := m.values.push a
        spec := fun c i => by
          simp only [Array.get?_eq_getElem?, HashMap.insert_find?, Array.push_getElem?]
          have s := m.spec c i
          split <;> rename_i h <;> simp only [beq_iff_eq] at h <;> split <;> rename_i h'
          · simp_all
          · replace h' := Ne.symm h'
            simp_all
          · replace h := Ne.symm h
            simp_all
          · simp_all })

def Indexer.lookup {α : Type _} [BEq α] [Hashable α] (m : Indexer α) (i : Nat) : Option α :=
  m.values[i]?

structure Problem where
  keyData : Indexer Coefficients

  constraints : HashMap Nat Constraint

  equalities : RBSet Nat compare
  equalities_spec : ∀ i, equalities.contains i ↔ constraints.find? i matches some (.exact _)

  -- lowerBounds : Array (HashSet Nat)
  -- lowerBounds_spec :
  -- upperBounds : Array (HashSet Nat)


namespace Problem

def addInequalityCore (p : Problem) (cs : List Int) (c : Int) : Problem :=
  let ((coeffs : List Int), (s : Bool)) := sorry
  let (n, keyData) := p.keyData.insert { coeffs }
  let i : Inequality := if s then Inequality.lowerBound (-c) else .upperBound c
  let cst := (p.constraints.find? n).getD .trivial
  let cst' := cst.combine i
  let constraints := p.constraints.insert n cst'
  { keyData
    constraints
    equalities := p.equalities
    equalities_spec := sorry }

end Problem
