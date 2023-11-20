import Mathlib.Tactic.Simps.Basic

structure P where
  x : Nat

def P.y (p : P) : Nat := p.x + 1

@[simps]
def p : P where
  x := 37
