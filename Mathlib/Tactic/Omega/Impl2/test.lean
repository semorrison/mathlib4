import Mathlib.Tactic.Omega.Impl2.Frontend

open Omega ProofProducing

example : True := by
  fail_if_success omega
  trivial

set_option trace.omega true

example (_ : (1 : Int) < (0 : Int)) : False := by omega

example (_ : (0 : Int) < (0 : Int)) : False := by omega
example (_ : (0 : Int) < (1 : Int)) : True := by (fail_if_success omega); trivial

example {x : Int} (_ : x % 2 < x - 2 * (x / 2)) : False := by omega
