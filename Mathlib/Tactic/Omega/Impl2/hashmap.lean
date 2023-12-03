-- import Std.Data.HashMap.Basic

-- open Std

-- #eval (HashMap.empty : HashMap Nat Nat).isEmpty  -- true
-- #eval (HashMap.empty.insert 1 1).isEmpty  -- false
-- example : (HashMap.empty : HashMap Nat Nat).isEmpty = true := rfl -- okay
-- example : (HashMap.empty.insert 1 1).isEmpty = false := rfl -- type mismatch
