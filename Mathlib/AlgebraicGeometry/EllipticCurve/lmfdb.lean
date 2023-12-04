import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Lean
import Std

-- #lmfdb EllipticCurve/Q 220890.c1

-- Go to https://www.lmfdb.org/EllipticCurve/Q/data/220890.c1?_format=json
-- Pull out the `data / ainvs` field: [1, 0, 1, -10009, 883196]
-- Add the declaration `def LMFDB.«EllipticCurve/Q».«220890.c1» : WeierstrassCurve ℚ := ⟨1, 0, 1, -10009, 883196⟩`

/-- Runs a terminal command and retrieves its output -/
def runCmd (cmd : String) (args : Array String) (throwFailure := true) : IO String := do
  let out ← IO.Process.output { cmd := cmd, args := args }
  if out.exitCode != 0 && throwFailure then throw $ IO.userError out.stderr
  else return out.stdout

def runCurl (args : Array String) (throwFailure := true) : IO String := do
  runCmd "curl" args throwFailure

def ellipticCurveJSON (label : String) : IO String :=
  runCurl #[s!"https://www.lmfdb.org/EllipticCurve/Q/data/{label}?_format=json"]

open Lean

def getWeierstrass (label : String) : IO (List Int) := do
  match Json.parse (← ellipticCurveJSON label) with
  | .ok r => match r.getObjVal? "data" with
    | .ok r =>
      match r.getArrVal? 0 with
      | .ok r => match r.getArrVal? 0 with
        | .ok r => match r.getObjVal? "ainvs" with
          | .ok r => match fromJson? r with
            | .ok r => return r
            | .error _ => return []
          | .error _ => return []
        | .error _ => return []
      | .error _ => return []
    | .error _ => return []
  | .error _ => return []

#eval getWeierstrass "220890.c1"

open Lean Elab Command

def WeierstrassCurve.ofList (x : List Int) : WeierstrassCurve ℚ :=
  match x with
  | [a1, a2, a3, a4, a6] => ⟨a1, a2, a3, a4, a6⟩
  | _ => ⟨0, 0, 0, 0, 0⟩

elab "#lmfdb " category:ident label:ident : command => liftTermElabM do
  if category.getId.toString != "«EllipticCurve/Q»" then
    throwError "Currently the only supported category is `#lmfdb «EllipticCurve/Q»`."
  let labelString := label.getId.toString.stripPrefix "«" |>.stripSuffix "»"
  let coeffs ← getWeierstrass labelString
  addAndCompile <| Declaration.defnDecl
    { name := (`LMFDB).str "EllipticCurve/Q" |>.str labelString
      levelParams := []
      safety := DefinitionSafety.safe
      hints := ReducibilityHints.regular 0
      type := .app (.const ``WeierstrassCurve [.zero]) (.const ``_root_.Rat [])
      value := .app (.const ``WeierstrassCurve.ofList []) (toExpr coeffs) }
