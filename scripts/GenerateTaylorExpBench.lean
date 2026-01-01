import CertifiedJL.Arithmetic.Transcendental.Exponential.TaylorExpData

/-! Emit an untrusted 128-point fixture; each generated theorem uses kernel replay. -/

open CertifiedJL

def outputs (fast : Bool) : List ℤ :=
  (List.range 128).map fun i =>
    let x : ℚ := i * 90 / 127
    (if fast then TaylorExp.negUpper 512 x 10 else Exp.negUpper 512 x 24).hi

def main (args : List String) : IO Unit := do
  let fast ← match args with
    | ["legacy"] => pure false
    | ["taylor"] => pure true
    | _ => throw (IO.userError "usage: GenerateTaylorExpBench.lean legacy|taylor")
  IO.println "import CertifiedJL.Arithmetic.Transcendental.Exponential.TaylorExpData"
  IO.println "open CertifiedJL"
  IO.println "set_option maxRecDepth 1000000"
  IO.println "set_option maxHeartbeats 40000000"
  IO.println "def output : List ℤ := (List.range 128).map fun i =>"
  IO.println "  let x : ℚ := i * 90 / 127"
  IO.println (if fast then "  (TaylorExp.negUpper 512 x 10).hi" else "  (Exp.negUpper 512 x 24).hi")
  IO.println ("theorem benchmark : output = [" ++ String.intercalate ", " ((outputs fast).map toString) ++ "] := by decide +kernel")
