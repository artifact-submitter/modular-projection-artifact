import CertifiedJL.Arithmetic.Transcendental.Exponential.TaylorExp

/-! Cheap exact endpoint checks for the alternative exponential evaluator. -/

namespace CertifiedJL.TaylorExp.Tests

example : negUpper 64 0 7 = ⟨0, Dyadic.scale 64⟩ := by
  decide +kernel

example : (negUpper 64 1 7).hi ≤ (Exp.negUpper 64 1 24).hi := by
  decide +kernel

example : (posUpper 64 1 7).hi ≤ (Exp.posUpper 64 1 30).hi := by
  decide +kernel

end CertifiedJL.TaylorExp.Tests
