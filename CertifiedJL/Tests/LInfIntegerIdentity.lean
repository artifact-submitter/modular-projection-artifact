import CertifiedJL.Certificates.Shared.TrigonometricBernstein

/-! Small exact regression checks for the integer identity route; no leaf replay. -/

namespace CertifiedJL.TrigonometricBernstein.IntegerIdentityTests

example : integerBernsteinIdentityBlockCheck [1, 2] 1 2 3 6 1 [5, 8] 3 0 2 = true := by
  decide +kernel

-- A changed Bernstein coefficient must not certify the original polynomial.
example : integerBernsteinIdentityBlockCheck [1, 2] 1 2 3 6 1 [5, 9] 3 0 2 = false := by
  decide +kernel

theorem original_rational_identity :
    affinePullbackQ (powerPolynomialQ [1, 2]) (1 / 3) (5 / 6) =
      bernsteinPolynomialQ 1 [5 / 3, 8 / 3] := by
  apply affinePullbackQ_eq_bernsteinPolynomialQ_of_integerCertificate
    (powerNumerators := [1, 2]) (powerDenominator := 1)
    (aNumerator := 2) (deltaNumerator := 3) (intervalDenominator := 6)
    (bernsteinNumerators := [5, 8]) (bernsteinDenominator := 3)
    (by decide) (by decide) (by decide)
  · intro i hi
    interval_cases i <;> norm_num
  · intro i hi
    interval_cases i <;> norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · decide +kernel

end CertifiedJL.TrigonometricBernstein.IntegerIdentityTests
