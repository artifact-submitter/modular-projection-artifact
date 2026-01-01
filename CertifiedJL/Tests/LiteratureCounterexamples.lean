import CertifiedJL.Projection.Counterexamples.L2Lower.LNPLowerTail
import CertifiedJL.Projection.Counterexamples.L2Lower.OrthusPrintedParameters

namespace CertifiedJL.Tests.LiteratureCounterexamples

open Counterexamples
open scoped ENNReal

example :
    eventProbability (sparseRademacherMatrix 256 1)
        (fun J => projectionSqNorm J LNPLowerTail.kappaOneWitness < 13) >
      failureTarget 256 :=
  LNPLowerTail.kappaOneCounterexample

example :
    eventProbability (sparseRademacherMatrix 256 1)
        (fun J => projectionSqNorm J LNPLowerTail.kappaOneWitness < 13) =
        ((∑ k ∈ Finset.range 13, (256 : ℕ).choose k : ℕ) : ℝ≥0∞) *
          ((2 ^ 256 : ℕ) : ℝ≥0∞)⁻¹ ∧
      eventProbability (sparseRademacherMatrix 256 1)
          (fun J => projectionSqNorm J LNPLowerTail.kappaOneWitness < 13) >
        failureTarget 256 :=
  LNPLowerTail.kappaOnePrintedCounterexample

example :
    eventProbability (LNPLowerTail.binTwoMatrixPMF 256 1)
        (fun J => projectionSqNorm J LNPLowerTail.kappaTwoWitness < 26) >
      failureTarget 256 :=
  LNPLowerTail.kappaTwoCounterexample

example :
    Odd 41 ∧
      CenteredInput 41 LNPLowerTail.kappaTwoWitness ∧
      0 < (1 : ℕ) ∧
      InputThresholdAtMostNorm 1 LNPLowerTail.kappaTwoWitness ∧
      41 * 1 * 1 ≤ 41 ∧
      eventProbability (LNPLowerTail.binTwoMatrixPMF 256 1)
          (L2ThresholdLowerFailure (NonnegativeRatio.ofNat 26)
            1 41 LNPLowerTail.kappaTwoWitness) >
        failureTarget 256 :=
  LNPLowerTail.lemmaTwoTenCounterexample

example (q : ℕ) (hq : Odd q) (hqLower : 2821 ≤ q) :
    CenteredInput q OrthusPrintedParameters.witness ∧
      31 ^ 2 < sqNorm OrthusPrintedParameters.witness ∧
      31 ≤ q / 91 ∧
      InputThresholdWithinModulus (NonnegativeRatio.ofNat 91) q 31 ∧
      eventProbability (sparseRademacherMatrix 256 2)
          (LInfThresholdSmallProjection OrthusPrintedParameters.parameters
            31 q OrthusPrintedParameters.witness) =
        (14 : ℝ≥0∞) ^ 256 * ((16 : ℝ≥0∞) ^ 256)⁻¹ ∧
      eventProbability (sparseRademacherMatrix 256 2)
          (LInfThresholdSmallProjection OrthusPrintedParameters.parameters
            31 q OrthusPrintedParameters.witness) >
        failureTarget 128 :=
  OrthusPrintedParameters.printedParameterBridge q hq hqLower

#print axioms LNPLowerTail.kappaOneProbability_exact
#print axioms LNPLowerTail.kappaOneCounterexample
#print axioms LNPLowerTail.kappaOnePrintedCounterexample
#print axioms LNPLowerTail.kappaTwo_integerComparison
#print axioms LNPLowerTail.kappaTwoCounterexample
#print axioms LNPLowerTail.lemmaTwoTenCounterexample
#print axioms OrthusPrintedParameters.printedParameterBridge

end CertifiedJL.Tests.LiteratureCounterexamples
