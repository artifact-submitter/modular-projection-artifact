import CertifiedJL.Protocol
import CertifiedJL.Statements.Transport.Scaling

namespace CertifiedJL.Tests.AffineTransports

#check centeredMod_odd_mul
#check centeredMod_three_mul
#check shiftedModularProjectionSqNorm_odd_mul
#check shiftedModularProjectionSqNorm_le_add_sq
#check sqrt_shiftedModularProjectionSqNorm_le
#check AffineLInfThresholdLowerTailAt.twoThirds
#check AffineL2ThresholdLowerTailAt.fourNinths
#check L2UpperTailAt.affine_radii
#check L2UpperTailAt.affine_norm
#check L2UpperTailAt.to_affine
#check affineL2UpperFailureWithShift_zeroShift
#check AffineL2UpperTailAt.to_unshifted
#check affineL2UpperTailAt_iff
#check LInfUpperTailAt.affine_radii
#check LInfUpperTailAt.affine_norm
#check LInfUpperTailAt.to_affine
#check affineLInfUpperFailureWithShift_zeroShift
#check AffineLInfUpperTailAt.to_unshifted
#check affineLInfUpperTailAt_iff
#check AffineL2ThresholdLowerTailAt.closedAcceptance
#check AffineL2ThresholdLowerTailAt.closedAcceptance_realThreshold
#check L2ThresholdLowerTailAt.closedAcceptance_realThreshold
#check AffineLInfThresholdLowerTailAt.closedAcceptance
#check AffineLInfThresholdLowerTailAt.closedAcceptance_realThreshold
#check LInfThresholdLowerTailAt.closedAcceptance_realThreshold
#check AffineL2UpperTailAt.history_le
#check AffineLInfUpperTailAt.history_le
#check AffineLInfThresholdLowerTailAt.history_joint_le
#check AffineLInfThresholdLowerTailAt.history_badWitness_le_add_invalid
#check AffineLInfThresholdLowerTailAt.history_closedAcceptance_le_add_invalid
#check AffineL2ThresholdLowerTailAt.history_joint_le
#check AffineL2ThresholdLowerTailAt.history_badWitness_le_add_invalid
#check AffineL2ThresholdLowerTailAt.history_closedAcceptance_le_add_invalid
#check eventProbability_finiteCall_le_sum

example : (NonnegativeRatio.ofNat 3).twoThirds =
    { numerator := 6, denominator := 3, denominator_pos := by decide } := rfl

example : (NonnegativeRatio.ofNat 3).fourNinths =
    { numerator := 12, denominator := 9, denominator_pos := by decide } := rfl

example : closedLInfInputThreshold (NonnegativeRatio.ofNat 1) 0 = 1 := by
  norm_num [closedLInfInputThreshold, NonnegativeRatio.toReal,
    NonnegativeRatio.ofNat]

example : ∃ (k b : ℕ), Odd k ∧ 0 < k ∧ 0 < b ∧
    (b : ℝ) ≤ k * 1 ∧ (k : ℝ) * 0 <
      (NonnegativeRatio.ofNat 1).toReal * b := by
  apply exists_odd_scale_nat_of_lInf_headroom (NonnegativeRatio.ofNat 1)
      (A := 0) (B := 1)
  · norm_num
  · norm_num
  · norm_num [NonnegativeRatio.ofNat]
  · norm_num [NonnegativeRatio.toReal, NonnegativeRatio.ofNat]

example : ¬ ((1 : ℝ) < (NonnegativeRatio.ofNat 1).toReal * 1) := by
  norm_num [NonnegativeRatio.toReal, NonnegativeRatio.ofNat]

#print axioms AffineLInfThresholdLowerTailAt.twoThirds
#print axioms AffineL2ThresholdLowerTailAt.fourNinths
#print axioms L2UpperTailAt.to_affine
#print axioms affineL2UpperFailureWithShift_zeroShift
#print axioms AffineL2UpperTailAt.to_unshifted
#print axioms affineL2UpperTailAt_iff
#print axioms LInfUpperTailAt.to_affine
#print axioms affineLInfUpperFailureWithShift_zeroShift
#print axioms AffineLInfUpperTailAt.to_unshifted
#print axioms affineLInfUpperTailAt_iff
#print axioms AffineL2ThresholdLowerTailAt.closedAcceptance_realThreshold
#print axioms AffineLInfThresholdLowerTailAt.closedAcceptance_realThreshold
#print axioms LInfThresholdLowerTailAt.closedAcceptance_realThreshold
#print axioms AffineL2UpperTailAt.history_le
#print axioms AffineLInfUpperTailAt.history_le
#print axioms AffineL2ThresholdLowerTailAt.history_closedAcceptance_le_add_invalid
#print axioms AffineLInfThresholdLowerTailAt.history_closedAcceptance_le_add_invalid

end CertifiedJL.Tests.AffineTransports
