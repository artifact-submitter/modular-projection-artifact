import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Replay.Cap24Diffuse.FourierBridge
import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Replay.Cap24Diffuse.GlobalLeaf00
import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Replay.Cap24Diffuse.GlobalLeaf01
import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Replay.Cap24Diffuse.GlobalLeaf02
import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Replay.Cap24Diffuse.GlobalLeaf03
import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Replay.Cap24Diffuse.GlobalLeaf04
import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Replay.Cap24Diffuse.GlobalLeaf05
import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Replay.Cap24Diffuse.DominationLeaf00

open CertifiedJL.TrigonometricBernstein

namespace CertifiedJL.TernaryLInfTwoDecimal.Cap24Diffuse

theorem globalTree :
    NonnegativeTree (rationalPowerValue power) (-1) 1 := by
  exact .branch
      (.branch
      (.branch
      (.branch
      (.branch
      ((by
        convert globalLeaf00Tree using 1
        all_goals norm_num))
      ((by
        convert globalLeaf01Tree using 1
        all_goals norm_num)))
      ((by
        convert globalLeaf02Tree using 1
        all_goals norm_num)))
      ((by
        convert globalLeaf03Tree using 1
        all_goals norm_num)))
      ((by
        convert globalLeaf04Tree using 1
        all_goals norm_num)))
      ((by
        convert globalLeaf05Tree using 1
        all_goals norm_num))

theorem rawNonnegative {y : ℝ} (hlo : (((-1 : ℚ)) : ℝ) ≤ y)
    (hhi : y ≤ (((1 : ℚ)) : ℝ)) :
    0 ≤ rationalPowerValue power y :=
  globalTree.nonneg hlo hhi

theorem dominationTree :
    NonnegativeTree (rationalPowerValue (subtractConstant power 1))
      (72896857 / 100000000 : ℚ) 1 := by
  exact dominationLeaf00Tree

theorem rawDominatesOne {y : ℝ} (hlo : (((72896857 / 100000000 : ℚ)) : ℝ) ≤ y)
    (hhi : y ≤ (((1 : ℚ)) : ℝ)) : 1 ≤ rationalPowerValue power y := by
  have h := dominationTree.nonneg hlo hhi
  rw [rationalPowerValue_subtractConstant_of_ne_nil (by simp [power]) 1] at h
  norm_num at h
  exact h

theorem cosineNonnegative (x : ℝ) :
    0 ≤ rationalCosineValue fourier x := by
  rw [← rationalPowerValue_cos_eq_rationalCosineValue fourierPowerCheck x]
  exact rawNonnegative (by simpa using Real.neg_one_le_cos x)
    (by simpa using Real.cos_le_one x)

theorem cosineDominatesOne {x : ℝ} (hx : (((72896857 / 100000000 : ℚ)) : ℝ) ≤ Real.cos x) :
    1 ≤ rationalCosineValue fourier x := by
  rw [← rationalPowerValue_cos_eq_rationalCosineValue fourierPowerCheck x]
  exact rawDominatesOne hx (by simpa using Real.cos_le_one x)

end CertifiedJL.TernaryLInfTwoDecimal.Cap24Diffuse
