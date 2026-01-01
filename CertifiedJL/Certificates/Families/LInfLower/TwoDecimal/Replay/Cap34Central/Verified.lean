import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Replay.Cap34Central.FourierBridge
import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Replay.Cap34Central.GlobalLeaf00
import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Replay.Cap34Central.GlobalLeaf01
import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Replay.Cap34Central.GlobalLeaf02
import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Replay.Cap34Central.GlobalLeaf03
import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Replay.Cap34Central.GlobalLeaf04
import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Replay.Cap34Central.GlobalLeaf05
import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Replay.Cap34Central.GlobalLeaf06
import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Replay.Cap34Central.GlobalLeaf07
import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Replay.Cap34Central.GlobalLeaf08
import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Replay.Cap34Central.GlobalLeaf09
import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Replay.Cap34Central.DominationLeaf00

open CertifiedJL.TrigonometricBernstein

namespace CertifiedJL.TernaryLInfTwoDecimal.Cap34Central

theorem globalTree :
    NonnegativeTree (rationalPowerValue power) (-1) 1 := by
  exact .branch
      (.branch
      ((by
        convert globalLeaf00Tree using 1
        all_goals norm_num))
      (.branch
      (.branch
      ((by
        convert globalLeaf01Tree using 1
        all_goals norm_num))
      ((by
        convert globalLeaf02Tree using 1
        all_goals norm_num)))
      (.branch
      ((by
        convert globalLeaf03Tree using 1
        all_goals norm_num))
      ((by
        convert globalLeaf04Tree using 1
        all_goals norm_num)))))
      (.branch
      (.branch
      (.branch
      ((by
        convert globalLeaf05Tree using 1
        all_goals norm_num))
      ((by
        convert globalLeaf06Tree using 1
        all_goals norm_num)))
      (.branch
      ((by
        convert globalLeaf07Tree using 1
        all_goals norm_num))
      ((by
        convert globalLeaf08Tree using 1
        all_goals norm_num))))
      ((by
        convert globalLeaf09Tree using 1
        all_goals norm_num)))

theorem rawNonnegative {y : ℝ} (hlo : (((-1 : ℚ)) : ℝ) ≤ y)
    (hhi : y ≤ (((1 : ℚ)) : ℝ)) :
    0 ≤ rationalPowerValue power y :=
  globalTree.nonneg hlo hhi

theorem dominationTree :
    NonnegativeTree (rationalPowerValue (subtractConstant power 1))
      (43045911 / 50000000 : ℚ) 1 := by
  exact dominationLeaf00Tree

theorem rawDominatesOne {y : ℝ} (hlo : (((43045911 / 50000000 : ℚ)) : ℝ) ≤ y)
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

theorem cosineDominatesOne {x : ℝ} (hx : (((43045911 / 50000000 : ℚ)) : ℝ) ≤ Real.cos x) :
    1 ≤ rationalCosineValue fourier x := by
  rw [← rationalPowerValue_cos_eq_rationalCosineValue fourierPowerCheck x]
  exact rawDominatesOne hx (by simpa using Real.cos_le_one x)

end CertifiedJL.TernaryLInfTwoDecimal.Cap34Central
