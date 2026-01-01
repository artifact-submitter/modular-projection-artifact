import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Replay.Cap47Diffuse.FourierBridge
import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Replay.Cap47Diffuse.GlobalLeaf00
import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Replay.Cap47Diffuse.GlobalLeaf01
import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Replay.Cap47Diffuse.GlobalLeaf02
import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Replay.Cap47Diffuse.GlobalLeaf03
import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Replay.Cap47Diffuse.GlobalLeaf04
import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Replay.Cap47Diffuse.GlobalLeaf05
import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Replay.Cap47Diffuse.GlobalLeaf06
import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Replay.Cap47Diffuse.GlobalLeaf07
import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Replay.Cap47Diffuse.DominationLeaf00
import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Replay.Cap47Diffuse.DominationLeaf01
import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Replay.Cap47Diffuse.DominationLeaf02
import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Replay.Cap47Diffuse.DominationLeaf03
import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Replay.Cap47Diffuse.DominationLeaf04
import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Replay.Cap47Diffuse.DominationLeaf05
import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Replay.Cap47Diffuse.DominationLeaf06
import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Replay.Cap47Diffuse.DominationLeaf07
import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Replay.Cap47Diffuse.DominationLeaf08

open CertifiedJL.TrigonometricBernstein

namespace CertifiedJL.TernaryLInfTwoDecimal.Cap47Diffuse

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
      (.branch
      ((by
        convert globalLeaf02Tree using 1
        all_goals norm_num))
      ((by
        convert globalLeaf03Tree using 1
        all_goals norm_num))))
      ((by
        convert globalLeaf04Tree using 1
        all_goals norm_num)))
      ((by
        convert globalLeaf05Tree using 1
        all_goals norm_num)))
      (.branch
      ((by
        convert globalLeaf06Tree using 1
        all_goals norm_num))
      ((by
        convert globalLeaf07Tree using 1
        all_goals norm_num)))

theorem rawNonnegative {y : ℝ} (hlo : (((-1 : ℚ)) : ℝ) ≤ y)
    (hhi : y ≤ (((1 : ℚ)) : ℝ)) :
    0 ≤ rationalPowerValue power y :=
  globalTree.nonneg hlo hhi

theorem dominationTree :
    NonnegativeTree (rationalPowerValue (subtractConstant power 1))
      (1176349 / 12500000 : ℚ) 1 := by
  exact .branch
      (.branch
      (.branch
      ((by
        convert dominationLeaf00Tree using 1
        all_goals norm_num))
      (.branch
      ((by
        convert dominationLeaf01Tree using 1
        all_goals norm_num))
      ((by
        convert dominationLeaf02Tree using 1
        all_goals norm_num))))
      (.branch
      (.branch
      ((by
        convert dominationLeaf03Tree using 1
        all_goals norm_num))
      (.branch
      ((by
        convert dominationLeaf04Tree using 1
        all_goals norm_num))
      ((by
        convert dominationLeaf05Tree using 1
        all_goals norm_num))))
      ((by
        convert dominationLeaf06Tree using 1
        all_goals norm_num))))
      (.branch
      ((by
        convert dominationLeaf07Tree using 1
        all_goals norm_num))
      ((by
        convert dominationLeaf08Tree using 1
        all_goals norm_num)))

theorem rawDominatesOne {y : ℝ} (hlo : (((1176349 / 12500000 : ℚ)) : ℝ) ≤ y)
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

theorem cosineDominatesOne {x : ℝ} (hx : (((1176349 / 12500000 : ℚ)) : ℝ) ≤ Real.cos x) :
    1 ≤ rationalCosineValue fourier x := by
  rw [← rationalPowerValue_cos_eq_rationalCosineValue fourierPowerCheck x]
  exact rawDominatesOne hx (by simpa using Real.cos_le_one x)

end CertifiedJL.TernaryLInfTwoDecimal.Cap47Diffuse
