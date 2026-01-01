import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Replay.Cap47Central.FourierBridge
import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Replay.Cap47Central.GlobalLeaf00
import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Replay.Cap47Central.GlobalLeaf01
import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Replay.Cap47Central.GlobalLeaf02
import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Replay.Cap47Central.GlobalLeaf03
import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Replay.Cap47Central.GlobalLeaf04
import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Replay.Cap47Central.GlobalLeaf05
import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Replay.Cap47Central.GlobalLeaf06
import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Replay.Cap47Central.GlobalLeaf07
import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Replay.Cap47Central.GlobalLeaf08
import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Replay.Cap47Central.GlobalLeaf09
import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Replay.Cap47Central.GlobalLeaf10
import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Replay.Cap47Central.GlobalLeaf11
import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Replay.Cap47Central.GlobalLeaf12
import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Replay.Cap47Central.GlobalLeaf13
import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Replay.Cap47Central.GlobalLeaf14
import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Replay.Cap47Central.GlobalLeaf15
import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Replay.Cap47Central.GlobalLeaf16
import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Replay.Cap47Central.GlobalLeaf17
import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Replay.Cap47Central.GlobalLeaf18
import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Replay.Cap47Central.GlobalLeaf19
import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Replay.Cap47Central.GlobalLeaf20
import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Replay.Cap47Central.GlobalLeaf21
import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Replay.Cap47Central.GlobalLeaf22
import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Replay.Cap47Central.GlobalLeaf23
import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Replay.Cap47Central.GlobalLeaf24
import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Replay.Cap47Central.GlobalLeaf25
import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Replay.Cap47Central.GlobalLeaf26
import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Replay.Cap47Central.DominationLeaf00

open CertifiedJL.TrigonometricBernstein

namespace CertifiedJL.TernaryLInfTwoDecimal.Cap47Central

theorem globalTree :
    NonnegativeTree (rationalPowerValue power) (-1) 1 := by
  exact .branch
      (.branch
      (.branch
      (.branch
      ((by
        convert globalLeaf00Tree using 1
        all_goals norm_num))
      (.branch
      (.branch
      (.branch
      ((by
        convert globalLeaf01Tree using 1
        all_goals norm_num))
      ((by
        convert globalLeaf02Tree using 1
        all_goals norm_num)))
      ((by
        convert globalLeaf03Tree using 1
        all_goals norm_num)))
      (.branch
      ((by
        convert globalLeaf04Tree using 1
        all_goals norm_num))
      ((by
        convert globalLeaf05Tree using 1
        all_goals norm_num)))))
      (.branch
      (.branch
      ((by
        convert globalLeaf06Tree using 1
        all_goals norm_num))
      ((by
        convert globalLeaf07Tree using 1
        all_goals norm_num)))
      (.branch
      (.branch
      ((by
        convert globalLeaf08Tree using 1
        all_goals norm_num))
      ((by
        convert globalLeaf09Tree using 1
        all_goals norm_num)))
      ((by
        convert globalLeaf10Tree using 1
        all_goals norm_num)))))
      (.branch
      (.branch
      (.branch
      (.branch
      ((by
        convert globalLeaf11Tree using 1
        all_goals norm_num))
      ((by
        convert globalLeaf12Tree using 1
        all_goals norm_num)))
      ((by
        convert globalLeaf13Tree using 1
        all_goals norm_num)))
      (.branch
      ((by
        convert globalLeaf14Tree using 1
        all_goals norm_num))
      ((by
        convert globalLeaf15Tree using 1
        all_goals norm_num))))
      (.branch
      (.branch
      ((by
        convert globalLeaf16Tree using 1
        all_goals norm_num))
      ((by
        convert globalLeaf17Tree using 1
        all_goals norm_num)))
      (.branch
      ((by
        convert globalLeaf18Tree using 1
        all_goals norm_num))
      ((by
        convert globalLeaf19Tree using 1
        all_goals norm_num))))))
      (.branch
      (.branch
      (.branch
      (.branch
      ((by
        convert globalLeaf20Tree using 1
        all_goals norm_num))
      (.branch
      ((by
        convert globalLeaf21Tree using 1
        all_goals norm_num))
      ((by
        convert globalLeaf22Tree using 1
        all_goals norm_num))))
      ((by
        convert globalLeaf23Tree using 1
        all_goals norm_num)))
      ((by
        convert globalLeaf24Tree using 1
        all_goals norm_num)))
      (.branch
      ((by
        convert globalLeaf25Tree using 1
        all_goals norm_num))
      ((by
        convert globalLeaf26Tree using 1
        all_goals norm_num))))

theorem rawNonnegative {y : ℝ} (hlo : (((-1 : ℚ)) : ℝ) ≤ y)
    (hhi : y ≤ (((1 : ℚ)) : ℝ)) :
    0 ≤ rationalPowerValue power y :=
  globalTree.nonneg hlo hhi

theorem dominationTree :
    NonnegativeTree (rationalPowerValue (subtractConstant power 1))
      (591961 / 800000 : ℚ) 1 := by
  exact dominationLeaf00Tree

theorem rawDominatesOne {y : ℝ} (hlo : (((591961 / 800000 : ℚ)) : ℝ) ≤ y)
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

theorem cosineDominatesOne {x : ℝ} (hx : (((591961 / 800000 : ℚ)) : ℝ) ≤ Real.cos x) :
    1 ≤ rationalCosineValue fourier x := by
  rw [← rationalPowerValue_cos_eq_rationalCosineValue fourierPowerCheck x]
  exact rawDominatesOne hx (by simpa using Real.cos_le_one x)

end CertifiedJL.TernaryLInfTwoDecimal.Cap47Central
