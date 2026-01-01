import CertifiedJL.Certificates.Families.L2Upper.Rows512Bits192.Spec
import CertifiedJL.Certificates.Families.L2Upper.Rows512Bits192.Soundness.Final

open scoped BigOperators ENNReal
namespace CertifiedJL.SparseUpperContour.ShortTail

/-- The semantic contract allows shorter tails or a closed core without
changing the strict probability statement or any profile-box target. -/
theorem normalized607_of_contract
    (verified : CertificateContracts.SparseL2UpperContour512Bits192)
    {d : ℕ} (a : Fin d → ℝ) (hnorm : ∑ i, a i ^ 2 = 1) :
    eventProbability (sparseRademacherMatrix rows d)
      (fun J => (threshold : ℝ) < realProjectionSqNorm a J) <
      failureTarget securityBits := by
  by_cases hprofile : sparseProfileFourthMoment a ≤ 1 / 20
  · have hp0 : 0 ≤ sparseProfileFourthMoment a := by
      unfold sparseProfileFourthMoment
      positivity
    obtain ⟨box, hbox, hlo, hhi⟩ := exists_profileBox_mem_and_contains hp0 hprofile
    obtain ⟨_, _, _, hlamQ, hlamOneQ, hsigmaQ, _, htarget⟩ := profileBox_numeric_facts hbox
    have hlam : 0 < (box.lam : ℝ) := by exact_mod_cast hlamQ
    have hlamOne : (box.lam : ℝ) < 1 := by exact_mod_cast hlamOneQ
    have hsigma : 0 < (box.sigma : ℝ) := by exact_mod_cast hsigmaQ
    have hfourth : ∀ frequency : ℝ,
        Real.sqrt (1 - (box.lam : ℝ)) *
          ‖quadraticComplexMGF (fun row : Fin d → ℤ => realRowDot row a)
            (sparseRademacherRow d).toMeasure
            ((box.lam : ℝ) + frequency * Complex.I)‖ ≤
          sparseUpperFourthOrderNormalizedMajorant
            (sparseProfileFourthMoment a) (box.lam : ℝ) frequency := by
      intro frequency
      apply normalized_rowMGF_le_fourthOrderMajorant_of_error
      have hs0 : 0 ≤ ((((box.lam : ℝ) : ℂ) + (frequency : ℂ) * Complex.I).re) := by
        simpa using hlam.le
      have hs1 : ((((box.lam : ℝ) : ℂ) + (frequency : ℂ) * Complex.I).re) < 1 := by
        simpa using hlamOne
      simpa using sparseUpper_fourthOrder a hnorm hs0 hs1
    have hscaled := scaled_realProjectionSqNorm_toReal_le_actualBoxEndpoint
      a box hnorm hfourth hlam hlamOne hsigma
    have hendpoint := verified.1 box hbox (sparseProfileFourthMoment a) ⟨hlo, hhi⟩
    have hscaledOne : (2 ^ securityBits : ℝ) *
        (eventProbability (sparseRademacherMatrix rows d)
          (fun J => (threshold : ℝ) < realProjectionSqNorm a J)).toReal < 1 :=
      hscaled.trans_lt (hendpoint.trans (by exact_mod_cast htarget))
    apply eventProbability_lt_failureTarget_of_toReal_lt
    rw [inv_pow, inv_eq_one_div]
    apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ securityBits)).2
    simpa [mul_comm] using hscaledOne
  · exact sparseUpper_highProfile_of_verified d a hnorm (le_of_not_ge hprofile) verified.2

end CertifiedJL.SparseUpperContour.ShortTail
