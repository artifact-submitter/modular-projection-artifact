import CertifiedJL.Certificates.Families.OneRow975.Finite.NatIntervalSoundness
import CertifiedJL.Certificates.Families.OneRow975.Finite.LocalSoundness

namespace CertifiedJL
namespace SparseOneRowCertificate
namespace NatInterval

variable {p k : ℕ}

theorem ofRat_pos_of_half {q : ℚ}
    (hscale : (2 : ℚ) ≤ (NatInterval.scale p : ℚ))
    (hq : (1 / 2 : ℚ) ≤ q) :
    0 < (ofRat p q).lo := by
  change 0 < Int.toNat (Dyadic.roundDown p q)
  have hmul : (1 : ℚ) ≤ q * (Dyadic.scale p : ℚ) := by
    calc
      (1 : ℚ) = (1 / 2 : ℚ) * 2 := by norm_num
      _ ≤ (1 / 2 : ℚ) * (Dyadic.scale p : ℚ) :=
        mul_le_mul_of_nonneg_left hscale (by norm_num)
      _ ≤ q * (Dyadic.scale p : ℚ) :=
        mul_le_mul_of_nonneg_right hq (by positivity)
  have hround : 0 < Dyadic.roundDown p q :=
    Dyadic.roundDown_pos hmul
  have hcast : ((Int.toNat (Dyadic.roundDown p q) : ℤ)) =
      Dyadic.roundDown p q :=
    Int.toNat_of_nonneg hround.le
  have hnat : (0 : ℤ) < (Int.toNat (Dyadic.roundDown p q) : ℤ) := by
    rw [hcast]
    exact hround
  exact_mod_cast hnat

theorem coshUpper_contains {q : ℚ}
    (hq0 : 0 ≤ q)
    (hupper : q < (2 ^ k : ℕ))
    (hbase : 0 < (ofRat p (1 - q / (2 ^ k : ℕ))).lo) :
    Contains (NatInterval.coshUpper p q k) (Real.cosh q) := by
  have hpos := contains_expPosUpper (p := p) k hq0
    hupper hbase
  have hneg := contains_expNegUpper (p := p) k hq0
  have hsum := contains_add hpos hneg
  have hhalf := contains_ofRat (p := p) (x := (1 / 2 : ℚ)) (by norm_num)
  have hmul := contains_mul hsum hhalf
  rw [Real.cosh_eq]
  simpa [NatInterval.coshUpper, div_eq_mul_inv] using hmul

theorem natCellUpper_contains_cellEnvelope
    {index : ℕ} (hindex : index < gridSize) :
    Contains (SparseOneRowCertificate.natCellUpper index)
      (SparseOneRowCertificate.cellEnvelope index) := by
  let left : ℚ := cellLeftRat index
  let right : ℚ := cellRightRat index
  have hleft := cellLeftRat_le_rightRat index
  have hright := cellRightRat_mem_unit hindex
  have hleft0 : (0 : ℚ) ≤ left := by simpa [left] using hleft.1
  have hright0 : (0 : ℚ) ≤ right := by simpa [right] using hright.1
  have hrightSquare : (0 : ℚ) ≤ right * right :=
    mul_nonneg hright0 hright0
  have hlinearLe : xUpper * right ≤ xUpper := by
    nlinarith [xUpper_nonneg]
  have hquadraticLe : xUpper * (right * right) ≤ xUpper := by
    have hsquareLe : right * right ≤ 1 := by nlinarith [hright.2]
    nlinarith [xUpper_nonneg]
  have hscale : (2 : ℚ) ≤ (NatInterval.scale precision : ℚ) := by
    norm_num [NatInterval.scale, precision]
  have hbaseLinear :
      0 < (ofRat precision
        (1 - xUpper * right / (2 ^ squarings : ℕ))).lo := by
    apply ofRat_pos_of_half hscale
    have hhalf : (1 / 2 : ℚ) ≤
        1 - xUpper * right / (2 ^ squarings : ℕ) := by
      have hq' : xUpper * right ≤ (2 ^ squarings : ℕ) / 2 := by
        exact hlinearLe.trans (by norm_num [xUpper, squarings])
      have hdenom : (0 : ℚ) < (2 ^ squarings : ℕ) := by positivity
      have hquot : xUpper * right / (2 ^ squarings : ℕ) ≤ (1 / 2 : ℚ) := by
        rw [div_le_iff₀ hdenom]
        nlinarith
      linarith
    exact hhalf
  have hbaseQuadratic :
      0 < (ofRat precision
        (1 - xUpper * (right * right) / (2 ^ squarings : ℕ))).lo := by
    apply ofRat_pos_of_half hscale
    have hhalf : (1 / 2 : ℚ) ≤
        1 - xUpper * (right * right) / (2 ^ squarings : ℕ) := by
      have hq' : xUpper * (right * right) ≤ (2 ^ squarings : ℕ) / 2 := by
        exact hquadraticLe.trans (by norm_num [xUpper, squarings])
      have hdenom : (0 : ℚ) < (2 ^ squarings : ℕ) := by positivity
      have hquot : xUpper * (right * right) /
          (2 ^ squarings : ℕ) ≤ (1 / 2 : ℚ) := by
        rw [div_le_iff₀ hdenom]
        nlinarith
      linarith
    exact hhalf
  have hexp :
      Contains (expNegUpper precision
        (exponentRate * (1 + left * left)) squarings)
        (Real.exp (-(exponentRate * (1 + left * left) : ℚ))) := by
    apply contains_expNegUpper
    exact mul_nonneg exponentRate_nonneg
      (by nlinarith [hleft0])
  have hcoshLinear := coshUpper_contains
    (p := precision) (k := squarings)
    (q := xUpper * right)
    (mul_nonneg xUpper_nonneg hright0)
    (hlinearLe.trans_lt (by norm_num [xUpper, squarings])) hbaseLinear
  have hcoshQuadratic := coshUpper_contains
    (p := precision) (k := squarings)
    (q := xUpper * (right * right))
    (mul_nonneg xUpper_nonneg hrightSquare)
    (hquadraticLe.trans_lt (by norm_num [xUpper, squarings])) hbaseQuadratic
  have hgaussian :
      Contains (ofRat precision gaussianCoefficientUpper)
        (gaussianCoefficientUpper : ℝ) :=
    contains_ofRat (p := precision) (x := gaussianCoefficientUpper)
      gaussianCoefficientUpper_nonneg
  have hberry :
      Contains (ofRat precision berryEsseenFactor)
        (berryEsseenFactor : ℝ) :=
    contains_ofRat (p := precision) (x := berryEsseenFactor)
      berryEsseenFactor_nonneg
  have hrightSquareInterval :
      Contains (ofRat precision (right * right)) ((right * right : ℚ) : ℝ) :=
    contains_ofRat (p := precision) (x := right * right) hrightSquare
  have hcoshCube :
      Contains
        (coshUpper precision (xUpper * (right * right)) squarings *
          coshUpper precision (xUpper * (right * right)) squarings *
          coshUpper precision (xUpper * (right * right)) squarings)
        (Real.cosh (xUpper * (right * right) : ℚ) ^ 3) := by
    have hmul := contains_mul
      (contains_mul hcoshQuadratic hcoshQuadratic) hcoshQuadratic
    simpa [pow_succ] using hmul
  have hbracket :
      Contains
        (ofRat precision gaussianCoefficientUpper *
            coshUpper precision (xUpper * (right * right)) squarings +
          ofRat precision berryEsseenFactor *
            ofRat precision (right * right) *
            (coshUpper precision (xUpper * (right * right)) squarings *
              coshUpper precision (xUpper * (right * right)) squarings *
              coshUpper precision (xUpper * (right * right)) squarings))
        ((gaussianCoefficientUpper : ℝ) *
            Real.cosh (xUpper * (right * right) : ℚ) +
          (berryEsseenFactor : ℝ) * (right * right : ℚ) *
            Real.cosh (xUpper * (right * right) : ℚ) ^ 3) := by
    exact contains_add
      (contains_mul hgaussian hcoshQuadratic)
      (contains_mul (contains_mul hberry hrightSquareInterval) hcoshCube)
  have htotal :=
    contains_mul (contains_mul hexp hcoshLinear) hbracket
  simpa [SparseOneRowCertificate.natCellUpper,
    SparseOneRowCertificate.cellEnvelope, left, right,
    pow_two, mul_pow, neg_mul, Rat.cast_mul, Rat.cast_add,
    Rat.cast_one, Rat.cast_neg] using htotal

theorem natCellCheck_of_cellEnvelope
    {index : ℕ} (hindex : index < gridSize)
    (hcheck : SparseOneRowCertificate.natCellCheck index = true) :
    SparseOneRowCertificate.cellEnvelope index < (target : ℝ) := by
  have hcontains := natCellUpper_contains_cellEnvelope hindex
  have hupper :
      ((SparseOneRowCertificate.natCellUpper index).hi : ℚ) /
          NatInterval.scale precision < target := by
    simpa [SparseOneRowCertificate.natCellCheck,
      SparseOneRowCertificate.NatInterval.upperLTCheck] using hcheck
  have hupperR :
      Dyadic.toReal precision
          ((SparseOneRowCertificate.natCellUpper index).hi : ℤ) <
        (target : ℝ) := by
    change ((SparseOneRowCertificate.natCellUpper index).hi : ℝ) /
        NatInterval.scale precision < (target : ℝ)
    have hupper' :
        ((((SparseOneRowCertificate.natCellUpper index).hi : ℚ) /
            NatInterval.scale precision : ℚ) : ℝ) < (target : ℝ) := by
      exact_mod_cast hupper
    simpa [Rat.cast_div] using hupper'
  exact hcontains.2.trans_lt hupperR

end NatInterval
end SparseOneRowCertificate
end CertifiedJL
