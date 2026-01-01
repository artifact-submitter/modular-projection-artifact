import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Intermediate.PMF

open MeasureTheory

namespace CertifiedJL.Tests

open CertifiedJL

/-- The exact sparse-entry masses and their order are pinned literally. -/
theorem sparse_entry_mix_canary (f : ℤ → ℝ) :
    ∫ z, f z ∂sparseEntryPMF.toMeasure =
      (1 / 4 : ℝ) * f (-1) + (1 / 2 : ℝ) * f 0 + (1 / 4 : ℝ) * f 1 :=
  sparseEntry_integral_eq_mix f

/-- The arbitrary-coordinate product-measure transport is consumed directly. -/
theorem sparse_row_coordinate_split_canary {n : ℕ} (i : Fin (n + 1))
    (f : (Fin (n + 1) → ℤ) → ℝ)
    (hf : Integrable f (sparseRademacherRow (n + 1)).toMeasure) :
    ∫ row, f row ∂(sparseRademacherRow (n + 1)).toMeasure =
      ∫ z, ∫ rest,
        f ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℤ) i).symm
          (z, rest))
          ∂(sparseRademacherRow n).toMeasure
        ∂sparseEntryPMF.toMeasure :=
  sparseRademacherRow_integral_split_coordinate i f hf

/-- A natural consumer can expose its arbitrary selected dimension as a
successor before applying the exact coordinate split. -/
theorem sparse_row_dimension_adapter_canary {d : ℕ} (i : Fin d) :
    ∃ n : ℕ, d = n + 1 :=
  exists_dimension_eq_succ_of_fin i

/-- The dot-product split pins the selected coefficient and residual indexing. -/
theorem sparse_row_dot_split_canary {n : ℕ} (i : Fin (n + 1))
    (z : ℤ) (rest : Fin n → ℤ) (a : Fin (n + 1) → ℝ) :
    realRowDot
        ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℤ) i).symm
          (z, rest)) a =
      (z : ℝ) * a i + realRowDot rest (fun j ↦ a (i.succAbove j)) :=
  realRowDot_piFinSuccAbove_symm i z rest a

/-- The shifted-square bridge exposes inactive, minus, and plus images with
weights `1/2,1/4,1/4`. -/
theorem sparse_row_shifted_square_mix_canary {n : ℕ}
    (i : Fin (n + 1)) (a : Fin (n + 1) → ℝ) (alpha shift : ℝ) :
    ∫ row, Real.exp (-alpha * (realRowDot row a - shift) ^ 2)
        ∂(sparseRademacherRow (n + 1)).toMeasure =
      (1 / 4 : ℝ) *
          (∫ rest, Real.exp (-alpha *
            ((-1 : ℝ) * a i +
              realRowDot rest (fun j ↦ a (i.succAbove j)) - shift) ^ 2)
            ∂(sparseRademacherRow n).toMeasure) +
        (1 / 2 : ℝ) *
          (∫ rest, Real.exp (-alpha *
            (realRowDot rest (fun j ↦ a (i.succAbove j)) - shift) ^ 2)
            ∂(sparseRademacherRow n).toMeasure) +
        (1 / 4 : ℝ) *
          (∫ rest, Real.exp (-alpha *
            (a i + realRowDot rest (fun j ↦ a (i.succAbove j)) - shift) ^ 2)
            ∂(sparseRademacherRow n).toMeasure) :=
  sparseRow_shiftedSquare_integral_eq_mix_coordinate i a alpha shift

/-- The generalized MGF retains the exact residual squared mass. -/
theorem sparse_row_mgf_mass_canary {d : ℕ} (a : Fin d → ℝ) (t : ℝ) :
    ∫ row, Real.exp (t * realRowDot row a) ∂(sparseRademacherRow d).toMeasure ≤
      Real.exp ((∑ i, a i ^ 2) * t ^ 2 / 4) :=
  sparseRowMGF_subGaussian_mass a t

/-- The residual mass enters the shifted denominator with coefficient one. -/
theorem sparse_row_shifted_envelope_canary {n : ℕ} (a : Fin n → ℝ)
    (alpha shift : ℝ) (halpha : 0 < alpha) :
    ∫ row, Real.exp (-alpha * (realRowDot row a - shift) ^ 2)
        ∂(sparseRademacherRow n).toMeasure ≤
      Real.exp (-alpha * shift ^ 2 / (1 + alpha * ∑ i, a i ^ 2)) :=
  sparseRow_shiftedGaussianEnvelope a alpha shift halpha

/-- The composed one-image bridge pins the inactive coefficient and both
asymmetric shifted images after the residual mass is rewritten as `1-r`. -/
theorem sparse_row_intermediate_image_canary {n : ℕ} (i : Fin (n + 1))
    (a : Fin (n + 1) → ℝ) (r shift : ℝ)
    (hnorm : ∑ j, a j ^ 2 = 1) (hr : a i ^ 2 = r) :
    ∫ row, Real.exp (-(23 / 10 : ℝ) * (realRowDot row a - shift) ^ 2)
        ∂(sparseRademacherRow (n + 1)).toMeasure ≤
      (1 / 4 : ℝ) * Real.exp
          (-intermediateAlpha r * (shift + a i) ^ 2) +
        (1 / 2 : ℝ) * Real.exp
          (-intermediateAlpha r * shift ^ 2) +
        (1 / 4 : ℝ) * Real.exp
          (-intermediateAlpha r * (shift - a i) ^ 2) :=
  sparseRow_intermediate_image_le i a r shift hnorm hr

/-- Opposite images are consumed together so both signed shifts and the
coefficient-free `sqrt r` replacement are mutation-visible. -/
theorem sparse_row_intermediate_paired_images_canary {n : ℕ}
    (i : Fin (n + 1)) (a : Fin (n + 1) → ℝ) (r shift : ℝ)
    (hnorm : ∑ j, a j ^ 2 = 1) (hr : a i ^ 2 = r) :
    (∫ row, Real.exp (-(23 / 10 : ℝ) * (realRowDot row a - shift) ^ 2)
        ∂(sparseRademacherRow (n + 1)).toMeasure) +
      (∫ row, Real.exp (-(23 / 10 : ℝ) * (realRowDot row a + shift) ^ 2)
        ∂(sparseRademacherRow (n + 1)).toMeasure) ≤
      Real.exp (-intermediateAlpha r * shift ^ 2) +
        (1 / 2 : ℝ) * Real.exp
          (-intermediateAlpha r * (shift - Real.sqrt r) ^ 2) +
        (1 / 2 : ℝ) * Real.exp
          (-intermediateAlpha r * (shift + Real.sqrt r) ^ 2) :=
  sparseRow_intermediate_paired_images_le i a r shift hnorm hr

/-- The exact paired-image producer is directly usable at an arbitrary
positive dimension supplied by a natural branch hypothesis. -/
theorem sparse_row_intermediate_paired_images_of_fin_canary {d : ℕ}
    (i : Fin d) (a : Fin d → ℝ) (r shift : ℝ)
    (hnorm : ∑ j, a j ^ 2 = 1) (hr : a i ^ 2 = r) :
    (∫ row, Real.exp (-(23 / 10 : ℝ) * (realRowDot row a - shift) ^ 2)
        ∂(sparseRademacherRow d).toMeasure) +
      (∫ row, Real.exp (-(23 / 10 : ℝ) * (realRowDot row a + shift) ^ 2)
        ∂(sparseRademacherRow d).toMeasure) ≤
      Real.exp (-intermediateAlpha r * shift ^ 2) +
        (1 / 2 : ℝ) * Real.exp
          (-intermediateAlpha r * (shift - Real.sqrt r) ^ 2) +
        (1 / 2 : ℝ) * Real.exp
          (-intermediateAlpha r * (shift + Real.sqrt r) ^ 2) :=
  sparseRow_intermediate_paired_images_le_of_fin i a r shift hnorm hr

/-- The complete nonzero-image series is bounded by the literal L13
definition, not merely by independent pointwise estimates. -/
theorem sparse_row_intermediate_nonzero_images_L13_canary {d : ℕ}
    (i : Fin d) (a : Fin d → ℝ) (r D : ℝ)
    (hnorm : ∑ j, a j ^ 2 = 1) (hr : a i ^ 2 = r)
    (hr0 : 2 / 3 ≤ r) (hr1 : r ≤ 2000 / 2309) (hD : 3 ≤ D) :
    (∑' n : ℕ, ((∫ row, Real.exp (-(23 / 10 : ℝ) *
          (realRowDot row a - ((n : ℝ) + 1) * D) ^ 2)
          ∂(sparseRademacherRow d).toMeasure) +
        (∫ row, Real.exp (-(23 / 10 : ℝ) *
          (realRowDot row a + ((n : ℝ) + 1) * D) ^ 2)
          ∂(sparseRademacherRow d).toMeasure))) ≤
      intermediateL13 r D :=
  sparseRow_intermediate_nonzero_images_le_L13 i a r D
    hnorm hr hr0 hr1 hD

end CertifiedJL.Tests
