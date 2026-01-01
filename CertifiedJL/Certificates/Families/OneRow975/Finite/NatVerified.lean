import CertifiedJL.Certificates.Families.OneRow975.Finite.NatLocalSoundness
import CertifiedJL.Certificates.Families.OneRow975.Finite.NatIntervalAll

namespace CertifiedJL
namespace SparseOneRowCertificate
namespace NatInterval

theorem natCellCheck_verified {index : ℕ} (hindex : index < gridSize) :
    natCellCheck index = true := by
  have hall : (List.range gridSize).all natCellCheck = true :=
    natCompleteCheck_verified
  have hmem : index ∈ List.range gridSize := List.mem_range.mpr hindex
  exact (List.all_eq_true.mp hall) index hmem

theorem natScalarEnvelope_lt_target
    {index : ℕ} {y : ℝ}
    (hcell :
      (cellLeftRat index : ℝ) ≤ y ∧
        y ≤ (cellRightRat index : ℝ))
    (hindex : index < gridSize) :
    scalarEnvelope y < (target : ℝ) := by
  have hcellEnv := natCellCheck_of_cellEnvelope hindex
    (natCellCheck_verified hindex)
  exact (scalarEnvelope_le_cellEnvelope hcell hindex).trans_lt hcellEnv

theorem natScalarEnvelope_lt_target_of_le_certifiedProfileUpper
    {y : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ (certifiedProfileUpper : ℝ)) :
    scalarEnvelope y < (target : ℝ) := by
  obtain ⟨index, hindex, hcell⟩ :=
    exists_certificate_cell_of_le_certifiedProfileUpper hy0 hy
  exact natScalarEnvelope_lt_target hcell hindex

end NatInterval
end SparseOneRowCertificate
end CertifiedJL
