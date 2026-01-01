import CertifiedJL.Certificates.Families.OneRow975.Finite.NatIntervalCore

namespace CertifiedJL.SparseOneRowCertificate

def natCompleteCheck : Bool :=
  (List.range gridSize).all natCellCheck

theorem natCompleteCheck_verified : natCompleteCheck = true := by
  decide +kernel

end CertifiedJL.SparseOneRowCertificate
