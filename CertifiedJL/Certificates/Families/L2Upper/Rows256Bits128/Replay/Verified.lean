/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Replay.Verified.Box00
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Replay.Verified.Box01
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Replay.Verified.Box02
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Replay.Verified.Box03
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Replay.Verified.Box04
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Replay.Verified.Box05
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Replay.Verified.Box06
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Replay.Verified.Box07
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Replay.Verified.Box08
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Replay.Verified.Box09
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Replay.Verified.Box10
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Replay.Verified.Box11
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Replay.Verified.Box12
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Replay.Verified.Box13
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Replay.Verified.Box14
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Replay.Verified.Box15
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Replay.Verified.Box16
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Replay.Verified.Box17

/-! # Aggregated providers for all centered-hybrid certificate boxes -/

namespace CertifiedJL
namespace SparseUpperHybrid

/-- Every box in the manifest has a kernel-checked endpoint below one. -/
theorem certificate_upperRat_lt_one
    {certificate : CertificateBox} (hcertificate : certificate ∈ certificateBoxes) :
    (certificateBound certificate).upperRat < 1 := by
  simp only [certificateBoxes, List.mem_cons, List.not_mem_nil, or_false] at hcertificate
  rcases hcertificate with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [certificateBoxes, replayBox] using certificate_00_upperRat_lt
  · simpa [certificateBoxes, replayBox] using certificate_01_upperRat_lt
  · simpa [certificateBoxes, replayBox] using certificate_02_upperRat_lt
  · simpa [certificateBoxes, replayBox] using certificate_03_upperRat_lt
  · simpa [certificateBoxes, replayBox] using certificate_04_upperRat_lt
  · simpa [certificateBoxes, replayBox] using certificate_05_upperRat_lt
  · simpa [certificateBoxes, replayBox] using certificate_06_upperRat_lt
  · simpa [certificateBoxes, replayBox] using certificate_07_upperRat_lt
  · simpa [certificateBoxes, replayBox] using certificate_08_upperRat_lt
  · simpa [certificateBoxes, replayBox] using certificate_09_upperRat_lt
  · simpa [certificateBoxes, replayBox] using certificate_10_upperRat_lt
  · simpa [certificateBoxes, replayBox] using certificate_11_upperRat_lt
  · simpa [certificateBoxes, replayBox] using certificate_12_upperRat_lt
  · simpa [certificateBoxes, replayBox] using certificate_13_upperRat_lt
  · simpa [certificateBoxes, replayBox] using certificate_14_upperRat_lt
  · simpa [certificateBoxes, replayBox] using certificate_15_upperRat_lt
  · simpa [certificateBoxes, replayBox] using certificate_16_upperRat_lt
  · simpa [certificateBoxes, replayBox] using certificate_17_upperRat_lt

/-- Every cell in every manifest box satisfies the interval sign conditions
used by the semantic rectangle consumer. -/
theorem certificate_sideChecks
    {certificate : CertificateBox} (hcertificate : certificate ∈ certificateBoxes) :
    ∀ segment ∈ certificate.segments, ∀ i < segment.count,
      hybridCellSideCheck certificate.box segment i = true := by
  simp only [certificateBoxes, List.mem_cons, List.not_mem_nil, or_false] at hcertificate
  rcases hcertificate with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [certificateBoxes, replayBox] using certificate_00_sideChecks
  · simpa [certificateBoxes, replayBox] using certificate_01_sideChecks
  · simpa [certificateBoxes, replayBox] using certificate_02_sideChecks
  · simpa [certificateBoxes, replayBox] using certificate_03_sideChecks
  · simpa [certificateBoxes, replayBox] using certificate_04_sideChecks
  · simpa [certificateBoxes, replayBox] using certificate_05_sideChecks
  · simpa [certificateBoxes, replayBox] using certificate_06_sideChecks
  · simpa [certificateBoxes, replayBox] using certificate_07_sideChecks
  · simpa [certificateBoxes, replayBox] using certificate_08_sideChecks
  · simpa [certificateBoxes, replayBox] using certificate_09_sideChecks
  · simpa [certificateBoxes, replayBox] using certificate_10_sideChecks
  · simpa [certificateBoxes, replayBox] using certificate_11_sideChecks
  · simpa [certificateBoxes, replayBox] using certificate_12_sideChecks
  · simpa [certificateBoxes, replayBox] using certificate_13_sideChecks
  · simpa [certificateBoxes, replayBox] using certificate_14_sideChecks
  · simpa [certificateBoxes, replayBox] using certificate_15_sideChecks
  · simpa [certificateBoxes, replayBox] using certificate_16_sideChecks
  · simpa [certificateBoxes, replayBox] using certificate_17_sideChecks

/-- The reflected finite-plus-tail interval starts exactly at zero for every
manifest box.  This supplies the lower endpoint needed to package the
analytic integral as an interval containment, without recomputing cells. -/
theorem certificate_finiteTail_lo_eq_zero
    {certificate : CertificateBox} (hcertificate : certificate ∈ certificateBoxes) :
    (finiteIntegralFrom
      ((certificateChunkPlan certificate).map
        (certificateChunkValue certificate)) + tail certificate.box).lo = 0 := by
  simp only [certificateBoxes, List.mem_cons, List.not_mem_nil, or_false] at hcertificate
  rcases hcertificate with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [certificateBoxes, replayBox] using certificate_00_finiteTail_lo_eq_zero
  · simpa [certificateBoxes, replayBox] using certificate_01_finiteTail_lo_eq_zero
  · simpa [certificateBoxes, replayBox] using certificate_02_finiteTail_lo_eq_zero
  · simpa [certificateBoxes, replayBox] using certificate_03_finiteTail_lo_eq_zero
  · simpa [certificateBoxes, replayBox] using certificate_04_finiteTail_lo_eq_zero
  · simpa [certificateBoxes, replayBox] using certificate_05_finiteTail_lo_eq_zero
  · simpa [certificateBoxes, replayBox] using certificate_06_finiteTail_lo_eq_zero
  · simpa [certificateBoxes, replayBox] using certificate_07_finiteTail_lo_eq_zero
  · simpa [certificateBoxes, replayBox] using certificate_08_finiteTail_lo_eq_zero
  · simpa [certificateBoxes, replayBox] using certificate_09_finiteTail_lo_eq_zero
  · simpa [certificateBoxes, replayBox] using certificate_10_finiteTail_lo_eq_zero
  · simpa [certificateBoxes, replayBox] using certificate_11_finiteTail_lo_eq_zero
  · simpa [certificateBoxes, replayBox] using certificate_12_finiteTail_lo_eq_zero
  · simpa [certificateBoxes, replayBox] using certificate_13_finiteTail_lo_eq_zero
  · simpa [certificateBoxes, replayBox] using certificate_14_finiteTail_lo_eq_zero
  · simpa [certificateBoxes, replayBox] using certificate_15_finiteTail_lo_eq_zero
  · simpa [certificateBoxes, replayBox] using certificate_16_finiteTail_lo_eq_zero
  · simpa [certificateBoxes, replayBox] using certificate_17_finiteTail_lo_eq_zero

/-- Every reflected finite-plus-tail interval is valid. -/
theorem certificate_finiteTail_valid
    {certificate : CertificateBox} (hcertificate : certificate ∈ certificateBoxes) :
    (finiteIntegralFrom
      ((certificateChunkPlan certificate).map
        (certificateChunkValue certificate)) + tail certificate.box).Valid := by
  simp only [certificateBoxes, List.mem_cons, List.not_mem_nil, or_false] at hcertificate
  rcases hcertificate with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [certificateBoxes, replayBox] using certificate_00_finiteTail_valid
  · simpa [certificateBoxes, replayBox] using certificate_01_finiteTail_valid
  · simpa [certificateBoxes, replayBox] using certificate_02_finiteTail_valid
  · simpa [certificateBoxes, replayBox] using certificate_03_finiteTail_valid
  · simpa [certificateBoxes, replayBox] using certificate_04_finiteTail_valid
  · simpa [certificateBoxes, replayBox] using certificate_05_finiteTail_valid
  · simpa [certificateBoxes, replayBox] using certificate_06_finiteTail_valid
  · simpa [certificateBoxes, replayBox] using certificate_07_finiteTail_valid
  · simpa [certificateBoxes, replayBox] using certificate_08_finiteTail_valid
  · simpa [certificateBoxes, replayBox] using certificate_09_finiteTail_valid
  · simpa [certificateBoxes, replayBox] using certificate_10_finiteTail_valid
  · simpa [certificateBoxes, replayBox] using certificate_11_finiteTail_valid
  · simpa [certificateBoxes, replayBox] using certificate_12_finiteTail_valid
  · simpa [certificateBoxes, replayBox] using certificate_13_finiteTail_valid
  · simpa [certificateBoxes, replayBox] using certificate_14_finiteTail_valid
  · simpa [certificateBoxes, replayBox] using certificate_15_finiteTail_valid
  · simpa [certificateBoxes, replayBox] using certificate_16_finiteTail_valid
  · simpa [certificateBoxes, replayBox] using certificate_17_finiteTail_valid

end SparseUpperHybrid
end CertifiedJL
