/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows256Bits152Threshold365

/-! Kernel replay shard 0 for box 3.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits152Threshold365

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_03_segment_00_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes).getD 3 default)
      ⟨0, 0, 25⟩ =
      ⟨0,
      768553831101811603276696016511868988369182621254936141646277699165562504966229832841047276997994992277145500636474821854799504411105797047368646271678638⟩ := by
  decide +kernel

theorem box_03_segment_00_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes).getD 3 default)
      ⟨0, 25, 25⟩ =
      ⟨0,
      272423711079805079819242552149349461939019558126213266995478789740432118250411947105348240791719843100469082158888870955352206724123261299142806527873⟩ := by
  decide +kernel

theorem box_03_segment_00_chunk_002 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes).getD 3 default)
      ⟨0, 50, 25⟩ =
      ⟨0,
      12334662490465143445528417659431777276481643664198715040607977232661568862722935885828555018979904522271880561685101770112729358939584093083487⟩ := by
  decide +kernel

theorem box_03_segment_00_chunk_003 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes).getD 3 default)
      ⟨0, 75, 25⟩ =
      ⟨0,
      10659948702915600265199682174915604762888140197535711653764072213445701267077629228623098720894273996830205341648102968985443589229048⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits152Threshold365
