/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows384Bits192Threshold509

/-! Kernel replay shard 0 for box 10.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_10_segment_00_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 10 default)
      ⟨0, 0, 25⟩ =
      ⟨0,
      551335716007336806245797765132812355511724015847374720069896771907745759453678157635284299559693750202710476676493967417561198679578666161441569035641549⟩ := by
  decide +kernel

theorem box_10_segment_00_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 10 default)
      ⟨0, 25, 25⟩ =
      ⟨0,
      1689793559930910169366082097467203509777666988938880319954046569471340400381803254608507222492094256492849570409256368415194069710060229094994215516794⟩ := by
  decide +kernel

theorem box_10_segment_00_chunk_002 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 10 default)
      ⟨0, 50, 25⟩ =
      ⟨0,
      4171802044439173563141273927374229362517666088031287456717897036837456647534588161581574533006258528332493136585516722571272851017552223233235716⟩ := by
  decide +kernel

theorem box_10_segment_00_chunk_003 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 10 default)
      ⟨0, 75, 25⟩ =
      ⟨0,
      63326480869712174466089549672693978092383625376422283639323723510986242897786780270167354983293312075996522217946768193072132289621735968⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509
