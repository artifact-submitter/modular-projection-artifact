/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256RescaledFrontier

/-! # Kernel-verified provider for the rescaled 256-row frontier -/

namespace CertifiedJL.CertificateProviders

open SparseUpperContourFamily.Instances.Rows256RescaledFrontier
open Certificates.Families.L2Upper.ContourFamily.Replay.Rows256RescaledFrontier

theorem sparseL2UpperContourRows256RescaledFrontier_verified :
    CertificateContracts.SparseL2UpperContourRows256RescaledFrontier := by
  intro endpoint hendpoint
  simp only [certifiedEndpoints, List.mem_cons, List.not_mem_nil, or_false] at hendpoint
  rcases hendpoint with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact endpointCheck_sound bits140Threshold5623Over16_check
  · exact endpointCheck_sound bits141Threshold5641Over16_check
  · exact endpointCheck_sound bits142Threshold5659Over16_check
  · exact endpointCheck_sound bits143Threshold5677Over16_check
  · exact endpointCheck_sound bits144Threshold2847Over8_check
  · exact endpointCheck_sound bits145Threshold357_check
  · exact endpointCheck_sound bits146Threshold2865Over8_check
  · exact endpointCheck_sound bits147Threshold1437Over4_check
  · exact endpointCheck_sound bits148Threshold5765Over16_check
  · exact endpointCheck_sound bits149Threshold5783Over16_check
  · exact endpointCheck_sound bits150Threshold5801Over16_check
  · exact endpointCheck_sound bits151Threshold2909Over8_check
  · exact endpointCheck_sound bits152Threshold1459Over4_check

end CertifiedJL.CertificateProviders
