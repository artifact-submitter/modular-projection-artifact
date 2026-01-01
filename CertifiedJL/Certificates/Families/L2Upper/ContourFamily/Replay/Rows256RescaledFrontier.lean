/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits152Threshold365.Verified
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256RescaledFrontier.EndpointArithmetic

/-! # Arithmetic-only replay of rescaled 256-row contour endpoints

The 1800 quadrature cells are imported from the fully replayed 152-bit
certificate.  The proofs below reduce definitionally to those same cells and
replay only the endpoint-dependent security prefactor and final comparison.
-/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256RescaledFrontier

open CertifiedJL.SparseUpperContourFamily
open CertifiedJL.SparseUpperContourFamily.Instances.Rows256RescaledFrontier

set_option linter.style.longLine false

private theorem box00ComputedChunks_eq_anchor (endpoint : Endpoint) :
    boxComputedChunks (parameters endpoint) (profileBoxes.getD 0 default) =
      Data.Rows256Bits152Threshold365.Box00.chunks := by
  change boxComputedChunks
      CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters
      (CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes.getD 0 default) = _
  exact Rows256Bits152Threshold365.Verified.box00ComputedChunks_eq_generated

private theorem box01ComputedChunks_eq_anchor (endpoint : Endpoint) :
    boxComputedChunks (parameters endpoint) (profileBoxes.getD 1 default) =
      Data.Rows256Bits152Threshold365.Box01.chunks := by
  change boxComputedChunks
      CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters
      (CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes.getD 1 default) = _
  exact Rows256Bits152Threshold365.Verified.box01ComputedChunks_eq_generated

private theorem box02ComputedChunks_eq_anchor (endpoint : Endpoint) :
    boxComputedChunks (parameters endpoint) (profileBoxes.getD 2 default) =
      Data.Rows256Bits152Threshold365.Box02.chunks := by
  change boxComputedChunks
      CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters
      (CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes.getD 2 default) = _
  exact Rows256Bits152Threshold365.Verified.box02ComputedChunks_eq_generated

private theorem box03ComputedChunks_eq_anchor (endpoint : Endpoint) :
    boxComputedChunks (parameters endpoint) (profileBoxes.getD 3 default) =
      Data.Rows256Bits152Threshold365.Box03.chunks := by
  change boxComputedChunks
      CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters
      (CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes.getD 3 default) = _
  exact Rows256Bits152Threshold365.Verified.box03ComputedChunks_eq_generated

private theorem box04ComputedChunks_eq_anchor (endpoint : Endpoint) :
    boxComputedChunks (parameters endpoint) (profileBoxes.getD 4 default) =
      Data.Rows256Bits152Threshold365.Box04.chunks := by
  change boxComputedChunks
      CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters
      (CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes.getD 4 default) = _
  exact Rows256Bits152Threshold365.Verified.box04ComputedChunks_eq_generated

private theorem box05ComputedChunks_eq_anchor (endpoint : Endpoint) :
    boxComputedChunks (parameters endpoint) (profileBoxes.getD 5 default) =
      Data.Rows256Bits152Threshold365.Box05.chunks := by
  change boxComputedChunks
      CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters
      (CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes.getD 5 default) = _
  exact Rows256Bits152Threshold365.Verified.box05ComputedChunks_eq_generated

private theorem box06ComputedChunks_eq_anchor (endpoint : Endpoint) :
    boxComputedChunks (parameters endpoint) (profileBoxes.getD 6 default) =
      Data.Rows256Bits152Threshold365.Box06.chunks := by
  change boxComputedChunks
      CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters
      (CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes.getD 6 default) = _
  exact Rows256Bits152Threshold365.Verified.box06ComputedChunks_eq_generated

private theorem box07ComputedChunks_eq_anchor (endpoint : Endpoint) :
    boxComputedChunks (parameters endpoint) (profileBoxes.getD 7 default) =
      Data.Rows256Bits152Threshold365.Box07.chunks := by
  change boxComputedChunks
      CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters
      (CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes.getD 7 default) = _
  exact Rows256Bits152Threshold365.Verified.box07ComputedChunks_eq_generated

private theorem box08ComputedChunks_eq_anchor (endpoint : Endpoint) :
    boxComputedChunks (parameters endpoint) (profileBoxes.getD 8 default) =
      Data.Rows256Bits152Threshold365.Box08.chunks := by
  change boxComputedChunks
      CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters
      (CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes.getD 8 default) = _
  exact Rows256Bits152Threshold365.Verified.box08ComputedChunks_eq_generated

private theorem box09ComputedChunks_eq_anchor (endpoint : Endpoint) :
    boxComputedChunks (parameters endpoint) (profileBoxes.getD 9 default) =
      Data.Rows256Bits152Threshold365.Box09.chunks := by
  change boxComputedChunks
      CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters
      (CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes.getD 9 default) = _
  exact Rows256Bits152Threshold365.Verified.box09ComputedChunks_eq_generated

/-- A successful arithmetic-only replay supplies both semantic endpoint checks. -/
theorem endpointCheck_sound {endpoint : Endpoint}
    (hcheck : endpointCheck endpoint = true) :
    allBoxesCheck (parameters endpoint) profileBoxes = true ∧
      highProfileCheck (parameters endpoint) highProfile = true := by
  simp only [endpointCheck, reducedBox00Check, reducedBox01Check,
    reducedBox02Check, reducedBox03Check, reducedBox04Check,
    reducedBox05Check, reducedBox06Check, reducedBox07Check,
    reducedBox08Check, reducedBox09Check, List.all_cons, List.all_nil,
    id_eq, Bool.and_eq_true] at hcheck
  rcases hcheck with
    ⟨h00, h01, h02, h03, h04, h05, h06, h07, h08, h09, hhigh, _⟩
  constructor
  · change [
      boxCheck (parameters endpoint) (profileBoxes.getD 0 default),
      boxCheck (parameters endpoint) (profileBoxes.getD 1 default),
      boxCheck (parameters endpoint) (profileBoxes.getD 2 default),
      boxCheck (parameters endpoint) (profileBoxes.getD 3 default),
      boxCheck (parameters endpoint) (profileBoxes.getD 4 default),
      boxCheck (parameters endpoint) (profileBoxes.getD 5 default),
      boxCheck (parameters endpoint) (profileBoxes.getD 6 default),
      boxCheck (parameters endpoint) (profileBoxes.getD 7 default),
      boxCheck (parameters endpoint) (profileBoxes.getD 8 default),
      boxCheck (parameters endpoint) (profileBoxes.getD 9 default)
    ].all id = true
    simp only [boxCheck, boxBound, boxIntegral,
      box00ComputedChunks_eq_anchor, box01ComputedChunks_eq_anchor,
      box02ComputedChunks_eq_anchor, box03ComputedChunks_eq_anchor,
      box04ComputedChunks_eq_anchor, box05ComputedChunks_eq_anchor,
      box06ComputedChunks_eq_anchor, box07ComputedChunks_eq_anchor,
      box08ComputedChunks_eq_anchor, box09ComputedChunks_eq_anchor,
      h00, h01, h02, h03, h04, h05, h06, h07, h08, h09,
      List.all_cons, List.all_nil, id_eq]
    rfl
  · exact hhigh

end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256RescaledFrontier
