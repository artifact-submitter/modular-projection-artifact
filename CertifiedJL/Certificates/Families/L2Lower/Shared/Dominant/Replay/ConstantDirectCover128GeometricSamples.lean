/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Soundness.ConstantNumeric

/-!
# Bounded samples for the direct-cover geometric-tail checker

These are the first two cells of the 128-bit constant direct cover, repeated
here so this bounded sample imports only the shared checker and soundness
kernel.  The public budget and every cell/certificate constant are unchanged.
-/

namespace CertifiedJL.SparseThresholdDominant.ConstantDirectCover128GeometricSamples

open ConstantNumeric

def budget : ℚ := 187 / (200 * 2 ^ 128)

def cell0 : Cell where
  lower := 5 / 256
  upper := 11 / 512
  thresholdUpper := 156875 / 153664
  modulusLower := 121 / 40
  z := 51 / 20

def certificate0 : Certificate where
  inactiveUpper := 24409 / 25000
  activeUpper := 22067 / 250000
  growthUpper := 618733454942712423755006649303040

/-- Cell 0 needs three exactly truncated terms before the geometric tail. -/
def tail0 : GeometricTailCertificate where
  prefixTerms := 3
  ratioUpper :=
    (256 - (29 + 3)) * certificate0.activeUpper /
      ((29 + 3 + 1) * certificate0.inactiveUpper)

def entry0 : Entry := ⟨cell0, certificate0⟩

theorem entry0_valid : cell0.Valid ∧ certificate0.Valid := by
  exact entryValidCheck_sound (entry := entry0) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem cell0_geometric_check :
    localCertifiedGeometricCheckAt cell0 certificate0 tail0 budget = true := by
  decide +kernel

/-- Same semantic proposition and same `187/(200*2^128)` budget as the
complete-sum production checker. -/
theorem cell0_bound :
    thresholdDominantCellMajorant cell0.decode < (budget : ℝ) :=
  localCertifiedGeometricCheckAt_sound cell0 certificate0 tail0 budget
    entry0_valid.1 entry0_valid.2 cell0_geometric_check

def cell1 : Cell where
  lower := 3 / 512
  upper := 1 / 128
  thresholdUpper := 309375 / 307328
  modulusLower := 1503 / 500
  z := 7 / 2

def certificate1 : Certificate where
  inactiveUpper := 198047 / 200000
  activeUpper := 33113 / 1000000
  growthUpper := 239231331664563921414970742190928920771035136

/-- Cell 1 has one saturated conditional term, then a geometric tail. -/
def tail1 : GeometricTailCertificate where
  prefixTerms := 1
  ratioUpper :=
    (256 - (29 + 1)) * certificate1.activeUpper /
      ((29 + 1 + 1) * certificate1.inactiveUpper)

def entry1 : Entry := ⟨cell1, certificate1⟩

theorem entry1_valid : cell1.Valid ∧ certificate1.Valid := by
  exact entryValidCheck_sound (entry := entry1) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem cell1_geometric_check :
    localCertifiedGeometricCheckAt cell1 certificate1 tail1 budget = true := by
  decide +kernel

/-- Same semantic proposition and unchanged public budget for cell 1. -/
theorem cell1_bound :
    thresholdDominantCellMajorant cell1.decode < (budget : ℝ) :=
  localCertifiedGeometricCheckAt_sound cell1 certificate1 tail1 budget
    entry1_valid.1 entry1_valid.2 cell1_geometric_check

end CertifiedJL.SparseThresholdDominant.ConstantDirectCover128GeometricSamples
