/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.CappedFourierCover256Bits192

/-! # Bounded samples for the 256/9/192 capped-Fourier replay -/

namespace CertifiedJL.SparseThresholdDominant.CappedFourierCover256Bits192

open CappedFourierNumeric256Bits192

example : certifiedCheck cell00 = true := by decide +kernel
example : certifiedCheck cell19 = true := by decide +kernel

end CertifiedJL.SparseThresholdDominant.CappedFourierCover256Bits192
