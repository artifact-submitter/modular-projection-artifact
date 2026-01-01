/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.SingletonPhaseFourierCover256Bits192

/-! # Bounded samples for the 256/9/192 singleton-Fourier replay -/

namespace CertifiedJL.SparseThresholdDominant.SingletonPhaseFourierCover256Bits192

open SingletonPhaseFourierNumeric256Bits192

example : certifiedCheck cell00 = true := by decide +kernel
example : certifiedCheck cell09 = true := by decide +kernel

end CertifiedJL.SparseThresholdDominant.SingletonPhaseFourierCover256Bits192
