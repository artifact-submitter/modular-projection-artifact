/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Probability.NormalApproximation.Tyurin.SmallLyapunovAssembly

/-!
# Tyurin's all-the-way-to-zero Lyapunov estimate

This umbrella module exports the direct small-Lyapunov proof.  The analytic
core and Gaussian budget live in `TyurinSmallLyapunovCore`; the four outer
Fourier bands live in `TyurinSmallLyapunovOuter`; the final scalar theorem
lives in `TyurinSmallLyapunovAssembly`.
-/
