/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Analysis.SmoothBounds.JensenSquare
import CertifiedJL.Analysis.Peano.PeanoIdentity
import CertifiedJL.Analysis.Peano.PeanoMoments
import CertifiedJL.Analysis.Peano.PeanoCutoff
import CertifiedJL.Analysis.Peano.PeanoCutoffSecond
import CertifiedJL.Analysis.Peano.PeanoCutoffProduct
import CertifiedJL.Analysis.Peano.PeanoQuadraticExpSecond
import CertifiedJL.Analysis.Peano.PeanoCutoffConcrete
import CertifiedJL.Analysis.Peano.PeanoGaussianRademacher
import CertifiedJL.Analysis.Peano.PeanoCutoffKernelData
import CertifiedJL.Analysis.SmoothBounds.QuadraticExponential.QuadraticExp
import CertifiedJL.Analysis.SmoothBounds.QuadraticExponential.QuadraticExpDerivative
import CertifiedJL.Analysis.SmoothBounds.QuadraticExponential.QuadraticExpHigherDerivative
import CertifiedJL.Analysis.SmoothBounds.QuadraticExponential.QuadraticExpDerivativeMajorant
import CertifiedJL.Analysis.SmoothBounds.QuadraticExponential.QuadraticExpMomentMajorant
import CertifiedJL.Analysis.SmoothBounds.QuadraticExponential.QuadraticExpGaussianHalfMoment
import CertifiedJL.Analysis.SmoothBounds.QuadraticExponential.QuadraticExpMomentComparison
import CertifiedJL.Analysis.SmoothBounds.QuadraticExponential.QuadraticExpIntegrability
import CertifiedJL.Analysis.SmoothBounds.ScaledSmoothCutoff

/-!
# Jensen and Peano interfaces for the Gaussian-replacement proof

The first analytic U1 bridges are isolated from the distribution-specific
replacement argument.  If a function of a squared variable is convex, Jensen
turns the exact second-moment normalization into an expectation bound.  The
generic compact-support Peano identity fixes the positive-part orientation;
the later cutoff theorem supplies the moment-matched noncompact consumer.
-/

namespace CertifiedJL

end CertifiedJL
