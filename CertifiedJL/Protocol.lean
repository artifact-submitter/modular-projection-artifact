/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Protocol.Acceptance
import CertifiedJL.Protocol.AffineFreshMatrix

/-!
# Protocol-facing composition adapters

This opt-in umbrella exposes the existing affine fresh-matrix soundness
adapters. `Protocol.Acceptance` connects closed real acceptance radii to the
strict integer events used by the public tail bounds. `Protocol.AffineFreshMatrix`
composes those pointwise bounds with an explicitly factored prior-history then
fresh-matrix experiment. This umbrella does not define a prover, verifier,
transcript semantics, or a complete interactive protocol.
-/
