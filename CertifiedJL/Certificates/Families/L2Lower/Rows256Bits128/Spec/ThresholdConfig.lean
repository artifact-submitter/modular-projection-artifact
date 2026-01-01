/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Statements.L2.Lower

/-!
# Configuration for threshold-relative sparse lower tails

This module packages only target-dependent matrix parameters and the two
budgets used by the low/high activity split. Dimensionless one-row geometry
remains independent of this configuration.
-/

namespace CertifiedJL

/-- Target-dependent data for a threshold-relative sparse lower-tail proof. -/
structure ThresholdTailConfig where
  rows : ℕ
  squaredNormFloor : ℕ
  bits : ℕ
  lowBudget : ENNReal
  highBudget : ENNReal

namespace ThresholdTailConfig

/-- Public theorem parameters determined by a target configuration. -/
def parameters (config : ThresholdTailConfig)
    (modulusMargin : NonnegativeRatio) : L2ThresholdLowerParameters where
  distribution := .balancedTernary
  rows := config.rows
  squaredNormFloor := NonnegativeRatio.ofNat config.squaredNormFloor
  modulusMargin := modulusMargin

/-- The target failure probability determined by a configuration. -/
noncomputable def target (config : ThresholdTailConfig) : ENNReal :=
  failureTarget config.bits

/-- The low/high split fits inside the advertised target. -/
def BudgetsValid (config : ThresholdTailConfig) : Prop :=
  config.lowBudget + config.highBudget ≤ config.target

end ThresholdTailConfig

end CertifiedJL
