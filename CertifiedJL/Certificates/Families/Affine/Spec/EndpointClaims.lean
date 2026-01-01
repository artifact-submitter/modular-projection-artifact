/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.Affine.Data.EndpointNumeric
import CertifiedJL.Projection.L2.Lower.BalancedTernary.L2General

/-! # Public propositions represented by affine endpoint data -/

namespace CertifiedJL.AffineEndpointNumeric

/-- Exact public proposition represented by one L2 endpoint record. -/
abbrev L2EndpointClaim (e : L2EndpointData) : Prop :=
  AffineL2ThresholdLowerTailAt
    { distribution := .balancedTernary, rows := e.rows,
      squaredNormFloor := NonnegativeRatio.ofNat e.squaredNormFloor,
      modulusMargin := NonnegativeRatio.ofNat 3 } (failureTarget e.bits)

/-- Convert the exact numerator and denominator in an endpoint record into the
public nonnegative-ratio coordinate cap. -/
def lInfCoordinateCap (e : LInfEndpointData) (hden : 0 < e.capDenominator) :
    NonnegativeRatio where
  numerator := e.capNumerator
  denominator := e.capDenominator
  denominator_pos := hden

/-- Exact public proposition represented by one L-infinity endpoint record. -/
abbrev LInfEndpointClaim (e : LInfEndpointData) (hden : 0 < e.capDenominator) : Prop :=
  AffineLInfThresholdLowerTailAt
    { distribution := .balancedTernary, rows := e.rows,
      coordinateCap := lInfCoordinateCap e hden,
      modulusMargin := NonnegativeRatio.ofNat 3 } (failureTarget e.bits)

end CertifiedJL.AffineEndpointNumeric
