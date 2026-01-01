/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import Mathlib.Data.Rat.Defs

/-! # Raw exact data for the affine lower-tail endpoint family

This file contains only the rational endpoint inventory.  Executable checks,
their soundness proofs, and coverage proofs live in a separate module.
-/

namespace CertifiedJL.AffineEndpointNumeric

/-- One affine Euclidean endpoint and the finite singleton/diffuse choices used
to close it. -/
structure L2EndpointData where
  rows : ℕ
  squaredNormFloor : ℕ
  bits : ℕ
  singletonTilt : ℚ
  singletonCap : ℚ
  singletonRCap : ℚ
  singletonUCap : ℚ
  singletonVCap : ℚ
  diffuseTilt : ℚ
  diffuseCap : ℚ
  deriving DecidableEq, Repr

/-- One affine infinity endpoint and its selected diffuse-row estimate. -/
structure LInfEndpointData where
  rows : ℕ
  capNumerator : ℕ
  capDenominator : ℕ
  bits : ℕ
  diffuseTilt : ℚ
  diffuseCap : ℚ
  deriving DecidableEq, Repr

abbrev l2_192_11_128 : L2EndpointData :=
  ⟨192, 11, 128, 23 / 8, 265806766031 / 500000000000,
    5790 / 1000000000000000, 63219024661671 / 1000000000000000,
    8039449077 / 1000000000000000, 33 / 10, 97 / 200⟩
abbrev l2_256_27_128 : L2EndpointData :=
  ⟨256, 27, 128, 109 / 50, 140421353901 / 250000000000,
    3013994 / 1000000000000000, 123233789507952 / 1000000000000000,
    137035300150 / 1000000000000000, 33 / 10, 97 / 200⟩
abbrev l2_256_9_194 : L2EndpointData :=
  ⟨256, 9, 194, 17 / 5, 129773016307 / 250000000000,
    52 / 1000000000000000, 38183186661915 / 1000000000000000,
    943792033 / 1000000000000000, 33 / 10, 97 / 200⟩
abbrev l2_384_40_192 : L2EndpointData :=
  ⟨384, 40, 192, 11 / 5, 35031737657 / 62500000000,
    2517499 / 1000000000000000, 120889303405810 / 1000000000000000,
    126296277819 / 1000000000000000, 33 / 10, 97 / 200⟩
abbrev l2_512_73_193 : L2EndpointData :=
  ⟨512, 73, 193, 9 / 5, 147269709277 / 250000000000,
    92136009 / 1000000000000000, 177511479308014 / 1000000000000000,
    645994221028 / 1000000000000000, 5 / 2, 539 / 1000⟩
abbrev l2_512_54_256 : L2EndpointData :=
  ⟨512, 54, 256, 109 / 50, 140421353901 / 250000000000,
    3013994 / 1000000000000000, 123233789507952 / 1000000000000000,
    137035300150 / 1000000000000000, 33 / 10, 97 / 200⟩
abbrev l2_195_12_128 : L2EndpointData :=
  ⟨195, 12, 128, 14 / 5, 66746976167 / 125000000000,
    11371 / 1000000000000000, 67940700889620 / 1000000000000000,
    10917757128 / 1000000000000000, 33 / 10, 97 / 200⟩
abbrev l2_264_29_128 : L2EndpointData :=
  ⟨264, 29, 128, 107 / 50, 141027673453 / 250000000000,
    4320046 / 1000000000000000, 128060048008613 / 1000000000000000,
    161330419667 / 1000000000000000, 33 / 10, 97 / 200⟩
abbrev l2_394_43_192 : L2EndpointData :=
  ⟨394, 43, 192, 107 / 50, 141027673453 / 250000000000,
    4320046 / 1000000000000000, 128060048008613 / 1000000000000000,
    161330419667 / 1000000000000000, 33 / 10, 97 / 200⟩
abbrev l2_524_57_256 : L2EndpointData :=
  ⟨524, 57, 256, 43 / 20, 28174773369 / 50000000000,
    3948224 / 1000000000000000, 126836046371552 / 1000000000000000,
    154879989846 / 1000000000000000, 33 / 10, 97 / 200⟩

/-- The complete ten-endpoint affine Euclidean inventory. -/
def l2Endpoints : List L2EndpointData := [
  l2_192_11_128, l2_256_27_128, l2_256_9_194, l2_384_40_192,
  l2_512_73_193, l2_512_54_256, l2_195_12_128, l2_264_29_128,
  l2_394_43_192, l2_524_57_256]

abbrev lInf_192_279_1000_129 : LInfEndpointData := ⟨192, 279, 1000, 129, 33 / 10, 97 / 200⟩
abbrev lInf_256_6_25_197 : LInfEndpointData := ⟨256, 6, 25, 197, 33 / 10, 97 / 200⟩
abbrev lInf_256_331_1000_133 : LInfEndpointData := ⟨256, 331, 1000, 133, 33 / 10, 97 / 200⟩
abbrev lInf_384_331_1000_200 : LInfEndpointData := ⟨384, 331, 1000, 200, 33 / 10, 97 / 200⟩
abbrev lInf_512_331_1000_266 : LInfEndpointData := ⟨512, 331, 1000, 266, 33 / 10, 97 / 200⟩
abbrev lInf_512_46_125_206 : LInfEndpointData := ⟨512, 46, 125, 206, 5 / 2, 539 / 1000⟩
abbrev lInf_256_67_200_130 : LInfEndpointData := ⟨256, 67, 200, 130, 33 / 10, 97 / 200⟩
abbrev lInf_256_9_25_109 : LInfEndpointData := ⟨256, 9, 25, 109, 33 / 10, 97 / 200⟩
abbrev lInf_462_9_25_197 : LInfEndpointData := ⟨462, 9, 25, 197, 33 / 10, 97 / 200⟩

/-- The complete nine-endpoint affine infinity inventory at modulus margin
three. The two previously published endpoints remain present here so coverage
is checked against the full mathematical family. -/
def lInfEndpoints : List LInfEndpointData := [
  lInf_192_279_1000_129, lInf_256_6_25_197, lInf_256_331_1000_133,
  lInf_384_331_1000_200, lInf_512_331_1000_266, lInf_512_46_125_206,
  lInf_256_67_200_130, lInf_256_9_25_109, lInf_462_9_25_197]

end CertifiedJL.AffineEndpointNumeric
