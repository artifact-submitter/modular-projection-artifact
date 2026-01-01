/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Soundness.SingletonPhaseFourierNumeric256Bits192

/-! # Phase-retaining singleton modulus cover for the 256-row, 192-bit endpoint -/

namespace CertifiedJL
namespace SparseThresholdDominant
namespace SingletonPhaseFourierCover256Bits192

open SingletonPhaseFourierNumeric256Bits192

def cell00 : Cell :=
  { lower := 40/20, upper := 41/20,
    thresholdUpper := (41 / 20) ^ 2 / 9, rowUpper := 556/1000 }
def cell01 : Cell :=
  { lower := 41/20, upper := 42/20,
    thresholdUpper := (42 / 20) ^ 2 / 9, rowUpper := 555/1000 }
def cell02 : Cell :=
  { lower := 42/20, upper := 43/20,
    thresholdUpper := (43 / 20) ^ 2 / 9, rowUpper := 553/1000 }
def cell03 : Cell :=
  { lower := 43/20, upper := 44/20,
    thresholdUpper := (44 / 20) ^ 2 / 9, rowUpper := 552/1000 }
def cell04 : Cell :=
  { lower := 44/20, upper := 45/20,
    thresholdUpper := (45 / 20) ^ 2 / 9, rowUpper := 550/1000 }
def cell05 : Cell :=
  { lower := 45/20, upper := 46/20,
    thresholdUpper := (46 / 20) ^ 2 / 9, rowUpper := 548/1000 }
def cell06 : Cell :=
  { lower := 46/20, upper := 47/20,
    thresholdUpper := (47 / 20) ^ 2 / 9, rowUpper := 546/1000 }
def cell07 : Cell :=
  { lower := 47/20, upper := 48/20,
    thresholdUpper := (48 / 20) ^ 2 / 9, rowUpper := 543/1000 }
def cell08 : Cell :=
  { lower := 48/20, upper := 49/20,
    thresholdUpper := (49 / 20) ^ 2 / 9, rowUpper := 541/1000 }
def cell09 : Cell :=
  { lower := 49/20, upper := 50/20,
    thresholdUpper := (50 / 20) ^ 2 / 9, rowUpper := 538/1000 }

def cells : List Cell :=
  [cell00, cell01, cell02, cell03, cell04, cell05, cell06, cell07, cell08, cell09]

end SingletonPhaseFourierCover256Bits192
end SparseThresholdDominant
end CertifiedJL
