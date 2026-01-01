/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Soundness.CappedFourierNumeric256Bits192

/-! # Retained-Fourier modulus cover for the 256-row, 192-bit endpoint -/

namespace CertifiedJL
namespace SparseThresholdDominant
namespace CappedFourierCover256Bits192

open CappedFourierNumeric256Bits192

def cell00 : Cell := { lower := 40/20, upper := 41/20, thresholdUpper := (41 / 20) ^ 2 / 9, rowUpper := 554/1000 }
def cell01 : Cell := { lower := 41/20, upper := 42/20, thresholdUpper := (42 / 20) ^ 2 / 9, rowUpper := 551/1000 }
def cell02 : Cell := { lower := 42/20, upper := 43/20, thresholdUpper := (43 / 20) ^ 2 / 9, rowUpper := 548/1000 }
def cell03 : Cell := { lower := 43/20, upper := 44/20, thresholdUpper := (44 / 20) ^ 2 / 9, rowUpper := 546/1000 }
def cell04 : Cell := { lower := 44/20, upper := 45/20, thresholdUpper := (45 / 20) ^ 2 / 9, rowUpper := 543/1000 }
def cell05 : Cell := { lower := 45/20, upper := 46/20, thresholdUpper := (46 / 20) ^ 2 / 9, rowUpper := 541/1000 }
def cell06 : Cell := { lower := 46/20, upper := 47/20, thresholdUpper := (47 / 20) ^ 2 / 9, rowUpper := 539/1000 }
def cell07 : Cell := { lower := 47/20, upper := 48/20, thresholdUpper := (48 / 20) ^ 2 / 9, rowUpper := 536/1000 }
def cell08 : Cell := { lower := 48/20, upper := 49/20, thresholdUpper := (49 / 20) ^ 2 / 9, rowUpper := 534/1000 }
def cell09 : Cell := { lower := 49/20, upper := 50/20, thresholdUpper := (50 / 20) ^ 2 / 9, rowUpper := 531/1000 }
def cell10 : Cell := { lower := 50/20, upper := 51/20, thresholdUpper := (51 / 20) ^ 2 / 9, rowUpper := 529/1000 }
def cell11 : Cell := { lower := 51/20, upper := 52/20, thresholdUpper := (52 / 20) ^ 2 / 9, rowUpper := 526/1000 }
def cell12 : Cell := { lower := 52/20, upper := 53/20, thresholdUpper := (53 / 20) ^ 2 / 9, rowUpper := 523/1000 }
def cell13 : Cell := { lower := 53/20, upper := 54/20, thresholdUpper := (54 / 20) ^ 2 / 9, rowUpper := 520/1000 }
def cell14 : Cell := { lower := 54/20, upper := 55/20, thresholdUpper := (55 / 20) ^ 2 / 9, rowUpper := 517/1000 }
def cell15 : Cell := { lower := 55/20, upper := 56/20, thresholdUpper := (56 / 20) ^ 2 / 9, rowUpper := 515/1000 }
def cell16 : Cell := { lower := 56/20, upper := 57/20, thresholdUpper := (57 / 20) ^ 2 / 9, rowUpper := 512/1000 }
def cell17 : Cell := { lower := 57/20, upper := 58/20, thresholdUpper := (58 / 20) ^ 2 / 9, rowUpper := 510/1000 }
def cell18 : Cell := { lower := 58/20, upper := 59/20, thresholdUpper := (59 / 20) ^ 2 / 9, rowUpper := 508/1000 }
def cell19 : Cell := { lower := 59/20, upper := 60/20, thresholdUpper := (60 / 20) ^ 2 / 9, rowUpper := 506/1000 }

def cells : List Cell :=
  [cell00, cell01, cell02, cell03, cell04, cell05, cell06, cell07,
    cell08, cell09, cell10, cell11, cell12, cell13, cell14, cell15,
    cell16, cell17, cell18, cell19]

end CappedFourierCover256Bits192
end SparseThresholdDominant
end CertifiedJL
