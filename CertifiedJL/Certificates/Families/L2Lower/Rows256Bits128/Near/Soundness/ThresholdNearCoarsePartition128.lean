/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Data.ThresholdNearCoarsePlans128

/-! # Fixed top-level partition of the coarse 128-bit near cover -/

namespace CertifiedJL
namespace ThresholdNearCoarse128

/-- The complete normalized near-band rectangle. -/
def rootCell : Cell where
  xLower := 1
  xUpper := 4901 / 2500
  aLower := 9 / 16
  aUpper := 2401 / 2500

def cell0 : Cell := leftX rootCell
def cell1 : Cell := rightX rootCell

def cell00 : Cell := leftA cell0
def cell01 : Cell := rightA cell0
def cell10 : Cell := leftA cell1
def cell11 : Cell := rightA cell1

def cell000 : Cell := leftX cell00
def cell001 : Cell := rightX cell00
def cell010 : Cell := leftX cell01
def cell011 : Cell := rightX cell01
def cell100 : Cell := leftX cell10
def cell101 : Cell := rightX cell10
def cell110 : Cell := leftX cell11
def cell111 : Cell := rightX cell11

def cell0000 : Cell := leftA cell000
def cell0001 : Cell := rightA cell000
def cell0010 : Cell := leftA cell001
def cell0011 : Cell := rightA cell001
def cell0100 : Cell := leftA cell010
def cell0101 : Cell := rightA cell010
def cell0110 : Cell := leftA cell011
def cell0111 : Cell := rightA cell011
def cell1000 : Cell := leftA cell100
def cell1001 : Cell := rightA cell100
def cell1010 : Cell := leftA cell101
def cell1011 : Cell := rightA cell101
def cell1100 : Cell := leftA cell110
def cell1101 : Cell := rightA cell110
def cell1110 : Cell := leftA cell111
def cell1111 : Cell := rightA cell111

def shardPlan (cell : Cell) : Plan := storedPlan cell

/- The lower-left shard carries most of the adaptive cover.  Split it two
more exact levels so its four kernel replays stay below the CI memory cap. -/
def cell00000 : Cell := leftX cell0000
def cell00001 : Cell := rightX cell0000
def cell000000 : Cell := leftA cell00000
def cell000001 : Cell := rightA cell00000
def cell000010 : Cell := leftA cell00001
def cell000011 : Cell := rightA cell00001

def shardPlan0000Child (cell : Cell) : Plan := storedPlan cell

/- A second numerically tight shard is split identically. -/
def cell01010 : Cell := leftX cell0101
def cell01011 : Cell := rightX cell0101
def cell010100 : Cell := leftA cell01010
def cell010101 : Cell := rightA cell01010
def cell010110 : Cell := leftA cell01011
def cell010111 : Cell := rightA cell01011

def shardPlan0101Child (cell : Cell) : Plan := storedPlan cell

/- Final resource splits for the two remaining heavy kernel leaves. -/
def cell0000000 : Cell := leftX cell000000
def cell0000001 : Cell := rightX cell000000
def cell00000000 : Cell := leftA cell0000000
def cell00000001 : Cell := rightA cell0000000
def cell00000010 : Cell := leftA cell0000001
def cell00000011 : Cell := rightA cell0000001

def shardPlan0000_00Child (cell : Cell) : Plan := storedPlan cell

/- The lower-left child remains the unique coarse replay above the CI memory
cap.  Split it two exact levels, and split only its lower-left grandchild two
levels further.  The resulting seven replays preserve the same cover while
keeping the largest kernel unit comfortably below four gigabytes. -/
def cell000000000 : Cell := leftX cell00000000
def cell000000001 : Cell := rightX cell00000000
def cell0000000000 : Cell := leftA cell000000000
def cell0000000001 : Cell := rightA cell000000000
def cell0000000010 : Cell := leftA cell000000001
def cell0000000011 : Cell := rightA cell000000001

def cell00000000000 : Cell := leftX cell0000000000
def cell00000000001 : Cell := rightX cell0000000000
def cell000000000000 : Cell := leftA cell00000000000
def cell000000000001 : Cell := rightA cell00000000000
def cell000000000010 : Cell := leftA cell00000000001
def cell000000000011 : Cell := rightA cell00000000001

def shardPlan0000_00_00Child (cell : Cell) : Plan := storedPlan cell
def shardPlan0000_00_00DeepChild (cell : Cell) : Plan := storedPlan cell

def shardPlan0000_00_00LowerLeft : Plan :=
  .splitX
    (.splitA (shardPlan0000_00_00DeepChild cell000000000000)
      (shardPlan0000_00_00DeepChild cell000000000001))
    (.splitA (shardPlan0000_00_00DeepChild cell000000000010)
      (shardPlan0000_00_00DeepChild cell000000000011))

def shardPlan0000_00_00 : Plan :=
  .splitX
    (.splitA shardPlan0000_00_00LowerLeft
      (shardPlan0000_00_00Child cell0000000001))
    (.splitA (shardPlan0000_00_00Child cell0000000010)
      (shardPlan0000_00_00Child cell0000000011))

def shardPlan0000_00 : Plan :=
  .splitX
    (.splitA shardPlan0000_00_00
      (shardPlan0000_00Child cell00000001))
    (.splitA (shardPlan0000_00Child cell00000010)
      (shardPlan0000_00Child cell00000011))

def cell0101010 : Cell := leftX cell010101
def cell0101011 : Cell := rightX cell010101
def cell01010100 : Cell := leftA cell0101010
def cell01010101 : Cell := rightA cell0101010
def cell01010110 : Cell := leftA cell0101011
def cell01010111 : Cell := rightA cell0101011

def shardPlan0101_01Child (cell : Cell) : Plan := storedPlan cell

def cell010101010 : Cell := leftX cell01010101
def cell010101011 : Cell := rightX cell01010101
def cell0101010100 : Cell := leftA cell010101010
def cell0101010101 : Cell := rightA cell010101010
def cell0101010110 : Cell := leftA cell010101011
def cell0101010111 : Cell := rightA cell010101011

def cell01010101010 : Cell := leftX cell0101010101
def cell01010101011 : Cell := rightX cell0101010101
def cell010101010100 : Cell := leftA cell01010101010
def cell010101010101 : Cell := rightA cell01010101010
def cell010101010110 : Cell := leftA cell01010101011
def cell010101010111 : Cell := rightA cell01010101011

def shardPlan0101_01_01Child (cell : Cell) : Plan := storedPlan cell
def shardPlan0101_01_01DeepChild (cell : Cell) : Plan := storedPlan cell

def shardPlan0101_01_01LowerRight : Plan :=
  .splitX
    (.splitA (shardPlan0101_01_01DeepChild cell010101010100)
      (shardPlan0101_01_01DeepChild cell010101010101))
    (.splitA (shardPlan0101_01_01DeepChild cell010101010110)
      (shardPlan0101_01_01DeepChild cell010101010111))

def shardPlan0101_01_01 : Plan :=
  .splitX
    (.splitA (shardPlan0101_01_01Child cell0101010100)
      shardPlan0101_01_01LowerRight)
    (.splitA (shardPlan0101_01_01Child cell0101010110)
      (shardPlan0101_01_01Child cell0101010111))

def shardPlan0101_01 : Plan :=
  .splitX
    (.splitA (shardPlan0101_01Child cell01010100)
      shardPlan0101_01_01)
    (.splitA (shardPlan0101_01Child cell01010110)
      (shardPlan0101_01Child cell01010111))

/- Split the remaining heavy `0000/01` child into four bounded replays. -/
def cell0000010 : Cell := leftX cell000001
def cell0000011 : Cell := rightX cell000001
def cell00000100 : Cell := leftA cell0000010
def cell00000101 : Cell := rightA cell0000010
def cell00000110 : Cell := leftA cell0000011
def cell00000111 : Cell := rightA cell0000011

def shardPlan0000_01Child (cell : Cell) : Plan := storedPlan cell

def shardPlan0000_01 : Plan :=
  .splitX
    (.splitA (shardPlan0000_01Child cell00000100)
      (shardPlan0000_01Child cell00000101))
    (.splitA (shardPlan0000_01Child cell00000110)
      (shardPlan0000_01Child cell00000111))

def shardPlan0000Final : Plan :=
  .splitX
    (.splitA shardPlan0000_00 shardPlan0000_01)
    (.splitA (shardPlan0000Child cell000010) (shardPlan0000Child cell000011))

def shardPlan0101Final : Plan :=
  .splitX
    (.splitA (shardPlan0101Child cell010100) shardPlan0101_01)
    (.splitA (shardPlan0101Child cell010110) (shardPlan0101Child cell010111))

/- The `0100` coarse shard is the other replay above the CI memory cap. -/
def cell01000 : Cell := leftX cell0100
def cell01001 : Cell := rightX cell0100
def cell010000 : Cell := leftA cell01000
def cell010001 : Cell := rightA cell01000
def cell010010 : Cell := leftA cell01001
def cell010011 : Cell := rightA cell01001

def shardPlan0100Child (cell : Cell) : Plan := storedPlan cell

def shardPlan0100 : Plan :=
  .splitX
    (.splitA (shardPlan0100Child cell010000)
      (shardPlan0100Child cell010001))
    (.splitA (shardPlan0100Child cell010010)
      (shardPlan0100Child cell010011))

/- Split the final heavy top-level coarse shard.  Its lower-left child alone
needs one additional exact split to keep comfortable memory headroom. -/
def cell00010 : Cell := leftX cell0001
def cell00011 : Cell := rightX cell0001
def cell000100 : Cell := leftA cell00010
def cell000101 : Cell := rightA cell00010
def cell000110 : Cell := leftA cell00011
def cell000111 : Cell := rightA cell00011

def cell0001000 : Cell := leftX cell000100
def cell0001001 : Cell := rightX cell000100
def cell00010000 : Cell := leftA cell0001000
def cell00010001 : Cell := rightA cell0001000
def cell00010010 : Cell := leftA cell0001001
def cell00010011 : Cell := rightA cell0001001

def shardPlan0001Child (cell : Cell) : Plan := storedPlan cell
def shardPlan0001DeepChild (cell : Cell) : Plan := storedPlan cell

def shardPlan0001LowerLeft : Plan :=
  .splitX
    (.splitA (shardPlan0001DeepChild cell00010000)
      (shardPlan0001DeepChild cell00010001))
    (.splitA (shardPlan0001DeepChild cell00010010)
      (shardPlan0001DeepChild cell00010011))

def shardPlan0001 : Plan :=
  .splitX
    (.splitA shardPlan0001LowerLeft (shardPlan0001Child cell000101))
    (.splitA (shardPlan0001Child cell000110)
      (shardPlan0001Child cell000111))

end ThresholdNearCoarse128
end CertifiedJL
