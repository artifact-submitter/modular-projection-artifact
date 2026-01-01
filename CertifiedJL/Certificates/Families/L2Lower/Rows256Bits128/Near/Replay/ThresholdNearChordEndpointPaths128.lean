/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Replay.ThresholdNearChordEndpoints128

/-! # Prefix-free endpoint replay frontiers -/

namespace CertifiedJL.ThresholdNearChord128

def endpointPaths_4_div_5 : List (List Bool) := [[false, false, false, false, false, false, false, false],
 [false, false, false, false, false, false, false, true],
 [false, false, false, false, false, false, true],
 [false, false, false, false, false, true, false, false],
 [false, false, false, false, false, true, false, true],
 [false, false, false, false, false, true, true],
 [false, false, false, false, true],
 [false, false, false, true, false, false, false, false],
 [false, false, false, true, false, false, false, true],
 [false, false, false, true, false, false, true],
 [false, false, false, true, false, true, false, false],
 [false, false, false, true, false, true, false, true],
 [false, false, false, true, false, true, true],
 [false, false, false, true, true],
 [false, false, true],
 [false, true, false, false, false, false, false, false],
 [false, true, false, false, false, false, false, true],
 [false, true, false, false, false, false, true],
 [false, true, false, false, false, true, false, false],
 [false, true, false, false, false, true, false, true],
 [false, true, false, false, false, true, true],
 [false, true, false, false, true],
 [false, true, false, true, false, false, false, false],
 [false, true, false, true, false, false, false, true],
 [false, true, false, true, false, false, true],
 [false, true, false, true, false, true, false, false, false, false],
 [false, true, false, true, false, true, false, false, false, true],
 [false, true, false, true, false, true, false, false, true],
 [false, true, false, true, false, true, false, true, false, false, false],
 [false, true, false, true, false, true, false, true, false, false, true],
 [false, true, false, true, false, true, false, true, false, true, false, false],
 [false, true, false, true, false, true, false, true, false, true, false, true, false, false],
 [false, true, false, true, false, true, false, true, false, true, false, true, false, true],
 [false, true, false, true, false, true, false, true, false, true, false, true, true],
 [false, true, false, true, false, true, false, true, false, true, true],
 [false, true, false, true, false, true, false, true, true],
 [false, true, false, true, false, true, true],
 [false, true, false, true, true],
 [false, true, true],
 [true, false],
 [true, true]]

def endpointPaths_17_div_20 : List (List Bool) := [[false, false, false, false, false, false, false, false],
 [false, false, false, false, false, false, false, true],
 [false, false, false, false, false, false, true],
 [false, false, false, false, false, true, false, false],
 [false, false, false, false, false, true, false, true],
 [false, false, false, false, false, true, true],
 [false, false, false, false, true],
 [false, false, false, true, false, false, false, false],
 [false, false, false, true, false, false, false, true],
 [false, false, false, true, false, false, true],
 [false, false, false, true, false, true, false, false],
 [false, false, false, true, false, true, false, true],
 [false, false, false, true, false, true, true],
 [false, false, false, true, true],
 [false, false, true],
 [false, true, false, false, false, false, false, false],
 [false, true, false, false, false, false, false, true],
 [false, true, false, false, false, false, true],
 [false, true, false, false, false, true, false, false],
 [false, true, false, false, false, true, false, true],
 [false, true, false, false, false, true, true],
 [false, true, false, false, true],
 [false, true, false, true, false, false, false, false],
 [false, true, false, true, false, false, false, true],
 [false, true, false, true, false, false, true],
 [false, true, false, true, false, true, false, false, false, false],
 [false, true, false, true, false, true, false, false, false, true],
 [false, true, false, true, false, true, false, false, true],
 [false, true, false, true, false, true, false, true, false, false, false],
 [false, true, false, true, false, true, false, true, false, false, true],
 [false, true, false, true, false, true, false, true, false, true, false, false],
 [false, true, false, true, false, true, false, true, false, true, false, true, false],
 [false, true, false, true, false, true, false, true, false, true, false, true, true],
 [false, true, false, true, false, true, false, true, false, true, true],
 [false, true, false, true, false, true, false, true, true],
 [false, true, false, true, false, true, true],
 [false, true, false, true, true],
 [false, true, true],
 [true, false],
 [true, true]]

def endpointPaths_9_div_10 : List (List Bool) := [[false, false, false, false, false, false, false, false],
 [false, false, false, false, false, false, false, true],
 [false, false, false, false, false, false, true],
 [false, false, false, false, false, true, false, false],
 [false, false, false, false, false, true, false, true],
 [false, false, false, false, false, true, true],
 [false, false, false, false, true],
 [false, false, false, true, false, false, false, false],
 [false, false, false, true, false, false, false, true],
 [false, false, false, true, false, false, true],
 [false, false, false, true, false, true, false],
 [false, false, false, true, false, true, true],
 [false, false, false, true, true],
 [false, false, true],
 [false, true, false, false, false, false, false],
 [false, true, false, false, false, false, true],
 [false, true, false, false, false, true, false, false],
 [false, true, false, false, false, true, false, true],
 [false, true, false, false, false, true, true],
 [false, true, false, false, true],
 [false, true, false, true, false, false, false, false],
 [false, true, false, true, false, false, false, true],
 [false, true, false, true, false, false, true],
 [false, true, false, true, false, true, false, false, false, false],
 [false, true, false, true, false, true, false, false, false, true],
 [false, true, false, true, false, true, false, false, true],
 [false, true, false, true, false, true, false, true, false, false, false],
 [false, true, false, true, false, true, false, true, false, false, true],
 [false, true, false, true, false, true, false, true, false, true, false, false],
 [false, true, false, true, false, true, false, true, false, true, false, true, false],
 [false, true, false, true, false, true, false, true, false, true, false, true, true],
 [false, true, false, true, false, true, false, true, false, true, true],
 [false, true, false, true, false, true, false, true, true],
 [false, true, false, true, false, true, true],
 [false, true, false, true, true],
 [false, true, true],
 [true, false],
 [true, true]]

def endpointPaths_19_div_20 : List (List Bool) := [[false, false, false, false, false, false, false, false],
 [false, false, false, false, false, false, false, true],
 [false, false, false, false, false, false, true],
 [false, false, false, false, false, true, false, false],
 [false, false, false, false, false, true, false, true],
 [false, false, false, false, false, true, true],
 [false, false, false, false, true],
 [false, false, false, true, false, false],
 [false, false, false, true, false, true],
 [false, false, false, true, true],
 [false, false, true],
 [false, true, false, false, false, false, false],
 [false, true, false, false, false, false, true],
 [false, true, false, false, false, true, false, false],
 [false, true, false, false, false, true, false, true],
 [false, true, false, false, false, true, true],
 [false, true, false, false, true],
 [false, true, false, true, false, false, false, false],
 [false, true, false, true, false, false, false, true],
 [false, true, false, true, false, false, true],
 [false, true, false, true, false, true, false, false, false, false],
 [false, true, false, true, false, true, false, false, false, true],
 [false, true, false, true, false, true, false, false, true],
 [false, true, false, true, false, true, false, true, false, false, false],
 [false, true, false, true, false, true, false, true, false, false, true],
 [false, true, false, true, false, true, false, true, false, true, false, false],
 [false, true, false, true, false, true, false, true, false, true, false, true, false],
 [false, true, false, true, false, true, false, true, false, true, false, true, true],
 [false, true, false, true, false, true, false, true, false, true, true],
 [false, true, false, true, false, true, false, true, true],
 [false, true, false, true, false, true, true],
 [false, true, false, true, true],
 [false, true, true],
 [true, false],
 [true, true]]

def endpointPaths_one : List (List Bool) := [[false, false, false, false, false, false],
 [false, false, false, false, false, true],
 [false, false, false, false, true],
 [false, false, false, true, false, false],
 [false, false, false, true, false, true],
 [false, false, false, true, true],
 [false, false, true],
 [false, true, false, false, false, false, false],
 [false, true, false, false, false, false, true],
 [false, true, false, false, false, true, false, false],
 [false, true, false, false, false, true, false, true],
 [false, true, false, false, false, true, true],
 [false, true, false, false, true],
 [false, true, false, true, false, false, false, false],
 [false, true, false, true, false, false, false, true],
 [false, true, false, true, false, false, true],
 [false, true, false, true, false, true, false, false, false, false],
 [false, true, false, true, false, true, false, false, false, true],
 [false, true, false, true, false, true, false, false, true],
 [false, true, false, true, false, true, false, true, false, false, false],
 [false, true, false, true, false, true, false, true, false, false, true],
 [false, true, false, true, false, true, false, true, false, true, false, false],
 [false, true, false, true, false, true, false, true, false, true, false, true, false],
 [false, true, false, true, false, true, false, true, false, true, false, true, true],
 [false, true, false, true, false, true, false, true, false, true, true],
 [false, true, false, true, false, true, false, true, true],
 [false, true, false, true, false, true, true],
 [false, true, false, true, true],
 [false, true, true],
 [true, false],
 [true, true]]

inductive EndpointReplay where
  | adaptive (depth : Nat) (splitXNext : Bool)
  | splitX (left right : EndpointReplay)
  | splitA (left right : EndpointReplay)

def EndpointReplay.plan : EndpointReplay → Cell → Plan
  | .adaptive depth splitXNext, cell => endpointRefine128 depth splitXNext cell
  | .splitX left right, cell =>
      .splitX (left.plan (leftX cell)) (right.plan (rightX cell))
  | .splitA left right, cell =>
      .splitA (left.plan (leftA cell)) (right.plan (rightA cell))

def EndpointReplay.units : EndpointReplay → Cell → List (Cell × Plan)
  | replay@(.adaptive ..), cell => [(cell, replay.plan cell)]
  | .splitX left right, cell =>
      left.units (leftX cell) ++ right.units (rightX cell)
  | .splitA left right, cell =>
      left.units (leftA cell) ++ right.units (rightA cell)

def EndpointReplay.check : EndpointReplay → Cell → Bool
  | replay@(.adaptive ..), cell => endpointUnitPass128 (cell, replay.plan cell)
  | .splitX left right, cell =>
      left.check (leftX cell) && right.check (rightX cell)
  | .splitA left right, cell =>
      left.check (leftA cell) && right.check (rightA cell)

def EndpointReplay.unitAtPath : EndpointReplay → Cell → List Bool → Cell × Plan
  | replay, cell, [] => (cell, replay.plan cell)
  | .splitX left _, cell, false :: rest => left.unitAtPath (leftX cell) rest
  | .splitX _ right, cell, true :: rest => right.unitAtPath (rightX cell) rest
  | .splitA left _, cell, false :: rest => left.unitAtPath (leftA cell) rest
  | .splitA _ right, cell, true :: rest => right.unitAtPath (rightA cell) rest
  | replay@(.adaptive ..), cell, _ :: _ => (cell, replay.plan cell)

theorem EndpointReplay.check_eq_units_all (replay : EndpointReplay) (cell : Cell) :
    replay.check cell = (replay.units cell).all endpointUnitPass128 := by
  induction replay generalizing cell with
  | adaptive => simp [EndpointReplay.check, EndpointReplay.units]
  | splitX left right ihLeft ihRight =>
      simp [EndpointReplay.check, EndpointReplay.units, List.all_append, ihLeft, ihRight]
  | splitA left right ihLeft ihRight =>
      simp [EndpointReplay.check, EndpointReplay.units, List.all_append, ihLeft, ihRight]

theorem EndpointReplay.check_eq_planCheck (replay : EndpointReplay) (cell : Cell) :
    replay.check cell = endpointPlanCheck128 cell (replay.plan cell) := by
  induction replay generalizing cell with
  | adaptive => rfl
  | splitX left right ihLeft ihRight =>
      simp [EndpointReplay.check, EndpointReplay.plan, endpointPlanCheck128,
        ihLeft, ihRight]
  | splitA left right ihLeft ihRight =>
      simp [EndpointReplay.check, EndpointReplay.plan, endpointPlanCheck128,
        ihLeft, ihRight]

private def hasEmptyPath (paths : List (List Bool)) : Bool :=
  paths.any List.isEmpty

private def tailsWithHead (head : Bool) (paths : List (List Bool)) : List (List Bool) :=
  paths.filterMap fun
    | [] => none
    | next :: tail => if next = head then some tail else none

def endpointReplayFromPaths : Nat → Bool → List (List Bool) → EndpointReplay
  | 0, splitXNext, _ => .adaptive 0 splitXNext
  | depth + 1, splitXNext, paths =>
      if hasEmptyPath paths then .adaptive (depth + 1) splitXNext
      else if splitXNext then
        .splitX
          (endpointReplayFromPaths depth false (tailsWithHead false paths))
          (endpointReplayFromPaths depth false (tailsWithHead true paths))
      else
        .splitA
          (endpointReplayFromPaths depth true (tailsWithHead false paths))
          (endpointReplayFromPaths depth true (tailsWithHead true paths))

def endpointReplayAt128 (paths : List (List Bool)) : EndpointReplay :=
  endpointReplayFromPaths 22 true paths

def endpointUnitFromPaths128 (y : ℚ) (paths : List (List Bool))
    (index : Nat) : Cell × Plan :=
  (endpointReplayAt128 paths).unitAtPath (endpointCell128 y)
    (paths[index]?.getD [])

def endpointUnitPassFromPaths128 (y : ℚ) (paths : List (List Bool))
    (index : Nat) : Bool :=
  endpointUnitPass128 (endpointUnitFromPaths128 y paths index)

end CertifiedJL.ThresholdNearChord128
