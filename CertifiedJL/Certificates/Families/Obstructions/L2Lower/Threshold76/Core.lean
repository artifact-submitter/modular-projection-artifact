/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Shared.FixedPointConvolutionSoundness

/-!
# Core arithmetic for the 512-row threshold-floor-76 obstruction

The one-row squared-magnitude distribution has denominator `2^162`. It is embedded exactly at
scale `2^255`, then squared nine times with downward rounding after every
squaring. Squared norms at least `6156 = 76 * 9^2` are truncated; nonnegativity
makes that truncation sound for the retained lower tail.
-/

namespace CertifiedJL.ThresholdLower76

open FixedPointConvolution

def cutoff : ℕ := 6156
def scale : ℕ := 2 ^ 255
def rowDenominator : ℕ := 2 ^ 162
def packingBase : ℕ := 2 ^ 525

/-- Exact numerators of the absolute centered residue classes `0,...,13`
for one 81-dimensional all-ones sparse row modulo 27. -/
def rowClassCount : Fin 14 → ℕ := ![
  365988212723933408294191531270801376502622439914,
  723088766044420703589268172266974771106179426228,
  697083360414890122738894713457539500972341376274,
  655858614858041548196043362494129362407038510824,
  602343531051125742011091064496255279088601229568,
  540186897435539887153654837545992481713937995658,
  473396409408162800810920956084924689665720750068,
  405982889703357664232952818757699981915175919514,
  341658510264067852019471651360534793715369557912,
  283622690201182644573623245922329553701177878684,
  234448972392553756539497178698791184604333371604,
  196065285609367123901794439703393917518918120644,
  169802922583216822396800681182859043931350477812,
  156479486633751596356534677622906141780963117200]

def rowMassAtSquaredNorm (energy : ℕ) : ℕ :=
  ∑ residue : {residue : Fin 14 // residue.1 ^ 2 = energy},
    rowClassCount residue

/-- The exact one-row squared-magnitude distribution at the certificate scale. -/
def state0 : List ℕ :=
  List.ofFn fun energy : Fin cutoff =>
    rowMassAtSquaredNorm energy * 2 ^ (255 - 162)

theorem getD_state0_of_lt {energy : ℕ} (henergy : energy < cutoff) :
    state0.getD energy 0 = rowMassAtSquaredNorm energy * 2 ^ (255 - 162) := by
  let f : Fin cutoff → ℕ := fun energy =>
    rowMassAtSquaredNorm energy * 2 ^ (255 - 162)
  have hi : energy < (List.ofFn f).length := by simpa using henergy
  rw [show state0 = List.ofFn f by rfl,
    List.getD_eq_getElem _ _ hi]
  simpa only [f] using (@List.getElem_ofFn cutoff ℕ energy f hi)

/-- The successive downward-rounded laws for `1,2,4,...` rows. -/
def roundedState : ℕ → List ℕ
  | 0 => state0
  | stages + 1 => roundedConvolution cutoff scale (roundedState stages)

/-- Compact encoding of `roundedState`; one squaring doubles the row count. -/
def packedState (stages : ℕ) : ℕ :=
  packedSquareIterate cutoff packingBase scale stages
    (Nat.ofDigits packingBase state0)

theorem packingBase_gt_one : 1 < packingBase := by
  norm_num [packingBase]

set_option exponentiation.threshold 1000 in
theorem convolution_digits_fit :
    (cutoff + cutoff) * (scale * scale) < packingBase := by
  norm_num [cutoff, scale, packingBase]

theorem scale_pos : 0 < scale := by
  norm_num [scale]

end CertifiedJL.ThresholdLower76
