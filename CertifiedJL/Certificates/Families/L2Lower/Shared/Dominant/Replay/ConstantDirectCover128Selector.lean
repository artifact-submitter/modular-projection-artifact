import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.ConstantDirectCover128Aggregate

/-!
# Exact no-gap selector for the low-residual 128-bit cover

A small generic interpreter proves soundness for a binary tree of exact
rational boxes. The generated tree is kernel-checked: split children share
their closed boundary; empty leaves lie strictly above `r = 1 + u`; and
every accepted leaf names one of the independently replayed shard entries.
-/

namespace CertifiedJL
namespace SparseThresholdDominant
namespace ConstantDirectCover128Selector

open ConstantNumeric

structure Box where
  uLower : ℚ
  uUpper : ℚ
  rLower : ℚ
  rUpper : ℚ

inductive CoverTree where
  | empty
  | leaf (index : Fin 188)
  | splitU (middle : ℚ) (left right : CoverTree)
  | splitR (middle : ℚ) (left right : CoverTree)

private def entries : List Entry := ConstantDirectCover128Shard46.allEntries

private theorem entries_length : entries.length = 188 := by
  decide +kernel

private def entryAt (index : Fin 188) : Entry :=
  entries.get ⟨index, by rw [entries_length]; exact index.isLt⟩

private theorem entryAt_mem (index : Fin 188) :
    entryAt index ∈ entries := by
  unfold entryAt
  exact List.get_mem _ _

private theorem entryAt_valid (index : Fin 188) :
    (entryAt index).cell.Valid :=
  ConstantDirectCover128Shard46.allEntries_valid (entryAt_mem index)

private theorem entryAt_bound (index : Fin 188) :
    thresholdDominantCellMajorant (entryAt index).cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  ConstantDirectCover128Shard46.allEntries_bound (entryAt_mem index)

private def leafValid (box : Box) (index : Fin 188) : Prop :=
  let entry := entryAt index
  entry.cell.lower = box.uLower ∧
    entry.cell.upper = box.uUpper ∧
    entry.cell.thresholdUpper = box.rUpper ∧
    (entry.cell.modulusLower = 2 ∨
      entry.cell.modulusLower ^ 2 ≤ 9 * box.rLower)

def CoverTree.Valid : CoverTree → Box → Prop
  | .empty, box => 1 + box.uUpper < box.rLower
  | .leaf index, box => leafValid box index
  | .splitU middle left right, box =>
      box.uLower ≤ middle ∧ middle ≤ box.uUpper ∧
        left.Valid { box with uUpper := middle } ∧
        right.Valid { box with uLower := middle }
  | .splitR middle left right, box =>
      box.rLower ≤ middle ∧ middle ≤ box.rUpper ∧
        left.Valid { box with rUpper := middle } ∧
        right.Valid { box with rLower := middle }

private def CoverTree.decidableValid :
    (tree : CoverTree) → (box : Box) → Decidable (tree.Valid box)
  | .empty, _ => by
      unfold CoverTree.Valid
      infer_instance
  | .leaf _, _ => by
      unfold CoverTree.Valid leafValid
      infer_instance
  | .splitU middle left right, box => by
      unfold CoverTree.Valid
      letI := left.decidableValid { box with uUpper := middle }
      letI := right.decidableValid { box with uLower := middle }
      exact inferInstance
  | .splitR middle left right, box => by
      unfold CoverTree.Valid
      letI := left.decidableValid { box with rUpper := middle }
      letI := right.decidableValid { box with rLower := middle }
      exact inferInstance

private instance (tree : CoverTree) (box : Box) :
    Decidable (tree.Valid box) := tree.decidableValid box

def CoverTree.leafIndices : CoverTree → List (Fin 188)
  | .empty => []
  | .leaf index => [index]
  | .splitU _ left right | .splitR _ left right =>
      left.leafIndices ++ right.leafIndices

private theorem CoverTree.sound (tree : CoverTree) (box : Box)
    (hvalid : tree.Valid box) (P : Cell → Prop)
    (hbound : ∀ index, P (entryAt index).cell) (u r B : ℝ)
    (huLower : (box.uLower : ℝ) ≤ u)
    (huUpper : u ≤ (box.uUpper : ℝ))
    (hrLower : (box.rLower : ℝ) ≤ r)
    (hrUpper : r ≤ (box.rUpper : ℝ))
    (hrFeasible : r ≤ 1 + u) (hBtwo : 2 ≤ B)
    (hrModulus : 9 * r ≤ B ^ 2) :
    ∃ entry : Entry,
      entry.cell.Valid ∧
      (entry.cell.lower : ℝ) ≤ u ∧
      u ≤ (entry.cell.upper : ℝ) ∧
      r ≤ (entry.cell.thresholdUpper : ℝ) ∧
      (entry.cell.modulusLower : ℝ) ≤ B ∧
      P entry.cell := by
  induction tree generalizing box with
  | empty =>
      have himpossible : (1 : ℝ) + (box.uUpper : ℝ) <
          (box.rLower : ℝ) := by exact_mod_cast hvalid
      exfalso
      linarith
  | leaf index =>
      rcases hvalid with ⟨huLowerEq, huUpperEq, hrUpperEq, hmodulus⟩
      refine ⟨entryAt index, entryAt_valid index, ?_, ?_, ?_, ?_,
        hbound index⟩
      · rw [huLowerEq]
        exact huLower
      · rw [huUpperEq]
        exact huUpper
      · rw [hrUpperEq]
        exact hrUpper
      · rcases hmodulus with htwo | hsquare
        · rw [htwo]
          exact hBtwo
        · have hsquareReal :
              ((entryAt index).cell.modulusLower : ℝ) ^ 2 ≤
                9 * (box.rLower : ℝ) := by exact_mod_cast hsquare
          have hrScaled : 9 * (box.rLower : ℝ) ≤ 9 * r :=
            mul_le_mul_of_nonneg_left hrLower (by norm_num)
          have hmSquare :
              ((entryAt index).cell.modulusLower : ℝ) ^ 2 ≤ B ^ 2 :=
            hsquareReal.trans (hrScaled.trans hrModulus)
          have hmPositive :
              0 < ((entryAt index).cell.modulusLower : ℝ) := by
            have := (entryAt_valid index).1.2.2.2.1
            exact_mod_cast (lt_trans (by norm_num : (0 : ℚ) < 1) this)
          nlinarith [hmSquare]
  | splitU middle left right ihLeft ihRight =>
      rcases hvalid with ⟨-, -, hleft, hright⟩
      by_cases hside : u ≤ (middle : ℝ)
      · exact ihLeft _ hleft huLower hside hrLower hrUpper
      · exact ihRight _ hright (le_of_not_ge hside) huUpper
          hrLower hrUpper
  | splitR middle left right ihLeft ihRight =>
      rcases hvalid with ⟨-, -, hleft, hright⟩
      by_cases hside : r ≤ (middle : ℝ)
      · exact ihLeft _ hleft huLower huUpper hrLower hside
      · exact ihRight _ hright huLower huUpper
          (le_of_not_ge hside) hrUpper

private def rootBox : Box :=
  ⟨0, 1 / 2, 0, 2500 / 2401⟩

private def rootTree : CoverTree :=
  .splitR (1250 / 2401)
    (.splitU (1 / 4)
      (.splitR (625 / 2401)
        (.splitU (1 / 8)
          (.leaf ⟨185, by decide⟩)
          (.leaf ⟨187, by decide⟩))
        (.splitU (1 / 8)
          (.splitR (1875 / 4802)
            (.leaf ⟨177, by decide⟩)
            (.splitU (1 / 16)
              (.leaf ⟨178, by decide⟩)
              (.leaf ⟨184, by decide⟩)))
          (.leaf ⟨168, by decide⟩)))
      (.splitR (625 / 2401)
        (.splitU (3 / 8)
          (.leaf ⟨186, by decide⟩)
          (.leaf ⟨183, by decide⟩))
        (.splitU (3 / 8)
          (.splitR (1875 / 4802)
            (.leaf ⟨181, by decide⟩)
            (.splitU (5 / 16)
              (.leaf ⟨182, by decide⟩)
              (.leaf ⟨170, by decide⟩)))
          (.splitR (1875 / 4802)
            (.splitU (7 / 16)
              (.leaf ⟨180, by decide⟩)
              (.leaf ⟨160, by decide⟩))
            (.splitU (7 / 16)
              (.splitR (625 / 1372)
                (.leaf ⟨165, by decide⟩)
                (.leaf ⟨125, by decide⟩))
              (.splitR (625 / 1372)
                (.splitU (15 / 32)
                  (.leaf ⟨158, by decide⟩)
                  (.splitR (8125 / 19208)
                    (.leaf ⟨149, by decide⟩)
                    (.splitU (31 / 64)
                      (.leaf ⟨148, by decide⟩)
                      (.leaf ⟨67, by decide⟩))))
                (.splitU (15 / 32)
                  (.splitR (9375 / 19208)
                    (.leaf ⟨154, by decide⟩)
                    (.leaf ⟨173, by decide⟩))
                  (.splitR (9375 / 19208)
                    (.splitU (31 / 64)
                      (.leaf ⟨141, by decide⟩)
                      (.splitR (18125 / 38416)
                        (.leaf ⟨136, by decide⟩)
                        (.leaf ⟨162, by decide⟩)))
                    (.leaf ⟨156, by decide⟩)))))))))
    (.splitU (1 / 4)
      (.splitR (1875 / 2401)
        (.splitU (1 / 8)
          (.splitR (3125 / 4802)
            (.splitU (1 / 16)
              (.leaf ⟨172, by decide⟩)
              (.leaf ⟨179, by decide⟩))
            (.splitU (1 / 16)
              (.leaf ⟨143, by decide⟩)
              (.leaf ⟨175, by decide⟩)))
          (.splitR (3125 / 4802)
            (.leaf ⟨164, by decide⟩)
            (.leaf ⟨155, by decide⟩)))
        (.splitU (1 / 8)
          (.splitR (625 / 686)
            (.splitU (1 / 16)
              (.splitR (8125 / 9604)
                (.splitU (1 / 32)
                  (.leaf ⟨163, by decide⟩)
                  (.leaf ⟨171, by decide⟩))
                (.splitU (1 / 32)
                  (.leaf ⟨95, by decide⟩)
                  (.leaf ⟨151, by decide⟩)))
              (.leaf ⟨135, by decide⟩))
            (.splitU (1 / 16)
              (.splitR (9375 / 9604)
                (.splitU (1 / 32)
                  (.splitR (18125 / 19208)
                    (.splitU (1 / 64)
                      (.leaf ⟨123, by decide⟩)
                      (.leaf ⟨140, by decide⟩))
                    (.splitU (1 / 64)
                      (.splitR (36875 / 38416)
                        (.splitU (1 / 128)
                          (.leaf ⟨132, by decide⟩)
                          (.leaf ⟨137, by decide⟩))
                        (.splitU (1 / 128)
                          (.leaf ⟨82, by decide⟩)
                          (.leaf ⟨120, by decide⟩)))
                      (.leaf ⟨36, by decide⟩)))
                  (.splitR (18125 / 19208)
                    (.leaf ⟨131, by decide⟩)
                    (.splitU (3 / 64)
                      (.leaf ⟨134, by decide⟩)
                      (.leaf ⟨147, by decide⟩))))
                (.splitU (1 / 32)
                  (.splitR (19375 / 19208)
                    (.splitU (1 / 64)
                      (.splitR (38125 / 38416)
                        (.splitU (1 / 128)
                          (.splitR (75625 / 76832)
                            (.splitU (1 / 256)
                              (.leaf ⟨108, by decide⟩)
                              (.leaf ⟨117, by decide⟩))
                            (.splitU (1 / 256)
                              (.leaf ⟨72, by decide⟩)
                              (.leaf ⟨81, by decide⟩)))
                          (.splitR (75625 / 76832)
                            (.leaf ⟨83, by decide⟩)
                            (.splitU (3 / 256)
                              (.leaf ⟨110, by decide⟩)
                              (.leaf ⟨121, by decide⟩))))
                        (.splitU (1 / 128)
                          (.splitR (76875 / 76832)
                            (.splitU (1 / 256)
                              (.splitR (3125 / 3136)
                                (.leaf ⟨8, by decide⟩)
                                (.splitU (1 / 512)
                                  (.leaf ⟨78, by decide⟩)
                                  (.leaf ⟨73, by decide⟩)))
                              (.splitR (3125 / 3136)
                                (.leaf ⟨38, by decide⟩)
                                (.splitU (3 / 512)
                                  (.leaf ⟨77, by decide⟩)
                                  (.leaf ⟨84, by decide⟩))))
                            (.splitU (1 / 256)
                              (.splitR (154375 / 153664)
                                (.splitU (1 / 512)
                                  (.leaf ⟨14, by decide⟩)
                                  (.leaf ⟨15, by decide⟩))
                                (.empty))
                              (.splitR (154375 / 153664)
                                (.splitU (3 / 512)
                                  (.leaf ⟨27, by decide⟩)
                                  (.leaf ⟨45, by decide⟩))
                                (.splitU (3 / 512)
                                  (.splitR (309375 / 307328)
                                    (.splitU (5 / 1024)
                                      (.leaf ⟨54, by decide⟩)
                                      (.leaf ⟨59, by decide⟩))
                                    (.empty))
                                  (.splitR (309375 / 307328)
                                    (.leaf ⟨1, by decide⟩)
                                    (.splitU (7 / 1024)
                                      (.leaf ⟨37, by decide⟩)
                                      (.leaf ⟨46, by decide⟩)))))))
                          (.splitR (76875 / 76832)
                            (.splitU (3 / 256)
                              (.leaf ⟨16, by decide⟩)
                              (.leaf ⟨87, by decide⟩))
                            (.splitU (3 / 256)
                              (.splitR (154375 / 153664)
                                (.splitU (5 / 512)
                                  (.leaf ⟨55, by decide⟩)
                                  (.leaf ⟨71, by decide⟩))
                                (.splitU (5 / 512)
                                  (.splitR (309375 / 307328)
                                    (.leaf ⟨30, by decide⟩)
                                    (.splitU (9 / 1024)
                                      (.leaf ⟨52, by decide⟩)
                                      (.leaf ⟨57, by decide⟩)))
                                  (.leaf ⟨20, by decide⟩)))
                              (.splitR (154375 / 153664)
                                (.leaf ⟨3, by decide⟩)
                                (.splitU (7 / 512)
                                  (.leaf ⟨48, by decide⟩)
                                  (.leaf ⟨91, by decide⟩)))))))
                      (.splitR (38125 / 38416)
                        (.splitU (3 / 128)
                          (.leaf ⟨101, by decide⟩)
                          (.leaf ⟨126, by decide⟩))
                        (.splitU (3 / 128)
                          (.splitR (76875 / 76832)
                            (.splitU (5 / 256)
                              (.leaf ⟨115, by decide⟩)
                              (.leaf ⟨124, by decide⟩))
                            (.splitU (5 / 256)
                              (.leaf ⟨39, by decide⟩)
                              (.leaf ⟨103, by decide⟩)))
                          (.leaf ⟨9, by decide⟩))))
                    (.splitU (1 / 64)
                      (.splitR (5625 / 5488)
                        (.splitU (1 / 128)
                          (.empty)
                          (.splitR (78125 / 76832)
                            (.splitU (3 / 256)
                              (.splitR (155625 / 153664)
                                (.splitU (5 / 512)
                                  (.splitR (44375 / 43904)
                                    (.splitU (9 / 1024)
                                      (.leaf ⟨19, by decide⟩)
                                      (.leaf ⟨33, by decide⟩))
                                    (.empty))
                                  (.splitR (44375 / 43904)
                                    (.splitU (11 / 1024)
                                      (.leaf ⟨43, by decide⟩)
                                      (.leaf ⟨51, by decide⟩))
                                    (.splitU (11 / 1024)
                                      (.leaf ⟨4, by decide⟩)
                                      (.leaf ⟨21, by decide⟩))))
                                (.empty))
                              (.splitR (155625 / 153664)
                                (.splitU (7 / 512)
                                  (.splitR (44375 / 43904)
                                    (.leaf ⟨10, by decide⟩)
                                    (.splitU (13 / 1024)
                                      (.leaf ⟨34, by decide⟩)
                                      (.leaf ⟨49, by decide⟩)))
                                  (.leaf ⟨5, by decide⟩))
                                (.splitU (7 / 512)
                                  (.splitR (311875 / 307328)
                                    (.splitU (13 / 1024)
                                      (.empty)
                                      (.leaf ⟨11, by decide⟩))
                                    (.empty))
                                  (.splitR (311875 / 307328)
                                    (.splitU (15 / 1024)
                                      (.leaf ⟨31, by decide⟩)
                                      (.leaf ⟨60, by decide⟩))
                                    (.splitU (15 / 1024)
                                      (.empty)
                                      (.leaf ⟨7, by decide⟩))))))
                            (.empty)))
                        (.empty))
                      (.splitR (5625 / 5488)
                        (.splitU (3 / 128)
                          (.splitR (78125 / 76832)
                            (.splitU (5 / 256)
                              (.splitR (155625 / 153664)
                                (.splitU (9 / 512)
                                  (.leaf ⟨68, by decide⟩)
                                  (.leaf ⟨100, by decide⟩))
                                (.splitU (9 / 512)
                                  (.splitR (311875 / 307328)
                                    (.leaf ⟨25, by decide⟩)
                                    (.splitU (17 / 1024)
                                      (.leaf ⟨47, by decide⟩)
                                      (.leaf ⟨69, by decide⟩)))
                                  (.leaf ⟨42, by decide⟩)))
                              (.splitR (155625 / 153664)
                                (.leaf ⟨61, by decide⟩)
                                (.splitU (11 / 512)
                                  (.leaf ⟨85, by decide⟩)
                                  (.leaf ⟨104, by decide⟩))))
                            (.splitU (5 / 256)
                              (.splitR (156875 / 153664)
                                (.splitU (9 / 512)
                                  (.splitR (313125 / 307328)
                                    (.splitU (17 / 1024)
                                      (.empty)
                                      (.leaf ⟨26, by decide⟩))
                                    (.empty))
                                  (.splitR (313125 / 307328)
                                    (.splitU (19 / 1024)
                                      (.leaf ⟨56, by decide⟩)
                                      (.leaf ⟨79, by decide⟩))
                                    (.splitU (19 / 1024)
                                      (.empty)
                                      (.leaf ⟨44, by decide⟩))))
                                (.empty))
                              (.splitR (156875 / 153664)
                                (.splitU (11 / 512)
                                  (.leaf ⟨0, by decide⟩)
                                  (.leaf ⟨63, by decide⟩))
                                (.splitU (11 / 512)
                                  (.splitR (314375 / 307328)
                                    (.splitU (21 / 1024)
                                      (.empty)
                                      (.leaf ⟨53, by decide⟩))
                                    (.empty))
                                  (.splitR (314375 / 307328)
                                    (.leaf ⟨17, by decide⟩)
                                    (.splitU (23 / 1024)
                                      (.empty)
                                      (.leaf ⟨62, by decide⟩)))))))
                          (.splitR (78125 / 76832)
                            (.splitU (7 / 256)
                              (.leaf ⟨76, by decide⟩)
                              (.leaf ⟨112, by decide⟩))
                            (.splitU (7 / 256)
                              (.splitR (156875 / 153664)
                                (.splitU (13 / 512)
                                  (.leaf ⟨98, by decide⟩)
                                  (.leaf ⟨109, by decide⟩))
                                (.splitU (13 / 512)
                                  (.leaf ⟨32, by decide⟩)
                                  (.leaf ⟨75, by decide⟩)))
                              (.leaf ⟨6, by decide⟩))))
                        (.splitU (3 / 128)
                          (.empty)
                          (.splitR (79375 / 76832)
                            (.splitU (7 / 256)
                              (.splitR (158125 / 153664)
                                (.splitU (13 / 512)
                                  (.splitR (315625 / 307328)
                                    (.splitU (25 / 1024)
                                      (.empty)
                                      (.leaf ⟨70, by decide⟩))
                                    (.empty))
                                  (.splitR (315625 / 307328)
                                    (.leaf ⟨41, by decide⟩)
                                    (.splitU (27 / 1024)
                                      (.empty)
                                      (.leaf ⟨74, by decide⟩))))
                                (.empty))
                              (.splitR (158125 / 153664)
                                (.splitU (15 / 512)
                                  (.leaf ⟨50, by decide⟩)
                                  (.leaf ⟨86, by decide⟩))
                                (.splitU (15 / 512)
                                  (.splitR (316875 / 307328)
                                    (.splitU (29 / 1024)
                                      (.empty)
                                      (.leaf ⟨80, by decide⟩))
                                    (.empty))
                                  (.leaf ⟨2, by decide⟩))))
                            (.empty))))))
                  (.splitR (19375 / 19208)
                    (.splitU (3 / 64)
                      (.splitR (38125 / 38416)
                        (.leaf ⟨107, by decide⟩)
                        (.splitU (5 / 128)
                          (.leaf ⟨114, by decide⟩)
                          (.leaf ⟨128, by decide⟩)))
                      (.leaf ⟨118, by decide⟩))
                    (.splitU (3 / 64)
                      (.splitR (5625 / 5488)
                        (.splitU (5 / 128)
                          (.splitR (78125 / 76832)
                            (.leaf ⟨40, by decide⟩)
                            (.splitU (9 / 256)
                              (.leaf ⟨93, by decide⟩)
                              (.leaf ⟨113, by decide⟩)))
                          (.leaf ⟨65, by decide⟩))
                        (.splitU (5 / 128)
                          (.splitR (79375 / 76832)
                            (.splitU (9 / 256)
                              (.splitR (158125 / 153664)
                                (.leaf ⟨24, by decide⟩)
                                (.splitU (17 / 512)
                                  (.leaf ⟨58, by decide⟩)
                                  (.leaf ⟨90, by decide⟩)))
                              (.leaf ⟨29, by decide⟩))
                            (.splitU (9 / 256)
                              (.splitR (159375 / 153664)
                                (.splitU (17 / 512)
                                  (.splitR (318125 / 307328)
                                    (.leaf ⟨12, by decide⟩)
                                    (.empty))
                                  (.leaf ⟨18, by decide⟩))
                                (.empty))
                              (.splitR (159375 / 153664)
                                (.splitU (19 / 512)
                                  (.leaf ⟨66, by decide⟩)
                                  (.leaf ⟨92, by decide⟩))
                                (.splitU (19 / 512)
                                  (.empty)
                                  (.leaf ⟨23, by decide⟩)))))
                          (.splitR (79375 / 76832)
                            (.splitU (11 / 256)
                              (.leaf ⟨94, by decide⟩)
                              (.leaf ⟨111, by decide⟩))
                            (.splitU (11 / 256)
                              (.splitR (159375 / 153664)
                                (.leaf ⟨28, by decide⟩)
                                (.splitU (21 / 512)
                                  (.leaf ⟨64, by decide⟩)
                                  (.leaf ⟨88, by decide⟩)))
                              (.leaf ⟨13, by decide⟩)))))
                      (.splitR (5625 / 5488)
                        (.splitU (7 / 128)
                          (.leaf ⟨119, by decide⟩)
                          (.leaf ⟨133, by decide⟩))
                        (.splitU (7 / 128)
                          (.splitR (79375 / 76832)
                            (.leaf ⟨96, by decide⟩)
                            (.splitU (13 / 256)
                              (.leaf ⟨99, by decide⟩)
                              (.leaf ⟨116, by decide⟩)))
                          (.leaf ⟨106, by decide⟩)))))))
              (.splitR (9375 / 9604)
                (.splitU (3 / 32)
                  (.leaf ⟨138, by decide⟩)
                  (.leaf ⟨161, by decide⟩))
                (.splitU (3 / 32)
                  (.splitR (19375 / 19208)
                    (.leaf ⟨35, by decide⟩)
                    (.splitU (5 / 64)
                      (.leaf ⟨22, by decide⟩)
                      (.leaf ⟨129, by decide⟩)))
                  (.leaf ⟨102, by decide⟩)))))
          (.splitR (625 / 686)
            (.splitU (3 / 16)
              (.leaf ⟨166, by decide⟩)
              (.leaf ⟨176, by decide⟩))
            (.splitU (3 / 16)
              (.splitR (9375 / 9604)
                (.leaf ⟨146, by decide⟩)
                (.splitU (5 / 32)
                  (.leaf ⟨145, by decide⟩)
                  (.leaf ⟨159, by decide⟩)))
              (.leaf ⟨127, by decide⟩)))))
      (.splitR (1875 / 2401)
        (.splitU (3 / 8)
          (.splitR (3125 / 4802)
            (.leaf ⟨105, by decide⟩)
            (.leaf ⟨157, by decide⟩))
          (.splitR (3125 / 4802)
            (.splitU (7 / 16)
              (.leaf ⟨144, by decide⟩)
              (.splitR (5625 / 9604)
                (.leaf ⟨130, by decide⟩)
                (.leaf ⟨169, by decide⟩)))
            (.splitU (7 / 16)
              (.leaf ⟨174, by decide⟩)
              (.leaf ⟨153, by decide⟩))))
        (.splitU (3 / 8)
          (.splitR (625 / 686)
            (.leaf ⟨89, by decide⟩)
            (.splitU (5 / 16)
              (.leaf ⟨142, by decide⟩)
              (.leaf ⟨139, by decide⟩)))
          (.splitR (625 / 686)
            (.splitU (7 / 16)
              (.leaf ⟨167, by decide⟩)
              (.leaf ⟨150, by decide⟩))
            (.splitU (7 / 16)
              (.leaf ⟨122, by decide⟩)
              (.splitR (9375 / 9604)
                (.leaf ⟨152, by decide⟩)
                (.leaf ⟨97, by decide⟩)))))))

set_option maxRecDepth 100000 in
private theorem rootTree_valid : rootTree.Valid rootBox := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem rootTree_indices_complete :
    rootTree.leafIndices.length = 188 ∧
      rootTree.leafIndices.Nodup := by
  decide +kernel

theorem exists_cover_cell (u r B : ℝ)
    (huZero : 0 ≤ u) (huHalf : u ≤ 1 / 2)
    (hrZero : 0 ≤ r) (hrUpper : r ≤ 2500 / 2401)
    (hrFeasible : r ≤ 1 + u) (hBtwo : 2 ≤ B)
    (hrModulus : 9 * r ≤ B ^ 2) :
    ∃ entry : Entry,
      entry.cell.Valid ∧
      (entry.cell.lower : ℝ) ≤ u ∧
      u ≤ (entry.cell.upper : ℝ) ∧
      r ≤ (entry.cell.thresholdUpper : ℝ) ∧
      (entry.cell.modulusLower : ℝ) ≤ B ∧
      thresholdDominantCellMajorant entry.cell.decode <
        (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) := by
  apply rootTree.sound rootBox rootTree_valid
    (fun cell => thresholdDominantCellMajorant cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ))) entryAt_bound u r B
  · simpa [rootBox] using huZero
  · simpa [rootBox] using huHalf
  · simpa [rootBox] using hrZero
  · simpa [rootBox] using hrUpper
  · exact hrFeasible
  · exact hBtwo
  · exact hrModulus

/-- Reuse the exact no-gap geometry tree with a target-dependent semantic
bound proved for every inherited cell. -/
theorem exists_cover_cell_at (rows squaredNormFloor : ℕ) (budget : ℚ)
    (hbound : ∀ entry ∈ ConstantDirectCover128Shard46.allEntries,
      thresholdDominantCellMajorantAt rows squaredNormFloor
          (entry.cell.decodeAt rows) < (budget : ℝ))
    (u r B : ℝ)
    (huZero : 0 ≤ u) (huHalf : u ≤ 1 / 2)
    (hrZero : 0 ≤ r) (hrUpper : r ≤ 2500 / 2401)
    (hrFeasible : r ≤ 1 + u) (hBtwo : 2 ≤ B)
    (hrModulus : 9 * r ≤ B ^ 2) :
    ∃ entry : Entry,
      entry.cell.Valid ∧
      (entry.cell.lower : ℝ) ≤ u ∧
      u ≤ (entry.cell.upper : ℝ) ∧
      r ≤ (entry.cell.thresholdUpper : ℝ) ∧
      (entry.cell.modulusLower : ℝ) ≤ B ∧
      thresholdDominantCellMajorantAt rows squaredNormFloor
        (entry.cell.decodeAt rows) < (budget : ℝ) := by
  apply rootTree.sound rootBox rootTree_valid
    (fun cell => thresholdDominantCellMajorantAt rows squaredNormFloor
      (cell.decodeAt rows) < (budget : ℝ))
    (fun index => hbound (entryAt index) (entryAt_mem index)) u r B
  · simpa [rootBox] using huZero
  · simpa [rootBox] using huHalf
  · simpa [rootBox] using hrZero
  · simpa [rootBox] using hrUpper
  · exact hrFeasible
  · exact hBtwo
  · exact hrModulus

/-- Reuse the exact no-gap geometry tree with an arbitrary semantic property
proved for every inherited cell. This supports target-specific tilt changes
and local cell refinements without duplicating the selector tree. -/
theorem exists_cover_cell_of_property (P : Cell → Prop)
    (hproperty : ∀ entry ∈ ConstantDirectCover128Shard46.allEntries,
      P entry.cell)
    (u r B : ℝ)
    (huZero : 0 ≤ u) (huHalf : u ≤ 1 / 2)
    (hrZero : 0 ≤ r) (hrUpper : r ≤ 2500 / 2401)
    (hrFeasible : r ≤ 1 + u) (hBtwo : 2 ≤ B)
    (hrModulus : 9 * r ≤ B ^ 2) :
    ∃ entry : Entry,
      entry.cell.Valid ∧
      (entry.cell.lower : ℝ) ≤ u ∧
      u ≤ (entry.cell.upper : ℝ) ∧
      r ≤ (entry.cell.thresholdUpper : ℝ) ∧
      (entry.cell.modulusLower : ℝ) ≤ B ∧
      P entry.cell := by
  apply rootTree.sound rootBox rootTree_valid P
    (fun index => hproperty (entryAt index) (entryAt_mem index)) u r B
  · simpa [rootBox] using huZero
  · simpa [rootBox] using huHalf
  · simpa [rootBox] using hrZero
  · simpa [rootBox] using hrUpper
  · exact hrFeasible
  · exact hBtwo
  · exact hrModulus

end ConstantDirectCover128Selector
end SparseThresholdDominant
end CertifiedJL
