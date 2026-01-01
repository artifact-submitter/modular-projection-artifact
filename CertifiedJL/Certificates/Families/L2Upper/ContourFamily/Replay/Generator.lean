/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Numeric.Core

/-!
# Generated replay scaffolding for upper-contour family instances

An instance-specific executable supplies the names and values exported by its
Lean module.  This generator then emits:

* raw interval endpoints for each profile box;
* bounded `decide +kernel` replay shards, each confined to one profile box;
* one checked assembly module per box;
* a root module identifying the complete list of verified endpoints; and
* optional high-profile and full analytic `CheckedCertificate` assemblies.

The cell count per theorem is the `ProfileBox.chunkSize` chosen by the
instance.  `Output.chunksPerShard` partitions the consecutive chunk plan of
each box, allowing one replay module to cross segment boundaries but never a
box boundary.  The theorem names retain their segment and segment-local chunk
indices.  No row count, threshold, security exponent, profile partition, or
chunk topology is fixed here.
-/

namespace CertifiedJL.SparseUpperContourFamily.Generator

/-- Names of semantic proofs exported by an instance's analytic soundness module. -/
structure SoundnessSource where
  moduleName : String
  namespaceName : String
  profileCoverName : String := "profileCover"
  lowTargetsName : String := "lowTargets"
  highTargetName : String := "highTarget"
  lowSoundName : String := "lowSound"
  highSoundName : String := "highSound"
  thresholdName : Option String := none
  thresholdEqualityName : Option String := none

/-- Values imported from the instance module, together with their source names. -/
structure SourceInstance where
  moduleName : String
  namespaceName : String
  parametersName : String := "parameters"
  boxesName : String := "profileBoxes"
  highProfileName : Option String := none
  parameters : Parameters
  boxes : List ProfileBox
  highProfile : Option HighProfileBox := none
  soundness : Option SoundnessSource := none

/-- Output location and namespace for one generated replay family. -/
structure Output where
  dataDirectory : String
  replayDirectory : String
  dataModulePrefix : String
  replayModulePrefix : String
  dataNamespace : String
  replayNamespace : String
  generatorRevision : String
  chunksPerShard : ℕ := 1

/-- Complete generator configuration. -/
structure Configuration where
  source : SourceInstance
  output : Output

/-- Lightweight generated-file topology, computed without evaluating any
quadrature cells or interval endpoints. -/
structure Topology where
  boxCount : ℕ
  cellCount : ℕ
  chunkCount : ℕ
  replayShardCount : ℕ
  moduleCount : ℕ
deriving DecidableEq, Repr

private def copyrightHeader : String :=
  "/-\n" ++
  "Copyright (c) 2026 Anonymous Author. All rights reserved.\n" ++
  "Released under Apache 2.0 license as described in the file LICENSE.\n" ++
  "Authors: Anonymous Author\n" ++
  "-/\n\n"

private def pad (width n : ℕ) : String :=
  let digits := toString n
  String.ofList (List.replicate (width - digits.length) '0') ++ digits

private def pad2 (n : ℕ) : String := pad 2 n
private def pad3 (n : ℕ) : String := pad 3 n

private def qualified (namespaceName definitionName : String) : String :=
  namespaceName ++ "." ++ definitionName

private def parametersRef (configuration : Configuration) : String :=
  qualified configuration.source.namespaceName configuration.source.parametersName

private def boxesRef (configuration : Configuration) : String :=
  qualified configuration.source.namespaceName configuration.source.boxesName

private def highProfileRef (configuration : Configuration) : Option String :=
  configuration.source.highProfileName.map
    (qualified configuration.source.namespaceName)

private def boxRef (configuration : Configuration) (boxIndex : ℕ) : String :=
  s!"(({boxesRef configuration}).getD {boxIndex} default)"

private def intervalLiteral {precision : ℕ}
    (interval : UpperContourKernel.DInterval precision) : String :=
  s!"⟨{interval.lo},\n      {interval.hi}⟩"

private def chunkLiteral (chunk : Chunk) : String :=
  s!"⟨{chunk.segmentIndex}, {chunk.start}, {chunk.count}⟩"

private def boxDataPath (configuration : Configuration) (boxIndex : ℕ) : String :=
  s!"{configuration.output.dataDirectory}/Box{pad2 boxIndex}.lean"

private def dataPath (configuration : Configuration) : String :=
  s!"{configuration.output.dataDirectory}/Data.lean"

private def replayPath (configuration : Configuration) (boxIndex shardIndex : ℕ) : String :=
  s!"{configuration.output.replayDirectory}/Box{pad2 boxIndex}/" ++
    s!"Shard{pad3 shardIndex}.lean"

private def verifiedBoxPath (configuration : Configuration)
    (boxIndex : ℕ) : String :=
  s!"{configuration.output.replayDirectory}/Verified/Box{pad2 boxIndex}.lean"

private def highProfilePath (configuration : Configuration) : String :=
  s!"{configuration.output.replayDirectory}/HighProfile.lean"

private def certificatePath (configuration : Configuration) : String :=
  s!"{configuration.output.replayDirectory}/Certificate.lean"

private def verifiedPath (configuration : Configuration) : String :=
  s!"{configuration.output.replayDirectory}/Verified.lean"

private def dataBoxModule (configuration : Configuration) (boxIndex : ℕ) : String :=
  s!"{configuration.output.dataModulePrefix}.Box{pad2 boxIndex}"

private def replayModule (configuration : Configuration) (boxIndex shardIndex : ℕ) : String :=
  s!"{configuration.output.replayModulePrefix}.Box{pad2 boxIndex}." ++
    s!"Shard{pad3 shardIndex}"

private def verifiedBoxModule (configuration : Configuration)
    (boxIndex : ℕ) : String :=
  s!"{configuration.output.replayModulePrefix}.Verified.Box{pad2 boxIndex}"

private def chunksInSegment (box : ProfileBox) (segmentIndex : ℕ) : List Chunk :=
  let segment := box.segments.getD segmentIndex default
  chunksForSegment box.chunkSize segmentIndex segment.count

private structure IndexedChunk where
  segmentIndex : ℕ
  chunkIndex : ℕ
  chunk : Chunk

private def indexedChunksInSegment (box : ProfileBox) (segmentIndex : ℕ) :
    List IndexedChunk :=
  (chunksInSegment box segmentIndex).zipIdx.map fun pair =>
    { segmentIndex := segmentIndex
      chunkIndex := pair.2
      chunk := pair.1 }

/-- Chunks in exact certificate order, with stable segment-local identities. -/
private def indexedChunksInBox (box : ProfileBox) : List IndexedChunk :=
  box.segments.zipIdx.flatMap fun pair =>
    indexedChunksInSegment box pair.2

private def replayShardCountForBox (configuration : Configuration)
    (box : ProfileBox) : ℕ :=
  let count := (indexedChunksInBox box).length
  (count + configuration.output.chunksPerShard - 1) /
    configuration.output.chunksPerShard

private def indexedChunksInShard (configuration : Configuration)
    (box : ProfileBox) (shardIndex : ℕ) : List IndexedChunk :=
  let start := configuration.output.chunksPerShard * shardIndex
  (indexedChunksInBox box).drop start |>.take configuration.output.chunksPerShard

private def chunkValue (configuration : Configuration) (boxIndex : ℕ)
    (chunk : Chunk) : UpperContourKernel.DInterval configuration.source.parameters.precision :=
  let box := configuration.source.boxes.getD boxIndex default
  boxChunkValue configuration.source.parameters box chunk

private def boxChunks (configuration : Configuration) (boxIndex : ℕ) :
    List (UpperContourKernel.DInterval configuration.source.parameters.precision) :=
  let box := configuration.source.boxes.getD boxIndex default
  boxComputedChunks configuration.source.parameters box

private def boxExpectedBound (configuration : Configuration) (boxIndex : ℕ) :
    UpperContourKernel.DInterval configuration.source.parameters.precision :=
  let box := configuration.source.boxes.getD boxIndex default
  boxPrefactor configuration.source.parameters box *
    boxIntegralFrom configuration.source.parameters box
      (boxChunks configuration boxIndex)

private def listLiteral (entries : List String) : String :=
  "[\n    " ++ String.intercalate ",\n    " entries ++ "\n  ]"

private def boxDataSource (configuration : Configuration) (boxIndex : ℕ) : String :=
  let chunks := boxChunks configuration boxIndex
  let bound := boxExpectedBound configuration boxIndex
  copyrightHeader ++
  s!"import {configuration.source.moduleName}\n" ++
  "import CertifiedJL.Arithmetic.Interval.Interval\n\n" ++
  s!"/-! Raw generated endpoints for upper-contour family box {boxIndex}. -/\n\n" ++
  s!"namespace {configuration.output.dataNamespace}.Box{pad2 boxIndex}\n\n" ++
  "set_option linter.style.longLine false\n\n" ++
  s!"def chunks : List (Interval ({parametersRef configuration}).precision) :=\n  " ++
  listLiteral (chunks.map intervalLiteral) ++ "\n\n" ++
  s!"def expectedBound : Interval ({parametersRef configuration}).precision :=\n  " ++
  intervalLiteral bound ++ "\n\n" ++
  s!"end {configuration.output.dataNamespace}.Box{pad2 boxIndex}\n"

private def dataImports (configuration : Configuration) : String :=
  String.join <| (List.range configuration.source.boxes.length).map fun boxIndex =>
    s!"import {dataBoxModule configuration boxIndex}\n"

private def dataSource (configuration : Configuration) : String :=
  let boxCount := configuration.source.boxes.length
  let chunkCounts := (List.range boxCount).map fun boxIndex =>
    (boxChunks configuration boxIndex).length
  copyrightHeader ++ dataImports configuration ++ "\n" ++
  "/-! Untrusted generated endpoints; `Verified` replays every chunk in the kernel. -/\n\n" ++
  s!"namespace {configuration.output.dataNamespace}.Data\n\n" ++
  "set_option linter.style.longLine false\n\n" ++
  s!"def generatorRevision : String := \"{configuration.output.generatorRevision}\"\n" ++
  s!"def precision : ℕ := ({parametersRef configuration}).precision\n" ++
  s!"def rows : ℕ := ({parametersRef configuration}).rows\n" ++
  s!"def securityBits : ℕ := ({parametersRef configuration}).securityBits\n" ++
  s!"def threshold : ℚ := ({parametersRef configuration}).threshold\n" ++
  s!"def boxCount : ℕ := {boxCount}\n" ++
  "def chunkCounts : List ℕ := " ++ listLiteral (chunkCounts.map toString) ++ "\n\n" ++
  "def chunks : List (List (Interval precision)) :=\n  " ++
  listLiteral ((List.range boxCount).map fun boxIndex =>
    s!"Box{pad2 boxIndex}.chunks") ++ "\n\n" ++
  "def expectedBounds : List (Interval precision) :=\n  " ++
  listLiteral ((List.range boxCount).map fun boxIndex =>
    s!"Box{pad2 boxIndex}.expectedBound") ++ "\n\n" ++
  s!"end {configuration.output.dataNamespace}.Data\n"

private def replayTheoremName (boxIndex segmentIndex chunkIndex : ℕ) : String :=
  s!"box_{pad2 boxIndex}_segment_{pad2 segmentIndex}_chunk_{pad3 chunkIndex}"

private def replayChunkTheorem (configuration : Configuration) (boxIndex : ℕ)
    (indexedChunk : IndexedChunk) : String :=
  let value := chunkValue configuration boxIndex indexedChunk.chunk
  s!"theorem {replayTheoremName boxIndex indexedChunk.segmentIndex indexedChunk.chunkIndex} :\n" ++
  s!"    boxChunkValue {parametersRef configuration} {boxRef configuration boxIndex}\n" ++
  s!"      {chunkLiteral indexedChunk.chunk} =\n      {intervalLiteral value} := by\n" ++
  "  decide +kernel\n"

private def replaySource (configuration : Configuration) (boxIndex shardIndex : ℕ) : String :=
  let box := configuration.source.boxes.getD boxIndex default
  let chunks := indexedChunksInShard configuration box shardIndex
  let theorems := chunks.map fun chunk =>
    replayChunkTheorem configuration boxIndex chunk
  copyrightHeader ++
  s!"import {configuration.source.moduleName}\n\n" ++
  s!"/-! Kernel replay shard {shardIndex} for box {boxIndex}.\n\n" ++
  "The shard may cross segment boundaries, while theorem names retain\n" ++
  "segment-local identities. -/\n\n" ++
  s!"namespace {configuration.output.replayNamespace}\n\n" ++
  "open CertifiedJL.SparseUpperContourFamily\n\n" ++
  "set_option linter.style.longLine false\n\n" ++
  String.intercalate "\n" theorems ++ "\n\n" ++
  s!"end {configuration.output.replayNamespace}\n"

private def replayImportsForBox (configuration : Configuration)
    (boxIndex : ℕ) : String :=
  let box := configuration.source.boxes.getD boxIndex default
  String.join <| (List.range (replayShardCountForBox configuration box)).map
    fun shardIndex => s!"import {replayModule configuration boxIndex shardIndex}\n"

private def computedChunkEntries (configuration : Configuration)
    (boxIndex : ℕ) : List String :=
  let box := configuration.source.boxes.getD boxIndex default
  (boxChunkPlan box).map fun chunk =>
    s!"boxChunkValue {parametersRef configuration} {boxRef configuration boxIndex} " ++
      chunkLiteral chunk

private def replayTheoremNames (configuration : Configuration)
    (boxIndex : ℕ) : List String :=
  let box := configuration.source.boxes.getD boxIndex default
  (indexedChunksInBox box).map fun chunk =>
    s!"{configuration.output.replayNamespace}." ++
      replayTheoremName boxIndex chunk.segmentIndex chunk.chunkIndex

private def verifiedBoxSource (configuration : Configuration) (boxIndex : ℕ) : String :=
  let boxName := s!"box{pad2 boxIndex}"
  let dataName := s!"{configuration.output.dataNamespace}.Box{pad2 boxIndex}"
  let replayNames := replayTheoremNames configuration boxIndex
  copyrightHeader ++
  s!"import {dataBoxModule configuration boxIndex}\n" ++
  replayImportsForBox configuration boxIndex ++ "\n" ++
  s!"/-! Kernel-checked assembly of upper-contour family box {boxIndex}. -/\n\n" ++
  s!"namespace {configuration.output.replayNamespace}.Verified\n\n" ++
  "open CertifiedJL.SparseUpperContourFamily\n\n" ++
  "set_option linter.style.longLine false\n\n" ++
  s!"private def {boxName}EnumeratedComputedChunks :\n" ++
  s!"    List (UpperContourKernel.DInterval ({parametersRef configuration}).precision) :=\n  " ++
  listLiteral (computedChunkEntries configuration boxIndex) ++ "\n\n" ++
  s!"private theorem {boxName}ComputedChunks_eq_enumerated :\n" ++
  s!"    boxComputedChunks {parametersRef configuration} {boxRef configuration boxIndex} =\n" ++
  s!"      {boxName}EnumeratedComputedChunks := by\n  rfl\n\n" ++
  s!"private theorem {boxName}EnumeratedComputedChunks_eq_generated :\n" ++
  s!"    {boxName}EnumeratedComputedChunks = {dataName}.chunks := by\n" ++
  s!"  simp only [{boxName}EnumeratedComputedChunks, {dataName}.chunks" ++
  (if replayNames.isEmpty then "" else ",\n    " ++ String.intercalate ",\n    " replayNames) ++
  "]\n\n" ++
  s!"theorem {boxName}ComputedChunks_eq_generated :\n" ++
  s!"    boxComputedChunks {parametersRef configuration} {boxRef configuration boxIndex} =\n" ++
  s!"      {dataName}.chunks :=\n" ++
  s!"  {boxName}ComputedChunks_eq_enumerated.trans\n" ++
  s!"    {boxName}EnumeratedComputedChunks_eq_generated\n\n" ++
  s!"private theorem {boxName}GeneratedBound_eq_expected :\n" ++
  s!"    boxPrefactor {parametersRef configuration} {boxRef configuration boxIndex} *\n" ++
  s!"      boxIntegralFrom {parametersRef configuration} {boxRef configuration boxIndex}\n" ++
  s!"        {dataName}.chunks = {dataName}.expectedBound := by\n" ++
  "  decide +kernel\n\n" ++
  s!"theorem {boxName}Bound_eq_expected :\n" ++
  s!"    boxBound {parametersRef configuration} {boxRef configuration boxIndex} =\n" ++
  s!"      {dataName}.expectedBound := by\n" ++
  s!"  simp only [boxBound, boxIntegral, {boxName}ComputedChunks_eq_generated]\n" ++
  s!"  exact {boxName}GeneratedBound_eq_expected\n\n" ++
  s!"private theorem {boxName}ExpectedCheck_eq_true :\n" ++
  s!"    Interval.upperLTCheck {dataName}.expectedBound\n" ++
  s!"      ({boxRef configuration boxIndex}).target = true := by\n" ++
  "  decide +kernel\n\n" ++
  s!"theorem {boxName}Check_eq_true :\n" ++
  s!"    boxCheck {parametersRef configuration} {boxRef configuration boxIndex} = true := by\n" ++
  s!"  rw [boxCheck, {boxName}Bound_eq_expected]\n" ++
  s!"  exact {boxName}ExpectedCheck_eq_true\n\n" ++
  s!"theorem {boxName}_upperRat_lt :\n" ++
  s!"    (boxBound {parametersRef configuration} {boxRef configuration boxIndex}).upperRat <\n" ++
  s!"      ({boxRef configuration boxIndex}).target :=\n" ++
  s!"  Interval.upperLTCheck_sound {boxName}Check_eq_true\n\n" ++
  s!"end {configuration.output.replayNamespace}.Verified\n"

private def highProfileSource (configuration : Configuration)
    (name : String) (box : HighProfileBox) : String :=
  let bound := highProfileBound configuration.source.parameters box
  let dataName := s!"{configuration.output.replayNamespace}.HighProfile"
  copyrightHeader ++
  s!"import {configuration.source.moduleName}\n\n" ++
  "/-! Independent kernel replay of the high-profile endpoint. -/\n\n" ++
  s!"namespace {dataName}\n\n" ++
  "open CertifiedJL.SparseUpperContourFamily\n\n" ++
  "set_option linter.style.longLine false\n\n" ++
  s!"def expectedBound : Interval ({parametersRef configuration}).precision :=\n  " ++
  intervalLiteral bound ++ "\n\n" ++
  "theorem bound_eq_expected :\n" ++
  s!"    highProfileBound {parametersRef configuration} {name} = expectedBound := by\n" ++
  "  decide +kernel\n\n" ++
  "private theorem expectedCheck_eq_true :\n" ++
  s!"    Interval.upperLTCheck expectedBound {name}.target = true := by\n" ++
  "  decide +kernel\n\n" ++
  "theorem check_eq_true :\n" ++
  s!"    highProfileCheck {parametersRef configuration} {name} = true := by\n" ++
  "  rw [highProfileCheck, bound_eq_expected]\n" ++
  "  exact expectedCheck_eq_true\n\n" ++
  "theorem upperRat_lt :\n" ++
  s!"    (highProfileBound {parametersRef configuration} {name}).upperRat < {name}.target :=\n" ++
  "  Interval.upperLTCheck_sound check_eq_true\n\n" ++
  s!"end {dataName}\n"

private def certificateSource (configuration : Configuration)
    (soundness : SoundnessSource) (highProfileName : String) : String :=
  let certificateName := s!"{configuration.output.replayNamespace}.Certificate"
  let verifiedName := s!"{configuration.output.replayNamespace}.Verified"
  let sourceRef (name : String) := qualified soundness.namespaceName name
  let highName := qualified configuration.source.namespaceName highProfileName
  let publicTheorem := match soundness.thresholdName,
      soundness.thresholdEqualityName with
    | some thresholdName, some equalityName =>
        "theorem l2UpperTail :\n" ++
        "    L2UpperTailAt\n" ++
        "      { distribution := .balancedTernary\n" ++
        s!"        rows := ({parametersRef configuration}).rows\n" ++
        s!"        threshold := {sourceRef thresholdName} }\n" ++
        s!"      (failureTarget ({parametersRef configuration}).securityBits) :=\n" ++
        "  l2UpperTailAt_of_checkedCertificate checkedCertificate\n" ++
        s!"    {sourceRef thresholdName} {sourceRef equalityName}\n\n"
    | _, _ => ""
  copyrightHeader ++
  "import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Soundness.Soundness\n" ++
  s!"import {soundness.moduleName}\n" ++
  s!"import {configuration.output.replayModulePrefix}.Verified\n\n" ++
  "/-! Checked numeric and analytic assembly for one upper-contour instance. -/\n\n" ++
  s!"namespace {certificateName}\n\n" ++
  "open CertifiedJL.SparseUpperContourFamily\n\n" ++
  "set_option linter.style.longLine false\n\n" ++
  "def checkedCertificate : CheckedCertificate " ++ parametersRef configuration ++ " where\n" ++
  s!"  lowBoxes := {boxesRef configuration}\n" ++
  s!"  highBox := {highName}\n" ++
  s!"  profileCover := {sourceRef soundness.profileCoverName}\n" ++
  s!"  lowTargets := {sourceRef soundness.lowTargetsName}\n" ++
  s!"  highTarget := {sourceRef soundness.highTargetName}\n" ++
  s!"  lowChecks := {verifiedName}.allBoxesCheck_eq_true\n" ++
  s!"  highCheck := {verifiedName}.highProfileCheck_eq_true\n" ++
  s!"  lowSound := {sourceRef soundness.lowSoundName}\n" ++
  s!"  highSound := {sourceRef soundness.highSoundName}\n\n" ++
  "theorem normalizedUpperTail :\n" ++
  s!"    NormalizedUpperTailAt {parametersRef configuration} :=\n" ++
  "  normalizedUpperTail_of_checkedCertificate checkedCertificate\n\n" ++
  publicTheorem ++
  s!"end {certificateName}\n"

private def verifiedImports (configuration : Configuration) : String :=
  String.join <| (List.range configuration.source.boxes.length).map fun boxIndex =>
    s!"import {verifiedBoxModule configuration boxIndex}\n"

private def boundTheoremNames (configuration : Configuration) : List String :=
  (List.range configuration.source.boxes.length).map fun boxIndex =>
    s!"{configuration.output.replayNamespace}.Verified.box{pad2 boxIndex}Bound_eq_expected"

private def checkTheoremNames (configuration : Configuration) : List String :=
  (List.range configuration.source.boxes.length).map fun boxIndex =>
    s!"{configuration.output.replayNamespace}.Verified.box{pad2 boxIndex}Check_eq_true"

private def verifiedSource (configuration : Configuration) : String :=
  let boxCount := configuration.source.boxes.length
  let dataName := configuration.output.dataNamespace
  let aggregateDataName := s!"{dataName}.Data"
  let verifiedName := s!"{configuration.output.replayNamespace}.Verified"
  let boxBounds := (List.range boxCount).map fun boxIndex =>
    s!"boxBound {parametersRef configuration} {boxRef configuration boxIndex}"
  let boxChecks := (List.range boxCount).map fun boxIndex =>
    s!"boxCheck {parametersRef configuration} {boxRef configuration boxIndex}"
  let upperTheorems := (List.range boxCount).map fun boxIndex =>
    s!"box{pad2 boxIndex}_upperRat_lt"
  let highProfileBlock := match highProfileRef configuration with
    | none => ""
    | some name =>
        "theorem highProfileCheck_eq_true :\n" ++
        s!"    highProfileCheck {parametersRef configuration} {name} = true :=\n" ++
        s!"  {configuration.output.replayNamespace}.HighProfile.check_eq_true\n\n" ++
        "theorem highProfile_upperRat_lt :\n" ++
        s!"    (highProfileBound {parametersRef configuration} {name}).upperRat <\n" ++
        s!"      {name}.target :=\n" ++
        s!"  {configuration.output.replayNamespace}.HighProfile.upperRat_lt\n\n"
  copyrightHeader ++
  s!"import {configuration.output.dataModulePrefix}.Data\n" ++
  verifiedImports configuration ++
  (if configuration.source.highProfile.isSome then
    s!"import {configuration.output.replayModulePrefix}.HighProfile\n" else "") ++ "\n" ++
  "/-! Aggregate kernel-verified endpoints for one upper-contour family instance. -/\n\n" ++
  s!"namespace {verifiedName}\n\n" ++
  "open CertifiedJL.SparseUpperContourFamily\n\n" ++
  "set_option linter.style.longLine false\n\n" ++
  "def verifiedEndpoints :\n" ++
  s!"    List (UpperContourKernel.DInterval ({parametersRef configuration}).precision) :=\n" ++
  s!"  {aggregateDataName}.expectedBounds\n\n" ++
  "theorem boxBounds_eq_verifiedEndpoints :\n" ++
  s!"    ({boxesRef configuration}).map (boxBound {parametersRef configuration}) =\n" ++
  "      verifiedEndpoints := by\n" ++
  "  change " ++ listLiteral boxBounds ++ " = " ++
  listLiteral ((List.range boxCount).map fun boxIndex =>
    s!"{dataName}.Box{pad2 boxIndex}.expectedBound") ++ "\n" ++
  (if boxCount = 0 then "  rfl\n\n" else
    "  rw [" ++ String.intercalate ",\n    " (boundTheoremNames configuration) ++ "]\n\n") ++
  "theorem allBoxesCheck_eq_true :\n" ++
  s!"    allBoxesCheck {parametersRef configuration} {boxesRef configuration} = true := by\n" ++
  "  change (" ++ listLiteral boxChecks ++ ").all id = true\n" ++
  (if boxCount = 0 then "  rfl\n\n" else
    "  simp only [" ++ String.intercalate ",\n    " (checkTheoremNames configuration) ++ "]\n" ++
    "  rfl\n\n") ++
  "theorem box_upperRat_lt_target {box : ProfileBox}\n" ++
  s!"    (hbox : box ∈ {boxesRef configuration}) :\n" ++
  s!"    (boxBound {parametersRef configuration} box).upperRat < box.target := by\n" ++
  (if boxCount = 0 then
    s!"  simpa [{boxesRef configuration}] at hbox\n\n"
  else
    s!"  simp only [{boxesRef configuration}, List.mem_cons, List.not_mem_nil,\n" ++
    "    or_false] at hbox\n" ++
    "  rcases hbox with " ++ String.intercalate " | " (List.replicate boxCount "rfl") ++ "\n" ++
    String.join ((List.range boxCount).map fun boxIndex =>
      let theoremName := upperTheorems.getD boxIndex ""
      s!"  · simpa [{boxesRef configuration}] using {theoremName}\n") ++ "\n") ++
  highProfileBlock ++
  s!"end {verifiedName}\n"

private def replaySources (configuration : Configuration) : List (String × String) :=
  configuration.source.boxes.zipIdx.flatMap fun boxPair =>
    let box := boxPair.1
    let boxIndex := boxPair.2
    (List.range (replayShardCountForBox configuration box)).map fun shardIndex =>
      (replayPath configuration boxIndex shardIndex,
        replaySource configuration boxIndex shardIndex)

/-- Count the generated topology without computing numeric endpoint source. -/
def topology (configuration : Configuration) : Topology :=
  let boxes := configuration.source.boxes
  let boxCount := boxes.length
  let cellCount := (boxes.map fun box ↦
    (box.segments.map Segment.count).sum).sum
  let chunkCount := (boxes.map fun box ↦ (boxChunkPlan box).length).sum
  let replayShardCount :=
    (boxes.map (replayShardCountForBox configuration)).sum
  let highProfileModuleCount :=
    if configuration.source.highProfile.isSome then 1 else 0
  let certificateModuleCount :=
    if configuration.source.soundness.isSome &&
        configuration.source.highProfileName.isSome then 1 else 0
  { boxCount := boxCount
    cellCount := cellCount
    chunkCount := chunkCount
    replayShardCount := replayShardCount
    moduleCount := 2 * boxCount + replayShardCount + 2 +
      highProfileModuleCount + certificateModuleCount }

/-- Complete list of generated paths and their deterministic source text. -/
def sources (configuration : Configuration) : List (String × String) :=
  let boxCount := configuration.source.boxes.length
  let boxData := (List.range boxCount).map fun boxIndex =>
    (boxDataPath configuration boxIndex, boxDataSource configuration boxIndex)
  let verifiedBoxes := (List.range boxCount).map fun boxIndex =>
    (verifiedBoxPath configuration boxIndex, verifiedBoxSource configuration boxIndex)
  let highProfile := match configuration.source.highProfileName,
      configuration.source.highProfile with
    | some name, some box => [(highProfilePath configuration,
        highProfileSource configuration
          (qualified configuration.source.namespaceName name) box)]
    | _, _ => []
  let certificate := match configuration.source.soundness,
      configuration.source.highProfileName with
    | some soundness, some highProfileName =>
        [(certificatePath configuration,
          certificateSource configuration soundness highProfileName)]
    | _, _ => []
  boxData ++ [(dataPath configuration, dataSource configuration)] ++
    replaySources configuration ++ verifiedBoxes ++ highProfile ++ certificate ++
    [(verifiedPath configuration, verifiedSource configuration)]

private def validate (configuration : Configuration) : IO Unit := do
  if configuration.source.moduleName.isEmpty then
    throw <| IO.userError "source module name must be nonempty"
  if configuration.source.namespaceName.isEmpty then
    throw <| IO.userError "source namespace must be nonempty"
  if configuration.output.dataDirectory.isEmpty || configuration.output.replayDirectory.isEmpty then
    throw <| IO.userError "output directories must be nonempty"
  if configuration.output.dataModulePrefix.isEmpty ||
      configuration.output.replayModulePrefix.isEmpty then
    throw <| IO.userError "output module prefixes must be nonempty"
  if configuration.output.dataNamespace.isEmpty ||
      configuration.output.replayNamespace.isEmpty then
    throw <| IO.userError "output namespaces must be nonempty"
  if configuration.output.chunksPerShard = 0 then
    throw <| IO.userError "chunksPerShard must be positive"
  for box in configuration.source.boxes do
    if box.chunkSize = 0 then
      throw <| IO.userError "every profile box must have positive chunkSize"
  unless configuration.source.highProfileName.isSome =
      configuration.source.highProfile.isSome do
    throw <| IO.userError
      "highProfileName and highProfile must either both be present or both be absent"
  if configuration.source.soundness.isSome &&
      configuration.source.highProfile.isNone then
    throw <| IO.userError
      "a checked soundness certificate requires a high-profile box"
  if let some soundness := configuration.source.soundness then
    unless soundness.thresholdName.isSome =
        soundness.thresholdEqualityName.isSome do
      throw <| IO.userError
        "thresholdName and thresholdEqualityName must either both be present or both be absent"

private def writeSource (path source : String) : IO Unit := do
  let filePath : System.FilePath := path
  if let some parent := filePath.parent then
    IO.FS.createDirAll parent
  IO.FS.writeFile filePath source

private def pruneStaleLeanSources (configuration : Configuration) : IO Unit := do
  let expectedPaths := (sources configuration).map Prod.fst
  for directory in [configuration.output.dataDirectory,
      configuration.output.replayDirectory] do
    let outputPath : System.FilePath := directory
    if ← outputPath.pathExists then
      let walked ← outputPath.walkDir
      for path in walked do
        if path.toString.endsWith ".lean" &&
            !(expectedPaths.contains path.toString) then
          IO.FS.removeFile path

/-- Generate every raw endpoint, bounded replay file, and checked assembly. -/
def generateAll (configuration : Configuration) : IO Unit := do
  validate configuration
  pruneStaleLeanSources configuration
  for (path, source) in sources configuration do
    writeSource path source
  IO.println s!"generated {sources configuration |>.length} upper-contour family modules"

private def checkSource (path expected : String) : IO Unit := do
  let actual ← IO.FS.readFile path
  unless actual == expected do
    throw <| IO.userError s!"generated source differs: {path}"

/-- Check every expected generated file byte-for-byte. -/
def checkAll (configuration : Configuration) : IO Unit := do
  validate configuration
  let expectedSources := sources configuration
  let chunkCount := configuration.source.boxes.map
    (boxComputedChunks configuration.source.parameters) |>.map List.length |>.sum
  for (path, source) in expectedSources do
    checkSource path source
  let actualLeanFiles ← [configuration.output.dataDirectory,
      configuration.output.replayDirectory].foldlM (init := []) fun files directory => do
    let walked ← System.FilePath.walkDir directory
    pure <| files ++ walked.toList.filterMap fun path =>
      if path.toString.endsWith ".lean" then some path.toString else none
  let expectedLeanFiles := expectedSources.map Prod.fst
  unless actualLeanFiles.length == expectedLeanFiles.length &&
      actualLeanFiles.all expectedLeanFiles.contains do
    throw <| IO.userError
      "unexpected generated Lean source topology under the output directory"
  IO.println <| s!"upper-contour family generation check passed: " ++
    s!"{configuration.source.boxes.length} boxes, " ++
    s!"{replaySources configuration |>.length} bounded replay shards, " ++
    s!"{chunkCount} chunks"

/-- Print a topology summary without evaluating numeric endpoints. -/
def printTopology (configuration : Configuration) : IO Unit := do
  validate configuration
  let result := topology configuration
  IO.println <| s!"upper-contour family topology: {result.boxCount} boxes, " ++
    s!"{result.cellCount} cells, {result.chunkCount} chunks, " ++
    s!"{result.replayShardCount} replay shards, {result.moduleCount} modules"

/-- Shared command-line entry point for an instance-specific generator executable. -/
def run (configuration : Configuration) (arguments : List String) : IO Unit := do
  match arguments with
  | [] | ["all"] => generateAll configuration
  | ["--check"] => checkAll configuration
  | ["--topology"] => printTopology configuration
  | _ => throw <| IO.userError "usage: GENERATOR [all|--check|--topology]"

end CertifiedJL.SparseUpperContourFamily.Generator
