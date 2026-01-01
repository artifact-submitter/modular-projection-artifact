/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Generator
import CertifiedJL.Tests.SparseUpperContourFamilyFixture

namespace GenerateSparseUpperContourFamilyFixture

open CertifiedJL.SparseUpperContourFamily

def configuration : Generator.Configuration where
  source :=
    { moduleName := "CertifiedJL.Tests.SparseUpperContourFamilyFixture"
      namespaceName := "CertifiedJL.Tests.SparseUpperContourFamilyFixture"
      parameters := CertifiedJL.Tests.SparseUpperContourFamilyFixture.parameters
      boxes := CertifiedJL.Tests.SparseUpperContourFamilyFixture.profileBoxes
      highProfileName := some "highProfile"
      highProfile := some CertifiedJL.Tests.SparseUpperContourFamilyFixture.highProfile
      soundness := some
        { moduleName :=
            "CertifiedJL.Tests.SparseUpperContourFamilyFixtureSoundness"
          namespaceName :=
            "CertifiedJL.Tests.SparseUpperContourFamilyFixtureSoundness"
          thresholdName := some "threshold"
          thresholdEqualityName := some "threshold_eq" } }
  output :=
    { dataDirectory :=
        "CertifiedJL/Tests/Generated/SparseUpperContourFamilyFixture/Data"
      replayDirectory :=
        "CertifiedJL/Tests/Generated/SparseUpperContourFamilyFixture/Replay"
      dataModulePrefix :=
        "CertifiedJL.Tests.Generated.SparseUpperContourFamilyFixture.Data"
      replayModulePrefix :=
        "CertifiedJL.Tests.Generated.SparseUpperContourFamilyFixture.Replay"
      dataNamespace :=
        "CertifiedJL.Tests.Generated.SparseUpperContourFamilyFixture.Data"
      replayNamespace :=
        "CertifiedJL.Tests.Generated.SparseUpperContourFamilyFixture.Replay"
      generatorRevision := "fixture-v3-box-shards"
      chunksPerShard := 2 }

end GenerateSparseUpperContourFamilyFixture

def main (arguments : List String) : IO Unit :=
  CertifiedJL.SparseUpperContourFamily.Generator.run
    GenerateSparseUpperContourFamilyFixture.configuration arguments
