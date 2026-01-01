/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Generator
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows192Bits128Threshold287

namespace GenerateSparseUpperContourFamilyRows192Bits128Threshold287

open CertifiedJL.SparseUpperContourFamily
open CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287

def configuration : Generator.Configuration where
  source :=
    { moduleName :=
        "CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows192Bits128Threshold287"
      namespaceName :=
        "CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287"
      parameters := parameters
      boxes := profileBoxes
      highProfileName := some "highProfile"
      highProfile := some highProfile
      soundness := some
        { moduleName :=
            "CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Soundness.Instances.Rows192Bits128Threshold287Soundness"
          namespaceName :=
            "CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287Soundness"
          thresholdName := some "threshold"
          thresholdEqualityName := some "threshold_eq" } }
  output :=
    { dataDirectory :=
        "CertifiedJL/Certificates/Families/L2Upper/ContourFamily/Data/Rows192Bits128Threshold287"
      replayDirectory :=
        "CertifiedJL/Certificates/Families/L2Upper/ContourFamily/Replay/Rows192Bits128Threshold287"
      dataModulePrefix :=
        "CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows192Bits128Threshold287"
      replayModulePrefix :=
        "CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287"
      dataNamespace :=
        "CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows192Bits128Threshold287"
      replayNamespace :=
        "CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287"
      generatorRevision := "rows192-security-frontiers-v1"
      chunksPerShard := 4 }

end GenerateSparseUpperContourFamilyRows192Bits128Threshold287

def main (arguments : List String) : IO Unit :=
  CertifiedJL.SparseUpperContourFamily.Generator.run
    GenerateSparseUpperContourFamilyRows192Bits128Threshold287.configuration
    arguments
