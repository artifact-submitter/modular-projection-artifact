/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Generator
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows512Bits256Threshold681

namespace GenerateSparseUpperContourFamilyRows512Bits256Threshold681

open CertifiedJL.SparseUpperContourFamily
open CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681

def configuration : Generator.Configuration where
  source :=
    { moduleName :=
        "CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows512Bits256Threshold681"
      namespaceName :=
        "CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681"
      parameters := parameters
      boxes := profileBoxes
      highProfileName := some "highProfile"
      highProfile := some highProfile
      soundness := some
        { moduleName :=
            "CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Soundness.Instances.Rows512Bits256Threshold681Soundness"
          namespaceName :=
            "CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681Soundness"
          thresholdName := some "threshold"
          thresholdEqualityName := some "threshold_eq" } }
  output :=
    { dataDirectory :=
        "CertifiedJL/Certificates/Families/L2Upper/ContourFamily/Data/Rows512Bits256Threshold681"
      replayDirectory :=
        "CertifiedJL/Certificates/Families/L2Upper/ContourFamily/Replay/Rows512Bits256Threshold681"
      dataModulePrefix :=
        "CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows512Bits256Threshold681"
      replayModulePrefix :=
        "CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681"
      dataNamespace :=
        "CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows512Bits256Threshold681"
      replayNamespace :=
        "CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681"
      generatorRevision := "high-security-upper-contour-configs-681-v1"
      chunksPerShard := 4 }

end GenerateSparseUpperContourFamilyRows512Bits256Threshold681

def main (arguments : List String) : IO Unit :=
  CertifiedJL.SparseUpperContourFamily.Generator.run
    GenerateSparseUpperContourFamilyRows512Bits256Threshold681.configuration
    arguments
