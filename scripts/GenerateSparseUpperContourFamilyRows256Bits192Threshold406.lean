/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Generator
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows256Bits192Threshold406

namespace GenerateSparseUpperContourFamilyRows256Bits192Threshold406

open CertifiedJL.SparseUpperContourFamily
open CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406

def configuration : Generator.Configuration where
  source :=
    { moduleName :=
        "CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows256Bits192Threshold406"
      namespaceName :=
        "CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406"
      parameters := parameters
      boxes := profileBoxes
      highProfileName := some "highProfile"
      highProfile := some highProfile
      soundness := some
        { moduleName :=
            "CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Soundness.Instances.Rows256Bits192Threshold406Soundness"
          namespaceName :=
            "CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406Soundness"
          thresholdName := some "threshold"
          thresholdEqualityName := some "threshold_eq" } }
  output :=
    { dataDirectory :=
        "CertifiedJL/Certificates/Families/L2Upper/ContourFamily/Data/Rows256Bits192Threshold406"
      replayDirectory :=
        "CertifiedJL/Certificates/Families/L2Upper/ContourFamily/Replay/Rows256Bits192Threshold406"
      dataModulePrefix :=
        "CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows256Bits192Threshold406"
      replayModulePrefix :=
        "CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits192Threshold406"
      dataNamespace :=
        "CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows256Bits192Threshold406"
      replayNamespace :=
        "CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits192Threshold406"
      generatorRevision := "high-security-upper-contour-configs-v1"
      chunksPerShard := 4 }

end GenerateSparseUpperContourFamilyRows256Bits192Threshold406

def main (arguments : List String) : IO Unit :=
  CertifiedJL.SparseUpperContourFamily.Generator.run
    GenerateSparseUpperContourFamilyRows256Bits192Threshold406.configuration
    arguments
