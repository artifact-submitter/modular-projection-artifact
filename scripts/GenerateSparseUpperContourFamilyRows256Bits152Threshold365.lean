/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Generator
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows256Bits152Threshold365

namespace GenerateSparseUpperContourFamilyRows256Bits152Threshold365

open CertifiedJL.SparseUpperContourFamily
open CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365

def configuration : Generator.Configuration where
  source :=
    { moduleName :=
        "CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows256Bits152Threshold365"
      namespaceName :=
        "CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365"
      parameters := parameters
      boxes := profileBoxes
      highProfileName := some "highProfile"
      highProfile := some highProfile
      soundness := some
        { moduleName :=
            "CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Soundness.Instances.Rows256Bits152Threshold365Soundness"
          namespaceName :=
            "CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365Soundness"
          thresholdName := some "threshold"
          thresholdEqualityName := some "threshold_eq" } }
  output :=
    { dataDirectory :=
        "CertifiedJL/Certificates/Families/L2Upper/ContourFamily/Data/Rows256Bits152Threshold365"
      replayDirectory :=
        "CertifiedJL/Certificates/Families/L2Upper/ContourFamily/Replay/Rows256Bits152Threshold365"
      dataModulePrefix :=
        "CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows256Bits152Threshold365"
      replayModulePrefix :=
        "CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits152Threshold365"
      dataNamespace :=
        "CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows256Bits152Threshold365"
      replayNamespace :=
        "CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits152Threshold365"
      generatorRevision := "akita-rows256-bits152-threshold365-v1"
      chunksPerShard := 4 }

end GenerateSparseUpperContourFamilyRows256Bits152Threshold365

def main (arguments : List String) : IO Unit :=
  CertifiedJL.SparseUpperContourFamily.Generator.run
    GenerateSparseUpperContourFamilyRows256Bits152Threshold365.configuration
    arguments
