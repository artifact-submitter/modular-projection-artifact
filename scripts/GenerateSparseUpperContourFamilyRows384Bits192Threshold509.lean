/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Generator
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows384Bits192Threshold509

namespace GenerateSparseUpperContourFamilyRows384Bits192Threshold509

open CertifiedJL.SparseUpperContourFamily
open CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509

def configuration : Generator.Configuration where
  source :=
    { moduleName :=
        "CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows384Bits192Threshold509"
      namespaceName :=
        "CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509"
      parameters := parameters
      boxes := profileBoxes
      highProfileName := some "highProfile"
      highProfile := some highProfile
      soundness := some
        { moduleName :=
            "CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Soundness.Instances.Rows384Bits192Threshold509Soundness"
          namespaceName :=
            "CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509Soundness"
          thresholdName := some "threshold"
          thresholdEqualityName := some "threshold_eq" } }
  output :=
    { dataDirectory :=
        "CertifiedJL/Certificates/Families/L2Upper/ContourFamily/Data/Rows384Bits192Threshold509"
      replayDirectory :=
        "CertifiedJL/Certificates/Families/L2Upper/ContourFamily/Replay/Rows384Bits192Threshold509"
      dataModulePrefix :=
        "CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows384Bits192Threshold509"
      replayModulePrefix :=
        "CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509"
      dataNamespace :=
        "CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows384Bits192Threshold509"
      replayNamespace :=
        "CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509"
      generatorRevision := "high-security-upper-contour-configs-v1"
      chunksPerShard := 4 }

end GenerateSparseUpperContourFamilyRows384Bits192Threshold509

def main (arguments : List String) : IO Unit :=
  CertifiedJL.SparseUpperContourFamily.Generator.run
    GenerateSparseUpperContourFamilyRows384Bits192Threshold509.configuration
    arguments
