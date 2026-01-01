/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Spec
import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Replay.Cap24Central.Verified
import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Replay.Cap24Diffuse.Verified
import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Replay.Cap34Central.Verified
import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Replay.Cap34Diffuse.Verified
import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Replay.Cap42Central.Verified
import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Replay.Cap42Diffuse.Verified
import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Replay.Cap47Central.Verified
import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Replay.Cap47Diffuse.Verified

/-! # Kernel-verified providers for the two-decimal ternary infinity majorants -/

namespace CertifiedJL.CertificateProviders

open TernaryLInfTwoDecimal

theorem ternaryLInfCap24Central_verified : Cap24CentralCertificate :=
  ⟨Cap24Central.fourierContract, Cap24Central.cosineNonnegative,
    fun hx => Cap24Central.cosineDominatesOne hx⟩

theorem ternaryLInfCap24Diffuse_verified : Cap24DiffuseCertificate :=
  ⟨Cap24Diffuse.fourierContract, Cap24Diffuse.cosineNonnegative,
    fun hx => Cap24Diffuse.cosineDominatesOne hx⟩

theorem ternaryLInfCap34Central_verified : Cap34CentralCertificate :=
  ⟨Cap34Central.fourierContract, Cap34Central.cosineNonnegative,
    fun hx ↦ Cap34Central.cosineDominatesOne hx⟩

theorem ternaryLInfCap34Diffuse_verified : Cap34DiffuseCertificate :=
  ⟨Cap34Diffuse.fourierContract, Cap34Diffuse.cosineNonnegative,
    fun hx ↦ Cap34Diffuse.cosineDominatesOne hx⟩

theorem ternaryLInfCap42Central_verified : Cap42CentralCertificate :=
  ⟨Cap42Central.fourierContract, Cap42Central.cosineNonnegative,
    fun hx => Cap42Central.cosineDominatesOne hx⟩

theorem ternaryLInfCap42Diffuse_verified : Cap42DiffuseCertificate :=
  ⟨Cap42Diffuse.fourierContract, Cap42Diffuse.cosineNonnegative,
    fun hx => Cap42Diffuse.cosineDominatesOne hx⟩

theorem ternaryLInfCap47Central_verified : Cap47CentralCertificate :=
  ⟨Cap47Central.fourierContract, Cap47Central.cosineNonnegative,
    fun hx => Cap47Central.cosineDominatesOne hx⟩

theorem ternaryLInfCap47Diffuse_verified : Cap47DiffuseCertificate :=
  ⟨Cap47Diffuse.fourierContract, Cap47Diffuse.cosineNonnegative,
    fun hx => Cap47Diffuse.cosineDominatesOne hx⟩

end CertifiedJL.CertificateProviders
