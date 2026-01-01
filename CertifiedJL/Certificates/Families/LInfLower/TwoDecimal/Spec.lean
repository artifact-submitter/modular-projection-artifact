/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Data.Cap24Central.Data
import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Data.Cap24Diffuse.Data
import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Data.Cap34Central.Data
import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Data.Cap34Diffuse.Data
import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Data.Cap42Central.Data
import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Data.Cap42Diffuse.Data
import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Data.Cap47Central.Data
import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Data.Cap47Diffuse.Data

/-!
# Semantic contracts for the two-decimal ternary infinity majorants

These propositions are the only expensive numerical boundaries consumed by
the analytic proof assembly. Exact providers replay the generated Bernstein
trees; the fast library may assume precisely these same propositions.
-/

namespace CertifiedJL.TernaryLInfTwoDecimal

open TrigonometricBernstein

structure MajorantCertificate (fourier : List ℚ) (contract : Prop)
    (endpoint : ℚ) : Prop where
  contractProof : contract
  cosineNonnegative : ∀ x : ℝ, 0 ≤ rationalCosineValue fourier x
  cosineDominatesOne : ∀ {x : ℝ},
    (endpoint : ℝ) ≤ Real.cos x → 1 ≤ rationalCosineValue fourier x

def Cap24CentralCertificate : Prop :=
  MajorantCertificate Cap24Central.fourier
    (CentralFourierContract Cap24Central.fourier Cap24Central.degree
      Cap24Central.phiOneBound Cap24Central.phiTwoBound
      Cap24Central.expectationBound)
    Cap24Central.endpoint

def Cap24DiffuseCertificate : Prop :=
  MajorantCertificate Cap24Diffuse.fourier
    (DiffuseFourierContract Cap24Diffuse.fourier Cap24Diffuse.degree
      Cap24Diffuse.diffuseMomentBound Cap24Diffuse.expectationBound)
    Cap24Diffuse.endpoint

def Cap34CentralCertificate : Prop :=
  MajorantCertificate Cap34Central.fourier
    (CentralFourierContract Cap34Central.fourier Cap34Central.degree
      Cap34Central.phiOneBound Cap34Central.phiTwoBound
      Cap34Central.expectationBound)
    Cap34Central.endpoint

def Cap34DiffuseCertificate : Prop :=
  MajorantCertificate Cap34Diffuse.fourier
    (DiffuseFourierContract Cap34Diffuse.fourier Cap34Diffuse.degree
      Cap34Diffuse.diffuseMomentBound Cap34Diffuse.expectationBound)
    Cap34Diffuse.endpoint

def Cap42CentralCertificate : Prop :=
  MajorantCertificate Cap42Central.fourier
    (CentralFourierContract Cap42Central.fourier Cap42Central.degree
      Cap42Central.phiOneBound Cap42Central.phiTwoBound
      Cap42Central.expectationBound)
    Cap42Central.endpoint

def Cap42DiffuseCertificate : Prop :=
  MajorantCertificate Cap42Diffuse.fourier
    (DiffuseFourierContract Cap42Diffuse.fourier Cap42Diffuse.degree
      Cap42Diffuse.diffuseMomentBound Cap42Diffuse.expectationBound)
    Cap42Diffuse.endpoint

def Cap47CentralCertificate : Prop :=
  MajorantCertificate Cap47Central.fourier
    (CentralFourierContract Cap47Central.fourier Cap47Central.degree
      Cap47Central.phiOneBound Cap47Central.phiTwoBound
      Cap47Central.expectationBound)
    Cap47Central.endpoint

def Cap47DiffuseCertificate : Prop :=
  MajorantCertificate Cap47Diffuse.fourier
    (DiffuseFourierContract Cap47Diffuse.fourier Cap47Diffuse.degree
      Cap47Diffuse.diffuseMomentBound Cap47Diffuse.expectationBound)
    Cap47Diffuse.endpoint

end CertifiedJL.TernaryLInfTwoDecimal
