/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows256Bits152Threshold365.Data
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows256RescaledFrontier

/-! # Bounded arithmetic sample for rescaled 256-row contour endpoints

This module checks only endpoint-dependent prefactors and final comparisons
against the generated U365 interval data.  It deliberately does not import the
full kernel replay that verifies those intervals; that replay remains the
anchor certificate's independently sampled proof boundary.
-/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256RescaledFrontier

open CertifiedJL.SparseUpperContourFamily
open CertifiedJL.SparseUpperContourFamily.Instances.Rows256RescaledFrontier

set_option linter.style.longLine false

def reducedBox00Check (endpoint : Endpoint) : Bool :=
  Interval.upperLTCheck
    (boxPrefactor (parameters endpoint) (profileBoxes.getD 0 default) *
      boxIntegralFrom (parameters endpoint) (profileBoxes.getD 0 default)
        Data.Rows256Bits152Threshold365.Box00.chunks)
    (profileBoxes.getD 0 default).target

def reducedBox01Check (endpoint : Endpoint) : Bool :=
  Interval.upperLTCheck
    (boxPrefactor (parameters endpoint) (profileBoxes.getD 1 default) *
      boxIntegralFrom (parameters endpoint) (profileBoxes.getD 1 default)
        Data.Rows256Bits152Threshold365.Box01.chunks)
    (profileBoxes.getD 1 default).target

def reducedBox02Check (endpoint : Endpoint) : Bool :=
  Interval.upperLTCheck
    (boxPrefactor (parameters endpoint) (profileBoxes.getD 2 default) *
      boxIntegralFrom (parameters endpoint) (profileBoxes.getD 2 default)
        Data.Rows256Bits152Threshold365.Box02.chunks)
    (profileBoxes.getD 2 default).target

def reducedBox03Check (endpoint : Endpoint) : Bool :=
  Interval.upperLTCheck
    (boxPrefactor (parameters endpoint) (profileBoxes.getD 3 default) *
      boxIntegralFrom (parameters endpoint) (profileBoxes.getD 3 default)
        Data.Rows256Bits152Threshold365.Box03.chunks)
    (profileBoxes.getD 3 default).target

def reducedBox04Check (endpoint : Endpoint) : Bool :=
  Interval.upperLTCheck
    (boxPrefactor (parameters endpoint) (profileBoxes.getD 4 default) *
      boxIntegralFrom (parameters endpoint) (profileBoxes.getD 4 default)
        Data.Rows256Bits152Threshold365.Box04.chunks)
    (profileBoxes.getD 4 default).target

def reducedBox05Check (endpoint : Endpoint) : Bool :=
  Interval.upperLTCheck
    (boxPrefactor (parameters endpoint) (profileBoxes.getD 5 default) *
      boxIntegralFrom (parameters endpoint) (profileBoxes.getD 5 default)
        Data.Rows256Bits152Threshold365.Box05.chunks)
    (profileBoxes.getD 5 default).target

def reducedBox06Check (endpoint : Endpoint) : Bool :=
  Interval.upperLTCheck
    (boxPrefactor (parameters endpoint) (profileBoxes.getD 6 default) *
      boxIntegralFrom (parameters endpoint) (profileBoxes.getD 6 default)
        Data.Rows256Bits152Threshold365.Box06.chunks)
    (profileBoxes.getD 6 default).target

def reducedBox07Check (endpoint : Endpoint) : Bool :=
  Interval.upperLTCheck
    (boxPrefactor (parameters endpoint) (profileBoxes.getD 7 default) *
      boxIntegralFrom (parameters endpoint) (profileBoxes.getD 7 default)
        Data.Rows256Bits152Threshold365.Box07.chunks)
    (profileBoxes.getD 7 default).target

def reducedBox08Check (endpoint : Endpoint) : Bool :=
  Interval.upperLTCheck
    (boxPrefactor (parameters endpoint) (profileBoxes.getD 8 default) *
      boxIntegralFrom (parameters endpoint) (profileBoxes.getD 8 default)
        Data.Rows256Bits152Threshold365.Box08.chunks)
    (profileBoxes.getD 8 default).target

def reducedBox09Check (endpoint : Endpoint) : Bool :=
  Interval.upperLTCheck
    (boxPrefactor (parameters endpoint) (profileBoxes.getD 9 default) *
      boxIntegralFrom (parameters endpoint) (profileBoxes.getD 9 default)
        Data.Rows256Bits152Threshold365.Box09.chunks)
    (profileBoxes.getD 9 default).target

/-- Endpoint checker after substituting the anchor's generated intervals. -/
def endpointCheck (endpoint : Endpoint) : Bool :=
  [ reducedBox00Check endpoint,
    reducedBox01Check endpoint,
    reducedBox02Check endpoint,
    reducedBox03Check endpoint,
    reducedBox04Check endpoint,
    reducedBox05Check endpoint,
    reducedBox06Check endpoint,
    reducedBox07Check endpoint,
    reducedBox08Check endpoint,
    reducedBox09Check endpoint,
    highProfileCheck (parameters endpoint) highProfile ].all id

theorem bits140Threshold5623Over16_check :
    endpointCheck bits140Threshold5623Over16 = true := by decide +kernel

theorem bits141Threshold5641Over16_check :
    endpointCheck bits141Threshold5641Over16 = true := by decide +kernel

theorem bits142Threshold5659Over16_check :
    endpointCheck bits142Threshold5659Over16 = true := by decide +kernel

theorem bits143Threshold5677Over16_check :
    endpointCheck bits143Threshold5677Over16 = true := by decide +kernel

theorem bits144Threshold2847Over8_check :
    endpointCheck bits144Threshold2847Over8 = true := by decide +kernel

theorem bits145Threshold357_check :
    endpointCheck bits145Threshold357 = true := by decide +kernel

theorem bits146Threshold2865Over8_check :
    endpointCheck bits146Threshold2865Over8 = true := by decide +kernel

theorem bits147Threshold1437Over4_check :
    endpointCheck bits147Threshold1437Over4 = true := by decide +kernel

theorem bits148Threshold5765Over16_check :
    endpointCheck bits148Threshold5765Over16 = true := by decide +kernel

theorem bits149Threshold5783Over16_check :
    endpointCheck bits149Threshold5783Over16 = true := by decide +kernel

theorem bits150Threshold5801Over16_check :
    endpointCheck bits150Threshold5801Over16 = true := by decide +kernel

theorem bits151Threshold2909Over8_check :
    endpointCheck bits151Threshold2909Over8 = true := by decide +kernel

theorem bits152Threshold1459Over4_check :
    endpointCheck bits152Threshold1459Over4 = true := by decide +kernel

end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256RescaledFrontier
