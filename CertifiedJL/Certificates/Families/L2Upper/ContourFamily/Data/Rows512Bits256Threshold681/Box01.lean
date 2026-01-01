/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows512Bits256Threshold681
import CertifiedJL.Arithmetic.Interval.Interval

/-! Raw generated endpoints for upper-contour family box 1. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows512Bits256Threshold681.Box01

set_option linter.style.longLine false

def chunks : List (Interval (CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters).precision) :=
  [
    ⟨0,
      829096609919007307895835680203978047576449241774008345397884819833056981299838848801281657721211066539081357506337768227171207762081560880718105014787722⟩,
    ⟨0,
      1344753337414124612186609147149652134940895320185531163254271855280250487736165681366077281865886⟩,
    ⟨0,
      10183276162956186059607418616704649444⟩,
    ⟨0,
      3⟩,
    ⟨0,
      262967084626035322423918294358040869691289002655075387349784366578388582993374754773476813283004711022227362929143543762940614158420205681597281920689589⟩
  ]

def expectedBound : Interval (CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters).precision :=
  ⟨0,
      11770116222683393036048460664842681009328169234868330811949999966160553774558700523504772109177374073809724476682107258170554563596381846531823827435901286⟩

end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows512Bits256Threshold681.Box01
