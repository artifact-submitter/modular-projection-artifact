/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows512Bits256Threshold681

/-! Kernel replay shard 0 for box 20.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_20_segment_00_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 20 default)
      ⟨0, 0, 25⟩ =
      ⟨0,
      692825718616225660874166324857713684318250500143833926911123263807776938435242289626385225790383202162726963687071413019726199770001254190638475015841378⟩ := by
  decide +kernel

theorem box_20_segment_01_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 20 default)
      ⟨1, 0, 10⟩ =
      ⟨0,
      1722438824083968657216353024411283304800326051731823486300276576641621595480119275805206790939665⟩ := by
  decide +kernel

theorem box_20_segment_02_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 20 default)
      ⟨2, 0, 5⟩ =
      ⟨0,
      124866718607198159706441505115761907259⟩ := by
  decide +kernel

theorem box_20_segment_03_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 20 default)
      ⟨3, 0, 3⟩ =
      ⟨0,
      329874488608806463135131045263180120704073759125684425562294187506198411021667454073847850825225531149329154528355216624465494443165953056577517848091215⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681
