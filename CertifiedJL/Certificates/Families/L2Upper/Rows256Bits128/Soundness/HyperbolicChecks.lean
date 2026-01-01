/- Generated exact scalar checks; replayed by Lean's kernel. -/
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.Core
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

namespace CertifiedJL.SparseUpperHybrid.HyperbolicChecks

set_option linter.style.longLine false

theorem box00_sinhUpper :
    sinhUpper (3 / 16) = 53039275766832159615349074813 / 281225433192052123309703168000 := by
  decide +kernel

theorem box00_coshUpperScalar :
    coshUpper (3 / 16) = 1052126529743706802662255421 / 1033899213527435497072230400 := by
  decide +kernel

theorem box00_sinh_le :
    Real.sinh (((3 / 16 : ℚ) : ℝ)) ≤
      (sinhUpper (3 / 16) : ℝ) := by
  rw [Real.sinh_eq]
  have hp := Real.exp_bound (x := (3 / 16 : ℝ))
    (n := 25) (by norm_num) (by norm_num)
  have hn := Real.exp_bound (x := -(3 / 16 : ℝ))
    (n := 25) (by norm_num) (by norm_num)
  have hp' := (abs_le.mp hp).2
  have hn' := (abs_le.mp hn).1
  rw [box00_sinhUpper]
  norm_num [Finset.sum_range_succ] at hp' hn' ⊢
  linarith

theorem box00_cosh_le :
    Real.cosh (((3 / 16 : ℚ) : ℝ)) ≤
      (coshUpper (3 / 16) : ℝ) := by
  rw [Real.cosh_eq]
  have hp := Real.exp_bound (x := (3 / 16 : ℝ))
    (n := 25) (by norm_num) (by norm_num)
  have hn := Real.exp_bound (x := -(3 / 16 : ℝ))
    (n := 25) (by norm_num) (by norm_num)
  have hp' := (abs_le.mp hp).2
  have hn' := (abs_le.mp hn).2
  rw [box00_coshUpperScalar]
  norm_num [Finset.sum_range_succ] at hp' hn' ⊢
  linarith

theorem box01_sinhUpper :
    sinhUpper (313 / 1250) = 1278650513370558921963599794402168760565816236092436670228967 / 5053457196935063693672418594360351562500000000000000000000000 := by
  decide +kernel

theorem box01_coshUpperScalar :
    coshUpper (313 / 1250) = 245296599726358076599861734109395611338831409619734254781 / 237802439587463065981864929199218750000000000000000000000 := by
  decide +kernel

theorem box01_sinh_le :
    Real.sinh (((313 / 1250 : ℚ) : ℝ)) ≤
      (sinhUpper (313 / 1250) : ℝ) := by
  rw [Real.sinh_eq]
  have hp := Real.exp_bound (x := (313 / 1250 : ℝ))
    (n := 25) (by norm_num) (by norm_num)
  have hn := Real.exp_bound (x := -(313 / 1250 : ℝ))
    (n := 25) (by norm_num) (by norm_num)
  have hp' := (abs_le.mp hp).2
  have hn' := (abs_le.mp hn).1
  rw [box01_sinhUpper]
  norm_num [Finset.sum_range_succ] at hp' hn' ⊢
  linarith

theorem box01_cosh_le :
    Real.cosh (((313 / 1250 : ℚ) : ℝ)) ≤
      (coshUpper (313 / 1250) : ℝ) := by
  rw [Real.cosh_eq]
  have hp := Real.exp_bound (x := (313 / 1250 : ℝ))
    (n := 25) (by norm_num) (by norm_num)
  have hn := Real.exp_bound (x := -(313 / 1250 : ℝ))
    (n := 25) (by norm_num) (by norm_num)
  have hp' := (abs_le.mp hp).2
  have hn' := (abs_le.mp hn).2
  rw [box01_coshUpperScalar]
  norm_num [Finset.sum_range_succ] at hp' hn' ⊢
  linarith

theorem box02_sinhUpper :
    sinhUpper (1 / 4) = 48227317689697911992671 / 190914355638174744576000 := by
  decide +kernel

theorem box02_coshUpperScalar :
    coshUpper (1 / 4) = 2895669605056765013597 / 2807478017677747814400 := by
  decide +kernel

theorem box02_sinh_le :
    Real.sinh (((1 / 4 : ℚ) : ℝ)) ≤
      (sinhUpper (1 / 4) : ℝ) := by
  rw [Real.sinh_eq]
  have hp := Real.exp_bound (x := (1 / 4 : ℝ))
    (n := 25) (by norm_num) (by norm_num)
  have hn := Real.exp_bound (x := -(1 / 4 : ℝ))
    (n := 25) (by norm_num) (by norm_num)
  have hp' := (abs_le.mp hp).2
  have hn' := (abs_le.mp hn).1
  rw [box02_sinhUpper]
  norm_num [Finset.sum_range_succ] at hp' hn' ⊢
  linarith

theorem box02_cosh_le :
    Real.cosh (((1 / 4 : ℚ) : ℝ)) ≤
      (coshUpper (1 / 4) : ℝ) := by
  rw [Real.cosh_eq]
  have hp := Real.exp_bound (x := (1 / 4 : ℝ))
    (n := 25) (by norm_num) (by norm_num)
  have hn := Real.exp_bound (x := -(1 / 4 : ℝ))
    (n := 25) (by norm_num) (by norm_num)
  have hp' := (abs_le.mp hp).2
  have hn' := (abs_le.mp hn).2
  rw [box02_coshUpperScalar]
  norm_num [Finset.sum_range_succ] at hp' hn' ⊢
  linarith

theorem box03_sinhUpper :
    sinhUpper (1 / 4) = 48227317689697911992671 / 190914355638174744576000 := by
  decide +kernel

theorem box03_coshUpperScalar :
    coshUpper (1 / 4) = 2895669605056765013597 / 2807478017677747814400 := by
  decide +kernel

theorem box03_sinh_le :
    Real.sinh (((1 / 4 : ℚ) : ℝ)) ≤
      (sinhUpper (1 / 4) : ℝ) := by
  rw [Real.sinh_eq]
  have hp := Real.exp_bound (x := (1 / 4 : ℝ))
    (n := 25) (by norm_num) (by norm_num)
  have hn := Real.exp_bound (x := -(1 / 4 : ℝ))
    (n := 25) (by norm_num) (by norm_num)
  have hp' := (abs_le.mp hp).2
  have hn' := (abs_le.mp hn).1
  rw [box03_sinhUpper]
  norm_num [Finset.sum_range_succ] at hp' hn' ⊢
  linarith

theorem box03_cosh_le :
    Real.cosh (((1 / 4 : ℚ) : ℝ)) ≤
      (coshUpper (1 / 4) : ℝ) := by
  rw [Real.cosh_eq]
  have hp := Real.exp_bound (x := (1 / 4 : ℝ))
    (n := 25) (by norm_num) (by norm_num)
  have hn := Real.exp_bound (x := -(1 / 4 : ℝ))
    (n := 25) (by norm_num) (by norm_num)
  have hp' := (abs_le.mp hp).2
  have hn' := (abs_le.mp hn).2
  rw [box03_coshUpperScalar]
  norm_num [Finset.sum_range_succ] at hp' hn' ⊢
  linarith

theorem box04_sinhUpper :
    sinhUpper (313 / 1000) = 56558075449175002862883596699261368734163856917359678978967 / 177779658272920704000000000000000000000000000000000000000000 := by
  decide +kernel

theorem box04_coshUpperScalar :
    coshUpper (313 / 1000) = 10973557203274807630514299872127415378996095374996004781 / 10457124558994713600000000000000000000000000000000000000 := by
  decide +kernel

theorem box04_sinh_le :
    Real.sinh (((313 / 1000 : ℚ) : ℝ)) ≤
      (sinhUpper (313 / 1000) : ℝ) := by
  rw [Real.sinh_eq]
  have hp := Real.exp_bound (x := (313 / 1000 : ℝ))
    (n := 25) (by norm_num) (by norm_num)
  have hn := Real.exp_bound (x := -(313 / 1000 : ℝ))
    (n := 25) (by norm_num) (by norm_num)
  have hp' := (abs_le.mp hp).2
  have hn' := (abs_le.mp hn).1
  rw [box04_sinhUpper]
  norm_num [Finset.sum_range_succ] at hp' hn' ⊢
  linarith

theorem box04_cosh_le :
    Real.cosh (((313 / 1000 : ℚ) : ℝ)) ≤
      (coshUpper (313 / 1000) : ℝ) := by
  rw [Real.cosh_eq]
  have hp := Real.exp_bound (x := (313 / 1000 : ℝ))
    (n := 25) (by norm_num) (by norm_num)
  have hn := Real.exp_bound (x := -(313 / 1000 : ℝ))
    (n := 25) (by norm_num) (by norm_num)
  have hp' := (abs_le.mp hp).2
  have hn' := (abs_le.mp hn).2
  rw [box04_coshUpperScalar]
  norm_num [Finset.sum_range_succ] at hp' hn' ⊢
  linarith

theorem box05_sinhUpper :
    sinhUpper (313 / 1000) = 56558075449175002862883596699261368734163856917359678978967 / 177779658272920704000000000000000000000000000000000000000000 := by
  decide +kernel

theorem box05_coshUpperScalar :
    coshUpper (313 / 1000) = 10973557203274807630514299872127415378996095374996004781 / 10457124558994713600000000000000000000000000000000000000 := by
  decide +kernel

theorem box05_sinh_le :
    Real.sinh (((313 / 1000 : ℚ) : ℝ)) ≤
      (sinhUpper (313 / 1000) : ℝ) := by
  rw [Real.sinh_eq]
  have hp := Real.exp_bound (x := (313 / 1000 : ℝ))
    (n := 25) (by norm_num) (by norm_num)
  have hn := Real.exp_bound (x := -(313 / 1000 : ℝ))
    (n := 25) (by norm_num) (by norm_num)
  have hp' := (abs_le.mp hp).2
  have hn' := (abs_le.mp hn).1
  rw [box05_sinhUpper]
  norm_num [Finset.sum_range_succ] at hp' hn' ⊢
  linarith

theorem box05_cosh_le :
    Real.cosh (((313 / 1000 : ℚ) : ℝ)) ≤
      (coshUpper (313 / 1000) : ℝ) := by
  rw [Real.cosh_eq]
  have hp := Real.exp_bound (x := (313 / 1000 : ℝ))
    (n := 25) (by norm_num) (by norm_num)
  have hn := Real.exp_bound (x := -(313 / 1000 : ℝ))
    (n := 25) (by norm_num) (by norm_num)
  have hp' := (abs_le.mp hp).2
  have hn' := (abs_le.mp hn).2
  rw [box05_coshUpperScalar]
  norm_num [Finset.sum_range_succ] at hp' hn' ⊢
  linarith

theorem box06_sinhUpper :
    sinhUpper (313 / 1000) = 56558075449175002862883596699261368734163856917359678978967 / 177779658272920704000000000000000000000000000000000000000000 := by
  decide +kernel

theorem box06_coshUpperScalar :
    coshUpper (313 / 1000) = 10973557203274807630514299872127415378996095374996004781 / 10457124558994713600000000000000000000000000000000000000 := by
  decide +kernel

theorem box06_sinh_le :
    Real.sinh (((313 / 1000 : ℚ) : ℝ)) ≤
      (sinhUpper (313 / 1000) : ℝ) := by
  rw [Real.sinh_eq]
  have hp := Real.exp_bound (x := (313 / 1000 : ℝ))
    (n := 25) (by norm_num) (by norm_num)
  have hn := Real.exp_bound (x := -(313 / 1000 : ℝ))
    (n := 25) (by norm_num) (by norm_num)
  have hp' := (abs_le.mp hp).2
  have hn' := (abs_le.mp hn).1
  rw [box06_sinhUpper]
  norm_num [Finset.sum_range_succ] at hp' hn' ⊢
  linarith

theorem box06_cosh_le :
    Real.cosh (((313 / 1000 : ℚ) : ℝ)) ≤
      (coshUpper (313 / 1000) : ℝ) := by
  rw [Real.cosh_eq]
  have hp := Real.exp_bound (x := (313 / 1000 : ℝ))
    (n := 25) (by norm_num) (by norm_num)
  have hn := Real.exp_bound (x := -(313 / 1000 : ℝ))
    (n := 25) (by norm_num) (by norm_num)
  have hp' := (abs_le.mp hp).2
  have hn' := (abs_le.mp hn).2
  rw [box06_coshUpperScalar]
  norm_num [Finset.sum_range_succ] at hp' hn' ⊢
  linarith

theorem box07_sinhUpper :
    sinhUpper (313 / 1000) = 56558075449175002862883596699261368734163856917359678978967 / 177779658272920704000000000000000000000000000000000000000000 := by
  decide +kernel

theorem box07_coshUpperScalar :
    coshUpper (313 / 1000) = 10973557203274807630514299872127415378996095374996004781 / 10457124558994713600000000000000000000000000000000000000 := by
  decide +kernel

theorem box07_sinh_le :
    Real.sinh (((313 / 1000 : ℚ) : ℝ)) ≤
      (sinhUpper (313 / 1000) : ℝ) := by
  rw [Real.sinh_eq]
  have hp := Real.exp_bound (x := (313 / 1000 : ℝ))
    (n := 25) (by norm_num) (by norm_num)
  have hn := Real.exp_bound (x := -(313 / 1000 : ℝ))
    (n := 25) (by norm_num) (by norm_num)
  have hp' := (abs_le.mp hp).2
  have hn' := (abs_le.mp hn).1
  rw [box07_sinhUpper]
  norm_num [Finset.sum_range_succ] at hp' hn' ⊢
  linarith

theorem box07_cosh_le :
    Real.cosh (((313 / 1000 : ℚ) : ℝ)) ≤
      (coshUpper (313 / 1000) : ℝ) := by
  rw [Real.cosh_eq]
  have hp := Real.exp_bound (x := (313 / 1000 : ℝ))
    (n := 25) (by norm_num) (by norm_num)
  have hn := Real.exp_bound (x := -(313 / 1000 : ℝ))
    (n := 25) (by norm_num) (by norm_num)
  have hp' := (abs_le.mp hp).2
  have hn' := (abs_le.mp hn).2
  rw [box07_coshUpperScalar]
  norm_num [Finset.sum_range_succ] at hp' hn' ⊢
  linarith

theorem box08_sinhUpper :
    sinhUpper (3 / 8) = 3293054810943653554759293 / 8578990880089861783552000 := by
  decide +kernel

theorem box08_coshUpperScalar :
    coshUpper (3 / 8) = 67563746207337606813757 / 63076464643686164070400 := by
  decide +kernel

theorem box08_sinh_le :
    Real.sinh (((3 / 8 : ℚ) : ℝ)) ≤
      (sinhUpper (3 / 8) : ℝ) := by
  rw [Real.sinh_eq]
  have hp := Real.exp_bound (x := (3 / 8 : ℝ))
    (n := 25) (by norm_num) (by norm_num)
  have hn := Real.exp_bound (x := -(3 / 8 : ℝ))
    (n := 25) (by norm_num) (by norm_num)
  have hp' := (abs_le.mp hp).2
  have hn' := (abs_le.mp hn).1
  rw [box08_sinhUpper]
  norm_num [Finset.sum_range_succ] at hp' hn' ⊢
  linarith

theorem box08_cosh_le :
    Real.cosh (((3 / 8 : ℚ) : ℝ)) ≤
      (coshUpper (3 / 8) : ℝ) := by
  rw [Real.cosh_eq]
  have hp := Real.exp_bound (x := (3 / 8 : ℝ))
    (n := 25) (by norm_num) (by norm_num)
  have hn := Real.exp_bound (x := -(3 / 8 : ℝ))
    (n := 25) (by norm_num) (by norm_num)
  have hp' := (abs_le.mp hp).2
  have hn' := (abs_le.mp hn).2
  rw [box08_coshUpperScalar]
  norm_num [Finset.sum_range_succ] at hp' hn' ⊢
  linarith

theorem box09_sinhUpper :
    sinhUpper (3 / 8) = 3293054810943653554759293 / 8578990880089861783552000 := by
  decide +kernel

theorem box09_coshUpperScalar :
    coshUpper (3 / 8) = 67563746207337606813757 / 63076464643686164070400 := by
  decide +kernel

theorem box09_sinh_le :
    Real.sinh (((3 / 8 : ℚ) : ℝ)) ≤
      (sinhUpper (3 / 8) : ℝ) := by
  rw [Real.sinh_eq]
  have hp := Real.exp_bound (x := (3 / 8 : ℝ))
    (n := 25) (by norm_num) (by norm_num)
  have hn := Real.exp_bound (x := -(3 / 8 : ℝ))
    (n := 25) (by norm_num) (by norm_num)
  have hp' := (abs_le.mp hp).2
  have hn' := (abs_le.mp hn).1
  rw [box09_sinhUpper]
  norm_num [Finset.sum_range_succ] at hp' hn' ⊢
  linarith

theorem box09_cosh_le :
    Real.cosh (((3 / 8 : ℚ) : ℝ)) ≤
      (coshUpper (3 / 8) : ℝ) := by
  rw [Real.cosh_eq]
  have hp := Real.exp_bound (x := (3 / 8 : ℝ))
    (n := 25) (by norm_num) (by norm_num)
  have hn := Real.exp_bound (x := -(3 / 8 : ℝ))
    (n := 25) (by norm_num) (by norm_num)
  have hp' := (abs_le.mp hp).2
  have hn' := (abs_le.mp hn).2
  rw [box09_coshUpperScalar]
  norm_num [Finset.sum_range_succ] at hp' hn' ⊢
  linarith

theorem box10_sinhUpper :
    sinhUpper (1881 / 5000) = 260529712759192904334057038383637368141075983589237182895387300749 / 676460342412968750000000000000000000000000000000000000000000000000 := by
  decide +kernel

theorem box10_coshUpperScalar :
    coshUpper (1881 / 5000) = 8527597213547423439805546520275654743938263822277121439317311 / 7957804565506250000000000000000000000000000000000000000000000 := by
  decide +kernel

theorem box10_sinh_le :
    Real.sinh (((1881 / 5000 : ℚ) : ℝ)) ≤
      (sinhUpper (1881 / 5000) : ℝ) := by
  rw [Real.sinh_eq]
  have hp := Real.exp_bound (x := (1881 / 5000 : ℝ))
    (n := 25) (by norm_num) (by norm_num)
  have hn := Real.exp_bound (x := -(1881 / 5000 : ℝ))
    (n := 25) (by norm_num) (by norm_num)
  have hp' := (abs_le.mp hp).2
  have hn' := (abs_le.mp hn).1
  rw [box10_sinhUpper]
  norm_num [Finset.sum_range_succ] at hp' hn' ⊢
  linarith

theorem box10_cosh_le :
    Real.cosh (((1881 / 5000 : ℚ) : ℝ)) ≤
      (coshUpper (1881 / 5000) : ℝ) := by
  rw [Real.cosh_eq]
  have hp := Real.exp_bound (x := (1881 / 5000 : ℝ))
    (n := 25) (by norm_num) (by norm_num)
  have hn := Real.exp_bound (x := -(1881 / 5000 : ℝ))
    (n := 25) (by norm_num) (by norm_num)
  have hp' := (abs_le.mp hp).2
  have hn' := (abs_le.mp hn).2
  rw [box10_coshUpperScalar]
  norm_num [Finset.sum_range_succ] at hp' hn' ⊢
  linarith

theorem box11_sinhUpper :
    sinhUpper (4389 / 10000) = 204943869150462731519696126436986474468933897696559292279936168731249 / 452287458338560000000000000000000000000000000000000000000000000000000 := by
  decide +kernel

theorem box11_coshUpperScalar :
    coshUpper (4389 / 10000) = 2920630224181172753511334372213589784169915999338700835160952919 / 2660263055590400000000000000000000000000000000000000000000000000 := by
  decide +kernel

theorem box11_sinh_le :
    Real.sinh (((4389 / 10000 : ℚ) : ℝ)) ≤
      (sinhUpper (4389 / 10000) : ℝ) := by
  rw [Real.sinh_eq]
  have hp := Real.exp_bound (x := (4389 / 10000 : ℝ))
    (n := 25) (by norm_num) (by norm_num)
  have hn := Real.exp_bound (x := -(4389 / 10000 : ℝ))
    (n := 25) (by norm_num) (by norm_num)
  have hp' := (abs_le.mp hp).2
  have hn' := (abs_le.mp hn).1
  rw [box11_sinhUpper]
  norm_num [Finset.sum_range_succ] at hp' hn' ⊢
  linarith

theorem box11_cosh_le :
    Real.cosh (((4389 / 10000 : ℚ) : ℝ)) ≤
      (coshUpper (4389 / 10000) : ℝ) := by
  rw [Real.cosh_eq]
  have hp := Real.exp_bound (x := (4389 / 10000 : ℝ))
    (n := 25) (by norm_num) (by norm_num)
  have hn := Real.exp_bound (x := -(4389 / 10000 : ℝ))
    (n := 25) (by norm_num) (by norm_num)
  have hp' := (abs_le.mp hp).2
  have hn' := (abs_le.mp hn).2
  rw [box11_coshUpperScalar]
  norm_num [Finset.sum_range_succ] at hp' hn' ⊢
  linarith

theorem box12_sinhUpper :
    sinhUpper (627 / 1250) = 329295181446941717218649378470494880768249125640782561207 / 629747698146384209394454956054687500000000000000000000000 := by
  decide +kernel

theorem box12_coshUpperScalar :
    coshUpper (627 / 1250) = 33438027787674279201023131836304861948816025089326119 / 29631527367606759071350097656250000000000000000000000 := by
  decide +kernel

theorem box12_sinh_le :
    Real.sinh (((627 / 1250 : ℚ) : ℝ)) ≤
      (sinhUpper (627 / 1250) : ℝ) := by
  rw [Real.sinh_eq]
  have hp := Real.exp_bound (x := (627 / 1250 : ℝ))
    (n := 25) (by norm_num) (by norm_num)
  have hn := Real.exp_bound (x := -(627 / 1250 : ℝ))
    (n := 25) (by norm_num) (by norm_num)
  have hp' := (abs_le.mp hp).2
  have hn' := (abs_le.mp hn).1
  rw [box12_sinhUpper]
  norm_num [Finset.sum_range_succ] at hp' hn' ⊢
  linarith

theorem box12_cosh_le :
    Real.cosh (((627 / 1250 : ℚ) : ℝ)) ≤
      (coshUpper (627 / 1250) : ℝ) := by
  rw [Real.cosh_eq]
  have hp := Real.exp_bound (x := (627 / 1250 : ℝ))
    (n := 25) (by norm_num) (by norm_num)
  have hn := Real.exp_bound (x := -(627 / 1250 : ℝ))
    (n := 25) (by norm_num) (by norm_num)
  have hp' := (abs_le.mp hp).2
  have hn' := (abs_le.mp hn).2
  rw [box12_coshUpperScalar]
  norm_num [Finset.sum_range_succ] at hp' hn' ⊢
  linarith

theorem box13_sinhUpper :
    sinhUpper (5643 / 10000) = 13174339707352110545843574189149640958141413743175991352549924928431343 / 22151828125423360000000000000000000000000000000000000000000000000000000 := by
  decide +kernel

theorem box13_coshUpperScalar :
    coshUpper (5643 / 10000) = 151584378880612161232688130378545982075023756157552576488579676359 / 130284507502822400000000000000000000000000000000000000000000000000 := by
  decide +kernel

theorem box13_sinh_le :
    Real.sinh (((5643 / 10000 : ℚ) : ℝ)) ≤
      (sinhUpper (5643 / 10000) : ℝ) := by
  rw [Real.sinh_eq]
  have hp := Real.exp_bound (x := (5643 / 10000 : ℝ))
    (n := 25) (by norm_num) (by norm_num)
  have hn := Real.exp_bound (x := -(5643 / 10000 : ℝ))
    (n := 25) (by norm_num) (by norm_num)
  have hp' := (abs_le.mp hp).2
  have hn' := (abs_le.mp hn).1
  rw [box13_sinhUpper]
  norm_num [Finset.sum_range_succ] at hp' hn' ⊢
  linarith

theorem box13_cosh_le :
    Real.cosh (((5643 / 10000 : ℚ) : ℝ)) ≤
      (coshUpper (5643 / 10000) : ℝ) := by
  rw [Real.cosh_eq]
  have hp := Real.exp_bound (x := (5643 / 10000 : ℝ))
    (n := 25) (by norm_num) (by norm_num)
  have hn := Real.exp_bound (x := -(5643 / 10000 : ℝ))
    (n := 25) (by norm_num) (by norm_num)
  have hp' := (abs_le.mp hp).2
  have hn' := (abs_le.mp hn).2
  rw [box13_coshUpperScalar]
  norm_num [Finset.sum_range_succ] at hp' hn' ⊢
  linarith

theorem box14_sinhUpper :
    sinhUpper (5643 / 10000) = 13174339707352110545843574189149640958141413743175991352549924928431343 / 22151828125423360000000000000000000000000000000000000000000000000000000 := by
  decide +kernel

theorem box14_coshUpperScalar :
    coshUpper (5643 / 10000) = 151584378880612161232688130378545982075023756157552576488579676359 / 130284507502822400000000000000000000000000000000000000000000000000 := by
  decide +kernel

theorem box14_sinh_le :
    Real.sinh (((5643 / 10000 : ℚ) : ℝ)) ≤
      (sinhUpper (5643 / 10000) : ℝ) := by
  rw [Real.sinh_eq]
  have hp := Real.exp_bound (x := (5643 / 10000 : ℝ))
    (n := 25) (by norm_num) (by norm_num)
  have hn := Real.exp_bound (x := -(5643 / 10000 : ℝ))
    (n := 25) (by norm_num) (by norm_num)
  have hp' := (abs_le.mp hp).2
  have hn' := (abs_le.mp hn).1
  rw [box14_sinhUpper]
  norm_num [Finset.sum_range_succ] at hp' hn' ⊢
  linarith

theorem box14_cosh_le :
    Real.cosh (((5643 / 10000 : ℚ) : ℝ)) ≤
      (coshUpper (5643 / 10000) : ℝ) := by
  rw [Real.cosh_eq]
  have hp := Real.exp_bound (x := (5643 / 10000 : ℝ))
    (n := 25) (by norm_num) (by norm_num)
  have hn := Real.exp_bound (x := -(5643 / 10000 : ℝ))
    (n := 25) (by norm_num) (by norm_num)
  have hp' := (abs_le.mp hp).2
  have hn' := (abs_le.mp hn).2
  rw [box14_coshUpperScalar]
  norm_num [Finset.sum_range_succ] at hp' hn' ⊢
  linarith

theorem box15_sinhUpper :
    sinhUpper (6941 / 10000) = 12123457754852660954865021609551540509718909501018755928789783102546605921 / 16138973796627951360000000000000000000000000000000000000000000000000000000 := by
  decide +kernel

theorem box15_coshUpperScalar :
    coshUpper (6941 / 10000) = 118708729755335196158256827231623062876399407327026057706232805009279 / 94912679924186342400000000000000000000000000000000000000000000000000 := by
  decide +kernel

theorem box15_sinh_le :
    Real.sinh (((6941 / 10000 : ℚ) : ℝ)) ≤
      (sinhUpper (6941 / 10000) : ℝ) := by
  rw [Real.sinh_eq]
  have hp := Real.exp_bound (x := (6941 / 10000 : ℝ))
    (n := 25) (by norm_num) (by norm_num)
  have hn := Real.exp_bound (x := -(6941 / 10000 : ℝ))
    (n := 25) (by norm_num) (by norm_num)
  have hp' := (abs_le.mp hp).2
  have hn' := (abs_le.mp hn).1
  rw [box15_sinhUpper]
  norm_num [Finset.sum_range_succ] at hp' hn' ⊢
  linarith

theorem box15_cosh_le :
    Real.cosh (((6941 / 10000 : ℚ) : ℝ)) ≤
      (coshUpper (6941 / 10000) : ℝ) := by
  rw [Real.cosh_eq]
  have hp := Real.exp_bound (x := (6941 / 10000 : ℝ))
    (n := 25) (by norm_num) (by norm_num)
  have hn := Real.exp_bound (x := -(6941 / 10000 : ℝ))
    (n := 25) (by norm_num) (by norm_num)
  have hp' := (abs_le.mp hp).2
  have hn' := (abs_le.mp hn).2
  rw [box15_coshUpperScalar]
  norm_num [Finset.sum_range_succ] at hp' hn' ⊢
  linarith

theorem box16_sinhUpper :
    sinhUpper (6941 / 10000) = 12123457754852660954865021609551540509718909501018755928789783102546605921 / 16138973796627951360000000000000000000000000000000000000000000000000000000 := by
  decide +kernel

theorem box16_coshUpperScalar :
    coshUpper (6941 / 10000) = 118708729755335196158256827231623062876399407327026057706232805009279 / 94912679924186342400000000000000000000000000000000000000000000000000 := by
  decide +kernel

theorem box16_sinh_le :
    Real.sinh (((6941 / 10000 : ℚ) : ℝ)) ≤
      (sinhUpper (6941 / 10000) : ℝ) := by
  rw [Real.sinh_eq]
  have hp := Real.exp_bound (x := (6941 / 10000 : ℝ))
    (n := 25) (by norm_num) (by norm_num)
  have hn := Real.exp_bound (x := -(6941 / 10000 : ℝ))
    (n := 25) (by norm_num) (by norm_num)
  have hp' := (abs_le.mp hp).2
  have hn' := (abs_le.mp hn).1
  rw [box16_sinhUpper]
  norm_num [Finset.sum_range_succ] at hp' hn' ⊢
  linarith

theorem box16_cosh_le :
    Real.cosh (((6941 / 10000 : ℚ) : ℝ)) ≤
      (coshUpper (6941 / 10000) : ℝ) := by
  rw [Real.cosh_eq]
  have hp := Real.exp_bound (x := (6941 / 10000 : ℝ))
    (n := 25) (by norm_num) (by norm_num)
  have hn := Real.exp_bound (x := -(6941 / 10000 : ℝ))
    (n := 25) (by norm_num) (by norm_num)
  have hp' := (abs_le.mp hp).2
  have hn' := (abs_le.mp hn).2
  rw [box16_coshUpperScalar]
  norm_num [Finset.sum_range_succ] at hp' hn' ⊢
  linarith

theorem box17_sinhUpper :
    sinhUpper (1893 / 2500) = 188556033926365452139634012052415311273974171776640219016188523 / 226722541291370391845703125000000000000000000000000000000000000 := by
  decide +kernel

theorem box17_coshUpperScalar :
    coshUpper (1893 / 2500) = 6936489473436027649054875990721203397123469408540333619949 / 5333145534696960449218750000000000000000000000000000000000 := by
  decide +kernel

theorem box17_sinh_le :
    Real.sinh (((1893 / 2500 : ℚ) : ℝ)) ≤
      (sinhUpper (1893 / 2500) : ℝ) := by
  rw [Real.sinh_eq]
  have hp := Real.exp_bound (x := (1893 / 2500 : ℝ))
    (n := 25) (by norm_num) (by norm_num)
  have hn := Real.exp_bound (x := -(1893 / 2500 : ℝ))
    (n := 25) (by norm_num) (by norm_num)
  have hp' := (abs_le.mp hp).2
  have hn' := (abs_le.mp hn).1
  rw [box17_sinhUpper]
  norm_num [Finset.sum_range_succ] at hp' hn' ⊢
  linarith

theorem box17_cosh_le :
    Real.cosh (((1893 / 2500 : ℚ) : ℝ)) ≤
      (coshUpper (1893 / 2500) : ℝ) := by
  rw [Real.cosh_eq]
  have hp := Real.exp_bound (x := (1893 / 2500 : ℝ))
    (n := 25) (by norm_num) (by norm_num)
  have hn := Real.exp_bound (x := -(1893 / 2500 : ℝ))
    (n := 25) (by norm_num) (by norm_num)
  have hp' := (abs_le.mp hp).2
  have hn' := (abs_le.mp hn).2
  rw [box17_coshUpperScalar]
  norm_num [Finset.sum_range_succ] at hp' hn' ⊢
  linarith

end CertifiedJL.SparseUpperHybrid.HyperbolicChecks
