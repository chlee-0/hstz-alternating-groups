import HSTZ.TauCetiFinite.Degrees.D13.Table

/-! Part of the degree-13 finite character certificate (`HSTZ.TauCetiFinite.D13`),
split into separate modules to bound memory use. -/
namespace HSTZ.TauCetiFinite.D13
open HSTZ.MurnaghanNakayama

theorem group0_checked : checkIndexedGroup table 0 = true := by decide

theorem group1_checked : checkIndexedGroup table 1 = true := by decide

theorem group2_checked : checkIndexedGroup table 2 = true := by decide

theorem group3_checked : checkIndexedGroup table 3 = true := by decide

theorem group4_checked : checkIndexedGroup table 4 = true := by decide

theorem group5_checked : checkIndexedGroup table 5 = true := by decide

theorem group6_checked : checkIndexedGroup table 6 = true := by decide

theorem group7_checked : checkIndexedGroup table 7 = true := by decide

end HSTZ.TauCetiFinite.D13
