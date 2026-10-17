import HSTZ.TauCetiFinite.Degrees.D13.Table

/-! Part of the degree-13 finite character certificate (`HSTZ.TauCetiFinite.D13`),
split into separate modules to bound memory use. -/
namespace HSTZ.TauCetiFinite.D13
open HSTZ.MurnaghanNakayama

theorem group8_checked : checkIndexedGroup table 8 = true := by decide

theorem group9_checked : checkIndexedGroup table 9 = true := by decide

theorem group10_checked : checkIndexedGroup table 10 = true := by decide

theorem group11_checked : checkIndexedGroup table 11 = true := by decide

theorem group12_checked : checkIndexedGroup table 12 = true := by decide

theorem group13_checked : checkIndexedGroup table 13 = true := by decide

theorem group14_checked : checkIndexedGroup table 14 = true := by decide

theorem group15_checked : checkIndexedGroup table 15 = true := by decide

end HSTZ.TauCetiFinite.D13
