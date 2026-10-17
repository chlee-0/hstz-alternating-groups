import HSTZ.TauCetiFinite.Degrees.D13.Table

/-! Part of the degree-13 finite character certificate (`HSTZ.TauCetiFinite.D13`),
split into separate modules to bound memory use. -/
namespace HSTZ.TauCetiFinite.D13
open HSTZ.MurnaghanNakayama

theorem group40_checked : checkIndexedGroup table 40 = true := by decide

theorem group41_checked : checkIndexedGroup table 41 = true := by decide

theorem group42_checked : checkIndexedGroup table 42 = true := by decide

theorem group43_checked : checkIndexedGroup table 43 = true := by decide

theorem group44_checked : checkIndexedGroup table 44 = true := by decide

theorem group45_checked : checkIndexedGroup table 45 = true := by decide

theorem group46_checked : checkIndexedGroup table 46 = true := by decide

theorem group47_checked : checkIndexedGroup table 47 = true := by decide

end HSTZ.TauCetiFinite.D13
