import HSTZ.TauCetiFinite.Degrees.D15.Table

/-! Part of the degree-15 finite character certificate (`HSTZ.TauCetiFinite.D15`),
split into separate modules to bound memory use. -/
namespace HSTZ.TauCetiFinite.D15
open HSTZ.MurnaghanNakayama

theorem group64_checked : checkIndexedGroup table 64 = true := by decide

theorem group65_checked : checkIndexedGroup table 65 = true := by decide

theorem group66_checked : checkIndexedGroup table 66 = true := by decide

theorem group67_checked : checkIndexedGroup table 67 = true := by decide

theorem group68_checked : checkIndexedGroup table 68 = true := by decide

theorem group69_checked : checkIndexedGroup table 69 = true := by decide

theorem group70_checked : checkIndexedGroup table 70 = true := by decide

theorem group71_checked : checkIndexedGroup table 71 = true := by decide

end HSTZ.TauCetiFinite.D15
