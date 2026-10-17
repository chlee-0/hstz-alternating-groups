import HSTZ.TauCetiFinite.Degrees.D15.Table

/-! Part of the degree-15 finite character certificate (`HSTZ.TauCetiFinite.D15`),
split into separate modules to bound memory use. -/
namespace HSTZ.TauCetiFinite.D15
open HSTZ.MurnaghanNakayama

theorem group32_checked : checkIndexedGroup table 32 = true := by decide

theorem group33_checked : checkIndexedGroup table 33 = true := by decide

theorem group34_checked : checkIndexedGroup table 34 = true := by decide

theorem group35_checked : checkIndexedGroup table 35 = true := by decide

theorem group36_checked : checkIndexedGroup table 36 = true := by decide

theorem group37_checked : checkIndexedGroup table 37 = true := by decide

theorem group38_checked : checkIndexedGroup table 38 = true := by decide

theorem group39_checked : checkIndexedGroup table 39 = true := by decide

end HSTZ.TauCetiFinite.D15
