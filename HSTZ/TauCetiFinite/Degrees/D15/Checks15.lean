import HSTZ.TauCetiFinite.Degrees.D15.Table

/-! Part of the degree-15 finite character certificate (`HSTZ.TauCetiFinite.D15`),
split into separate modules to bound memory use. -/
namespace HSTZ.TauCetiFinite.D15
open HSTZ.MurnaghanNakayama

theorem group120_checked : checkIndexedGroup table 120 = true := by decide

theorem group121_checked : checkIndexedGroup table 121 = true := by decide

theorem group122_checked : checkIndexedGroup table 122 = true := by decide

theorem group123_checked : checkIndexedGroup table 123 = true := by decide

theorem group124_checked : checkIndexedGroup table 124 = true := by decide

theorem group125_checked : checkIndexedGroup table 125 = true := by decide

theorem group126_checked : checkIndexedGroup table 126 = true := by decide

theorem group127_checked : checkIndexedGroup table 127 = true := by decide

end HSTZ.TauCetiFinite.D15
