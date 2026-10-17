import HSTZ.TauCetiFinite.Degrees.D15.Table

/-! Part of the degree-15 finite character certificate (`HSTZ.TauCetiFinite.D15`),
split into separate modules to bound memory use. -/
namespace HSTZ.TauCetiFinite.D15
open HSTZ.MurnaghanNakayama

theorem group128_checked : checkIndexedGroup table 128 = true := by decide

theorem group129_checked : checkIndexedGroup table 129 = true := by decide

theorem group130_checked : checkIndexedGroup table 130 = true := by decide

theorem group131_checked : checkIndexedGroup table 131 = true := by decide

theorem group132_checked : checkIndexedGroup table 132 = true := by decide

theorem group133_checked : checkIndexedGroup table 133 = true := by decide

theorem group134_checked : checkIndexedGroup table 134 = true := by decide

theorem group135_checked : checkIndexedGroup table 135 = true := by decide

end HSTZ.TauCetiFinite.D15
