import HSTZ.TauCetiFinite.Degrees.D15.Table

/-! Part of the degree-15 finite character certificate (`HSTZ.TauCetiFinite.D15`),
split into separate modules to bound memory use. -/
namespace HSTZ.TauCetiFinite.D15
open HSTZ.MurnaghanNakayama

theorem group144_checked : checkIndexedGroup table 144 = true := by decide

theorem group145_checked : checkIndexedGroup table 145 = true := by decide

theorem group146_checked : checkIndexedGroup table 146 = true := by decide

theorem group147_checked : checkIndexedGroup table 147 = true := by decide

end HSTZ.TauCetiFinite.D15
