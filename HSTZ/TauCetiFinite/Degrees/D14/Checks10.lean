import HSTZ.TauCetiFinite.Degrees.D14.Table

/-! Part of the degree-14 finite character certificate (`HSTZ.TauCetiFinite.D14`),
split into separate modules to bound memory use. -/
namespace HSTZ.TauCetiFinite.D14
open HSTZ.MurnaghanNakayama

theorem group80_checked : checkIndexedGroup table 80 = true := by decide

theorem group81_checked : checkIndexedGroup table 81 = true := by decide

theorem group82_checked : checkIndexedGroup table 82 = true := by decide

theorem group83_checked : checkIndexedGroup table 83 = true := by decide

theorem group84_checked : checkIndexedGroup table 84 = true := by decide

theorem group85_checked : checkIndexedGroup table 85 = true := by decide

theorem group86_checked : checkIndexedGroup table 86 = true := by decide

theorem group87_checked : checkIndexedGroup table 87 = true := by decide

end HSTZ.TauCetiFinite.D14
