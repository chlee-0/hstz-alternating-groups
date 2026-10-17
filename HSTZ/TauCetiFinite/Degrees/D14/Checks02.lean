import HSTZ.TauCetiFinite.Degrees.D14.Table

/-! Part of the degree-14 finite character certificate (`HSTZ.TauCetiFinite.D14`),
split into separate modules to bound memory use. -/
namespace HSTZ.TauCetiFinite.D14
open HSTZ.MurnaghanNakayama

theorem group16_checked : checkIndexedGroup table 16 = true := by decide

theorem group17_checked : checkIndexedGroup table 17 = true := by decide

theorem group18_checked : checkIndexedGroup table 18 = true := by decide

theorem group19_checked : checkIndexedGroup table 19 = true := by decide

theorem group20_checked : checkIndexedGroup table 20 = true := by decide

theorem group21_checked : checkIndexedGroup table 21 = true := by decide

theorem group22_checked : checkIndexedGroup table 22 = true := by decide

theorem group23_checked : checkIndexedGroup table 23 = true := by decide

end HSTZ.TauCetiFinite.D14
