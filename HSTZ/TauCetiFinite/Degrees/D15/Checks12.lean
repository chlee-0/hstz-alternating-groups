import HSTZ.TauCetiFinite.Degrees.D15.Table

/-! Part of the degree-15 finite character certificate (`HSTZ.TauCetiFinite.D15`),
split into separate modules to bound memory use. -/
namespace HSTZ.TauCetiFinite.D15
open HSTZ.MurnaghanNakayama

theorem group96_checked : checkIndexedGroup table 96 = true := by decide

theorem group97_checked : checkIndexedGroup table 97 = true := by decide

theorem group98_checked : checkIndexedGroup table 98 = true := by decide

theorem group99_checked : checkIndexedGroup table 99 = true := by decide

theorem group100_checked : checkIndexedGroup table 100 = true := by decide

theorem group101_checked : checkIndexedGroup table 101 = true := by decide

theorem group102_checked : checkIndexedGroup table 102 = true := by decide

theorem group103_checked : checkIndexedGroup table 103 = true := by decide

end HSTZ.TauCetiFinite.D15
