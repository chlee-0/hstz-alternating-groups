import HSTZ.TauCetiFinite.Degrees.D13.Table

/-! Part of the degree-13 finite character certificate (`HSTZ.TauCetiFinite.D13`),
split into separate modules to bound memory use. -/
namespace HSTZ.TauCetiFinite.D13
open HSTZ.MurnaghanNakayama

theorem group48_checked : checkIndexedGroup table 48 = true := by decide

theorem group49_checked : checkIndexedGroup table 49 = true := by decide

end HSTZ.TauCetiFinite.D13
