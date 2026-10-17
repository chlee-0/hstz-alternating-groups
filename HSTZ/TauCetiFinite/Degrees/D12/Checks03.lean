import HSTZ.TauCetiFinite.Degrees.D12.Table

/-! Part of the degree-12 finite character certificate (`HSTZ.TauCetiFinite.D12`),
split into separate modules to bound memory use. -/
namespace HSTZ.TauCetiFinite.D12
open HSTZ.MurnaghanNakayama

theorem group24_checked : checkIndexedGroup table 24 = true := by decide

theorem group25_checked : checkIndexedGroup table 25 = true := by decide

theorem group26_checked : checkIndexedGroup table 26 = true := by decide

theorem group27_checked : checkIndexedGroup table 27 = true := by decide

theorem group28_checked : checkIndexedGroup table 28 = true := by decide

end HSTZ.TauCetiFinite.D12
