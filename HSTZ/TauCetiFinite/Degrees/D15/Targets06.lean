import HSTZ.TauCetiFinite.Degrees.D15.Segments
import HSTZ.TauCetiFinite.Degrees.D15.Moments12
import HSTZ.TauCetiFinite.Degrees.D15.Moments13

/-! Part of the degree-15 finite character certificate (`HSTZ.TauCetiFinite.D15`),
split into separate modules to bound memory use. -/
namespace HSTZ.TauCetiFinite.D15
open HSTZ.MurnaghanNakayama

theorem targetsSegment6 : ∀ nu ∈ classSegment6, ∃ refs,
    checkIndexedRow table nu classes refs = true ∧
    (2 * indexedCoverSum table 15 classes refs49 refs) % 1000000007 ≠ 0 := by
  intro nu hnu
  simp only [classSegment6, List.mem_cons, List.not_mem_nil, or_false] at hnu
  rcases hnu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨refs96, row96_checked, residue96_checked⟩
  · exact ⟨refs97, row97_checked, residue97_checked⟩
  · exact ⟨refs98, row98_checked, residue98_checked⟩
  · exact ⟨refs99, row99_checked, residue99_checked⟩
  · exact ⟨refs100, row100_checked, residue100_checked⟩
  · exact ⟨refs101, row101_checked, residue101_checked⟩
  · exact ⟨refs102, row102_checked, residue102_checked⟩
  · exact ⟨refs103, row103_checked, residue103_checked⟩
  · exact ⟨refs104, row104_checked, residue104_checked⟩
  · exact ⟨refs105, row105_checked, residue105_checked⟩
  · exact ⟨refs106, row106_checked, residue106_checked⟩
  · exact ⟨refs107, row107_checked, residue107_checked⟩
  · exact ⟨refs108, row108_checked, residue108_checked⟩
  · exact ⟨refs109, row109_checked, residue109_checked⟩
  · exact ⟨refs110, row110_checked, residue110_checked⟩
  · exact ⟨refs111, row111_checked, residue111_checked⟩

end HSTZ.TauCetiFinite.D15
