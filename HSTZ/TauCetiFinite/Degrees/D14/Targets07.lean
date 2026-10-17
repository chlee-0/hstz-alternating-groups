import HSTZ.TauCetiFinite.Degrees.D14.Segments
import HSTZ.TauCetiFinite.Degrees.D14.Moments14
import HSTZ.TauCetiFinite.Degrees.D14.Moments15

/-! Part of the degree-14 finite character certificate (`HSTZ.TauCetiFinite.D14`),
split into separate modules to bound memory use. -/
namespace HSTZ.TauCetiFinite.D14
open HSTZ.MurnaghanNakayama

theorem targetsSegment7 : ∀ nu ∈ classSegment7, ∃ refs,
    checkIndexedRow table nu classes refs = true ∧
    (2 * indexedCoverSum table 14 classes refs48 refs) % 1000000007 ≠ 0 := by
  intro nu hnu
  simp only [classSegment7, List.mem_cons, List.not_mem_nil, or_false] at hnu
  rcases hnu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨refs112, row112_checked, residue112_checked⟩
  · exact ⟨refs113, row113_checked, residue113_checked⟩
  · exact ⟨refs114, row114_checked, residue114_checked⟩
  · exact ⟨refs115, row115_checked, residue115_checked⟩
  · exact ⟨refs116, row116_checked, residue116_checked⟩
  · exact ⟨refs117, row117_checked, residue117_checked⟩
  · exact ⟨refs118, row118_checked, residue118_checked⟩
  · exact ⟨refs119, row119_checked, residue119_checked⟩
  · exact ⟨refs120, row120_checked, residue120_checked⟩
  · exact ⟨refs121, row121_checked, residue121_checked⟩
  · exact ⟨refs122, row122_checked, residue122_checked⟩
  · exact ⟨refs123, row123_checked, residue123_checked⟩
  · exact ⟨refs124, row124_checked, residue124_checked⟩
  · exact ⟨refs125, row125_checked, residue125_checked⟩
  · exact ⟨refs126, row126_checked, residue126_checked⟩
  · exact ⟨refs127, row127_checked, residue127_checked⟩

end HSTZ.TauCetiFinite.D14
