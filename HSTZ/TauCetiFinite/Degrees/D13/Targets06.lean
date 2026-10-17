import HSTZ.TauCetiFinite.Degrees.D13.Segments
import HSTZ.TauCetiFinite.Degrees.D13.Moments12

/-! Part of the degree-13 finite character certificate (`HSTZ.TauCetiFinite.D13`),
split into separate modules to bound memory use. -/
namespace HSTZ.TauCetiFinite.D13
open HSTZ.MurnaghanNakayama

theorem targetsSegment6 : ∀ nu ∈ classSegment6, ∃ refs,
    checkIndexedRow table nu classes refs = true ∧
    (2 * indexedCoverSum table 13 classes refs34 refs) % 1000000007 ≠ 0 := by
  intro nu hnu
  simp only [classSegment6, List.mem_cons, List.not_mem_nil, or_false] at hnu
  rcases hnu with rfl | rfl | rfl | rfl | rfl
  · exact ⟨refs96, row96_checked, residue96_checked⟩
  · exact ⟨refs97, row97_checked, residue97_checked⟩
  · exact ⟨refs98, row98_checked, residue98_checked⟩
  · exact ⟨refs99, row99_checked, residue99_checked⟩
  · exact ⟨refs100, row100_checked, residue100_checked⟩

end HSTZ.TauCetiFinite.D13
