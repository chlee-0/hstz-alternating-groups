import HSTZ.TauCetiFinite.Degrees.D15.Segments
import HSTZ.TauCetiFinite.Degrees.D15.Moments04
import HSTZ.TauCetiFinite.Degrees.D15.Moments05

/-! Part of the degree-15 finite character certificate (`HSTZ.TauCetiFinite.D15`),
split into separate modules to bound memory use. -/
namespace HSTZ.TauCetiFinite.D15
open HSTZ.MurnaghanNakayama

theorem targetsSegment2 : ∀ nu ∈ classSegment2, ∃ refs,
    checkIndexedRow table nu classes refs = true ∧
    (2 * indexedCoverSum table 15 classes refs49 refs) % 1000000007 ≠ 0 := by
  intro nu hnu
  simp only [classSegment2, List.mem_cons, List.not_mem_nil, or_false] at hnu
  rcases hnu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨refs32, row32_checked, residue32_checked⟩
  · exact ⟨refs33, row33_checked, residue33_checked⟩
  · exact ⟨refs34, row34_checked, residue34_checked⟩
  · exact ⟨refs35, row35_checked, residue35_checked⟩
  · exact ⟨refs36, row36_checked, residue36_checked⟩
  · exact ⟨refs37, row37_checked, residue37_checked⟩
  · exact ⟨refs38, row38_checked, residue38_checked⟩
  · exact ⟨refs39, row39_checked, residue39_checked⟩
  · exact ⟨refs40, row40_checked, residue40_checked⟩
  · exact ⟨refs41, row41_checked, residue41_checked⟩
  · exact ⟨refs42, row42_checked, residue42_checked⟩
  · exact ⟨refs43, row43_checked, residue43_checked⟩
  · exact ⟨refs44, row44_checked, residue44_checked⟩
  · exact ⟨refs45, row45_checked, residue45_checked⟩
  · exact ⟨refs46, row46_checked, residue46_checked⟩
  · exact ⟨refs47, row47_checked, residue47_checked⟩

end HSTZ.TauCetiFinite.D15
