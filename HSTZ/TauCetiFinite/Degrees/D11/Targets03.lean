import HSTZ.TauCetiFinite.Degrees.D11.Segments
import HSTZ.TauCetiFinite.Degrees.D11.Moments06

/-! Part of the degree-11 finite character certificate (`HSTZ.TauCetiFinite.D11`),
split into separate modules to bound memory use. -/
namespace HSTZ.TauCetiFinite.D11
open HSTZ.MurnaghanNakayama

theorem targetsSegment3 : ∀ nu ∈ classSegment3, ∃ refs,
    checkIndexedRow table nu classes refs = true ∧
    (2 * indexedCoverSum table 11 classes refs23 refs) % 1000000007 ≠ 0 := by
  intro nu hnu
  simp only [classSegment3, List.mem_cons, List.not_mem_nil, or_false] at hnu
  rcases hnu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨refs48, row48_checked, residue48_checked⟩
  · exact ⟨refs49, row49_checked, residue49_checked⟩
  · exact ⟨refs50, row50_checked, residue50_checked⟩
  · exact ⟨refs51, row51_checked, residue51_checked⟩
  · exact ⟨refs52, row52_checked, residue52_checked⟩
  · exact ⟨refs53, row53_checked, residue53_checked⟩
  · exact ⟨refs54, row54_checked, residue54_checked⟩
  · exact ⟨refs55, row55_checked, residue55_checked⟩

end HSTZ.TauCetiFinite.D11
