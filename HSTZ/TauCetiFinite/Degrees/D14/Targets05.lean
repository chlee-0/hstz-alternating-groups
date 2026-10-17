import HSTZ.TauCetiFinite.Degrees.D14.Segments
import HSTZ.TauCetiFinite.Degrees.D14.Moments10
import HSTZ.TauCetiFinite.Degrees.D14.Moments11

/-! Part of the degree-14 finite character certificate (`HSTZ.TauCetiFinite.D14`),
split into separate modules to bound memory use. -/
namespace HSTZ.TauCetiFinite.D14
open HSTZ.MurnaghanNakayama

theorem targetsSegment5 : ∀ nu ∈ classSegment5, ∃ refs,
    checkIndexedRow table nu classes refs = true ∧
    (2 * indexedCoverSum table 14 classes refs48 refs) % 1000000007 ≠ 0 := by
  intro nu hnu
  simp only [classSegment5, List.mem_cons, List.not_mem_nil, or_false] at hnu
  rcases hnu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨refs80, row80_checked, residue80_checked⟩
  · exact ⟨refs81, row81_checked, residue81_checked⟩
  · exact ⟨refs82, row82_checked, residue82_checked⟩
  · exact ⟨refs83, row83_checked, residue83_checked⟩
  · exact ⟨refs84, row84_checked, residue84_checked⟩
  · exact ⟨refs85, row85_checked, residue85_checked⟩
  · exact ⟨refs86, row86_checked, residue86_checked⟩
  · exact ⟨refs87, row87_checked, residue87_checked⟩
  · exact ⟨refs88, row88_checked, residue88_checked⟩
  · exact ⟨refs89, row89_checked, residue89_checked⟩
  · exact ⟨refs90, row90_checked, residue90_checked⟩
  · exact ⟨refs91, row91_checked, residue91_checked⟩
  · exact ⟨refs92, row92_checked, residue92_checked⟩
  · exact ⟨refs93, row93_checked, residue93_checked⟩
  · exact ⟨refs94, row94_checked, residue94_checked⟩
  · exact ⟨refs95, row95_checked, residue95_checked⟩

end HSTZ.TauCetiFinite.D14
