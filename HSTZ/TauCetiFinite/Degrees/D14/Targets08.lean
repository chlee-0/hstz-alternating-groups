import HSTZ.TauCetiFinite.Degrees.D14.Segments
import HSTZ.TauCetiFinite.Degrees.D14.Moments16

/-! Part of the degree-14 finite character certificate (`HSTZ.TauCetiFinite.D14`),
split into separate modules to bound memory use. -/
namespace HSTZ.TauCetiFinite.D14
open HSTZ.MurnaghanNakayama

theorem targetsSegment8 : ∀ nu ∈ classSegment8, ∃ refs,
    checkIndexedRow table nu classes refs = true ∧
    (2 * indexedCoverSum table 14 classes refs48 refs) % 1000000007 ≠ 0 := by
  intro nu hnu
  simp only [classSegment8, List.mem_cons, List.not_mem_nil, or_false] at hnu
  rcases hnu with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨refs128, row128_checked, residue128_checked⟩
  · exact ⟨refs129, row129_checked, residue129_checked⟩
  · exact ⟨refs130, row130_checked, residue130_checked⟩
  · exact ⟨refs131, row131_checked, residue131_checked⟩
  · exact ⟨refs132, row132_checked, residue132_checked⟩
  · exact ⟨refs133, row133_checked, residue133_checked⟩
  · exact ⟨refs134, row134_checked, residue134_checked⟩

end HSTZ.TauCetiFinite.D14
