import HSTZ.TauCetiFinite.Degrees.D15.Segments
import HSTZ.TauCetiFinite.Degrees.D15.Moments16
import HSTZ.TauCetiFinite.Degrees.D15.Moments17

/-! Part of the degree-15 finite character certificate (`HSTZ.TauCetiFinite.D15`),
split into separate modules to bound memory use. -/
namespace HSTZ.TauCetiFinite.D15
open HSTZ.MurnaghanNakayama

theorem targetsSegment8 : ∀ nu ∈ classSegment8, ∃ refs,
    checkIndexedRow table nu classes refs = true ∧
    (2 * indexedCoverSum table 15 classes refs49 refs) % 1000000007 ≠ 0 := by
  intro nu hnu
  simp only [classSegment8, List.mem_cons, List.not_mem_nil, or_false] at hnu
  rcases hnu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨refs128, row128_checked, residue128_checked⟩
  · exact ⟨refs129, row129_checked, residue129_checked⟩
  · exact ⟨refs130, row130_checked, residue130_checked⟩
  · exact ⟨refs131, row131_checked, residue131_checked⟩
  · exact ⟨refs132, row132_checked, residue132_checked⟩
  · exact ⟨refs133, row133_checked, residue133_checked⟩
  · exact ⟨refs134, row134_checked, residue134_checked⟩
  · exact ⟨refs135, row135_checked, residue135_checked⟩
  · exact ⟨refs136, row136_checked, residue136_checked⟩
  · exact ⟨refs137, row137_checked, residue137_checked⟩
  · exact ⟨refs138, row138_checked, residue138_checked⟩
  · exact ⟨refs139, row139_checked, residue139_checked⟩
  · exact ⟨refs140, row140_checked, residue140_checked⟩
  · exact ⟨refs141, row141_checked, residue141_checked⟩
  · exact ⟨refs142, row142_checked, residue142_checked⟩
  · exact ⟨refs143, row143_checked, residue143_checked⟩

end HSTZ.TauCetiFinite.D15
