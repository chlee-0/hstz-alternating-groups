import HSTZ.TauCetiFinite.Degrees.D15.Segments
import HSTZ.TauCetiFinite.Degrees.D15.Moments20
import HSTZ.TauCetiFinite.Degrees.D15.Moments21

/-! Part of the degree-15 finite character certificate (`HSTZ.TauCetiFinite.D15`),
split into separate modules to bound memory use. -/
namespace HSTZ.TauCetiFinite.D15
open HSTZ.MurnaghanNakayama

theorem targetsSegment10 : ∀ nu ∈ classSegment10, ∃ refs,
    checkIndexedRow table nu classes refs = true ∧
    (2 * indexedCoverSum table 15 classes refs49 refs) % 1000000007 ≠ 0 := by
  intro nu hnu
  simp only [classSegment10, List.mem_cons, List.not_mem_nil, or_false] at hnu
  rcases hnu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨refs160, row160_checked, residue160_checked⟩
  · exact ⟨refs161, row161_checked, residue161_checked⟩
  · exact ⟨refs162, row162_checked, residue162_checked⟩
  · exact ⟨refs163, row163_checked, residue163_checked⟩
  · exact ⟨refs164, row164_checked, residue164_checked⟩
  · exact ⟨refs165, row165_checked, residue165_checked⟩
  · exact ⟨refs166, row166_checked, residue166_checked⟩
  · exact ⟨refs167, row167_checked, residue167_checked⟩
  · exact ⟨refs168, row168_checked, residue168_checked⟩
  · exact ⟨refs169, row169_checked, residue169_checked⟩
  · exact ⟨refs170, row170_checked, residue170_checked⟩
  · exact ⟨refs171, row171_checked, residue171_checked⟩
  · exact ⟨refs172, row172_checked, residue172_checked⟩
  · exact ⟨refs173, row173_checked, residue173_checked⟩
  · exact ⟨refs174, row174_checked, residue174_checked⟩
  · exact ⟨refs175, row175_checked, residue175_checked⟩

end HSTZ.TauCetiFinite.D15
