import HSTZ.TauCetiFinite.Degrees.D15.Segments
import HSTZ.TauCetiFinite.Degrees.D15.Moments18
import HSTZ.TauCetiFinite.Degrees.D15.Moments19

/-! Part of the degree-15 finite character certificate (`HSTZ.TauCetiFinite.D15`),
split into separate modules to bound memory use. -/
namespace HSTZ.TauCetiFinite.D15
open HSTZ.MurnaghanNakayama

theorem targetsSegment9 : ∀ nu ∈ classSegment9, ∃ refs,
    checkIndexedRow table nu classes refs = true ∧
    (2 * indexedCoverSum table 15 classes refs49 refs) % 1000000007 ≠ 0 := by
  intro nu hnu
  simp only [classSegment9, List.mem_cons, List.not_mem_nil, or_false] at hnu
  rcases hnu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨refs144, row144_checked, residue144_checked⟩
  · exact ⟨refs145, row145_checked, residue145_checked⟩
  · exact ⟨refs146, row146_checked, residue146_checked⟩
  · exact ⟨refs147, row147_checked, residue147_checked⟩
  · exact ⟨refs148, row148_checked, residue148_checked⟩
  · exact ⟨refs149, row149_checked, residue149_checked⟩
  · exact ⟨refs150, row150_checked, residue150_checked⟩
  · exact ⟨refs151, row151_checked, residue151_checked⟩
  · exact ⟨refs152, row152_checked, residue152_checked⟩
  · exact ⟨refs153, row153_checked, residue153_checked⟩
  · exact ⟨refs154, row154_checked, residue154_checked⟩
  · exact ⟨refs155, row155_checked, residue155_checked⟩
  · exact ⟨refs156, row156_checked, residue156_checked⟩
  · exact ⟨refs157, row157_checked, residue157_checked⟩
  · exact ⟨refs158, row158_checked, residue158_checked⟩
  · exact ⟨refs159, row159_checked, residue159_checked⟩

end HSTZ.TauCetiFinite.D15
