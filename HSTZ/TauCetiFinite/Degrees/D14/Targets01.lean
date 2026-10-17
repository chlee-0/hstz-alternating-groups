import HSTZ.TauCetiFinite.Degrees.D14.Segments
import HSTZ.TauCetiFinite.Degrees.D14.Moments02
import HSTZ.TauCetiFinite.Degrees.D14.Moments03

/-! Part of the degree-14 finite character certificate (`HSTZ.TauCetiFinite.D14`),
split into separate modules to bound memory use. -/
namespace HSTZ.TauCetiFinite.D14
open HSTZ.MurnaghanNakayama

theorem targetsSegment1 : ∀ nu ∈ classSegment1, ∃ refs,
    checkIndexedRow table nu classes refs = true ∧
    (2 * indexedCoverSum table 14 classes refs48 refs) % 1000000007 ≠ 0 := by
  intro nu hnu
  simp only [classSegment1, List.mem_cons, List.not_mem_nil, or_false] at hnu
  rcases hnu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨refs16, row16_checked, residue16_checked⟩
  · exact ⟨refs17, row17_checked, residue17_checked⟩
  · exact ⟨refs18, row18_checked, residue18_checked⟩
  · exact ⟨refs19, row19_checked, residue19_checked⟩
  · exact ⟨refs20, row20_checked, residue20_checked⟩
  · exact ⟨refs21, row21_checked, residue21_checked⟩
  · exact ⟨refs22, row22_checked, residue22_checked⟩
  · exact ⟨refs23, row23_checked, residue23_checked⟩
  · exact ⟨refs24, row24_checked, residue24_checked⟩
  · exact ⟨refs25, row25_checked, residue25_checked⟩
  · exact ⟨refs26, row26_checked, residue26_checked⟩
  · exact ⟨refs27, row27_checked, residue27_checked⟩
  · exact ⟨refs28, row28_checked, residue28_checked⟩
  · exact ⟨refs29, row29_checked, residue29_checked⟩
  · exact ⟨refs30, row30_checked, residue30_checked⟩
  · exact ⟨refs31, row31_checked, residue31_checked⟩

end HSTZ.TauCetiFinite.D14
