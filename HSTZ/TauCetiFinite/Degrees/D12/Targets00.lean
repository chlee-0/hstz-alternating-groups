import HSTZ.TauCetiFinite.Degrees.D12.Segments
import HSTZ.TauCetiFinite.Degrees.D12.Moments00
import HSTZ.TauCetiFinite.Degrees.D12.Moments01

/-! Part of the degree-12 finite character certificate (`HSTZ.TauCetiFinite.D12`),
split into separate modules to bound memory use. -/
namespace HSTZ.TauCetiFinite.D12
open HSTZ.MurnaghanNakayama

theorem targetsSegment0 : ∀ nu ∈ classSegment0, ∃ refs,
    checkIndexedRow table nu classes refs = true ∧
    (2 * indexedCoverSum table 12 classes refs33 refs) % 1000000007 ≠ 0 := by
  intro nu hnu
  simp only [classSegment0, List.mem_cons, List.not_mem_nil, or_false] at hnu
  rcases hnu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨refs0, row0_checked, residue0_checked⟩
  · exact ⟨refs1, row1_checked, residue1_checked⟩
  · exact ⟨refs2, row2_checked, residue2_checked⟩
  · exact ⟨refs3, row3_checked, residue3_checked⟩
  · exact ⟨refs4, row4_checked, residue4_checked⟩
  · exact ⟨refs5, row5_checked, residue5_checked⟩
  · exact ⟨refs6, row6_checked, residue6_checked⟩
  · exact ⟨refs7, row7_checked, residue7_checked⟩
  · exact ⟨refs8, row8_checked, residue8_checked⟩
  · exact ⟨refs9, row9_checked, residue9_checked⟩
  · exact ⟨refs10, row10_checked, residue10_checked⟩
  · exact ⟨refs11, row11_checked, residue11_checked⟩
  · exact ⟨refs12, row12_checked, residue12_checked⟩
  · exact ⟨refs13, row13_checked, residue13_checked⟩
  · exact ⟨refs14, row14_checked, residue14_checked⟩
  · exact ⟨refs15, row15_checked, residue15_checked⟩

end HSTZ.TauCetiFinite.D12
