import HSTZ.WitnessPathCells

/-! The core and two-row attachment cells of the witness diagram, and their
embeddings into it. Uses the staircase from OpenAI's `math` repository
(commit adc7f1241, Apache-2.0) and Mathlib's `YoungDiagram.ofRowLens`. -/
namespace HSTZ
open OAI.Saxl

def witnessAttachment (b delta : ℕ) : YoungDiagram :=
  YoungDiagram.ofRowLens [b+delta,b] (by rw [List.sortedGE_iff_pairwise]; simp)

theorem mem_witnessAttachment (b delta i c : ℕ) :
    (i,c) ∈ witnessAttachment b delta ↔
      (i=0 ∧ c<b+delta) ∨ (i=1 ∧ c<b) := by
  rw [witnessAttachment, YoungDiagram.mem_ofRowLens]
  constructor
  · rintro ⟨hi,hc⟩
    have hi' : i<2 := by simpa using hi
    interval_cases i <;> simp_all
  · rintro (⟨rfl,hc⟩ | ⟨rfl,hc⟩) <;> exact ⟨by simp, by simpa using hc⟩

def witnessCoreCell (k b delta : ℕ) (hk : 5 ≤ k)
    (x : (staircase (k-2)).cells) : (witnessDiagram k b delta hk).cells :=
  ⟨x.val, by
    rcases x with ⟨⟨i,c⟩,hx⟩
    have hh : i+c<k-2 := mem_staircase.mp hx
    change (i,c) ∈ witnessDiagram k b delta hk
    apply YoungDiagram.mem_iff_lt_rowLen.mpr
    rw [witnessDiagram_row_length]
    unfold witnessRow
    split_ifs <;> omega⟩

theorem witnessCoreCell_injective (k b delta : ℕ) (hk : 5 ≤ k) :
    Function.Injective (witnessCoreCell k b delta hk) := by
  intro x y he
  apply Subtype.ext
  exact congrArg (fun z : (witnessDiagram k b delta hk).cells => z.val) he

def witnessAttachmentCell (k b delta : ℕ) (hk : 5 ≤ k)
    (x : (witnessAttachment b delta).cells) : (witnessDiagram k b delta hk).cells :=
  ⟨(x.val.1,k-1+x.val.2), by
    have hx := (mem_witnessAttachment b delta x.val.1 x.val.2).mp x.property
    apply YoungDiagram.mem_iff_lt_rowLen.mpr
    rw [witnessDiagram_row_length]
    unfold witnessRow
    rcases hx with ⟨hr,hc⟩ | ⟨hr,hc⟩ <;> split_ifs <;> omega⟩

theorem witnessAttachmentCell_injective (k b delta : ℕ) (hk : 5 ≤ k) :
    Function.Injective (witnessAttachmentCell k b delta hk) := by
  intro x y he
  apply Subtype.ext
  have he' := congrArg Subtype.val he
  change (x.val.1,k-1+x.val.2) = (y.val.1,k-1+y.val.2) at he'
  have hr := congrArg (fun z : ℕ × ℕ => z.1) he'
  have hc := congrArg (fun z : ℕ × ℕ => z.2) he'
  dsimp at hr hc
  exact Prod.ext hr (by omega)

theorem witnessCoreCell_value (k b delta : ℕ) (hk : 5 ≤ k)
    (x : (staircase (k-2)).cells) : (witnessCoreCell k b delta hk x).val=x.val := rfl

theorem witnessAttachmentCell_value (k b delta : ℕ) (hk : 5 ≤ k)
    (x : (witnessAttachment b delta).cells) :
    (witnessAttachmentCell k b delta hk x).val=(x.val.1,k-1+x.val.2) := rfl

end HSTZ
#print axioms HSTZ.mem_witnessAttachment
#print axioms HSTZ.witnessCoreCell_injective
#print axioms HSTZ.witnessAttachmentCell_injective
#print axioms HSTZ.witnessCoreCell_value
#print axioms HSTZ.witnessAttachmentCell_value
