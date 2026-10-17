import HSTZ.YoungDiagramCompat
import HSTZ.WitnessAttachmentTargetParity

/-! Half-row target geometry for the contraction with the paper's H.
Builds on OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
The original row order is retained; the finite filter constructs floor(rowLen/2). -/
namespace HSTZ
noncomputable section
open OAI.Saxl

def attachmentTargetHalf (mu : YoungDiagram) : YoungDiagram where
  cells := mu.cells.filter (fun x => 2*x.2+1 < mu.rowLen x.1)
  isLowerSet := by
    intro x y hxy hy
    simp only [Finset.mem_coe, Finset.mem_filter] at hy ⊢
    refine ⟨mu.isLowerSet hxy hy.1, ?_⟩
    have hr := mu.rowLen_anti y.1 x.1 hxy.1
    have hc := hxy.2
    omega

theorem mem_attachmentTargetHalf (mu : YoungDiagram) (r c : ℕ) :
    (r,c) ∈ attachmentTargetHalf mu ↔ 2*c+1 < mu.rowLen r := by
  change (r,c) ∈ mu.cells.filter (fun x => 2*x.2+1 < mu.rowLen x.1) ↔ _
  rw [Finset.mem_filter, YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen]
  dsimp
  omega

theorem attachmentTargetHalf_rowLen (mu : YoungDiagram) (r : ℕ) :
    (attachmentTargetHalf mu).rowLen r = mu.rowLen r / 2 := by
  apply eq_of_forall_lt_iff
  intro c
  rw [← YoungDiagram.mem_iff_lt_rowLen, mem_attachmentTargetHalf]
  omega

abbrev AttachmentTargetPair (mu : YoungDiagram) := (attachmentTargetHalf mu).cells × Fin 2

def attachmentTargetPairCell (mu : YoungDiagram) (p : AttachmentTargetPair mu) : mu.cells :=
  ⟨(p.1.val.1,2*p.1.val.2+p.2.val), by
    have hm := (mem_attachmentTargetHalf mu p.1.val.1 p.1.val.2).mp p.1.property
    have hs := p.2.isLt
    apply YoungDiagram.mem_iff_lt_rowLen.mpr
    change 2*p.1.val.2+p.2.val < mu.rowLen p.1.val.1
    omega⟩

def attachmentTargetPairIndex (mu : YoungDiagram) (x : mu.cells)
    (hx : x.val.2 < 2*(mu.rowLen x.val.1/2)) : AttachmentTargetPair mu :=
  (⟨(x.val.1,x.val.2/2), by
    apply (mem_attachmentTargetHalf mu x.val.1 (x.val.2/2)).mpr
    omega⟩, ⟨x.val.2%2, Nat.mod_lt _ (by decide)⟩)

theorem attachmentTargetPairCell_bound (mu : YoungDiagram) (p : AttachmentTargetPair mu) :
    (attachmentTargetPairCell mu p).val.2 <
      2*(mu.rowLen (attachmentTargetPairCell mu p).val.1/2) := by
  have hm := (mem_attachmentTargetHalf mu p.1.val.1 p.1.val.2).mp p.1.property
  have hs := p.2.isLt
  change 2*p.1.val.2+p.2.val < 2*(mu.rowLen p.1.val.1/2)
  omega

theorem attachmentTargetPairIndex_cell (mu : YoungDiagram) (p : AttachmentTargetPair mu) :
    attachmentTargetPairIndex mu (attachmentTargetPairCell mu p)
      (attachmentTargetPairCell_bound mu p) = p := by
  apply Prod.ext
  · apply Subtype.ext
    apply Prod.ext
    · rfl
    · change (2*p.1.val.2+p.2.val)/2 = p.1.val.2
      have hs := p.2.isLt
      omega
  · apply Fin.ext
    change (2*p.1.val.2+p.2.val)%2 = p.2.val
    have hs := p.2.isLt
    omega

theorem attachmentTargetPairCell_index (mu : YoungDiagram) (x : mu.cells)
    (hx : x.val.2 < 2*(mu.rowLen x.val.1/2)) :
    attachmentTargetPairCell mu (attachmentTargetPairIndex mu x hx) = x := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change 2*(x.val.2/2)+x.val.2%2 = x.val.2
    omega

end
end HSTZ
#print axioms HSTZ.attachmentTargetHalf_rowLen
#print axioms HSTZ.attachmentTargetPairCell
#print axioms HSTZ.attachmentTargetPairIndex_cell
#print axioms HSTZ.attachmentTargetPairCell_index
