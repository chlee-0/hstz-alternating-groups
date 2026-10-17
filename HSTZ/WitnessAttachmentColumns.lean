import HSTZ.WitnessAttachmentWords

/-! Column-ordered attachment cells and canonical positions.
Reuses tableau interfaces from OpenAI's `math` repository (commit adc7f1241, Apache-2.0). -/
namespace HSTZ
noncomputable section
open OAI.Saxl

abbrev WitnessAttachmentColumnOrder (b delta : ℕ) := (Fin b × Fin 2) ⊕ Fin delta

def witnessAttachmentColumnCell (b delta : ℕ) :
    WitnessAttachmentColumnOrder b delta → (witnessAttachment b delta).cells
  | .inl p => ⟨(p.2.val,p.1.val), by
      change (p.2.val,p.1.val) ∈ witnessAttachment b delta
      rw [mem_witnessAttachment]
      have hr := p.2.isLt
      have hc := p.1.isLt
      by_cases h : p.2.val=0
      · exact Or.inl ⟨h,by omega⟩
      · exact Or.inr ⟨by omega,hc⟩⟩
  | .inr j => ⟨(0,b+j.val), by
      change (0,b+j.val) ∈ witnessAttachment b delta
      rw [mem_witnessAttachment]
      exact Or.inl ⟨rfl,by have hj := j.isLt; omega⟩⟩

def witnessAttachmentColumnIndex (b delta : ℕ)
    (x : (witnessAttachment b delta).cells) : WitnessAttachmentColumnOrder b delta :=
  if hc : x.val.2 < b then
    .inl (⟨x.val.2,hc⟩,⟨x.val.1,by
      have hm := (mem_witnessAttachment b delta x.val.1 x.val.2).mp x.property
      rcases hm with h | h <;> omega⟩)
  else .inr ⟨x.val.2-b,by
    have hm := (mem_witnessAttachment b delta x.val.1 x.val.2).mp x.property
    rcases hm with h | h <;> omega⟩

theorem witnessAttachmentColumnIndex_cell (b delta : ℕ)
    (i : WitnessAttachmentColumnOrder b delta) :
    witnessAttachmentColumnIndex b delta (witnessAttachmentColumnCell b delta i)=i := by
  cases i with
  | inl p =>
    dsimp only [witnessAttachmentColumnCell,witnessAttachmentColumnIndex]
    split_ifs with hc
    · rfl
    · exact False.elim (hc p.1.isLt)
  | inr j =>
    dsimp only [witnessAttachmentColumnCell,witnessAttachmentColumnIndex]
    split_ifs with hc
    · change b+j.val<b at hc
      omega
    · congr 1
      apply Fin.ext
      change b+j.val-b = j.val
      omega

theorem witnessAttachmentColumnCell_index (b delta : ℕ)
    (x : (witnessAttachment b delta).cells) :
    witnessAttachmentColumnCell b delta (witnessAttachmentColumnIndex b delta x)=x := by
  apply Subtype.ext
  have hm := (mem_witnessAttachment b delta x.val.1 x.val.2).mp x.property
  dsimp only [witnessAttachmentColumnIndex]
  split_ifs with hc
  · rfl
  · change (0,b+(x.val.2-b))=x.val
    apply Prod.ext
    · rcases hm with h | h <;> omega
    · dsimp
      omega

def witnessAttachmentColumnCells (b delta : ℕ) :
    WitnessAttachmentColumnOrder b delta ≃ (witnessAttachment b delta).cells where
  toFun := witnessAttachmentColumnCell b delta
  invFun := witnessAttachmentColumnIndex b delta
  left_inv := witnessAttachmentColumnIndex_cell b delta
  right_inv := witnessAttachmentColumnCell_index b delta

def witnessAttachmentColumnPositions (b delta : ℕ) :
    WitnessAttachmentColumnOrder b delta ≃ Fin (witnessAttachment b delta).card :=
  (witnessAttachmentColumnCells b delta).trans (witnessCanonicalAttachment b delta).symm

theorem witnessAttachmentColumnPositions_cell (b delta : ℕ)
    (i : WitnessAttachmentColumnOrder b delta) :
    witnessCanonicalAttachment b delta (witnessAttachmentColumnPositions b delta i)=
      witnessAttachmentColumnCell b delta i :=
  (witnessCanonicalAttachment b delta).apply_symm_apply _

@[simp] theorem witnessAttachmentColumnCell_pair (b delta : ℕ) (c : Fin b) (r : Fin 2) :
    (witnessAttachmentColumnCell b delta (.inl (c,r))).val=(r.val,c.val) := rfl
@[simp] theorem witnessAttachmentColumnCell_single (b delta : ℕ) (j : Fin delta) :
    (witnessAttachmentColumnCell b delta (.inr j)).val=(0,b+j.val) := rfl

def witnessAttachmentOrderedColumn (b delta : ℕ) :
    WitnessAttachmentColumnOrder b delta → ℕ
  | .inl p => p.1.val
  | .inr j => b+j.val

def witnessAttachmentOrderedRow (b delta : ℕ) :
    WitnessAttachmentColumnOrder b delta → Fin 2
  | .inl p => p.2
  | .inr _ => 0

theorem witnessAttachmentColumnPositions_column (b delta : ℕ)
    (i : WitnessAttachmentColumnOrder b delta) :
    (witnessCanonicalAttachment b delta (witnessAttachmentColumnPositions b delta i)).val.2=
      witnessAttachmentOrderedColumn b delta i := by
  rw [witnessAttachmentColumnPositions_cell]
  cases i <;> rfl

theorem witnessAttachmentColumnPositions_row (b delta : ℕ)
    (i : WitnessAttachmentColumnOrder b delta) :
    (witnessCanonicalAttachment b delta (witnessAttachmentColumnPositions b delta i)).val.1=
      (witnessAttachmentOrderedRow b delta i).val := by
  rw [witnessAttachmentColumnPositions_cell]
  cases i <;> rfl

/-- Full canonical column fibers, tested at every explicitly ordered position. -/
theorem witnessAttachmentColumnGroup_ordered (b delta : ℕ)
    (g : Equiv.Perm (Fin (witnessAttachment b delta).card)) :
    g ∈ columnGroup (witnessCanonicalAttachment b delta) ↔
    ∀ i : WitnessAttachmentColumnOrder b delta,
      (witnessCanonicalAttachment b delta (g (witnessAttachmentColumnPositions b delta i))).val.2=
        witnessAttachmentOrderedColumn b delta i := by
  constructor
  · intro hg i
    exact (hg (witnessAttachmentColumnPositions b delta i)).trans
      (witnessAttachmentColumnPositions_column b delta i)
  · intro hg
    change ∀ j, _
    intro j
    have he := hg ((witnessAttachmentColumnPositions b delta).symm j)
    rw [Equiv.apply_symm_apply] at he
    simpa only [Equiv.apply_symm_apply] using
      he.trans (witnessAttachmentColumnPositions_column b delta
        ((witnessAttachmentColumnPositions b delta).symm j)).symm


end
end HSTZ
#print axioms HSTZ.witnessAttachmentColumnIndex_cell
#print axioms HSTZ.witnessAttachmentColumnCell_index
#print axioms HSTZ.witnessAttachmentColumnPositions
#print axioms HSTZ.witnessAttachmentColumnPositions_cell

#print axioms HSTZ.witnessAttachmentColumnPositions_column
#print axioms HSTZ.witnessAttachmentColumnPositions_row
#print axioms HSTZ.witnessAttachmentColumnGroup_ordered
