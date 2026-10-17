import HSTZ.WitnessSelectedProjection

/-! Ordered path/attachment factors after the sector projection. Reuses `fiberSplit`
and the tensor formula from OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
The unprojected full row group still has cross-block permutations. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped TensorProduct

def witnessSelectedPathRowWord (k b delta : ℕ) (hp : PaperWitnessGuard k b delta) :=
  altWord (fiberGroup (fun j : Fin (witnessPathSize k) =>
    (witnessPathPositionCell k b delta hp.staircase_bound j).val.1))
    (leftWord (witnessComplementOrder k b delta).symm
      (witnessExchangedRowBase k b delta hp.staircase_bound
        (paperWitness_attachment_positive k b delta hp)))
def witnessSelectedAttachmentRowWord (k b delta : ℕ) (hp : PaperWitnessGuard k b delta) :=
  altWord (fiberGroup (fun j : Fin (witnessAttachment b delta).card =>
    (witnessCanonicalAttachment b delta j).val.1))
    (rightWord (witnessComplementOrder k b delta).symm
      (witnessExchangedRowBase k b delta hp.staircase_bound
        (paperWitness_attachment_positive k b delta hp)))
def witnessSelectedPathColumnWord (k b delta : ℕ) (hp : PaperWitnessGuard k b delta) :=
  altWord (fiberGroup (fun j : Fin (witnessPathSize k) =>
    (witnessPathPositionCell k b delta hp.staircase_bound j).val.2))
    (leftWord (witnessComplementOrder k b delta).symm
      (witnessComplementColumnBase k b delta hp.staircase_bound))
def witnessSelectedAttachmentColumnWord (k b delta : ℕ) (hp : PaperWitnessGuard k b delta) :=
  altWord (fiberGroup (fun j : Fin (witnessAttachment b delta).card =>
    k-1+(witnessCanonicalAttachment b delta j).val.2))
    (rightWord (witnessComplementOrder k b delta).symm
      (witnessComplementColumnBase k b delta hp.staircase_bound))

theorem witness_selected_row_factor (k b delta : ℕ) (hp : PaperWitnessGuard k b delta) :
    witnessSelectedRowWord k b delta hp=
      positionProduct (witnessComplementOrder k b delta).symm
        (witnessSelectedPathRowWord k b delta hp)
        (witnessSelectedAttachmentRowWord k b delta hp) := by
  unfold witnessSelectedRowWord
  change altWord (fiberGroup (fun i => (witnessComplementCell k b delta hp.staircase_bound i).val.1) ⊓
    sectorGroup (fun i => ((witnessComplementOrder k b delta).symm i).isLeft=true)) _=_
  rw [altWord_fiber_split]
  simp only [Equiv.symm_symm,witnessComplementCell_path,witnessComplementCell_attachment]
  rfl

theorem witness_selected_column_factor (k b delta : ℕ) (hp : PaperWitnessGuard k b delta) :
    altWord (witnessComplementColumnGroup k b delta hp.staircase_bound)
      (witnessComplementColumnBase k b delta hp.staircase_bound)=
      positionProduct (witnessComplementOrder k b delta).symm
        (witnessSelectedPathColumnWord k b delta hp)
        (witnessSelectedAttachmentColumnWord k b delta hp) := by
  have hgroup : witnessComplementColumnGroup k b delta hp.staircase_bound ⊓
      sectorGroup (witnessComplementPathMask k b delta)=
      witnessComplementColumnGroup k b delta hp.staircase_bound :=
    inf_eq_left.mpr (witness_complement_column_sector k b delta hp.staircase_bound)
  rw [← hgroup]
  change altWord (fiberGroup (fun i => (witnessComplementCell k b delta hp.staircase_bound i).val.2) ⊓
    sectorGroup (fun i => ((witnessComplementOrder k b delta).symm i).isLeft=true)) _=_
  rw [altWord_fiber_split]
  simp only [Equiv.symm_symm,witnessComplementCell_path,witnessComplementCell_attachment]
  rfl

def witnessSelectedPathPairWord (k b delta : ℕ) (hp : PaperWitnessGuard k b delta) :=
  wordTensor _ _ _ (witnessSelectedPathRowWord k b delta hp ⊗ₜ[ℂ]
    witnessSelectedPathColumnWord k b delta hp)
def witnessSelectedAttachmentPairWord (k b delta : ℕ) (hp : PaperWitnessGuard k b delta) :=
  wordTensor _ _ _ (witnessSelectedAttachmentRowWord k b delta hp ⊗ₜ[ℂ]
    witnessSelectedAttachmentColumnWord k b delta hp)

theorem witness_selected_pair_factor (k b delta : ℕ) (hp : PaperWitnessGuard k b delta) :
    witnessSelectedComplementPairWord k b delta hp=
      positionProduct (witnessComplementOrder k b delta).symm
        (witnessSelectedPathPairWord k b delta hp)
        (witnessSelectedAttachmentPairWord k b delta hp) := by
  unfold witnessSelectedComplementPairWord
  rw [witness_selected_row_factor,witness_selected_column_factor,wordTensor_positionProduct]
  rfl

theorem witness_selected_pair_projected_factor (k b delta : ℕ) (hp : PaperWitnessGuard k b delta)
    {n : ℕ} (t : Tableau n (witnessDiagram k b delta hp.staircase_bound)) :
    witnessComplementLowProjection k b delta hp
      (witnessComplementPairWord k b delta hp.staircase_bound t)=
      -positionProduct (witnessComplementOrder k b delta).symm
        (witnessSelectedPathPairWord k b delta hp)
        (witnessSelectedAttachmentPairWord k b delta hp) := by
  rw [witness_selected_pair_projection,witness_selected_pair_factor]

theorem witnessSelectedPathPairWord_ne_zero (k b delta : ℕ) (hp : PaperWitnessGuard k b delta) :
    witnessSelectedPathPairWord k b delta hp≠0 := by
  intro hz
  have he := witness_selected_pair_factor k b delta hp
  rw [hz] at he
  have hh : positionProduct (witnessComplementOrder k b delta).symm 0
      (witnessSelectedAttachmentPairWord k b delta hp)=0 := by
    funext w
    exact zero_mul _
  rw [hh] at he
  exact witnessSelectedComplementPairWord_ne_zero k b delta hp he

theorem witnessSelectedAttachmentPairWord_ne_zero (k b delta : ℕ) (hp : PaperWitnessGuard k b delta) :
    witnessSelectedAttachmentPairWord k b delta hp≠0 := by
  intro hz
  have he := witness_selected_pair_factor k b delta hp
  rw [hz] at he
  have hh : positionProduct (witnessComplementOrder k b delta).symm
      (witnessSelectedPathPairWord k b delta hp) 0=0 := by
    funext w
    exact mul_zero _
  rw [hh] at he
  exact witnessSelectedComplementPairWord_ne_zero k b delta hp he

end
end HSTZ
#print axioms HSTZ.witness_selected_row_factor
#print axioms HSTZ.witness_selected_column_factor
#print axioms HSTZ.witness_selected_pair_factor
#print axioms HSTZ.witnessSelectedPathPairWord_ne_zero
#print axioms HSTZ.witnessSelectedAttachmentPairWord_ne_zero

#print axioms HSTZ.witness_selected_pair_projected_factor
