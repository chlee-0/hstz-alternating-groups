import HSTZ.WitnessAttachmentColumnFactors

/-! The ordered paper H tensor for the repeated attachment generator.
Reuses pair alternation, `wordTensor_positionProduct` and `wordTensor_single` from
OpenAI's `math` repository (commit adc7f1241, Apache-2.0). No target contraction is computed here. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped TensorProduct

/-- e00⊗e11 + e11⊗e00 - e01⊗e10 - e10⊗e01, with pair letter2*a+b. -/
def attachmentPaperH : WordSpace 2 4 :=
  Pi.single (![0,3] : Fin 2 → Fin 4) (1:ℂ) +
  Pi.single (![3,0] : Fin 2 → Fin 4) (1:ℂ) -
  Pi.single (![1,2] : Fin 2 → Fin 4) (1:ℂ) -
  Pi.single (![2,1] : Fin 2 → Fin 4) (1:ℂ)

def attachmentTwoCellRepeated : WordSpace 2 4 :=
  wordTensor 2 2 2
    (altWord (⊤ : Subgroup (Equiv.Perm (Fin 2))) id ⊗ₜ[ℂ]
      altWord (⊤ : Subgroup (Equiv.Perm (Fin 2))) id)

theorem attachmentTwoCellRepeated_H : attachmentTwoCellRepeated=attachmentPaperH := by
  funext w
  have hw : w=![w 0,w 1] := by ext i; fin_cases i <;> rfl
  unfold attachmentTwoCellRepeated
  rw [wordTensor_tmul]
  change altWord (⊤ : Subgroup (Equiv.Perm (Fin 2))) (fun i => i) (splitLeft (d := 2) (e := 2) w) *
    altWord (⊤ : Subgroup (Equiv.Perm (Fin 2))) (fun i => i) (splitRight (d := 2) (e := 2) w)=attachmentPaperH w
  rw [PathLayer.pair_alt,PathLayer.pair_alt,hw]
  generalize h0 : w 0=a
  generalize h1 : w 1=b
  fin_cases a <;> fin_cases b <;>
    norm_num [attachmentPaperH,splitLeft,splitRight,finProdFinEquiv,Fin.divNat,Fin.modNat,
      PathLayer.J,Pi.single_apply,funext_iff,Fin.forall_fin_two,Fin.ext_iff]

def attachmentRepeatedColumns (b : ℕ) : WordSpace (2*b) 4 :=
  wordTensor _ 2 2 (attachmentPairColumnAlt b ⊗ₜ[ℂ] attachmentPairColumnAlt b)

def attachmentHPower : (b : ℕ) → WordSpace (2*b) 4
  | 0 => Pi.single (fun _ => 0) (1:ℂ)
  | b+1 => positionProduct (attachmentAppendColumn b) (attachmentHPower b) attachmentPaperH

theorem attachmentRepeatedColumns_zero :
    attachmentRepeatedColumns 0=Pi.single (fun _ : Fin (2*0) => (0 : Fin 4)) (1:ℂ) := by
  unfold attachmentRepeatedColumns
  rw [attachmentPairColumnAlt_zero,wordTensor_single]
  have hm : mergeWords (fun _ : Fin (2*0) => (0 : Fin 2)) (fun _ => (0 : Fin 2))=
      (fun _ => (0 : Fin 4)) := by
    funext i
    exact Fin.elim0 i
  rw [hm]

theorem attachmentRepeatedColumns_step (b : ℕ) :
    attachmentRepeatedColumns (b+1)=positionProduct (attachmentAppendColumn b)
      (attachmentRepeatedColumns b) attachmentTwoCellRepeated := by
  unfold attachmentRepeatedColumns
  rw [attachmentPairColumnAlt_step,wordTensor_positionProduct]
  rfl

theorem attachmentRepeatedColumns_HPower (b : ℕ) :
    attachmentRepeatedColumns b=attachmentHPower b := by
  induction b with
  | zero => exact attachmentRepeatedColumns_zero
  | succ b ih =>
    change attachmentRepeatedColumns (b+1)=positionProduct (attachmentAppendColumn b)
      (attachmentHPower b) attachmentPaperH
    rw [attachmentRepeatedColumns_step,ih,attachmentTwoCellRepeated_H]

theorem attachmentOrderedRepeatedWord_factor (b delta : ℕ) :
    attachmentOrderedRepeatedWord b delta=positionProduct (attachmentColumnSplit b delta)
      (attachmentRepeatedColumns b) (Pi.single (fun _ : Fin delta => (0 : Fin 4)) (1:ℂ)) := by
  unfold attachmentOrderedRepeatedWord
  rw [attachmentOrderedColumnAlt_factor,wordTensor_positionProduct,
    attachmentSingletonColumnAlt_single,wordTensor_single]
  have hm : mergeWords (fun _ : Fin delta => (0 : Fin 2)) (fun _ => (0 : Fin 2))=
      (fun _ => (0 : Fin 4)) := by
    funext i
    apply Fin.ext
    rfl
  rw [hm]
  rfl

theorem attachmentOrderedRepeatedWord_HPower (b delta : ℕ) :
    attachmentOrderedRepeatedWord b delta=positionProduct (attachmentColumnSplit b delta)
      (attachmentHPower b) (Pi.single (fun _ : Fin delta => (0 : Fin 4)) (1:ℂ)) := by
  rw [attachmentOrderedRepeatedWord_factor,attachmentRepeatedColumns_HPower]

/-- All coordinates of the repeated canonical generator, in the fixed order. -/
theorem witnessAttachmentBinaryRepeated_HPower (b delta : ℕ)
    (w : Fin (witnessAttachment b delta).card → Fin 4) :
    witnessAttachmentBinaryRepeatedWord b delta
      (w ∘ (witnessAttachmentColumnEnumeration b delta).symm)=
      positionProduct (attachmentColumnSplit b delta) (attachmentHPower b)
        (Pi.single (fun _ : Fin delta => (0 : Fin 4)) (1:ℂ)) w := by
  rw [attachmentOrderedRepeatedWord_encoding,attachmentOrderedRepeatedWord_HPower]

/-- The coefficient form of the same paper H, on four-letter indices. -/
def attachmentHForm : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0,0,0,1; 0,0,-1,0; 0,-1,0,0; 1,0,0,0]

theorem attachmentPaperH_form (w : Fin 2 → Fin 4) :
    attachmentPaperH w=attachmentHForm (w 0) (w 1) := by
  have hw : w=![w 0,w 1] := by ext i; fin_cases i <;> rfl
  rw [hw]
  generalize h0 : w 0=a
  generalize h1 : w 1=b
  fin_cases a <;> fin_cases b <;>
    norm_num [attachmentPaperH,attachmentHForm,Pi.single_apply,funext_iff,Fin.forall_fin_two,Fin.ext_iff]

theorem attachmentHForm_symmetric : attachmentHForm.transpose=attachmentHForm := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [attachmentHForm,Matrix.transpose_apply]

theorem attachmentHForm_square : attachmentHForm*attachmentHForm=1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [attachmentHForm,Matrix.mul_apply,Fin.sum_univ_succ,Matrix.one_apply]

end
end HSTZ
#print axioms HSTZ.attachmentTwoCellRepeated_H
#print axioms HSTZ.attachmentRepeatedColumns_HPower
#print axioms HSTZ.attachmentOrderedRepeatedWord_HPower
#print axioms HSTZ.witnessAttachmentBinaryRepeated_HPower
#print axioms HSTZ.attachmentPaperH_form
#print axioms HSTZ.attachmentHForm_symmetric
#print axioms HSTZ.attachmentHForm_square
