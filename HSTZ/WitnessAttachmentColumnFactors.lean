import HSTZ.WitnessAttachmentPairColumns
import HSTZ.WitnessAttachmentOrderedAlternant

/-! Full column fibers split into ordered paired columns and singletons.
Reuses fiber and tensor declarations from OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
The column order and the full groups are retained. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped TensorProduct

def attachmentColumnSplit (b delta : ℕ) :
    Fin (witnessAttachment b delta).card ≃ Fin (2*b) ⊕ Fin delta :=
  (witnessAttachmentColumnOrderFin b delta).symm.trans
    (Equiv.sumCongr
      ((finProdFinEquiv : Fin b × Fin 2 ≃ Fin (b*2)).trans
        (finCongr (by omega : b*2=2*b))) (Equiv.refl (Fin delta)))

theorem attachmentColumnSplit_label_left (b delta : ℕ) (i : Fin (2*b)) :
    witnessAttachmentOrderedColumnLabel b delta ((attachmentColumnSplit b delta).symm (.inl i))=
      attachmentPairColumnTag b i := by
  change witnessAttachmentOrderedColumn b delta
    ((witnessAttachmentColumnOrderFin b delta).symm
      ((witnessAttachmentColumnOrderFin b delta)
        (.inl (finProdFinEquiv.symm ((finCongr (by omega : b*2=2*b)).symm i)))))=_
  rw [Equiv.symm_apply_apply]
  rfl

theorem attachmentColumnSplit_label_right (b delta : ℕ) (i : Fin delta) :
    witnessAttachmentOrderedColumnLabel b delta ((attachmentColumnSplit b delta).symm (.inr i))=b+i.val := by
  change witnessAttachmentOrderedColumn b delta
    ((witnessAttachmentColumnOrderFin b delta).symm
      ((witnessAttachmentColumnOrderFin b delta) (.inr i)))=_
  rw [Equiv.symm_apply_apply]
  rfl

theorem attachmentColumnSplit_base_left (b delta : ℕ) (i : Fin (2*b)) :
    witnessAttachmentOrderedBinaryBase b delta ((attachmentColumnSplit b delta).symm (.inl i))=
      attachmentPairColumnBase b i := by
  change witnessAttachmentOrderedRow b delta
    ((witnessAttachmentColumnOrderFin b delta).symm
      ((witnessAttachmentColumnOrderFin b delta)
        (.inl (finProdFinEquiv.symm ((finCongr (by omega : b*2=2*b)).symm i)))))=_
  rw [Equiv.symm_apply_apply]
  apply Fin.ext
  rfl

theorem attachmentColumnSplit_base_right (b delta : ℕ) (i : Fin delta) :
    witnessAttachmentOrderedBinaryBase b delta ((attachmentColumnSplit b delta).symm (.inr i))=0 := by
  change witnessAttachmentOrderedRow b delta
    ((witnessAttachmentColumnOrderFin b delta).symm
      ((witnessAttachmentColumnOrderFin b delta) (.inr i)))=_
  rw [Equiv.symm_apply_apply]
  rfl

theorem attachmentColumnSplit_mask (b delta : ℕ) (i : Fin (witnessAttachment b delta).card) :
    (attachmentColumnSplit b delta i).isLeft=true ↔ witnessAttachmentOrderedColumnLabel b delta i<b := by
  obtain ⟨j,rfl⟩ := (attachmentColumnSplit b delta).symm.surjective i
  cases j with
  | inl j =>
    simp only [Equiv.apply_symm_apply,Sum.isLeft_inl,true_iff,attachmentColumnSplit_label_left]
    unfold attachmentPairColumnTag
    have hj:=j.isLt
    omega
  | inr j =>
    simp only [Equiv.apply_symm_apply,Sum.isLeft_inr,Bool.false_eq_true,attachmentColumnSplit_label_right,false_iff]
    omega

def attachmentSingletonColumnAlt (delta : ℕ) : WordSpace delta 2 :=
  altWord (fiberGroup (fun i : Fin delta => i.val)) (fun _ => 0)

def attachmentOrderedColumnAlt (b delta : ℕ) : WordSpace (witnessAttachment b delta).card 2 :=
  altWord (fiberGroup (witnessAttachmentOrderedColumnLabel b delta))
    (witnessAttachmentOrderedBinaryBase b delta)

theorem attachmentOrderedColumnAlt_factor (b delta : ℕ) :
    attachmentOrderedColumnAlt b delta=positionProduct (attachmentColumnSplit b delta)
      (attachmentPairColumnAlt b) (attachmentSingletonColumnAlt delta) := by
  have hs : fiberGroup (witnessAttachmentOrderedColumnLabel b delta)=
      fiberGroup (witnessAttachmentOrderedColumnLabel b delta) ⊓
        sectorGroup (fun i => (attachmentColumnSplit b delta i).isLeft=true) := by
    apply le_antisymm
    · intro g hg
      refine ⟨hg,?_⟩
      intro i
      change (attachmentColumnSplit b delta (g i)).isLeft=true ↔
        (attachmentColumnSplit b delta i).isLeft=true
      rw [attachmentColumnSplit_mask,attachmentColumnSplit_mask]
      change ∀ i, witnessAttachmentOrderedColumnLabel b delta (g i)=witnessAttachmentOrderedColumnLabel b delta i at hg
      rw [hg]
    · exact inf_le_left
  unfold attachmentOrderedColumnAlt
  rw [hs,altWord_fiber_split]
  have hl : (fun i => witnessAttachmentOrderedColumnLabel b delta
      ((attachmentColumnSplit b delta).symm (.inl i)))=attachmentPairColumnTag b :=
    funext (attachmentColumnSplit_label_left b delta)
  have hr : fiberGroup (fun i => witnessAttachmentOrderedColumnLabel b delta
      ((attachmentColumnSplit b delta).symm (.inr i)))=
      fiberGroup (fun i : Fin delta => i.val) := by
    ext g
    change (∀ i, _=_) ↔ (∀ i, _=_)
    simp only [attachmentColumnSplit_label_right,Nat.add_left_cancel_iff]
  have hbl : leftWord (attachmentColumnSplit b delta) (witnessAttachmentOrderedBinaryBase b delta)=
      attachmentPairColumnBase b := funext (attachmentColumnSplit_base_left b delta)
  have hbr : rightWord (attachmentColumnSplit b delta) (witnessAttachmentOrderedBinaryBase b delta)=
      (fun _ => 0) := funext (attachmentColumnSplit_base_right b delta)
  rw [hl,hr,hbl,hbr]
  rfl

theorem attachmentSingletonColumnAlt_single (delta : ℕ) :
    attachmentSingletonColumnAlt delta=Pi.single (fun _ : Fin delta => (0 : Fin 2)) (1:ℂ) := by
  classical
  unfold attachmentSingletonColumnAlt altWord
  letI := Fintype.ofFinite (fiberGroup (fun i : Fin delta => i.val))
  have hu : (Finset.univ : Finset (fiberGroup (fun i : Fin delta => i.val)))={1} := by
    ext g
    simp only [Finset.mem_univ,Finset.mem_singleton,true_iff]
    apply Subtype.ext
    apply Equiv.ext
    intro i
    exact Fin.ext (g.property i)
  rw [hu,Finset.sum_singleton]
  simp only [OneMemClass.coe_one,map_one,one_smul]
  rfl

/-- The repeated pair in the original canonical carrier, read in explicit column order. -/
def attachmentOrderedRepeatedWord (b delta : ℕ) : WordSpace (witnessAttachment b delta).card 4 :=
  wordTensor _ 2 2 (attachmentOrderedColumnAlt b delta ⊗ₜ[ℂ] attachmentOrderedColumnAlt b delta)

theorem attachmentOrderedRepeatedWord_encoding (b delta : ℕ)
    (w : Fin (witnessAttachment b delta).card → Fin 4) :
    witnessAttachmentBinaryRepeatedWord b delta
      (w ∘ (witnessAttachmentColumnEnumeration b delta).symm)=attachmentOrderedRepeatedWord b delta w := by
  have he := witnessAttachmentOrderedRepeated_coordinates b delta (splitLeft (d := 2) (e := 2) w) (splitRight (d := 2) (e := 2) w)
  have hm : mergeWords (splitLeft (d := 2) (e := 2) w ∘ (witnessAttachmentColumnEnumeration b delta).symm)
      (splitRight (d := 2) (e := 2) w ∘ (witnessAttachmentColumnEnumeration b delta).symm)=
      w ∘ (witnessAttachmentColumnEnumeration b delta).symm := by
    funext i
    exact congrFun (merge_split (d := 2) (e := 2) w) ((witnessAttachmentColumnEnumeration b delta).symm i)
  rw [hm] at he
  simpa only [attachmentOrderedRepeatedWord,wordTensor_tmul,attachmentOrderedColumnAlt] using he

end
end HSTZ
#print axioms HSTZ.attachmentColumnSplit_mask
#print axioms HSTZ.attachmentOrderedColumnAlt_factor
#print axioms HSTZ.attachmentSingletonColumnAlt_single
#print axioms HSTZ.attachmentOrderedRepeatedWord_encoding
