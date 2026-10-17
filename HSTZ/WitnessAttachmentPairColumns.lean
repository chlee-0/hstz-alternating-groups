import HSTZ.PositionLayer
import OAI.RepresentationTheory.Saxl.PathAlternation

/-! Adjacent two-cell column factors of the attachment. Reuses `altWord_fiber_split`
and `pair_alt` from OpenAI's `math` repository (commit adc7f1241, Apache-2.0),
keeping the position order 2*c+r. -/
namespace HSTZ
noncomputable section
open OAI.Saxl

def attachmentPairColumnTag (b : ℕ) (i : Fin (2*b)) : ℕ := i.val/2
def attachmentPairColumnBase (b : ℕ) (i : Fin (2*b)) : Fin 2 :=
  ⟨i.val%2,Nat.mod_lt _ (by omega)⟩
def attachmentPairColumnAlt (b : ℕ) : WordSpace (2*b) 2 :=
  altWord (fiberGroup (attachmentPairColumnTag b)) (attachmentPairColumnBase b)

def attachmentAppendColumn (b : ℕ) : Fin (2*(b+1)) ≃ Fin (2*b) ⊕ Fin 2 :=
  (finCongr (by omega : 2*(b+1)=2*b+2)).trans finSumFinEquiv.symm

@[simp] theorem attachmentAppendColumn_left (b : ℕ) (i : Fin (2*b)) :
    ((attachmentAppendColumn b).symm (.inl i)).val=i.val := rfl
@[simp] theorem attachmentAppendColumn_right (b : ℕ) (i : Fin 2) :
    ((attachmentAppendColumn b).symm (.inr i)).val=2*b+i.val := rfl

theorem attachmentPairColumnTag_left (b : ℕ) (i : Fin (2*b)) :
    attachmentPairColumnTag (b+1) ((attachmentAppendColumn b).symm (.inl i))=
      attachmentPairColumnTag b i := rfl

theorem attachmentPairColumnTag_right (b : ℕ) (i : Fin 2) :
    attachmentPairColumnTag (b+1) ((attachmentAppendColumn b).symm (.inr i))=b := by
  unfold attachmentPairColumnTag
  rw [attachmentAppendColumn_right]
  have hi:=i.isLt
  omega

theorem attachmentAppendColumn_mask (b : ℕ) (i : Fin (2*(b+1))) :
    (attachmentAppendColumn b i).isLeft=true ↔ attachmentPairColumnTag (b+1) i<b := by
  obtain ⟨j,rfl⟩ := (attachmentAppendColumn b).symm.surjective i
  cases j with
  | inl j =>
    simp only [Equiv.apply_symm_apply,Sum.isLeft_inl,true_iff,attachmentPairColumnTag_left]
    unfold attachmentPairColumnTag
    have hj:=j.isLt
    omega
  | inr j =>
    simp only [Equiv.apply_symm_apply,Sum.isLeft_inr,Bool.false_eq_true,
      attachmentPairColumnTag_right,lt_self_iff_false]

theorem attachmentPairColumnAlt_step (b : ℕ) :
    attachmentPairColumnAlt (b+1)=positionProduct (attachmentAppendColumn b)
      (attachmentPairColumnAlt b) (altWord (⊤ : Subgroup (Equiv.Perm (Fin 2))) id) := by
  have hs : fiberGroup (attachmentPairColumnTag (b+1))=
      fiberGroup (attachmentPairColumnTag (b+1)) ⊓
        sectorGroup (fun i => (attachmentAppendColumn b i).isLeft=true) := by
    apply le_antisymm
    · intro g hg
      refine ⟨hg,?_⟩
      intro i
      change (attachmentAppendColumn b (g i)).isLeft=true ↔
        (attachmentAppendColumn b i).isLeft=true
      rw [attachmentAppendColumn_mask,attachmentAppendColumn_mask]
      change ∀ i, attachmentPairColumnTag (b+1) (g i)=attachmentPairColumnTag (b+1) i at hg
      rw [hg]
    · exact inf_le_left
  unfold attachmentPairColumnAlt
  rw [hs,altWord_fiber_split]
  have hl : (fun i => attachmentPairColumnTag (b+1)
      ((attachmentAppendColumn b).symm (.inl i)))=attachmentPairColumnTag b := rfl
  have hr : fiberGroup (fun i => attachmentPairColumnTag (b+1)
      ((attachmentAppendColumn b).symm (.inr i)))=⊤ := by
    ext g
    change (∀ i, _=_) ↔ True
    simp only [attachmentPairColumnTag_right,implies_true]
  rw [hl,hr]
  congr 2
  funext i
  apply Fin.ext
  change (2*b+i.val)%2=i.val
  have hi:=i.isLt
  omega

theorem attachmentPairColumnAlt_zero :
    attachmentPairColumnAlt 0=Pi.single (fun _ : Fin (2*0) => (0 : Fin 2)) (1:ℂ) := by
  classical
  unfold attachmentPairColumnAlt altWord
  letI := Fintype.ofFinite (fiberGroup (attachmentPairColumnTag 0))
  have hu : (Finset.univ : Finset (fiberGroup (attachmentPairColumnTag 0)))={1} := by
    ext g
    simp only [Finset.mem_univ,Finset.mem_singleton,true_iff]
    apply Subtype.ext
    apply Equiv.ext
    intro i
    exact Fin.elim0 i
  rw [hu,Finset.sum_singleton]
  simp only [OneMemClass.coe_one,map_one,one_smul]
  have hb : attachmentPairColumnBase 0=(fun _ : Fin (2*0) => (0 : Fin 2)) := by
    funext i
    exact Fin.elim0 i
  rw [hb]
  rfl

end
end HSTZ
#print axioms HSTZ.attachmentAppendColumn_mask
#print axioms HSTZ.attachmentPairColumnAlt_step
#print axioms HSTZ.attachmentPairColumnAlt_zero
