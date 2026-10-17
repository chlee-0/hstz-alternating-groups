import HSTZ.IntertwiningCompat
import HSTZ.WitnessNativePath

/-! Transport of the attachment column generator, keeping canonical positions.
Reuses `letterLift` from OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
The exchanged row factor requires a separate first-row rotation. -/
namespace HSTZ
noncomputable section
open OAI.Saxl

def witnessAttachmentColumnLetter (k b delta : ℕ) (hk : 5 ≤ k) :
    Fin ((witnessAttachment b delta).colLen 0) ↪
      Fin ((witnessDiagram k b delta hk).colLen 0) where
  toFun i := ⟨i.val,by
    rw [witnessDiagram_height]
    have hi := i.isLt
    have hh := witnessAttachment_rows b delta
    omega⟩
  inj' := by
    intro i j he
    exact Fin.ext (congrArg (fun x : Fin ((witnessDiagram k b delta hk).colLen 0) => x.val) he)

theorem witness_attachment_column_group (k b delta : ℕ) :
    fiberGroup (fun i : Fin (witnessAttachment b delta).card =>
      k-1+(witnessCanonicalAttachment b delta i).val.2)=
      columnGroup (witnessCanonicalAttachment b delta) := by
  ext g
  change (∀ i, k-1+(witnessCanonicalAttachment b delta (g i)).val.2=
    k-1+(witnessCanonicalAttachment b delta i).val.2) ↔
    (∀ i, (witnessCanonicalAttachment b delta (g i)).val.2=
      (witnessCanonicalAttachment b delta i).val.2)
  simp only [Nat.add_left_cancel_iff]

theorem witness_attachment_column_base (k b delta : ℕ) (hk : 5 ≤ k) :
    rightWord (witnessComplementOrder k b delta).symm (witnessComplementColumnBase k b delta hk)=
      witnessAttachmentColumnLetter k b delta hk ∘ rowWord (witnessCanonicalAttachment b delta) := by
  funext i
  apply Fin.ext
  have he := congrFun (witness_complement_column_base k b delta hk (witnessTableau k b delta hk))
    (witnessComplementOrder k b delta (.inr i))
  have hv := congrArg (fun x : Fin ((witnessDiagram k b delta hk).colLen 0) => x.val) he
  change (witnessAttachmentColumnRestriction k b delta hk (witnessTableau k b delta hk) i).val=
    (witnessComplementColumnBase k b delta hk (witnessComplementOrder k b delta (.inr i))).val at hv
  change (witnessComplementColumnBase k b delta hk (witnessComplementOrder k b delta (.inr i))).val=
    (witnessCanonicalAttachment b delta i).val.1
  rw [← hv,witness_attachment_column_value]

theorem witnessSelectedAttachmentColumnWord_generator (k b delta : ℕ)
    (hp : PaperWitnessGuard k b delta) :
    witnessSelectedAttachmentColumnWord k b delta hp=
      letterLift (witnessAttachmentColumnLetter k b delta hp.staircase_bound)
        (polytabloid (witnessCanonicalAttachment b delta)) := by
  unfold witnessSelectedAttachmentColumnWord
  rw [witness_attachment_column_group,witness_attachment_column_base,
    polytabloid_eq_altWord,letterLift_altWord]

def witnessAttachmentColumnCyclic (k b delta : ℕ) (hp : PaperWitnessGuard k b delta) :=
  cyclicSubrepresentation (wordRep _ _) (witnessSelectedAttachmentColumnWord k b delta hp)

/-- Every position permutation acts through the existing letter intertwiner. -/
def witnessAttachmentColumnSpechtMap (k b delta : ℕ) (hp : PaperWitnessGuard k b delta) :
    Representation.IntertwiningMap (spechtRep (witnessCanonicalAttachment b delta))
      (witnessAttachmentColumnCyclic k b delta hp).toRepresentation where
  toLinearMap := ((letterLift (witnessAttachmentColumnLetter k b delta hp.staircase_bound)).toLinearMap.domRestrict
    (spechtSub (witnessCanonicalAttachment b delta)).toSubmodule).codRestrict
      (witnessAttachmentColumnCyclic k b delta hp).toSubmodule (fun x => by
        have hx := cyclicSpan_apply_mem
          (letterLift (witnessAttachmentColumnLetter k b delta hp.staircase_bound))
          (polytabloid (witnessCanonicalAttachment b delta)) x.property
        rw [← witnessSelectedAttachmentColumnWord_generator] at hx
        exact hx)
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact (letterLift (witnessAttachmentColumnLetter k b delta hp.staircase_bound)).map_action g x.val

theorem witnessAttachmentColumnSpechtMap_injective (k b delta : ℕ)
    (hp : PaperWitnessGuard k b delta) : Function.Injective (witnessAttachmentColumnSpechtMap k b delta hp) := by
  intro x y he
  apply Subtype.ext
  exact letterLift_injective _ (witnessAttachmentColumnLetter k b delta hp.staircase_bound).injective
    (congrArg Subtype.val he)

theorem witnessAttachmentColumnSpechtMap_encoding (k b delta : ℕ)
    (hp : PaperWitnessGuard k b delta) (x : Specht (witnessCanonicalAttachment b delta)) :
    (witnessAttachmentColumnSpechtMap k b delta hp x).val=
      letterLift (witnessAttachmentColumnLetter k b delta hp.staircase_bound) x.val := rfl

end
end HSTZ
#print axioms HSTZ.witness_attachment_column_group
#print axioms HSTZ.witness_attachment_column_base
#print axioms HSTZ.witnessSelectedAttachmentColumnWord_generator
#print axioms HSTZ.witnessAttachmentColumnSpechtMap
#print axioms HSTZ.witnessAttachmentColumnSpechtMap_injective
#print axioms HSTZ.witnessAttachmentColumnSpechtMap_encoding
