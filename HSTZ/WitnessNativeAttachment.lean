import HSTZ.IntertwiningCompat
import HSTZ.WitnessAttachmentRowLetters
import HSTZ.WitnessNativeAttachmentColumn

/-! Transport of the signed paired canonical attachment generator, and the
cyclic bijection. Reuses the encoded letter lift and cyclic-image interfaces from
OpenAI's `math` repository (commit adc7f1241, Apache-2.0). The full diagonal positions are retained. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped TensorProduct

def witnessCanonicalAttachmentPair (b delta : ℕ) :
    WordSpace (witnessAttachment b delta).card
      ((witnessAttachment b delta).transpose.colLen 0 * (witnessAttachment b delta).colLen 0) :=
  wordTensor _ _ _ (polytabloid (transposeTableau (witnessCanonicalAttachment b delta)) ⊗ₜ[ℂ]
    polytabloid (witnessCanonicalAttachment b delta))

def witnessNativeAttachmentMap (k b delta : ℕ) (hk : 5 ≤ k) :
    Representation.IntertwiningMap
      (wordRep (witnessAttachment b delta).card
        ((witnessAttachment b delta).transpose.colLen 0 * (witnessAttachment b delta).colLen 0))
      (wordRep (witnessAttachment b delta).card
        ((witnessDiagram k b delta hk).transpose.colLen 0 * (witnessDiagram k b delta hk).colLen 0)) :=
  signC (witnessAttachmentCyclePositions b delta) •
    encodedLetterLift (n := (witnessAttachment b delta).card)
      (witnessAttachmentRowLetter k b delta hk) (witnessAttachmentColumnLetter k b delta hk)

theorem witnessNativeAttachmentMap_injective (k b delta : ℕ) (hk : 5 ≤ k) :
    Function.Injective (witnessNativeAttachmentMap k b delta hk) := by
  intro x y he
  apply encodedLetterLift_injective _ _ (witnessAttachmentRowLetter k b delta hk).injective
    (witnessAttachmentColumnLetter k b delta hk).injective
  change signC (witnessAttachmentCyclePositions b delta) • encodedLetterLift _ _ x=
    signC (witnessAttachmentCyclePositions b delta) • encodedLetterLift _ _ y at he
  have hh := congrArg (fun z : WordSpace (witnessAttachment b delta).card
    ((witnessDiagram k b delta hk).transpose.colLen 0 * (witnessDiagram k b delta hk).colLen 0) =>
    signC (witnessAttachmentCyclePositions b delta) • z) he
  simpa only [smul_smul,signC_mul_self,one_smul] using hh

theorem witnessNativeAttachmentMap_generator (k b delta : ℕ) (hp : PaperWitnessGuard k b delta) :
    witnessNativeAttachmentMap k b delta hp.staircase_bound (witnessCanonicalAttachmentPair b delta)=
      witnessSelectedAttachmentPairWord k b delta hp := by
  change signC (witnessAttachmentCyclePositions b delta) •
    encodedLetterLift _ _ (witnessCanonicalAttachmentPair b delta)=_
  unfold witnessCanonicalAttachmentPair witnessSelectedAttachmentPairWord
  rw [encodedLetterLift_tensor,witnessSelectedAttachmentRowWord_generator,
    witnessSelectedAttachmentColumnWord_generator,TensorProduct.smul_tmul,TensorProduct.tmul_smul,map_smul]

def witnessCanonicalAttachmentCyclic (b delta : ℕ) :=
  cyclicSubrepresentation (wordRep _ _) (witnessCanonicalAttachmentPair b delta)
def witnessAttachmentCyclic (k b delta : ℕ) (hp : PaperWitnessGuard k b delta) :=
  cyclicSubrepresentation (wordRep _ _) (witnessSelectedAttachmentPairWord k b delta hp)

theorem witnessNativeAttachmentMap_cyclic_image (k b delta : ℕ) (hp : PaperWitnessGuard k b delta) :
    (witnessCanonicalAttachmentCyclic b delta).toSubmodule.map
      (witnessNativeAttachmentMap k b delta hp.staircase_bound).toLinearMap=
      (witnessAttachmentCyclic k b delta hp).toSubmodule := by
  change (cyclicSpan (wordRep _ _) _).map _=cyclicSpan (wordRep _ _) _
  rw [cyclicSpan_image,witnessNativeAttachmentMap_generator]

def witnessNativeAttachmentCyclicMap (k b delta : ℕ) (hp : PaperWitnessGuard k b delta) :
    Representation.IntertwiningMap (witnessCanonicalAttachmentCyclic b delta).toRepresentation
      (witnessAttachmentCyclic k b delta hp).toRepresentation where
  toLinearMap := ((witnessNativeAttachmentMap k b delta hp.staircase_bound).toLinearMap.domRestrict
    (witnessCanonicalAttachmentCyclic b delta).toSubmodule).codRestrict
    (witnessAttachmentCyclic k b delta hp).toSubmodule (fun x => by
      have hx := cyclicSpan_apply_mem (witnessNativeAttachmentMap k b delta hp.staircase_bound)
        (witnessCanonicalAttachmentPair b delta) x.property
      rw [witnessNativeAttachmentMap_generator] at hx
      exact hx)
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact (witnessNativeAttachmentMap k b delta hp.staircase_bound).map_action g x.val

theorem witnessNativeAttachmentCyclicMap_encoding (k b delta : ℕ) (hp : PaperWitnessGuard k b delta)
    (x : witnessCanonicalAttachmentCyclic b delta) :
    (witnessNativeAttachmentCyclicMap k b delta hp x).val=
      witnessNativeAttachmentMap k b delta hp.staircase_bound x.val := rfl

theorem witnessNativeAttachmentCyclicMap_bijective (k b delta : ℕ) (hp : PaperWitnessGuard k b delta) :
    Function.Bijective (witnessNativeAttachmentCyclicMap k b delta hp) := by
  constructor
  · intro x y he
    apply Subtype.ext
    exact witnessNativeAttachmentMap_injective k b delta hp.staircase_bound (congrArg Subtype.val he)
  · intro y
    have hy : y.val ∈ (witnessCanonicalAttachmentCyclic b delta).toSubmodule.map
        (witnessNativeAttachmentMap k b delta hp.staircase_bound).toLinearMap :=
      (congrArg (fun S : Submodule ℂ (WordSpace (witnessAttachment b delta).card
        ((witnessDiagram k b delta hp.staircase_bound).transpose.colLen 0 *
          (witnessDiagram k b delta hp.staircase_bound).colLen 0)) => y.val ∈ S)
        (witnessNativeAttachmentMap_cyclic_image k b delta hp).symm).mp y.property
    obtain ⟨x,hx,he⟩ := Submodule.mem_map.mp hy
    exact ⟨⟨x,hx⟩,Subtype.ext he⟩

/-- Both canonical generators in the caller's ordered selected projection. -/
theorem witness_selected_native_factors (k b delta : ℕ) (hp : PaperWitnessGuard k b delta)
    {n : ℕ} (t : Tableau n (witnessDiagram k b delta hp.staircase_bound)) :
    witnessComplementLowProjection k b delta hp (witnessComplementPairWord k b delta hp.staircase_bound t)=
      -positionProduct (witnessComplementOrder k b delta).symm
        (witnessNativePathMap k b delta hp.staircase_bound (pathPairWord ((k-2)+1)))
        (witnessNativeAttachmentMap k b delta hp.staircase_bound (witnessCanonicalAttachmentPair b delta)) := by
  rw [witnessNativeAttachmentMap_generator]
  exact witness_selected_native_path_factor k b delta hp t

end
end HSTZ
#print axioms HSTZ.witnessNativeAttachmentMap_injective
#print axioms HSTZ.witnessNativeAttachmentMap_generator
#print axioms HSTZ.witnessNativeAttachmentMap_cyclic_image
#print axioms HSTZ.witnessNativeAttachmentCyclicMap
#print axioms HSTZ.witnessNativeAttachmentCyclicMap_encoding
#print axioms HSTZ.witnessNativeAttachmentCyclicMap_bijective
#print axioms HSTZ.witness_selected_native_factors
