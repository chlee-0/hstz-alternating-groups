import HSTZ.IntertwiningCompat
import HSTZ.WitnessNativePathLetters
import HSTZ.FourRowSupport

/-! The native paired path generator, its injection for the full group, and its
use for the selected path factor. Uses results adapted from
OpenAI's `math` repository (commit adc7f1241, Apache-2.0). -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped TensorProduct

def witnessNativePathMap (k b delta : ℕ) (hk : 5 ≤ k) :=
  encodedLetterLift (n := witnessPathSize k)
    (witnessLowRowLetter k b delta hk) (witnessLowColumnLetter k b delta hk)

theorem witnessNativePathMap_injective (k b delta : ℕ) (hk : 5 ≤ k) :
    Function.Injective (witnessNativePathMap k b delta hk) :=
  encodedLetterLift_injective _ _ (witnessLowRowLetter k b delta hk).injective
    (witnessLowColumnLetter k b delta hk).injective

theorem witnessNativePathMap_generator (k b delta : ℕ) (hp : PaperWitnessGuard k b delta) :
    witnessNativePathMap k b delta hp.staircase_bound (pathPairWord ((k-2)+1))=
      witnessSelectedPathPairWord k b delta hp := by
  unfold witnessNativePathMap pathPairWord witnessSelectedPathPairWord
  rw [encodedLetterLift_tensor,← witness_native_path_row_word,← witness_native_path_column_word]

def witnessPathCyclic (k b delta : ℕ) (hp : PaperWitnessGuard k b delta) :=
  cyclicSubrepresentation (wordRep _ _) (witnessSelectedPathPairWord k b delta hp)

theorem witnessNativePathMap_cyclic_image (k b delta : ℕ) (hp : PaperWitnessGuard k b delta) :
    (cyclicSpan (wordRep _ 4) (pathPairWord ((k-2)+1))).map
      (witnessNativePathMap k b delta hp.staircase_bound).toLinearMap=
      (witnessPathCyclic k b delta hp).toSubmodule := by
  change _=cyclicSpan (wordRep _ _) _
  rw [cyclicSpan_image,witnessNativePathMap_generator]

def witnessNativePathCyclicMap (k b delta : ℕ) (hp : PaperWitnessGuard k b delta) :
    Representation.IntertwiningMap
      (cyclicSubrepresentation (wordRep _ 4) (pathPairWord ((k-2)+1))).toRepresentation
      (witnessPathCyclic k b delta hp).toRepresentation where
  toLinearMap := ((witnessNativePathMap k b delta hp.staircase_bound).toLinearMap.domRestrict
    (cyclicSpan (wordRep _ 4) (pathPairWord ((k-2)+1)))).codRestrict
    (witnessPathCyclic k b delta hp).toSubmodule (fun x => by
      have hx := cyclicSpan_apply_mem (witnessNativePathMap k b delta hp.staircase_bound)
        (pathPairWord ((k-2)+1)) x.property
      rw [witnessNativePathMap_generator] at hx
      exact hx)
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact (witnessNativePathMap k b delta hp.staircase_bound).map_action g x.val

theorem witnessNativePathCyclicMap_encoding (k b delta : ℕ) (hp : PaperWitnessGuard k b delta)
    (x : cyclicSubrepresentation (wordRep _ 4) (pathPairWord ((k-2)+1))) :
    (witnessNativePathCyclicMap k b delta hp x).val=
      witnessNativePathMap k b delta hp.staircase_bound x.val := rfl

theorem witnessNativePathCyclicMap_bijective (k b delta : ℕ) (hp : PaperWitnessGuard k b delta) :
    Function.Bijective (witnessNativePathCyclicMap k b delta hp) := by
  constructor
  · intro x y he
    apply Subtype.ext
    exact witnessNativePathMap_injective k b delta hp.staircase_bound (congrArg Subtype.val he)
  · intro y
    have hy : y.val ∈ (cyclicSpan (wordRep _ 4) (pathPairWord ((k-2)+1))).map
        (witnessNativePathMap k b delta hp.staircase_bound).toLinearMap :=
      (congrArg (fun S : Submodule ℂ (WordSpace (witnessPathSize k)
        ((witnessDiagram k b delta hp.staircase_bound).transpose.colLen 0 *
          (witnessDiagram k b delta hp.staircase_bound).colLen 0)) => y.val ∈ S)
        (witnessNativePathMap_cyclic_image k b delta hp).symm).mp y.property
    obtain ⟨x,hx,he⟩ := Submodule.mem_map.mp hy
    exact ⟨⟨x,hx⟩,Subtype.ext he⟩

theorem witnessSelectedPath_four_row_embedding (k b delta : ℕ) (hp : PaperWitnessGuard k b delta)
    {mu : YoungDiagram} (t : Tableau (witnessPathSize k) mu) (hmu : mu.colLen 0≤4) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (witnessPathCyclic k b delta hp).toRepresentation, Function.Injective F := by
  obtain ⟨F,hF⟩ := fourRow_pathPair_embedding ((k-2)+1) (by have hk := hp.staircase_bound; omega) t hmu
  exact ⟨(witnessNativePathCyclicMap k b delta hp).comp F,
    (witnessNativePathCyclicMap_bijective k b delta hp).1.comp hF⟩

/-- The projection keeps the ordered attachment factor unchanged. -/
theorem witness_selected_native_path_factor (k b delta : ℕ) (hp : PaperWitnessGuard k b delta)
    {n : ℕ} (t : Tableau n (witnessDiagram k b delta hp.staircase_bound)) :
    witnessComplementLowProjection k b delta hp
      (witnessComplementPairWord k b delta hp.staircase_bound t)=
      -positionProduct (witnessComplementOrder k b delta).symm
        (witnessNativePathMap k b delta hp.staircase_bound (pathPairWord ((k-2)+1)))
        (witnessSelectedAttachmentPairWord k b delta hp) := by
  rw [witnessNativePathMap_generator]
  exact witness_selected_pair_projected_factor k b delta hp t

end
end HSTZ
#print axioms HSTZ.witnessNativePathMap_injective
#print axioms HSTZ.witnessNativePathMap_generator
#print axioms HSTZ.witnessNativePathMap_cyclic_image
#print axioms HSTZ.witnessNativePathCyclicMap
#print axioms HSTZ.witnessNativePathCyclicMap_encoding
#print axioms HSTZ.witnessNativePathCyclicMap_bijective
#print axioms HSTZ.witnessSelectedPath_four_row_embedding

#print axioms HSTZ.witness_selected_native_path_factor
