import HSTZ.IntertwiningCompat
import HSTZ.WitnessNativeCoreLetters
import HSTZ.WitnessCoreFactorization

/-! Transport of the prescribed native staircase word into the asymmetric core.
Uses interfaces adapted from OpenAI's `math` repository (commit adc7f1241, Apache-2.0); the
existing `encodedLetterLift` and cyclic-image lemmas supply the maps. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped TensorProduct

abbrev WitnessCoreWordSpace (k b delta : ℕ) (hk : 5 ≤ k) :=
  WordSpace (staircase (k-2)).card
    ((witnessDiagram k b delta hk).transpose.colLen 0 * (witnessDiagram k b delta hk).colLen 0)

def witnessNativeCoreMap (k b delta : ℕ) (hk : 5 ≤ k) :
    Representation.IntertwiningMap
      (wordRep (staircase (k-2)).card ((staircase (k-2)).colLen 0 * (staircase (k-2)).colLen 0))
      (wordRep (staircase (k-2)).card
        ((witnessDiagram k b delta hk).transpose.colLen 0 * (witnessDiagram k b delta hk).colLen 0)) :=
  encodedLetterLift (witnessNativeCoreRowLetter k b delta hk) (witnessCoreColumnLetter k b delta hk)

theorem witnessNativeCoreMap_injective (k b delta : ℕ) (hk : 5 ≤ k) :
    Function.Injective (witnessNativeCoreMap k b delta hk) :=
  encodedLetterLift_injective _ _ (witnessNativeCoreRowLetter_injective k b delta hk)
    (witnessCoreColumnLetter_injective k b delta hk)

theorem witnessNativeCoreMap_generator (k b delta : ℕ) (hk : 5 ≤ k) :
    witnessNativeCoreMap k b delta hk (staircaseWord (k-2))=witnessEmbeddedCorePair k b delta hk := by
  unfold witnessNativeCoreMap staircaseWord witnessEmbeddedCorePair
  rw [encodedLetterLift_tensor,witness_native_core_row_polytabloid]

def witnessCoreCyclic (k b delta : ℕ) (hk : 5 ≤ k) : Subrepresentation
    (wordRep (staircase (k-2)).card
      ((witnessDiagram k b delta hk).transpose.colLen 0 * (witnessDiagram k b delta hk).colLen 0)) :=
  cyclicSubrepresentation (wordRep _ _) (witnessEmbeddedCorePair k b delta hk)

theorem witnessNativeCoreMap_cyclic_image (k b delta : ℕ) (hk : 5 ≤ k) :
    (staircaseCyclic (k-2)).toSubmodule.map (witnessNativeCoreMap k b delta hk).toLinearMap=
      (witnessCoreCyclic k b delta hk).toSubmodule := by
  change (cyclicSpan (wordRep _ _) (staircaseWord (k-2))).map _=
    cyclicSpan (wordRep _ _) (witnessEmbeddedCorePair k b delta hk)
  rw [cyclicSpan_image,witnessNativeCoreMap_generator]

/-- The original native source and the embedded-core cyclic target. -/
def witnessNativeCoreCyclicMap (k b delta : ℕ) (hk : 5 ≤ k) :
    Representation.IntertwiningMap (staircaseCyclic (k-2)).toRepresentation
      (witnessCoreCyclic k b delta hk).toRepresentation where
  toLinearMap := ((witnessNativeCoreMap k b delta hk).toLinearMap.domRestrict
    (staircaseCyclic (k-2)).toSubmodule).codRestrict (witnessCoreCyclic k b delta hk).toSubmodule
    (fun x => by
      have hx := cyclicSpan_apply_mem (witnessNativeCoreMap k b delta hk) (staircaseWord (k-2)) x.property
      rw [witnessNativeCoreMap_generator] at hx
      exact hx)
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact (witnessNativeCoreMap k b delta hk).map_action g x.val

theorem witnessNativeCoreCyclicMap_encoding (k b delta : ℕ) (hk : 5 ≤ k)
    (x : staircaseCyclic (k-2)) :
    (witnessNativeCoreCyclicMap k b delta hk x).val=witnessNativeCoreMap k b delta hk x.val := rfl

theorem witnessNativeCoreCyclicMap_bijective (k b delta : ℕ) (hk : 5 ≤ k) :
    Function.Bijective (witnessNativeCoreCyclicMap k b delta hk) := by
  constructor
  · intro x y he
    apply Subtype.ext
    exact witnessNativeCoreMap_injective k b delta hk (congrArg Subtype.val he)
  · intro y
    have hy : y.val ∈ (staircaseCyclic (k-2)).toSubmodule.map
        (witnessNativeCoreMap k b delta hk).toLinearMap :=
      (congrArg (fun S : Submodule ℂ (WitnessCoreWordSpace k b delta hk) => y.val ∈ S)
        (witnessNativeCoreMap_cyclic_image k b delta hk).symm).mp y.property
    obtain ⟨x,hx,he⟩ := Submodule.mem_map.mp hy
    exact ⟨⟨x,hx⟩,Subtype.ext he⟩

end
end HSTZ
#print axioms HSTZ.witnessNativeCoreMap_injective
#print axioms HSTZ.witnessNativeCoreMap_generator
#print axioms HSTZ.witnessNativeCoreMap_cyclic_image
#print axioms HSTZ.witnessNativeCoreCyclicMap
#print axioms HSTZ.witnessNativeCoreCyclicMap_encoding
#print axioms HSTZ.witnessNativeCoreCyclicMap_bijective
