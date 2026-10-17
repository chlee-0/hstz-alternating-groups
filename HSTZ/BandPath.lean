import HSTZ.LetterLift
import HSTZ.BandPathLayers

namespace HSTZ
open scoped Classical TensorProduct

noncomputable def pathPairWord (r : ℕ) : OAI.Saxl.WordSpace (2*r+1) 4 :=
  OAI.Saxl.wordTensor _ 2 2 (OAI.Saxl.PathLayer.rowAlt r ⊗ₜ[ℂ]
    OAI.Saxl.wordRep _ 2 Fin.revPerm (OAI.Saxl.PathLayer.rowAlt r))

noncomputable def bandPathMap (h : ℕ) :=
  (positionRelabelIntertwiner (OAI.Saxl.bandPathEquiv h)).comp
    (encodedLetterLift (OAI.Saxl.lowLetter h) (OAI.Saxl.lowLetter h))

theorem bandPathMap_injective (h : ℕ) : Function.Injective (bandPathMap h) :=
  (positionRelabel (OAI.Saxl.bandPathEquiv h)).injective.comp
    (encodedLetterLift_injective _ _ (OAI.Saxl.lowLetter_injective h) (OAI.Saxl.lowLetter_injective h))

theorem bandPathMap_generator (h : ℕ) : bandPathMap h (pathPairWord (h+1)) = bandPairWord h 2 := by
  change positionRelabel (OAI.Saxl.bandPathEquiv h)
    (encodedLetterLift _ _ (OAI.Saxl.wordTensor _ 2 2 (_ ⊗ₜ[ℂ] _))) = _
  rw [encodedLetterLift_tensor,positionRelabel_tensor]
  rw [← bandRowWord_path,← bandColumnWord_path]
  rfl

/-- A surjective change of acting group does not change the orbit span. -/
theorem cyclicSpan_comp_surjective {R G H V : Type*} [CommRing R] [Monoid G] [Monoid H]
    [AddCommMonoid V] [Module R V] (rho : Representation R G V) (f : H →* G)
    (hf : Function.Surjective f) (v : V) : cyclicSpan (rho.comp f) v = cyclicSpan rho v := by
  unfold cyclicSpan
  apply congrArg (Submodule.span R)
  ext x
  constructor
  · rintro ⟨h,rfl⟩
    exact ⟨f h,rfl⟩
  · rintro ⟨g,rfl⟩
    obtain ⟨h,rfl⟩ := hf g
    exact ⟨h,rfl⟩

theorem bandPath_cyclic_image (h : ℕ) :
    (cyclicSpan (OAI.Saxl.wordRep _ 4) (pathPairWord (h+1))).map (bandPathMap h).toLinearMap =
    cyclicSpan (OAI.Saxl.wordRep _ _) (bandPairWord h 2) := by
  rw [cyclicSpan_image,bandPathMap_generator]
  exact cyclicSpan_comp_surjective _ _ (positionPermHom_bijective _).2 _

theorem bandPath_cyclic_bijective (h : ℕ) :
    Function.Bijective (cyclicImageMap (bandPathMap h) (pathPairWord (h+1))) := by
  constructor
  · intro x y he
    apply Subtype.ext
    exact bandPathMap_injective h (congrArg Subtype.val he)
  · exact cyclicImageMap_surjective _ _

end HSTZ
#print axioms HSTZ.bandPathMap_injective
#print axioms HSTZ.bandPathMap_generator
#print axioms HSTZ.cyclicSpan_comp_surjective
#print axioms HSTZ.bandPath_cyclic_image
#print axioms HSTZ.bandPath_cyclic_bijective
