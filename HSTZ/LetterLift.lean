import HSTZ.IntertwiningCompat
import HSTZ.StaircaseBlockCarrier
import OAI.RepresentationTheory.Saxl.PathAlternation

/-! Injective letter maps preserve word cyclic spaces, including the prescribed shifted
smaller-staircase vector. No universality is asserted. -/
namespace HSTZ
open scoped Classical TensorProduct

/-- Evaluate an injective letter lift on a lifted word. -/
theorem letterLift_eval {n d e : ℕ} (phi : Fin d → Fin e)
    (hphi : Function.Injective phi) (x : OAI.Saxl.WordSpace n d) (a : Fin n → Fin d) :
    OAI.Saxl.letterLift phi x (phi ∘ a) = x a := by
  change (∑ b : Fin n → Fin d, x b *
    ∏ i : Fin n, if phi (b i) = phi (a i) then (1 : ℂ) else 0) = x a
  rw [Finset.sum_eq_single a]
  · simp
  · intro b hb hne
    have hn : ∃ i, b i ≠ a i := by
      by_contra h
      push_neg at h
      exact hne (funext h)
    obtain ⟨i,hi⟩ := hn
    have hp : (∏ j : Fin n, if phi (b j) = phi (a j) then (1 : ℂ) else 0) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (if_neg (fun he => hi (hphi he)))
    rw [hp,mul_zero]
  · simp

theorem letterLift_injective {n d e : ℕ} (phi : Fin d → Fin e)
    (hphi : Function.Injective phi) : Function.Injective (OAI.Saxl.letterLift (n := n) phi) := by
  intro x y he
  funext a
  have h := congrArg (fun z : OAI.Saxl.WordSpace n e => z (phi ∘ a)) he
  simpa only [letterLift_eval phi hphi] using h

theorem highLetter_injective (h s : ℕ) : Function.Injective (OAI.Saxl.highLetter h s) := by
  intro a b he
  apply Fin.ext
  have hv := congrArg Fin.val he
  change a.val+s = b.val+s at hv
  omega

/-- Inverse native tensor coordinate map, with the diagonal position action. -/
noncomputable def wordTensorInverse (n d e : ℕ) : Representation.IntertwiningMap
    (OAI.Saxl.wordRep n (d*e)) ((OAI.Saxl.wordRep n d).tprod (OAI.Saxl.wordRep n e)) where
  toLinearMap := (OAI.Saxl.wordTensor n d e).symm.toLinearMap
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply (OAI.Saxl.wordTensor n d e).injective
    change OAI.Saxl.wordTensor n d e ((OAI.Saxl.wordTensor n d e).symm (_)) = _
    rw [LinearEquiv.apply_symm_apply]
    have he := OAI.Saxl.wordTensor_equivariant g ((OAI.Saxl.wordTensor n d e).symm x)
    rw [LinearEquiv.apply_symm_apply] at he
    exact he.symm

/-- Tensor letter maps, restricting the independent-layer map along the diagonal
position action. -/
noncomputable def tensorLetterLift {n d e D E : ℕ} (phi : Fin d → Fin D) (psi : Fin e → Fin E) :
    Representation.IntertwiningMap
      ((OAI.Saxl.wordRep n d).tprod (OAI.Saxl.wordRep n e))
      ((OAI.Saxl.wordRep n D).tprod (OAI.Saxl.wordRep n E)) where
  toLinearMap := TensorProduct.map (OAI.Saxl.letterLift phi).toLinearMap
    (OAI.Saxl.letterLift psi).toLinearMap
  isIntertwining' g := LinearMap.ext fun z =>
    (independentTensorMap (OAI.Saxl.letterLift phi) (OAI.Saxl.letterLift psi)).map_action (g,g) z

noncomputable def encodedLetterLift {n d e D E : ℕ} (phi : Fin d → Fin D) (psi : Fin e → Fin E) :=
  (OAI.Saxl.wordTensorIntertwiner n D E).comp
    ((tensorLetterLift phi psi).comp (wordTensorInverse n d e))

/-- Embedding of the full word module after injective letter changes. -/
theorem encodedLetterLift_injective {n d e D E : ℕ} (phi : Fin d → Fin D) (psi : Fin e → Fin E)
    (hphi : Function.Injective phi) (hpsi : Function.Injective psi) :
    Function.Injective (encodedLetterLift (n := n) phi psi) := by
  have ht := independentTensorMap_injective (OAI.Saxl.letterLift (n := n) phi)
    (OAI.Saxl.letterLift (n := n) psi) (letterLift_injective phi hphi) (letterLift_injective psi hpsi)
  exact (OAI.Saxl.wordTensor n D E).injective.comp
    (ht.comp (OAI.Saxl.wordTensor n d e).symm.injective)

/-- Formula for the tensor generating vector under the word embedding. -/
theorem encodedLetterLift_tensor {n d e D E : ℕ} (phi : Fin d → Fin D) (psi : Fin e → Fin E)
    (u : OAI.Saxl.WordSpace n d) (v : OAI.Saxl.WordSpace n e) :
    encodedLetterLift phi psi (OAI.Saxl.wordTensor n d e (u ⊗ₜ[ℂ] v)) =
      OAI.Saxl.wordTensor n D E (OAI.Saxl.letterLift phi u ⊗ₜ[ℂ] OAI.Saxl.letterLift psi v) := by
  change OAI.Saxl.wordTensor n D E
    (TensorProduct.map _ _ ((OAI.Saxl.wordTensor n d e).symm
      (OAI.Saxl.wordTensor n d e (u ⊗ₜ[ℂ] v)))) = _
  rw [LinearEquiv.symm_apply_apply,TensorProduct.map_tmul]
  rfl

noncomputable def shiftedCoreMap (h s : ℕ) :=
  encodedLetterLift (n := (OAI.Saxl.staircase h).card)
    (OAI.Saxl.highLetter h s) (OAI.Saxl.highLetter h s)

theorem shiftedCoreMap_generator (h s : ℕ) :
    shiftedCoreMap h s (OAI.Saxl.staircaseWord h) = shiftedCoreWord h s :=
  encodedLetterLift_tensor _ _ _ _

theorem shiftedCoreMap_injective (h s : ℕ) : Function.Injective (shiftedCoreMap h s) :=
  encodedLetterLift_injective _ _ (highLetter_injective h s) (highLetter_injective h s)

/-- Equivariant image of the original prescribed smaller-staircase space. -/
theorem shiftedCore_cyclic_image (h s : ℕ) :
    (cyclicSpan (OAI.Saxl.wordRep _ _) (OAI.Saxl.staircaseWord h)).map
      (shiftedCoreMap h s).toLinearMap =
    cyclicSpan (OAI.Saxl.wordRep _ _) (shiftedCoreWord h s) := by
  rw [cyclicSpan_image,shiftedCoreMap_generator]

theorem shiftedCore_cyclic_bijective (h s : ℕ) :
    Function.Bijective (cyclicImageMap (shiftedCoreMap h s) (OAI.Saxl.staircaseWord h)) := by
  constructor
  · intro x y he
    apply Subtype.ext
    exact shiftedCoreMap_injective h s (congrArg Subtype.val he)
  · exact cyclicImageMap_surjective _ _

end HSTZ
#print axioms HSTZ.letterLift_eval
#print axioms HSTZ.letterLift_injective
#print axioms HSTZ.encodedLetterLift_injective
#print axioms HSTZ.encodedLetterLift_tensor
#print axioms HSTZ.shiftedCoreMap_generator
#print axioms HSTZ.shiftedCore_cyclic_image
#print axioms HSTZ.shiftedCore_cyclic_bijective
