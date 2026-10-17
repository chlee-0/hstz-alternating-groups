import HSTZ.CyclicSpan
import OAI.RepresentationTheory.Saxl.StaircaseTensor

/-! Positional reindexing as a linear equivalence.
Position-action and band-specific maps are connected separately below. -/
namespace HSTZ
open scoped Classical TensorProduct

noncomputable def positionRelabel {m n d : ℕ} (e : Fin m ≃ Fin n) :
    OAI.Saxl.WordSpace m d ≃ₗ[ℂ] OAI.Saxl.WordSpace n d :=
  LinearEquiv.funCongrLeft ℂ ℂ (Equiv.arrowCongr e.symm (Equiv.refl (Fin d)))

def positionPermHom {m n : ℕ} (e : Fin m ≃ Fin n) :
    Equiv.Perm (Fin m) →* Equiv.Perm (Fin n) where
  toFun g := e.permCongr g
  map_one' := by
    apply Equiv.ext
    intro i
    exact e.apply_symm_apply i
  map_mul' g h := by
    apply Equiv.ext
    intro i
    change e (g (h (e.symm i))) = e (g (e.symm (e (h (e.symm i)))))
    rw [e.symm_apply_apply]

theorem positionPermHom_bijective {m n : ℕ} (e : Fin m ≃ Fin n) :
    Function.Bijective (positionPermHom e) := e.permCongr.bijective

noncomputable def positionRelabelIntertwiner {m n d : ℕ} (e : Fin m ≃ Fin n) :
    Representation.IntertwiningMap (OAI.Saxl.wordRep m d)
      ((OAI.Saxl.wordRep n d).comp (positionPermHom e)) where
  toLinearMap := (positionRelabel e).toLinearMap
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    funext w
    change x ((w ∘ e) ∘ g) = x ((w ∘ (positionPermHom e g)) ∘ e)
    apply congrArg x
    funext i
    change w (e (g i)) = w (e (g (e.symm (e i))))
    rw [e.symm_apply_apply]

theorem positionRelabel_tensor {m n d f : ℕ} (e : Fin m ≃ Fin n)
    (u : OAI.Saxl.WordSpace m d) (v : OAI.Saxl.WordSpace m f) :
    positionRelabel e (OAI.Saxl.wordTensor m d f (u ⊗ₜ[ℂ] v)) =
      OAI.Saxl.wordTensor n d f (positionRelabel e u ⊗ₜ[ℂ] positionRelabel e v) := by
  funext w
  change OAI.Saxl.wordTensor m d f (u ⊗ₜ[ℂ] v) (w ∘ e) = _
  rw [OAI.Saxl.wordTensor_tmul,OAI.Saxl.wordTensor_tmul]
  rfl

end HSTZ
#print axioms HSTZ.positionRelabel
#print axioms HSTZ.positionPermHom_bijective
#print axioms HSTZ.positionRelabelIntertwiner
#print axioms HSTZ.positionRelabel_tensor
