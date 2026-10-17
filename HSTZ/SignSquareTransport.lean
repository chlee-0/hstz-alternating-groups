import HSTZ.IntertwiningCompat
import HSTZ.SpechtSignTransport

/-! Sign cancellation for diagonal tensor squares. This does not identify
independently generated layer spaces or prescribed cyclic generators. -/
namespace HSTZ
open OAI.Saxl
open scoped TensorProduct
noncomputable section
section Generic
variable {n : ℕ} {V W : Type*} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]
  {rho : Representation ℂ (Equiv.Perm (Fin n)) V}
  {sigma : Representation ℂ (Equiv.Perm (Fin n)) W}

/-- Tensoring the sign intertwiner with itself cancels the two scalar signs. -/
noncomputable def signSquareMap (f : Representation.IntertwiningMap rho (signTwist sigma)) :
    Representation.IntertwiningMap (rho.tprod rho) (sigma.tprod sigma) where
  toLinearMap := TensorProduct.map f.toLinearMap f.toLinearMap
  isIntertwining' g := by
    apply LinearMap.ext
    intro z
    have heq : (TensorProduct.map f.toLinearMap f.toLinearMap).comp (rho.tprod rho g) =
        (sigma.tprod sigma g).comp (TensorProduct.map f.toLinearMap f.toLinearMap) := by
      ext x y
      change f (rho g x) ⊗ₜ[ℂ] f (rho g y) =
        sigma g (f x) ⊗ₜ[ℂ] sigma g (f y)
      rw [Representation.IntertwiningMap.isIntertwining _ _ f,
        Representation.IntertwiningMap.isIntertwining _ _ f]
      change (signC g • sigma g (f x)) ⊗ₜ[ℂ] (signC g • sigma g (f y)) = _
      rw [TensorProduct.smul_tmul_smul, signC_mul_self, one_smul]
    exact DFunLike.congr_fun heq z

@[simp] theorem signSquareMap_tmul (f : Representation.IntertwiningMap rho (signTwist sigma))
    (x y : V) : signSquareMap f (x ⊗ₜ[ℂ] y) = f x ⊗ₜ[ℂ] f y := rfl
end Generic

noncomputable def spechtSignSquareMap {n : ℕ} {mu : YoungDiagram} (t : Tableau n mu) :
    Representation.IntertwiningMap ((spechtRep t).tprod (spechtRep t))
      ((spechtRep (transposeTableau t)).tprod (spechtRep (transposeTableau t))) :=
  signSquareMap (spechtSignMap t)

noncomputable def spechtSignSquareEquiv {n : ℕ} {mu : YoungDiagram} (t : Tableau n mu) :
    (Specht t ⊗[ℂ] Specht t) ≃ₗ[ℂ]
      (Specht (transposeTableau t) ⊗[ℂ] Specht (transposeTableau t)) :=
  TensorProduct.congr (spechtSignEquiv t) (spechtSignEquiv t)

theorem spechtSignSquareMap_bijective {n : ℕ} {mu : YoungDiagram} (t : Tableau n mu) :
    Function.Bijective (spechtSignSquareMap t).toLinearMap :=
  (spechtSignSquareEquiv t).bijective

noncomputable def spechtSignSquareInverseMap {n : ℕ} {mu : YoungDiagram} (t : Tableau n mu) :
    Representation.IntertwiningMap
      ((spechtRep (transposeTableau t)).tprod (spechtRep (transposeTableau t)))
      ((spechtRep t).tprod (spechtRep t)) where
  toLinearMap := (spechtSignSquareEquiv t).symm.toLinearMap
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply (spechtSignSquareEquiv t).injective
    have he : ∀ y, spechtSignSquareEquiv t (((spechtRep t).tprod (spechtRep t)) g y) =
        ((spechtRep (transposeTableau t)).tprod (spechtRep (transposeTableau t))) g
          (spechtSignSquareEquiv t y) := fun y => (spechtSignSquareMap t).map_action g y
    change spechtSignSquareEquiv t ((spechtSignSquareEquiv t).symm
      (((spechtRep (transposeTableau t)).tprod (spechtRep (transposeTableau t))) g x)) =
      spechtSignSquareEquiv t (((spechtRep t).tprod (spechtRep t)) g
        ((spechtSignSquareEquiv t).symm x))
    rw [LinearEquiv.apply_symm_apply, he, LinearEquiv.apply_symm_apply]

theorem spechtSignSquareMap_leftInverse {n : ℕ} {mu : YoungDiagram} (t : Tableau n mu) :
    Function.LeftInverse (spechtSignSquareInverseMap t) (spechtSignSquareMap t) := by
  intro x
  exact (spechtSignSquareEquiv t).symm_apply_apply x

theorem spechtSignSquareMap_rightInverse {n : ℕ} {mu : YoungDiagram} (t : Tableau n mu) :
    Function.RightInverse (spechtSignSquareInverseMap t) (spechtSignSquareMap t) := by
  intro x
  exact (spechtSignSquareEquiv t).apply_symm_apply x

end
end HSTZ
#print axioms HSTZ.signSquareMap
#print axioms HSTZ.signSquareMap_tmul
#print axioms HSTZ.spechtSignSquareMap_bijective
#print axioms HSTZ.spechtSignSquareInverseMap
#print axioms HSTZ.spechtSignSquareMap_leftInverse
#print axioms HSTZ.spechtSignSquareMap_rightInverse
