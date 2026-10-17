import HSTZ.IntertwiningCompat
import OAI.RepresentationTheory.Saxl.SignEquivalence

/-! Forward and inverse Specht sign-transpose maps.
The scalar sign action stays explicit on the original carriers. The mathematics
follows HSTZ and OpenAI's `math` repository; the isomorphism is constructed directly
rather than deduced from characters or dimensions. -/
namespace HSTZ
open OAI.Saxl
noncomputable section

noncomputable def spechtSignMap {n : ℕ} {mu : YoungDiagram} (t : Tableau n mu) :
    Representation.IntertwiningMap (spechtRep t)
      (signTwist (spechtRep (transposeTableau t))) :=
  (Classical.choice (specht_sign_transpose t)).toIntertwiningMap

theorem spechtSignMap_bijective {n : ℕ} {mu : YoungDiagram} (t : Tableau n mu) :
    Function.Bijective (spechtSignMap t).toLinearMap :=
  (Classical.choice (specht_sign_transpose t)).toLinearEquiv.bijective

noncomputable def spechtSignEquiv {n : ℕ} {mu : YoungDiagram} (t : Tableau n mu) :
    Specht t ≃ₗ[ℂ] Specht (transposeTableau t) :=
  LinearEquiv.ofBijective (spechtSignMap t).toLinearMap (spechtSignMap_bijective t)

theorem spechtSignEquiv_equivariant {n : ℕ} {mu : YoungDiagram} (t : Tableau n mu)
    (g : Equiv.Perm (Fin n)) (x : Specht t) :
    spechtSignEquiv t (spechtRep t g x) =
      signC g • spechtRep (transposeTableau t) g (spechtSignEquiv t x) :=
  (spechtSignMap t).map_action g x

noncomputable def spechtSignInverseMap {n : ℕ} {mu : YoungDiagram} (t : Tableau n mu) :
    Representation.IntertwiningMap (signTwist (spechtRep (transposeTableau t)))
      (spechtRep t) where
  toLinearMap := (spechtSignEquiv t).symm.toLinearMap
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply (spechtSignEquiv t).injective
    change spechtSignEquiv t ((spechtSignEquiv t).symm
      (signC g • spechtRep (transposeTableau t) g x)) =
      spechtSignEquiv t (spechtRep t g ((spechtSignEquiv t).symm x))
    rw [LinearEquiv.apply_symm_apply, spechtSignEquiv_equivariant,
      LinearEquiv.apply_symm_apply]

theorem spechtSignMap_leftInverse {n : ℕ} {mu : YoungDiagram} (t : Tableau n mu) :
    Function.LeftInverse (spechtSignInverseMap t) (spechtSignMap t) := by
  intro x
  exact (spechtSignEquiv t).symm_apply_apply x

theorem spechtSignMap_rightInverse {n : ℕ} {mu : YoungDiagram} (t : Tableau n mu) :
    Function.RightInverse (spechtSignInverseMap t) (spechtSignMap t) := by
  intro x
  exact (spechtSignEquiv t).apply_symm_apply x

end
end HSTZ
#print axioms HSTZ.spechtSignMap_bijective
#print axioms HSTZ.spechtSignEquiv_equivariant
#print axioms HSTZ.spechtSignInverseMap
#print axioms HSTZ.spechtSignMap_leftInverse
#print axioms HSTZ.spechtSignMap_rightInverse
