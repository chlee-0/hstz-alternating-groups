import HSTZ.OneRowTensor
import HSTZ.InducedEmbedding

/-! Induce the split one-row tensor map. The explicit coordinate
retraction supplies injectivity for arbitrary groups and inducing homs. -/
namespace HSTZ
open scoped TensorProduct
section
variable {G H U : Type*} [Group G] [Group H] [AddCommGroup U] [Module ℂ U]
  (rho : Representation ℂ G U) {b : ℕ} {mu : YoungDiagram}
  (u : OAI.Saxl.Tableau b mu) (hmu : mu.colLen 0 ≤ 1)
  (phi : (G × Equiv.Perm (Fin b)) →* H)

noncomputable def oneRowInducedMap :=
  @inducedMap ℂ (G × Equiv.Perm (Fin b)) H U (U ⊗[ℂ] OAI.Saxl.Specht u)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    TensorProduct.addCommGroup TensorProduct.leftModule
    _ _ phi (oneRowTensorMap rho u hmu)

noncomputable def oneRowInducedRetraction :=
  @inducedMap ℂ (G × Equiv.Perm (Fin b)) H (U ⊗[ℂ] OAI.Saxl.Specht u) U
    inferInstance inferInstance inferInstance
    TensorProduct.addCommGroup TensorProduct.leftModule inferInstance inferInstance
    _ _ phi (oneRowTensorRetraction rho u hmu)

/-- The generator maps to the tensor with the polytabloid. -/
noncomputable def oneRowInducedMap_mk (g : H) (x : U) :=
  @inducedMap_mk ℂ (G × Equiv.Perm (Fin b)) H U (U ⊗[ℂ] OAI.Saxl.Specht u)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    TensorProduct.addCommGroup TensorProduct.leftModule
    _ _ phi (oneRowTensorMap rho u hmu) g x

theorem oneRowInduced_leftInverse :
    Function.LeftInverse (oneRowInducedRetraction rho u hmu phi).toLinearMap
      (oneRowInducedMap rho u hmu phi).toLinearMap :=
  @inducedMap_leftInverse ℂ (G × Equiv.Perm (Fin b)) H U (U ⊗[ℂ] OAI.Saxl.Specht u)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    TensorProduct.addCommGroup TensorProduct.leftModule
    _ _ phi (oneRowTensorMap rho u hmu) (oneRowTensorRetraction rho u hmu)
    (oneRowTensor_leftInverse rho u hmu)

theorem oneRowInducedMap_injective :
    Function.Injective (oneRowInducedMap rho u hmu phi).toLinearMap :=
  (oneRowInduced_leftInverse rho u hmu phi).injective

end
end HSTZ
#check HSTZ.oneRowInducedMap_mk
#print axioms HSTZ.oneRowInducedMap_mk
#print axioms HSTZ.oneRowInduced_leftInverse
#print axioms HSTZ.oneRowInducedMap_injective
