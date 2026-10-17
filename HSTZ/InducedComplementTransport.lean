import Mathlib.Data.Complex.Basic
import HSTZ.InducedEmbedding
import HSTZ.IndependentTensor

/-! Transport full-product induced embeddings along a complement embedding. -/
namespace HSTZ
open scoped TensorProduct

theorem product_induced_embedding_transport_complement
    {G H A U W W' V : Type*} [Group G] [Group H] [Finite G] [Finite H] [Group A]
    [AddCommGroup U] [Module ℂ U] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup W'] [Module ℂ W'] [AddCommGroup V] [Module ℂ V]
    (phi : G × H →* A) (rho : Representation ℂ G U)
    (sigma : Representation ℂ H W) (sigma' : Representation ℂ H W')
    (tau : Representation ℂ A V)
    (j : Representation.IntertwiningMap sigma sigma') (hj : Function.Injective j)
    (E : Representation.IntertwiningMap tau
      (Representation.ind phi (independentTensor rho sigma))) (hE : Function.Injective E) :
    ∃ F : Representation.IntertwiningMap tau
      (Representation.ind phi (independentTensor rho sigma')), Function.Injective F := by
  letI : AddCommGroup (U ⊗[ℂ] W) := TensorProduct.addCommGroup
  letI : Module ℂ (U ⊗[ℂ] W) := TensorProduct.leftModule
  letI : AddCommGroup (U ⊗[ℂ] W') := TensorProduct.addCommGroup
  letI : Module ℂ (U ⊗[ℂ] W') := TensorProduct.leftModule
  letI : NeZero (Nat.card (G × H) : ℂ) :=
    ⟨by exact_mod_cast (Nat.card_pos : 0 < Nat.card (G × H)).ne'⟩
  let t : Representation.IntertwiningMap (independentTensor rho sigma)
      (independentTensor rho sigma') :=
    independentTensorMap (Representation.IntertwiningMap.id rho) j
  have ht : Function.Injective t :=
    independentTensorMap_injective (Representation.IntertwiningMap.id rho) j
      (fun _ _ h => h) hj
  let T := @inducedMap ℂ (G × H) A (U ⊗[ℂ] W) (U ⊗[ℂ] W')
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance (independentTensor rho sigma) (independentTensor rho sigma') phi t
  have hT : Function.Injective T := inducedMap_injective phi t ht
  exact ⟨T.comp E, hT.comp hE⟩

end HSTZ
#print axioms HSTZ.product_induced_embedding_transport_complement
