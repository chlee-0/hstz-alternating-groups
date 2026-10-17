import HSTZ.IndependentTensor
import HSTZ.InducedEmbedding
import HSTZ.InducedReparam

/-! Swapping the two tensor factors together with the factors of the inducing
product group; the ambient group is unchanged. These maps exchange position
factors, not word layers. No field, finiteness or dimension hypotheses are used. -/
namespace HSTZ
open scoped TensorProduct
section
variable {R G H A U W : Type*} [CommRing R] [Group G] [Group H] [Group A]
  [AddCommGroup U] [Module R U] [AddCommGroup W] [Module R W]

/-- The swap isomorphism `G × H ≃* H × G`. -/
def productSwap (G H : Type*) [Group G] [Group H] : G × H ≃* H × G where
  toFun := Prod.swap
  invFun := Prod.swap
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

variable (rho : Representation R G U) (sigma : Representation R H W)

noncomputable def tensorSwapMap : Representation.IntertwiningMap
    (independentTensor rho sigma)
    ((independentTensor sigma rho).comp (productSwap G H).toMonoidHom) where
  toLinearMap := (TensorProduct.comm R U W).toLinearMap
  isIntertwining' gh := by
    apply LinearMap.ext
    intro z
    have he : (TensorProduct.comm R U W).toLinearMap.comp (independentTensor rho sigma gh) =
        ((independentTensor sigma rho).comp (productSwap G H).toMonoidHom gh).comp
          (TensorProduct.comm R U W).toLinearMap := by
      ext u w
      rfl
    exact DFunLike.congr_fun he z

noncomputable def tensorSwapInverse : Representation.IntertwiningMap
    ((independentTensor sigma rho).comp (productSwap G H).toMonoidHom)
    (independentTensor rho sigma) where
  toLinearMap := (TensorProduct.comm R U W).symm.toLinearMap
  isIntertwining' gh := by
    apply LinearMap.ext
    intro z
    have he : (TensorProduct.comm R U W).symm.toLinearMap.comp
        ((independentTensor sigma rho).comp (productSwap G H).toMonoidHom gh) =
        (independentTensor rho sigma gh).comp (TensorProduct.comm R U W).symm.toLinearMap := by
      ext w u
      simp only [TensorProduct.comm_symm]
      rfl
    exact DFunLike.congr_fun he z

theorem tensorSwap_leftInverse : Function.LeftInverse
    (tensorSwapInverse rho sigma) (tensorSwapMap rho sigma) :=
  (TensorProduct.comm R U W).left_inv

theorem tensorSwap_rightInverse : Function.RightInverse
    (tensorSwapInverse rho sigma) (tensorSwapMap rho sigma) :=
  (TensorProduct.comm R U W).right_inv

variable (phi : G × H →* A)

theorem productSwap_inducing_normalization :
    (phi.comp (productSwap H G).toMonoidHom).comp (productSwap G H).toMonoidHom = phi := by
  ext gh
  rfl

noncomputable def inducedTensorSwap : Representation.IntertwiningMap
    (Representation.ind phi (independentTensor rho sigma))
    (Representation.ind (phi.comp (productSwap H G).toMonoidHom)
      (independentTensor sigma rho)) :=
  (inducedReparam (productSwap G H) (phi.comp (productSwap H G).toMonoidHom)
    (independentTensor sigma rho)).comp (inducedMap phi (tensorSwapMap rho sigma))

theorem inducedTensorSwap_mk (g : A) (z : U ⊗[R] W) :
    inducedTensorSwap rho sigma phi (Representation.IndV.mk phi (independentTensor rho sigma) g z) =
      Representation.IndV.mk (phi.comp (productSwap H G).toMonoidHom)
        (independentTensor sigma rho) g (TensorProduct.comm R U W z) := by
  change inducedReparam (productSwap G H) (phi.comp (productSwap H G).toMonoidHom)
    (independentTensor sigma rho) (inducedMap phi (tensorSwapMap rho sigma)
      (Representation.IndV.mk phi (independentTensor rho sigma) g z)) = _
  rw [inducedMap_mk]
  exact inducedReparam_mk (productSwap G H) (phi.comp (productSwap H G).toMonoidHom)
    (independentTensor sigma rho) g (tensorSwapMap rho sigma z)

theorem inducedTensorSwap_bijective : Function.Bijective (inducedTensorSwap rho sigma phi) := by
  have hT : Function.Bijective (inducedMap phi (tensorSwapMap rho sigma)) := by
    constructor
    · exact (inducedMap_leftInverse phi (tensorSwapMap rho sigma) (tensorSwapInverse rho sigma)
        (tensorSwap_leftInverse rho sigma)).injective
    · exact (inducedMap_leftInverse phi (tensorSwapInverse rho sigma) (tensorSwapMap rho sigma)
        (tensorSwap_rightInverse rho sigma)).surjective
  exact (inducedReparam_bijective (productSwap G H)
    (phi.comp (productSwap H G).toMonoidHom) (independentTensor sigma rho)).comp hT

end
end HSTZ
#print axioms HSTZ.tensorSwap_leftInverse
#print axioms HSTZ.tensorSwap_rightInverse
#print axioms HSTZ.productSwap_inducing_normalization
#print axioms HSTZ.inducedTensorSwap_mk
#print axioms HSTZ.inducedTensorSwap_bijective
