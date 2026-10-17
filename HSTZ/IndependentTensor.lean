import HSTZ.CyclicSpan
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! Tensor products with independent actions on the two factors, used before
the HSTZ/OpenAI balance projection. This file identifies the spaces only;
diagonal tensor cyclicity, disjoint sector induction, Specht identification and
support are separate steps. -/
namespace HSTZ
open TensorProduct

section Rings
variable {R G H V W : Type*} [CommRing R] [Monoid G] [Monoid H]
  [AddCommMonoid V] [Module R V] [AddCommMonoid W] [Module R W]

/-- Product-monoid action with independent elements in the two factors. -/
noncomputable def independentTensor (rho : Representation R G V)
    (sigma : Representation R H W) : Representation R (G × H) (V ⊗[R] W) :=
  Representation.tprod (rho.comp (MonoidHom.fst G H)) (sigma.comp (MonoidHom.snd G H))

@[simp] theorem independentTensor_tmul (rho : Representation R G V)
    (sigma : Representation R H W) (g : G) (h : H) (v : V) (w : W) :
    independentTensor rho sigma (g,h) (v ⊗ₜ[R] w) = rho g v ⊗ₜ[R] sigma h w := rfl

/-- Tensor product of intertwiners for independent actions on the two factors. -/
noncomputable def independentTensorMap {V' W' : Type*}
    [AddCommMonoid V'] [Module R V'] [AddCommMonoid W'] [Module R W']
    {rho : Representation R G V} {rho' : Representation R G V'}
    {sigma : Representation R H W} {sigma' : Representation R H W'}
    (phi : Representation.IntertwiningMap rho rho')
    (psi : Representation.IntertwiningMap sigma sigma') :
    Representation.IntertwiningMap (independentTensor rho sigma) (independentTensor rho' sigma') where
  toLinearMap := TensorProduct.map phi.toLinearMap psi.toLinearMap
  isIntertwining' gh := by
    apply LinearMap.ext
    intro z
    have heq : (TensorProduct.map phi.toLinearMap psi.toLinearMap).comp
        (independentTensor rho sigma gh) =
        (independentTensor rho' sigma' gh).comp (TensorProduct.map phi.toLinearMap psi.toLinearMap) := by
      ext u x
      change phi (rho gh.1 u) ⊗ₜ[R] psi (sigma gh.2 x) =
        rho' gh.1 (phi u) ⊗ₜ[R] sigma' gh.2 (psi x)
      rw [Representation.IntertwiningMap.isIntertwining _ _ phi,
        Representation.IntertwiningMap.isIntertwining _ _ psi]
    exact DFunLike.congr_fun heq z

/-- The independent orbit span maps onto the independent orbit span of the
two image generators. This is not a constituent occurrence assertion. -/
theorem independentTensorMap_cyclic_image {V' W' : Type*}
    [AddCommMonoid V'] [Module R V'] [AddCommMonoid W'] [Module R W']
    {rho : Representation R G V} {rho' : Representation R G V'}
    {sigma : Representation R H W} {sigma' : Representation R H W'}
    (phi : Representation.IntertwiningMap rho rho')
    (psi : Representation.IntertwiningMap sigma sigma') (v : V) (w : W) :
    (cyclicSpan (independentTensor rho sigma) (v ⊗ₜ[R] w)).map
        (independentTensorMap phi psi).toLinearMap =
      cyclicSpan (independentTensor rho' sigma') (phi v ⊗ₜ[R] psi w) :=
  cyclicSpan_image (independentTensorMap phi psi) (v ⊗ₜ[R] w)

/-- Tensor inclusion of the two cyclic factors has as range exactly the span
of independently generated pure tensors, over any commutative ring. -/
theorem cyclic_tensor_range (rho : Representation R G V)
    (sigma : Representation R H W) (v : V) (w : W) :
    LinearMap.range (TensorProduct.mapIncl (cyclicSpan rho v) (cyclicSpan sigma w)) =
      Submodule.span R (Set.range (fun gh : G × H => rho gh.1 v ⊗ₜ[R] sigma gh.2 w)) := by
  rw [TensorProduct.range_mapIncl,cyclicSpan,cyclicSpan,Submodule.map₂_span_span]
  apply congrArg (Submodule.span R)
  ext z
  constructor
  · rintro ⟨_,⟨g,rfl⟩,_,⟨h,rfl⟩,rfl⟩
    exact ⟨(g,h),rfl⟩
  · rintro ⟨⟨g,h⟩,rfl⟩
    exact ⟨rho g v,⟨g,rfl⟩,sigma h w,⟨h,rfl⟩,rfl⟩

/-- The same range is the prescribed pure tensor's product-monoid cyclic span. -/
theorem cyclic_tensor_range_eq (rho : Representation R G V)
    (sigma : Representation R H W) (v : V) (w : W) :
    LinearMap.range (TensorProduct.mapIncl (cyclicSpan rho v) (cyclicSpan sigma w)) =
      cyclicSpan (independentTensor rho sigma) (v ⊗ₜ[R] w) := by
  rw [cyclic_tensor_range,cyclicSpan]
  rfl

/-- Equivariant inclusion of the independently generated factors. -/
noncomputable def cyclicTensorInclusion (rho : Representation R G V)
    (sigma : Representation R H W) (v : V) (w : W) :
    Representation.IntertwiningMap
      (independentTensor (cyclicSubrepresentation rho v).toRepresentation
        (cyclicSubrepresentation sigma w).toRepresentation)
      (independentTensor rho sigma) where
  toLinearMap := TensorProduct.mapIncl (cyclicSpan rho v) (cyclicSpan sigma w)
  isIntertwining' gh := by
    apply LinearMap.ext
    intro z
    have heq : (TensorProduct.mapIncl (cyclicSpan rho v) (cyclicSpan sigma w)).comp
        (independentTensor (cyclicSubrepresentation rho v).toRepresentation
          (cyclicSubrepresentation sigma w).toRepresentation gh) =
        (independentTensor rho sigma gh).comp
          (TensorProduct.mapIncl (cyclicSpan rho v) (cyclicSpan sigma w)) := by
      ext u x
      rfl
    exact DFunLike.congr_fun heq z

/-- Restrict the codomain to the exact product-orbit span, not the ambient square. -/
noncomputable def cyclicTensorMap (rho : Representation R G V)
    (sigma : Representation R H W) (v : V) (w : W) :
    Representation.IntertwiningMap
      (independentTensor (cyclicSubrepresentation rho v).toRepresentation
        (cyclicSubrepresentation sigma w).toRepresentation)
      (cyclicSubrepresentation (independentTensor rho sigma) (v ⊗ₜ[R] w)).toRepresentation where
  toLinearMap := (cyclicTensorInclusion rho sigma v w).toLinearMap.codRestrict
    (cyclicSpan (independentTensor rho sigma) (v ⊗ₜ[R] w)) (by
      intro z
      rw [← cyclic_tensor_range_eq rho sigma v w]
      exact LinearMap.mem_range.mpr ⟨z,rfl⟩)
  isIntertwining' gh := by
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    exact Representation.IntertwiningMap.isIntertwining _ _
      (cyclicTensorInclusion rho sigma v w) gh z

theorem cyclicTensorMap_surjective (rho : Representation R G V)
    (sigma : Representation R H W) (v : V) (w : W) :
    Function.Surjective (cyclicTensorMap rho sigma v w) := by
  intro z
  have hz : z.val ∈ cyclicSpan (independentTensor rho sigma) (v ⊗ₜ[R] w) := z.property
  rw [← cyclic_tensor_range_eq rho sigma v w] at hz
  obtain ⟨u,hu⟩ := LinearMap.mem_range.mp hz
  exact ⟨u,Subtype.ext hu⟩

/-- Diagonal generation is contained in independent generation. Equality is
not asserted: the two factors must remain independent in the balance argument. -/
theorem diagonal_cyclic_le_independent (rho : Representation R G V)
    (sigma : Representation R G W) (v : V) (w : W) :
    cyclicSpan (rho.tprod sigma) (v ⊗ₜ[R] w) ≤
      cyclicSpan (independentTensor rho sigma) (v ⊗ₜ[R] w) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨g,rfl⟩
  exact orbit_mem_cyclicSpan (independentTensor rho sigma) (v ⊗ₜ[R] w) (g,g)
end Rings

section Fields
variable {K G H V W : Type*} [Field K] [Monoid G] [Monoid H]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- Tensor products of embeddings are embeddings over a field. -/
theorem independentTensorMap_injective {V' W' : Type*}
    [AddCommGroup V'] [Module K V'] [AddCommGroup W'] [Module K W']
    {rho : Representation K G V} {rho' : Representation K G V'}
    {sigma : Representation K H W} {sigma' : Representation K H W'}
    (phi : Representation.IntertwiningMap rho rho')
    (psi : Representation.IntertwiningMap sigma sigma')
    (hphi : Function.Injective phi) (hpsi : Function.Injective psi) :
    Function.Injective (independentTensorMap phi psi) :=
  TensorProduct.map_injective_of_flat_flat _ _ hphi hpsi

/-- Over a field, the tensor product of the factors embeds as a subspace. -/
theorem cyclicTensorInclusion_injective (rho : Representation K G V)
    (sigma : Representation K H W) (v : V) (w : W) :
    Function.Injective (cyclicTensorInclusion rho sigma v w) :=
  Module.Flat.tensorProduct_mapIncl_injective_of_right _ _

/-- The tensor product of the cyclic factors is equivariantly in bijection with
the product-orbit span; no finiteness of the group or characteristic assumption
is needed. -/
theorem cyclicTensorMap_bijective (rho : Representation K G V)
    (sigma : Representation K H W) (v : V) (w : W) :
    Function.Bijective (cyclicTensorMap rho sigma v w) := by
  refine ⟨?_,cyclicTensorMap_surjective rho sigma v w⟩
  intro z u h
  apply cyclicTensorInclusion_injective rho sigma v w
  exact congrArg Subtype.val h
end Fields
end HSTZ

#print axioms HSTZ.cyclic_tensor_range
#print axioms HSTZ.cyclic_tensor_range_eq
#print axioms HSTZ.cyclicTensorMap_surjective
#print axioms HSTZ.diagonal_cyclic_le_independent
#print axioms HSTZ.cyclicTensorInclusion_injective
#print axioms HSTZ.cyclicTensorMap_bijective
#print axioms HSTZ.independentTensorMap_cyclic_image
#print axioms HSTZ.independentTensorMap_injective
