import HSTZ.FinsuppAction
import HSTZ.CoordinateFilter

/-! Dual-image transfer for the surviving pair-coordinate argument. The source is
a stable subspace of a permutation module, and the filtered image's dual embeds
equivariantly in the source dual. -/
namespace HSTZ

section Dual
variable {R G V W : Type*} [CommRing R] [Group G]
  [AddCommMonoid V] [Module R V] [AddCommMonoid W] [Module R W]
  {rho : Representation R G V} {sigma : Representation R G W}

/-- Contravariant dual of an intertwiner, for the dual actions (inverse group
action). -/
def dualIntertwiner (phi : Representation.IntertwiningMap rho sigma) :
    Representation.IntertwiningMap sigma.dual rho.dual where
  toLinearMap := phi.toLinearMap.dualMap
  isIntertwining' g := by
    apply LinearMap.ext
    intro lam
    apply LinearMap.ext
    intro v
    change lam (sigma g⁻¹ (phi v)) = lam (phi (rho g⁻¹ v))
    exact congrArg lam (Representation.IntertwiningMap.isIntertwining _ _ phi g⁻¹ v).symm

theorem dualIntertwiner_injective (phi : Representation.IntertwiningMap rho sigma)
    (hphi : Function.Surjective phi) : Function.Injective (dualIntertwiner phi) :=
  LinearMap.dualMap_injective_of_surjective hphi
end Dual

section WordImage
variable {R G X : Type*} [CommRing R] [Group G] [MulAction G X]

/-- The filtered image of a stable subspace, which is again stable. -/
noncomputable def filteredSubrepresentation (S : Set X)
    (hS : ∀ (g : G) x, g • x ∈ S ↔ x ∈ S)
    (U : Subrepresentation (finsuppAction R G X)) :
    Subrepresentation (finsuppAction R G X) where
  toSubmodule := U.toSubmodule.map (coordinateFilter S)
  apply_mem_toSubmodule g z hz := by
    obtain ⟨u,hu,rfl⟩ := Submodule.mem_map.mp hz
    exact Submodule.mem_map.mpr
      ⟨finsuppAction R G X g u,U.apply_mem_toSubmodule g hu,
        Representation.IntertwiningMap.isIntertwining _ _ (coordinateFilterIntertwiner S hS) g u⟩

/-- Surjective intertwiner from the source to its filtered image. -/
noncomputable def filteredSubrepresentationMap (S : Set X)
    (hS : ∀ (g : G) x, g • x ∈ S ↔ x ∈ S)
    (U : Subrepresentation (finsuppAction R G X)) :
    Representation.IntertwiningMap U.toRepresentation
      (filteredSubrepresentation S hS U).toRepresentation where
  toLinearMap := filteredImageMap S U.toSubmodule
  isIntertwining' g := by
    apply LinearMap.ext
    intro u
    apply Subtype.ext
    exact Representation.IntertwiningMap.isIntertwining _ _ (coordinateFilterIntertwiner S hS) g u.val

theorem filteredSubrepresentationMap_surjective (S : Set X)
    (hS : ∀ (g : G) x, g • x ∈ S ↔ x ∈ S)
    (U : Subrepresentation (finsuppAction R G X)) :
    Function.Surjective (filteredSubrepresentationMap S hS U) :=
  filteredImageMap_surjective S U.toSubmodule

/-- The dual of the filtered image embeds equivariantly in the source dual. -/
noncomputable def filteredDualEmbedding (S : Set X)
    (hS : ∀ (g : G) x, g • x ∈ S ↔ x ∈ S)
    (U : Subrepresentation (finsuppAction R G X)) :
    Representation.IntertwiningMap (filteredSubrepresentation S hS U).toRepresentation.dual
      U.toRepresentation.dual :=
  dualIntertwiner (filteredSubrepresentationMap S hS U)

theorem filteredDualEmbedding_injective (S : Set X)
    (hS : ∀ (g : G) x, g • x ∈ S ↔ x ∈ S)
    (U : Subrepresentation (finsuppAction R G X)) :
    Function.Injective (filteredDualEmbedding S hS U) :=
  dualIntertwiner_injective _ (filteredSubrepresentationMap_surjective S hS U)

theorem filteredDualEmbedding_coordinate (S : Set X)
    (hS : ∀ (g : G) x, g • x ∈ S ↔ x ∈ S)
    (U : Subrepresentation (finsuppAction R G X)) (x : X) (hx : x ∈ S) :
    filteredDualEmbedding S hS U (imageCoordinate S U.toSubmodule x) =
      (Finsupp.lapply x).comp U.toSubmodule.subtype :=
  survivingCoordinate_pullback S U.toSubmodule x hx

/-- The embedded image dual maps the cyclic span of a surviving coordinate onto the
cyclic span of the corresponding source coordinate. -/
theorem filtered_coordinate_cyclic_image (S : Set X)
    (hS : ∀ (g : G) x, g • x ∈ S ↔ x ∈ S)
    (U : Subrepresentation (finsuppAction R G X)) (x : X) (hx : x ∈ S) :
    (cyclicSpan (filteredSubrepresentation S hS U).toRepresentation.dual
      (imageCoordinate S U.toSubmodule x)).map (filteredDualEmbedding S hS U).toLinearMap =
      cyclicSpan U.toRepresentation.dual ((Finsupp.lapply x).comp U.toSubmodule.subtype) := by
  erw [cyclicSpan_image,filteredDualEmbedding_coordinate S hS U x hx]

/-- The restricted dual embedding is a bijection between the two coordinate cyclic
spaces. -/
theorem filtered_coordinate_cyclic_bijective (S : Set X)
    (hS : ∀ (g : G) x, g • x ∈ S ↔ x ∈ S)
    (U : Subrepresentation (finsuppAction R G X)) (x : X) :
    Function.Bijective (cyclicImageMap (filteredDualEmbedding S hS U)
      (imageCoordinate S U.toSubmodule x)) := by
  constructor
  · intro z u h
    apply Subtype.ext
    exact filteredDualEmbedding_injective S hS U (congrArg Subtype.val h)
  · exact cyclicImageMap_surjective _ _
end WordImage
end HSTZ

#print axioms HSTZ.dualIntertwiner
#print axioms HSTZ.dualIntertwiner_injective
#print axioms HSTZ.filteredSubrepresentationMap_surjective
#print axioms HSTZ.filteredDualEmbedding_injective
#print axioms HSTZ.filteredDualEmbedding_coordinate
#print axioms HSTZ.filtered_coordinate_cyclic_image
#print axioms HSTZ.filtered_coordinate_cyclic_bijective
