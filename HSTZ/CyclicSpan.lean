import Mathlib.RepresentationTheory.Intertwining
import Mathlib.RepresentationTheory.Subrepresentation
import Mathlib.LinearAlgebra.Span.Basic

/-! Generic orbit spans used in the projection arguments. `cyclicSpan rho v` is
the span of the orbit of one vector, not a full tensor square or isotypic summand. -/
namespace HSTZ

variable {R G V W : Type*} [CommRing R] [Monoid G]
  [AddCommMonoid V] [Module R V] [AddCommMonoid W] [Module R W]

/-- Linear span of the orbit of one vector. -/
def cyclicSpan (rho : Representation R G V) (v : V) : Submodule R V :=
  Submodule.span R (Set.range (fun g => rho g v))

theorem orbit_mem_cyclicSpan (rho : Representation R G V) (v : V) (g : G) :
    rho g v ∈ cyclicSpan rho v := Submodule.subset_span ⟨g,rfl⟩

theorem generator_mem_cyclicSpan (rho : Representation R G V) (v : V) :
    v ∈ cyclicSpan rho v := by
  simpa using orbit_mem_cyclicSpan rho v 1

/-- The orbit span is stable under the action; neither inverses nor finiteness are
needed. -/
theorem cyclicSpan_stable (rho : Representation R G V) (v : V) (g : G)
    {w : V} (hw : w ∈ cyclicSpan rho v) : rho g w ∈ cyclicSpan rho v := by
  have hmap : (cyclicSpan rho v).map (rho g) ≤ cyclicSpan rho v := by
    apply (Submodule.map_span_le (rho g) (Set.range (fun h => rho h v)) (cyclicSpan rho v)).mpr
    rintro _ ⟨h,rfl⟩
    simpa only [map_mul,Module.End.mul_apply] using orbit_mem_cyclicSpan rho v (g*h)
  exact hmap (Submodule.mem_map.mpr ⟨w,hw,rfl⟩)

/-- The orbit span bundled as a subrepresentation. -/
def cyclicSubrepresentation (rho : Representation R G V) (v : V) :
    Subrepresentation rho where
  toSubmodule := cyclicSpan rho v
  apply_mem_toSubmodule g _ hw := cyclicSpan_stable rho v g hw

/-- The orbit span is the smallest stable subspace containing the vector. -/
theorem cyclicSpan_le_iff (rho : Representation R G V) (v : V)
    (P : Subrepresentation rho) : cyclicSpan rho v ≤ P.toSubmodule ↔ v ∈ P := by
  constructor
  · intro h
    exact h (generator_mem_cyclicSpan rho v)
  · intro hv
    apply Submodule.span_le.mpr
    rintro _ ⟨g,rfl⟩
    exact P.apply_mem_toSubmodule g hv

theorem cyclicSubrepresentation_le_iff (rho : Representation R G V) (v : V)
    (P : Subrepresentation rho) : cyclicSubrepresentation rho v ≤ P ↔ v ∈ P := by
  change cyclicSpan rho v ≤ P.toSubmodule ↔ v ∈ P
  exact cyclicSpan_le_iff rho v P

/-- The image of a cyclic span under an intertwiner is the cyclic span of the
image vector. -/
theorem cyclicSpan_image {rho : Representation R G V} {sigma : Representation R G W}
    (phi : Representation.IntertwiningMap rho sigma) (v : V) :
    (cyclicSpan rho v).map phi.toLinearMap = cyclicSpan sigma (phi v) := by
  rw [cyclicSpan,Submodule.map_span,cyclicSpan]
  apply congrArg (Submodule.span R)
  ext w
  constructor
  · rintro ⟨_,⟨g,rfl⟩,rfl⟩
    exact ⟨g,(Representation.IntertwiningMap.isIntertwining rho sigma phi g v).symm⟩
  · rintro ⟨g,rfl⟩
    exact ⟨rho g v,⟨g,rfl⟩,Representation.IntertwiningMap.isIntertwining rho sigma phi g v⟩

theorem cyclicSpan_eq_bot_iff (rho : Representation R G V) (v : V) :
    cyclicSpan rho v = ⊥ ↔ v=0 := by
  constructor
  · intro h
    have hv := generator_mem_cyclicSpan rho v
    rw [h] at hv
    simpa using hv
  · rintro rfl
    apply le_antisymm _ bot_le
    apply Submodule.span_le.mpr
    rintro _ ⟨g,rfl⟩
    simp

/-- Vanishing of the image space is exactly vanishing of the projected vector. -/
theorem cyclicSpan_image_eq_bot_iff {rho : Representation R G V} {sigma : Representation R G W}
    (phi : Representation.IntertwiningMap rho sigma) (v : V) :
    (cyclicSpan rho v).map phi.toLinearMap = ⊥ ↔ phi v=0 := by
  rw [cyclicSpan_image,cyclicSpan_eq_bot_iff]

/-- An intertwiner maps the cyclic span of `v` into the cyclic span of `phi v`. -/
theorem cyclicSpan_apply_mem {rho : Representation R G V} {sigma : Representation R G W}
    (phi : Representation.IntertwiningMap rho sigma) (v : V) {w : V}
    (hw : w ∈ cyclicSpan rho v) : phi w ∈ cyclicSpan sigma (phi v) := by
  rw [← cyclicSpan_image phi v]
  exact Submodule.mem_map.mpr ⟨w,hw,rfl⟩

/-- Restriction of an intertwiner to the source and target cyclic spans. -/
def cyclicImageMap {rho : Representation R G V} {sigma : Representation R G W}
    (phi : Representation.IntertwiningMap rho sigma) (v : V) :
    Representation.IntertwiningMap (cyclicSubrepresentation rho v).toRepresentation
      (cyclicSubrepresentation sigma (phi v)).toRepresentation where
  toLinearMap := (phi.toLinearMap.domRestrict (cyclicSpan rho v)).codRestrict
    (cyclicSpan sigma (phi v)) (fun w => cyclicSpan_apply_mem phi v w.property)
  isIntertwining' g := by
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    exact Representation.IntertwiningMap.isIntertwining rho sigma phi g w.val

/-- The restricted cyclic-image map is surjective, even when `phi` is not. -/
theorem cyclicImageMap_surjective {rho : Representation R G V} {sigma : Representation R G W}
    (phi : Representation.IntertwiningMap rho sigma) (v : V) :
    Function.Surjective (cyclicImageMap phi v) := by
  intro w
  have hw : w.val ∈ cyclicSpan sigma (phi v) := w.property
  rw [← cyclicSpan_image phi v] at hw
  obtain ⟨u,hu,hew⟩ := Submodule.mem_map.mp hw
  exact ⟨⟨u,hu⟩,Subtype.ext hew⟩

end HSTZ
#print axioms HSTZ.cyclicSpan_stable
#print axioms HSTZ.cyclicSpan_le_iff
#print axioms HSTZ.cyclicSubrepresentation_le_iff
#print axioms HSTZ.cyclicSpan_image
#print axioms HSTZ.cyclicSpan_eq_bot_iff
#print axioms HSTZ.cyclicSpan_image_eq_bot_iff
#print axioms HSTZ.cyclicImageMap_surjective
