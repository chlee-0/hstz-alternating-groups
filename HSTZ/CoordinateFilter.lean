import HSTZ.FinsuppAction
import HSTZ.SectorInduction
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.LinearAlgebra.Dual.Defs

/-! Coordinate filters and label-fiber sectors for the HSTZ/OpenAI pair-word
argument. Filtering keeps the original basis; labels are not replacement letters.
No concrete pair-word or Specht support statement is assumed. -/
namespace HSTZ
noncomputable section
open scoped Classical

section Fibers
variable {R X I : Type*} [CommRing R]

/-- Word functions supported on a single label fiber. -/
def labelSector (ell : X → I) (i : I) : Submodule R (X →₀ R) :=
  Finsupp.supported R R {x | ell x = i}

/-- Full family independence, including infinite families and empty fibers. -/
theorem labelSector_independent (ell : X → I) : iSupIndep (labelSector (R := R) ell) := by
  intro i
  have hd : Disjoint (labelSector (R := R) ell i)
      (Finsupp.supported R R {x | ell x ≠ i}) :=
    Finsupp.disjoint_supported_supported (Set.disjoint_left.mpr (fun _ hx hn => hn hx))
  apply hd.mono_right
  apply iSup_le
  intro j
  apply iSup_le
  intro hji
  exact Finsupp.supported_mono (fun _ hx => fun hi => hji (hx.symm.trans hi))

/-- The fibers exhaust the word space; surjectivity of `ell` is not needed. -/
theorem labelSector_iSup (ell : X → I) : (⨆ i, labelSector (R := R) ell i) = ⊤ := by
  simp only [labelSector]
  rw [← Finsupp.supported_iUnion]
  have h : (⋃ i, {x | ell x = i}) = Set.univ := by
    ext x
    simp
  rw [h,Finsupp.supported_univ]
end Fibers

section Actions
variable {R G X I : Type*} [CommRing R] [Monoid G]
  [MulAction G X] [MulAction G I]

/-- Equivariant labels give covariant supported sectors. -/
theorem labelSector_covariant (ell : X → I) (hell : ∀ (g : G) x, ell (g • x) = g • ell x)
    (g : G) (i : I) :
    (labelSector (R := R) ell i).map (finsuppAction R G X g) ≤
      labelSector ell (g • i) := by
  rw [labelSector,finsuppAction_def,Finsupp.lmapDomain_supported]
  apply Finsupp.supported_mono
  rintro _ ⟨x,hx,rfl⟩
  change ell (g • x) = g • i
  rw [hell,hx]
end Actions

section Filters
variable {R X : Type*} [CommRing R]

/-- A coordinate filter in the original word module, not a map to new labels. -/
noncomputable def coordinateFilter (S : Set X) : (X →₀ R) →ₗ[R] (X →₀ R) := by
  classical
  exact (Finsupp.supported R R S).subtype.comp (Finsupp.restrictDom R R S)

@[simp] theorem coordinateFilter_apply (S : Set X) (f : X →₀ R) (x : X) :
    coordinateFilter S f x = if x ∈ S then f x else 0 := by
  classical
  rfl

@[simp] theorem coordinateFilter_single (S : Set X) (x : X) (r : R) :
    coordinateFilter S (Finsupp.single x r) = if x ∈ S then Finsupp.single x r else 0 := by
  classical
  ext y
  by_cases hx : x ∈ S
  · by_cases hy : y = x
    · subst y; simp [hx]
    · simp [hx,hy]
  · by_cases hy : y = x
    · subst y; simp [hx]
    · simp [hx,hy]

theorem coordinateFilter_mem (S : Set X) (f : X →₀ R) :
    coordinateFilter S f ∈ Finsupp.supported R R S :=
  (Finsupp.restrictDom R R S f).property

/-- Supported vectors are fixed, so this is a projection. -/
theorem coordinateFilter_fixed (S : Set X) {f : X →₀ R}
    (hf : f ∈ Finsupp.supported R R S) : coordinateFilter S f = f := by
  classical
  ext x
  by_cases hx : x ∈ S
  · simp [hx]
  · simpa [hx] using ((Finsupp.mem_supported' R f).mp hf x hx).symm

theorem coordinateFilter_idempotent (S : Set X) :
    (coordinateFilter (R := R) S).comp (coordinateFilter S) = coordinateFilter S := by
  apply LinearMap.ext
  intro f
  exact coordinateFilter_fixed S (coordinateFilter_mem S f)

theorem coordinateFilter_range (S : Set X) :
    (coordinateFilter (R := R) S).range = Finsupp.supported R R S := by
  apply le_antisymm
  · rintro _ ⟨f,rfl⟩
    exact coordinateFilter_mem S f
  · intro f hf
    exact ⟨f,coordinateFilter_fixed S hf⟩

/-- One-sector support is exactly a condition on surviving original coordinates. -/
theorem coordinateFilter_sector_iff {I : Type*} (ell : X → I) (S : Set X)
    (v : X →₀ R) (i0 : I) :
    coordinateFilter S v ∈ labelSector ell i0 ↔
      ∀ x ∈ S, v x ≠ 0 → ell x = i0 := by
  rw [labelSector,Finsupp.mem_supported']
  constructor
  · intro hv x hx hn
    by_contra hi
    have hz := hv x hi
    rw [coordinateFilter_apply,if_pos hx] at hz
    exact hn hz
  · intro hv x hx
    by_cases hs : x ∈ S
    · have hz : v x = 0 := by
        by_contra hn
        exact hx (hv x hs hn)
      simp [hs,hz]
    · simp [hs]

variable {G : Type*} [Monoid G] [MulAction G X]

/-- Invariance of `S` gives an intertwiner on the original coordinates. -/
noncomputable def coordinateFilterIntertwiner (S : Set X)
    (hS : ∀ (g : G) x, g • x ∈ S ↔ x ∈ S) : Representation.IntertwiningMap
      (finsuppAction R G X) (finsuppAction R G X) where
  toLinearMap := coordinateFilter S
  isIntertwining' g := by
    apply LinearMap.ext
    intro f
    have heq : (coordinateFilter (R := R) S).comp (finsuppAction R G X g) =
        (finsuppAction R G X g).comp (coordinateFilter S) := by
      apply Finsupp.lhom_ext
      intro x r
      change coordinateFilter S (finsuppAction R G X g (Finsupp.single x r)) =
        finsuppAction R G X g (coordinateFilter S (Finsupp.single x r))
      rw [finsuppAction_single,coordinateFilter_single,coordinateFilter_single]
      classical
      by_cases hx : x ∈ S
      · simp [hx,(hS g x).mpr hx]
      · simp [hx,mt (hS g x).mp hx]
    exact DFunLike.congr_fun heq f

/-- The projection of the original prescribed-vector span is exactly the
filtered vector's cyclic span, retaining the original word coordinates. -/
theorem coordinateFilter_cyclic_image (S : Set X)
    (hS : ∀ (g : G) x, g • x ∈ S ↔ x ∈ S) (v : X →₀ R) :
    (cyclicSpan (finsuppAction R G X) v).map (coordinateFilter S) =
      cyclicSpan (finsuppAction R G X) (coordinateFilter S v) :=
  cyclicSpan_image (coordinateFilterIntertwiner S hS) v
end Filters

section Assembly
variable {R G X I : Type*} [CommRing R] [Group G]
  [MulAction G X] [MulAction G I] [DecidableEq I]

/-- Ordinary induction is identified with the filtered cyclic word space.
Only the filtered generator's one-fiber support and transitive representatives
are required beyond the concrete equivariant label. Filter invariance is needed
for transfer from the original vector, not for this filtered orbit itself. -/
theorem filtered_sectorInduction_bijective (ell : X → I)
    (hell : ∀ (g : G) x, ell (g • x) = g • ell x) (S : Set X)
    (v : X →₀ R) (i0 : I) (s : I → G) (hs : ∀ i, s i • i0 = i)
    (hv : coordinateFilter S v ∈ labelSector ell i0) :
    Function.Bijective (sectorInductionMap (finsuppAction R G X) i0
      (coordinateFilter S v)) :=
  sectorInductionMap_bijective _ i0 _ s hs (labelSector ell) hv
    (labelSector_covariant ell hell) (labelSector_independent ell)
end Assembly

section OrbitAssembly
variable {R G X I : Type*} [CommRing R] [Group G]
  [MulAction G X] [MulAction G I]

/-- The base label in its orbit. No global transitivity is assumed. -/
def labelOrbitBase (G : Type*) [Group G] [MulAction G I] (i0 : I) :
    MulAction.orbit G i0 := ⟨i0,MulAction.mem_orbit_self i0⟩

/-- Representatives exist on the label orbit, including infinite orbits. -/
noncomputable def labelOrbitRepresentative (i0 : I) (i : MulAction.orbit G i0) : G :=
  Classical.choose (MulAction.mem_orbit_iff.mp i.property)

theorem labelOrbitRepresentative_spec (i0 : I) (i : MulAction.orbit G i0) :
    labelOrbitRepresentative i0 i • labelOrbitBase G i0 = i := by
  apply Subtype.ext
  exact Classical.choose_spec (MulAction.mem_orbit_iff.mp i.property)

theorem labelOrbitBase_stabilizer (i0 : I) :
    MulAction.stabilizer G (labelOrbitBase G i0) = MulAction.stabilizer G i0 := by
  ext g
  simp [MulAction.mem_stabilizer_iff,Subtype.ext_iff,labelOrbitBase]

/-- Restrict the index to the label orbit, not the ambient word module. -/
def labelOrbitSector (ell : X → I) (i0 : I) (i : MulAction.orbit G i0) :
    Submodule R (X →₀ R) := labelSector ell i.val

omit [MulAction G X] in
theorem labelOrbitSector_independent (ell : X → I) (i0 : I) :
    iSupIndep (labelOrbitSector (R := R) (G := G) ell i0) :=
  (labelSector_independent ell).comp Subtype.val_injective

theorem labelOrbitSector_covariant (ell : X → I)
    (hell : ∀ (g : G) x, ell (g • x) = g • ell x) (i0 : I)
    (g : G) (i : MulAction.orbit G i0) :
    (labelOrbitSector (R := R) ell i0 i).map (finsuppAction R G X g) ≤
      labelOrbitSector ell i0 (g • i) :=
  labelSector_covariant ell hell g i.val

/-- One-fiber generators give ordinary induction on their label orbit.
Representatives, covariance and independence are supplied by the lemmas above. -/
theorem labelOrbit_sectorInduction_bijective (ell : X → I)
    (hell : ∀ (g : G) x, ell (g • x) = g • ell x) (v : X →₀ R) (i0 : I)
    (hv : v ∈ labelSector ell i0) :
    Function.Bijective (sectorInductionMap (finsuppAction R G X)
      (labelOrbitBase G i0) v) := by
  classical
  exact sectorInductionMap_bijective _ (labelOrbitBase G i0) v
    (labelOrbitRepresentative i0) (labelOrbitRepresentative_spec i0)
    (labelOrbitSector ell i0) hv (labelOrbitSector_covariant ell hell i0)
    (labelOrbitSector_independent ell i0)
end OrbitAssembly

section ImageCoordinates
variable {R X : Type*} [CommRing R]

/-- Restrict the coordinate filter to a submodule and its image. -/
noncomputable def filteredImageMap (S : Set X) (U : Submodule R (X →₀ R)) :
    U →ₗ[R] U.map (coordinateFilter S) :=
  ((coordinateFilter S).domRestrict U).codRestrict (U.map (coordinateFilter S))
    (fun u => Submodule.mem_map.mpr ⟨u.val,u.property,rfl⟩)

theorem filteredImageMap_surjective (S : Set X) (U : Submodule R (X →₀ R)) :
    Function.Surjective (filteredImageMap S U) := by
  intro z
  obtain ⟨u,hu,heq⟩ := Submodule.mem_map.mp z.property
  exact ⟨⟨u,hu⟩,Subtype.ext heq⟩

/-- The dual of the filtered image embeds in the dual of the original
submodule. -/
theorem filteredImageMap_dual_injective (S : Set X) (U : Submodule R (X →₀ R)) :
    Function.Injective (filteredImageMap S U).dualMap :=
  LinearMap.dualMap_injective_of_surjective (filteredImageMap_surjective S U)

def imageCoordinate (S : Set X) (U : Submodule R (X →₀ R)) (x : X) :
    Module.Dual R (U.map (coordinateFilter S)) :=
  (Finsupp.lapply x).comp (U.map (coordinateFilter S)).subtype

/-- A surviving coordinate is the pullback of a functional on the filtered
image. -/
theorem survivingCoordinate_pullback (S : Set X) (U : Submodule R (X →₀ R))
    (x : X) (hx : x ∈ S) :
    (filteredImageMap S U).dualMap (imageCoordinate S U x) =
      (Finsupp.lapply x).comp U.subtype := by
  apply LinearMap.ext
  intro u
  change coordinateFilter S u.val x = u.val x
  rw [coordinateFilter_apply,if_pos hx]

theorem survivingCoordinate_mem_dual_range (S : Set X) (U : Submodule R (X →₀ R))
    (x : X) (hx : x ∈ S) :
    (Finsupp.lapply x).comp U.subtype ∈ (filteredImageMap S U).dualMap.range :=
  ⟨imageCoordinate S U x,survivingCoordinate_pullback S U x hx⟩

/-- A nonzero coefficient of some vector of `U` at a surviving coordinate makes
that coordinate functional nonzero. -/
theorem imageCoordinate_ne_zero (S : Set X) (U : Submodule R (X →₀ R))
    (x : X) (hx : x ∈ S) (u : U) (hu : u.val x ≠ 0) :
    imageCoordinate S U x ≠ 0 := by
  intro hz
  have heq := DFunLike.congr_fun hz (filteredImageMap S U u)
  change coordinateFilter S u.val x = 0 at heq
  rw [coordinateFilter_apply,if_pos hx] at heq
  exact hu heq
end ImageCoordinates

end
end HSTZ

#print axioms HSTZ.labelSector_independent
#print axioms HSTZ.labelSector_iSup
#print axioms HSTZ.labelSector_covariant
#print axioms HSTZ.coordinateFilter_idempotent
#print axioms HSTZ.coordinateFilter_range
#print axioms HSTZ.coordinateFilterIntertwiner
#print axioms HSTZ.coordinateFilter_sector_iff
#print axioms HSTZ.coordinateFilter_cyclic_image
#print axioms HSTZ.filtered_sectorInduction_bijective
#print axioms HSTZ.labelOrbitRepresentative_spec
#print axioms HSTZ.labelOrbitBase_stabilizer
#print axioms HSTZ.labelOrbitSector_independent
#print axioms HSTZ.labelOrbitSector_covariant
#print axioms HSTZ.labelOrbit_sectorInduction_bijective
#print axioms HSTZ.filteredImageMap_surjective
#print axioms HSTZ.filteredImageMap_dual_injective
#print axioms HSTZ.survivingCoordinate_pullback
#print axioms HSTZ.survivingCoordinate_mem_dual_range
#print axioms HSTZ.imageCoordinate_ne_zero
