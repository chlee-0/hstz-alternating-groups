import HSTZ.FinsuppAction
import HSTZ.CoordinateFilter
import HSTZ.IndependentTensor
import Mathlib.LinearAlgebra.DirectSum.Finsupp

/-! Paired-word coordinates for the balance filter. Position permutations act by
inverse precomposition. A scalar output selects paired coordinates; it does not
replace the paired-word basis. -/
namespace HSTZ
open TensorProduct
open scoped Classical

/-- A word with explicit position type, separated from pointwise letter actions. -/
structure PositionWord (J A : Type*) where
  letters : J → A

namespace PositionWord
variable {J A B C G : Type*}

@[ext] theorem ext {u v : PositionWord J A} (h : ∀ j, u.letters j = v.letters j) : u = v := by
  cases u
  cases v
  congr
  funext j
  exact h j

/-- Move positions, keeping the letters fixed. -/
instance [Group G] [MulAction G J] : MulAction G (PositionWord J A) where
  smul g w := ⟨fun j => w.letters (g⁻¹ • j)⟩
  one_smul w := by
    apply ext
    intro j
    change w.letters ((1 : G)⁻¹ • j) = w.letters j
    simp
  mul_smul g h w := by
    apply ext
    intro j
    change w.letters ((g*h)⁻¹ • j) = w.letters (h⁻¹ • (g⁻¹ • j))
    simp [mul_inv_rev,mul_smul]

@[simp] theorem smul_letters [Group G] [MulAction G J]
    (g : G) (w : PositionWord J A) (j : J) :
    (g • w).letters j = w.letters (g⁻¹ • j) := rfl

/-- Pointwise letter output, used only to define labels or selectors. -/
def mapLetters (f : A → B) (w : PositionWord J A) : PositionWord J B :=
  ⟨fun j => f (w.letters j)⟩

@[simp] theorem mapLetters_letters (f : A → B) (w : PositionWord J A) (j : J) :
    (mapLetters f w).letters j = f (w.letters j) := rfl

@[simp] theorem mapLetters_smul [Group G] [MulAction G J]
    (f : A → B) (g : G) (w : PositionWord J A) :
    mapLetters f (g • w) = g • mapLetters f w := rfl

/-- Pairing two words is a bijection of basis index sets. -/
def pairEquiv : PositionWord J A × PositionWord J B ≃ PositionWord J (A × B) where
  toFun uv := ⟨fun j => (uv.1.letters j,uv.2.letters j)⟩
  invFun w := (⟨fun j => (w.letters j).1⟩,⟨fun j => (w.letters j).2⟩)
  left_inv _ := rfl
  right_inv w := by apply ext; intro j; rfl

@[simp] theorem pairEquiv_letters (u : PositionWord J A) (v : PositionWord J B) (j : J) :
    (pairEquiv (u,v)).letters j = (u.letters j,v.letters j) := rfl

@[simp] theorem pairEquiv_smul [Group G] [MulAction G J]
    (g : G) (u : PositionWord J A) (v : PositionWord J B) :
    pairEquiv (g • u,g • v) = g • pairEquiv (u,v) := rfl
end PositionWord

section Coordinates
variable {R J A B G : Type*} [CommRing R]

/-- The tensor product is identified with the paired-word coordinate module. -/
noncomputable def pairWordTensorEquiv :
    ((PositionWord J A →₀ R) ⊗[R] (PositionWord J B →₀ R)) ≃ₗ[R]
      (PositionWord J (A × B) →₀ R) :=
  finsuppTensorFinsupp' R (PositionWord J A) (PositionWord J B) ≪≫ₗ
    Finsupp.domLCongr PositionWord.pairEquiv

@[simp] theorem pairWordTensorEquiv_single (u : PositionWord J A) (v : PositionWord J B)
    (r s : R) :
    pairWordTensorEquiv (Finsupp.single u r ⊗ₜ[R] Finsupp.single v s) =
      Finsupp.single (PositionWord.pairEquiv (u,v)) (r*s) := by
  simp [pairWordTensorEquiv]

/-- The coefficient of a pure tensor at each paired-word coordinate is the product
of the two coefficients. -/
theorem pairWordTensorEquiv_coefficient (f : PositionWord J A →₀ R)
    (h : PositionWord J B →₀ R) (w : PositionWord J (A × B)) :
    pairWordTensorEquiv (f ⊗ₜ[R] h) w =
      f (PositionWord.pairEquiv.symm w).1 * h (PositionWord.pairEquiv.symm w).2 := by
  simp [pairWordTensorEquiv,Finsupp.domLCongr_apply,Finsupp.domCongr_apply]
  exact finsuppTensorFinsupp'_apply_apply R (PositionWord J A) (PositionWord J B)
    f h (PositionWord.pairEquiv.symm w).1 (PositionWord.pairEquiv.symm w).2

variable [Group G] [MulAction G J]

/-- The paired-word identification intertwines the simultaneous (diagonal)
position action on the tensor product. -/
noncomputable def pairWordTensorIntertwiner : Representation.IntertwiningMap
    (Representation.tprod (finsuppAction R G (PositionWord J A))
      (finsuppAction R G (PositionWord J B)))
    (finsuppAction R G (PositionWord J (A × B))) where
  toLinearMap := pairWordTensorEquiv.toLinearMap
  isIntertwining' g := by
    apply LinearMap.ext
    intro z
    have heq : pairWordTensorEquiv.toLinearMap.comp
        (Representation.tprod (finsuppAction R G (PositionWord J A))
          (finsuppAction R G (PositionWord J B)) g) =
        (finsuppAction R G (PositionWord J (A × B)) g).comp
          pairWordTensorEquiv.toLinearMap := by
      apply TensorProduct.ext
      apply Finsupp.lhom_ext
      intro u r
      apply Finsupp.lhom_ext
      intro v s
      change pairWordTensorEquiv
        (finsuppAction R G (PositionWord J A) g (Finsupp.single u r) ⊗ₜ[R]
          finsuppAction R G (PositionWord J B) g (Finsupp.single v s)) =
        finsuppAction R G (PositionWord J (A × B)) g
          (pairWordTensorEquiv (Finsupp.single u r ⊗ₜ[R] Finsupp.single v s))
      simp
    exact DFunLike.congr_fun heq z

theorem pairWordTensorIntertwiner_bijective :
    Function.Bijective (pairWordTensorIntertwiner (R := R) (G := G) (J := J) (A := A) (B := B)) :=
  pairWordTensorEquiv.bijective
end Coordinates

section Selectors
variable {R J A B C G : Type*} [CommRing R] [Group G] [MulAction G J]

/-- Scalar output chooses coordinates in the paired-word module. -/
def pairSelected (out : A × B → C) (T : Set (PositionWord J C)) :
    Set (PositionWord J (A × B)) := PositionWord.mapLetters out ⁻¹' T

theorem pairSelected_invariant (out : A × B → C) (T : Set (PositionWord J C))
    (hT : ∀ (g : G) w, g • w ∈ T ↔ w ∈ T) (g : G) (w : PositionWord J (A × B)) :
    g • w ∈ pairSelected out T ↔ w ∈ pairSelected out T := by
  change PositionWord.mapLetters out (g • w) ∈ T ↔ PositionWord.mapLetters out w ∈ T
  rw [PositionWord.mapLetters_smul]
  exact hT g _

/-- Coordinate projection onto the paired words selected by a scalar output,
in the paired-word basis. -/
noncomputable def pairWordFilter (out : A × B → C) (T : Set (PositionWord J C)) :
    (PositionWord J (A × B) →₀ R) →ₗ[R] (PositionWord J (A × B) →₀ R) :=
  coordinateFilter (pairSelected out T)

@[simp] theorem pairWordFilter_single (out : A × B → C) (T : Set (PositionWord J C))
    (w : PositionWord J (A × B)) (r : R) :
    pairWordFilter out T (Finsupp.single w r) =
      if PositionWord.mapLetters out w ∈ T then Finsupp.single w r else 0 :=
  coordinateFilter_single (pairSelected out T) w r

noncomputable def pairWordFilterIntertwiner (out : A × B → C) (T : Set (PositionWord J C))
    (hT : ∀ (g : G) w, g • w ∈ T ↔ w ∈ T) : Representation.IntertwiningMap
      (finsuppAction R G (PositionWord J (A × B)))
      (finsuppAction R G (PositionWord J (A × B))) :=
  coordinateFilterIntertwiner (pairSelected out T) (pairSelected_invariant out T hT)

/-- The map from the tensor product to filtered paired words, equivariant for the
simultaneous position action. -/
noncomputable def filteredPairWordMap (out : A × B → C) (T : Set (PositionWord J C))
    (hT : ∀ (g : G) w, g • w ∈ T ↔ w ∈ T) : Representation.IntertwiningMap
      (Representation.tprod (finsuppAction R G (PositionWord J A))
        (finsuppAction R G (PositionWord J B)))
      (finsuppAction R G (PositionWord J (A × B))) :=
  (pairWordFilterIntertwiner out T hT).comp pairWordTensorIntertwiner

/-- Coefficients are multiplied and then selected; equal scalar outputs never
cause distinct paired coordinates to be added together. -/
theorem filteredPairWordMap_coefficient (out : A × B → C) (T : Set (PositionWord J C))
    (hT : ∀ (g : G) w, g • w ∈ T ↔ w ∈ T)
    (f : PositionWord J A →₀ R) (h : PositionWord J B →₀ R)
    (w : PositionWord J (A × B)) :
    filteredPairWordMap out T hT (f ⊗ₜ[R] h) w =
      if PositionWord.mapLetters out w ∈ T then
        f (PositionWord.pairEquiv.symm w).1 * h (PositionWord.pairEquiv.symm w).2 else 0 := by
  change coordinateFilter (pairSelected out T) (pairWordTensorEquiv (f ⊗ₜ[R] h)) w = _
  rw [coordinateFilter_apply,pairWordTensorEquiv_coefficient]
  rfl

theorem filteredPairWordMap_cyclic_image (out : A × B → C) (T : Set (PositionWord J C))
    (hT : ∀ (g : G) w, g • w ∈ T ↔ w ∈ T)
    (z : (PositionWord J A →₀ R) ⊗[R] (PositionWord J B →₀ R)) :
    (cyclicSpan (Representation.tprod
      (finsuppAction R G (PositionWord J A))
      (finsuppAction R G (PositionWord J B))) z).map
        (filteredPairWordMap out T hT).toLinearMap =
      cyclicSpan (finsuppAction R G (PositionWord J (A × B)))
        (pairWordFilter out T (pairWordTensorEquiv z)) :=
  cyclicSpan_image (filteredPairWordMap out T hT) z

/-- The full tensor module maps onto precisely the selected paired coordinates.
This is a statement about the full module, not any prescribed cyclic vector. -/
theorem filteredPairWordMap_range (out : A × B → C) (T : Set (PositionWord J C))
    (hT : ∀ (g : G) w, g • w ∈ T ↔ w ∈ T) :
    (filteredPairWordMap (R := R) out T hT).toLinearMap.range =
      Finsupp.supported R R (pairSelected out T) := by
  change LinearMap.range ((coordinateFilter (pairSelected out T)).comp
    pairWordTensorEquiv.toLinearMap) = _
  rw [LinearMap.range_comp,LinearMap.range_eq_top.mpr pairWordTensorEquiv.surjective,
    Submodule.map_top,coordinateFilter_range]

/-- Orbits of output labels are invariant selectors. -/
theorem pairOutput_orbit_invariant (w0 : PositionWord J C) (g : G) (w : PositionWord J C) :
    g • w ∈ MulAction.orbit G w0 ↔ w ∈ MulAction.orbit G w0 := by
  constructor
  · intro hw
    simpa using MulAction.mem_orbit_of_mem_orbit g⁻¹ hw
  · exact MulAction.mem_orbit_of_mem_orbit g

/-- The fibers of the output word form independent paired-coordinate sectors. -/
theorem pairOutput_sectors_independent (out : A × B → C) :
    iSupIndep (labelSector (R := R) (PositionWord.mapLetters (J := J) out)) :=
  labelSector_independent _

theorem pairOutput_sectors_covariant (out : A × B → C) (g : G) (w : PositionWord J C) :
    (labelSector (R := R) (PositionWord.mapLetters out) w).map
        (finsuppAction R G (PositionWord J (A × B)) g) ≤
      labelSector (PositionWord.mapLetters out) (g • w) :=
  labelSector_covariant _ (PositionWord.mapLetters_smul out) g w

/-- The output-label orbit of the selected word supplies transitivity and sector
independence. The coefficient condition `hf` remains a hypothesis. -/
theorem pairOutput_orbit_induction (out : A × B → C) (T : Set (PositionWord J C))
    (f : PositionWord J (A × B) →₀ R) (w0 : PositionWord J C)
    (hf : ∀ w, PositionWord.mapLetters out w ∈ T → f w ≠ 0 →
      PositionWord.mapLetters out w = w0) :
    Function.Bijective (sectorInductionMap
      (finsuppAction R G (PositionWord J (A × B)))
      (labelOrbitBase G w0) (pairWordFilter out T f)) := by
  exact labelOrbit_sectorInduction_bijective (PositionWord.mapLetters out)
    (PositionWord.mapLetters_smul out) (pairWordFilter out T f) w0
    ((coordinateFilter_sector_iff (PositionWord.mapLetters out) (pairSelected out T) f w0).mpr hf)
end Selectors

section IndependentRange
variable {R J A B G H : Type*} [CommRing R] [Monoid G] [Monoid H]

/-- The tensor product of independently generated cyclic factors, viewed in paired
words before projection, is the image of the independent cyclic span. This is not a
diagonal orbit. -/
theorem pairWord_independent_range
    (rho : Representation R G (PositionWord J A →₀ R))
    (sigma : Representation R H (PositionWord J B →₀ R))
    (f : PositionWord J A →₀ R) (h : PositionWord J B →₀ R) :
    LinearMap.range (pairWordTensorEquiv.toLinearMap.comp
      (TensorProduct.mapIncl (cyclicSpan rho f) (cyclicSpan sigma h))) =
      (cyclicSpan (independentTensor rho sigma) (f ⊗ₜ[R] h)).map
        pairWordTensorEquiv.toLinearMap := by
  rw [LinearMap.range_comp,cyclic_tensor_range_eq]
end IndependentRange

section IndependentEmbedding
variable {K J A B G H : Type*} [Field K] [Monoid G] [Monoid H]

/-- Over a field, the tensor product of the independent cyclic factors embeds in
paired words before filtering. Injectivity of the coordinate projection is not
claimed. -/
theorem pairWord_independent_injective
    (rho : Representation K G (PositionWord J A →₀ K))
    (sigma : Representation K H (PositionWord J B →₀ K))
    (f : PositionWord J A →₀ K) (h : PositionWord J B →₀ K) :
    Function.Injective (pairWordTensorEquiv.toLinearMap.comp
      (TensorProduct.mapIncl (cyclicSpan rho f) (cyclicSpan sigma h))) :=
  pairWordTensorEquiv.injective.comp (cyclicTensorInclusion_injective rho sigma f h)
end IndependentEmbedding
end HSTZ

#print axioms HSTZ.PositionWord.mapLetters_smul
#print axioms HSTZ.PositionWord.pairEquiv_smul
#print axioms HSTZ.pairWordTensorEquiv_single
#print axioms HSTZ.pairWordTensorEquiv_coefficient
#print axioms HSTZ.pairWordTensorIntertwiner
#print axioms HSTZ.pairWordTensorIntertwiner_bijective
#print axioms HSTZ.pairSelected_invariant
#print axioms HSTZ.pairWordFilter_single
#print axioms HSTZ.filteredPairWordMap_coefficient
#print axioms HSTZ.filteredPairWordMap_cyclic_image
#print axioms HSTZ.filteredPairWordMap_range
#print axioms HSTZ.pairOutput_orbit_invariant
#print axioms HSTZ.pairOutput_sectors_independent
#print axioms HSTZ.pairOutput_sectors_covariant
#print axioms HSTZ.pairOutput_orbit_induction
#print axioms HSTZ.pairWord_independent_range
#print axioms HSTZ.pairWord_independent_injective
