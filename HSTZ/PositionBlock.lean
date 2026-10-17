import HSTZ.IndependentTensor
import OAI.RepresentationTheory.Saxl.PositionTensor

/-! Independent position-block tensor spaces for the native staircase cut.
These are distinct from independent word layers on the same position set. -/
namespace HSTZ
open scoped Classical TensorProduct

/-- Product-group inclusion acting on disjoint positions. -/
def sumPermHom {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b) :
    (Equiv.Perm (Fin a) × Equiv.Perm (Fin b)) →* Equiv.Perm (Fin n) where
  toFun gh := OAI.Saxl.sumPerm e gh.1 gh.2
  map_one' := by
    ext i
    simp [OAI.Saxl.sumPerm,Equiv.permCongr_apply]
  map_mul' g h := by
    ext i
    simp [OAI.Saxl.sumPerm,Equiv.permCongr_apply]

theorem sumPermHom_injective {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b) :
    Function.Injective (sumPermHom e) := OAI.Saxl.sumPerm_injective e

/-- Concatenation is an intertwining bijection for independent blocks. -/
noncomputable def positionTensorIntertwiner {n a b d : ℕ}
    (e : Fin n ≃ Fin a ⊕ Fin b) : Representation.IntertwiningMap
      (independentTensor (OAI.Saxl.wordRep a d) (OAI.Saxl.wordRep b d))
      ((OAI.Saxl.wordRep n d).comp (sumPermHom e)) where
  toLinearMap := (OAI.Saxl.positionTensor e).toLinearMap
  isIntertwining' gh := LinearMap.ext fun z =>
    OAI.Saxl.positionTensor_equivariant e gh.1 gh.2 z

theorem positionTensorIntertwiner_bijective {n a b d : ℕ}
    (e : Fin n ≃ Fin a ⊕ Fin b) :
    Function.Bijective (positionTensorIntertwiner (d := d) e) :=
  (OAI.Saxl.positionTensor e).bijective

theorem positionTensor_cyclic_image {n a b d : ℕ}
    (e : Fin n ≃ Fin a ⊕ Fin b) (v : OAI.Saxl.WordSpace a d)
    (u : OAI.Saxl.WordSpace b d) :
    (cyclicSpan (independentTensor (OAI.Saxl.wordRep a d) (OAI.Saxl.wordRep b d))
      (v ⊗ₜ[ℂ] u)).map (OAI.Saxl.positionTensor e).toLinearMap =
    cyclicSpan ((OAI.Saxl.wordRep n d).comp (sumPermHom e))
      (OAI.Saxl.positionProduct e v u) := by
  have he := cyclicSpan_image (positionTensorIntertwiner e) (v ⊗ₜ[ℂ] u)
  change _ = cyclicSpan ((OAI.Saxl.wordRep n d).comp (sumPermHom e))
    (OAI.Saxl.positionTensor e (v ⊗ₜ[ℂ] u)) at he
  rw [OAI.Saxl.positionTensor_tmul] at he
  exact he

/-- The range of the tensor inclusion equals the block-orbit cyclic space. -/
theorem positionTensor_factor_range {n a b d : ℕ}
    (e : Fin n ≃ Fin a ⊕ Fin b) (v : OAI.Saxl.WordSpace a d)
    (u : OAI.Saxl.WordSpace b d) :
    (LinearMap.range (TensorProduct.mapIncl (cyclicSpan (OAI.Saxl.wordRep a d) v)
      (cyclicSpan (OAI.Saxl.wordRep b d) u))).map (OAI.Saxl.positionTensor e).toLinearMap =
    cyclicSpan ((OAI.Saxl.wordRep n d).comp (sumPermHom e))
      (OAI.Saxl.positionProduct e v u) := by
  rw [cyclic_tensor_range_eq]
  exact positionTensor_cyclic_image e v u

/-- Factor spaces, identified equivariantly with their block cyclic image. -/
noncomputable def positionFactorMap {n a b d : ℕ}
    (e : Fin n ≃ Fin a ⊕ Fin b) (v : OAI.Saxl.WordSpace a d)
    (u : OAI.Saxl.WordSpace b d) :=
  (cyclicImageMap (positionTensorIntertwiner e) (v ⊗ₜ[ℂ] u)).comp
    (cyclicTensorMap (OAI.Saxl.wordRep a d) (OAI.Saxl.wordRep b d) v u)

theorem positionFactorMap_bijective {n a b d : ℕ}
    (e : Fin n ≃ Fin a ⊕ Fin b) (v : OAI.Saxl.WordSpace a d)
    (u : OAI.Saxl.WordSpace b d) : Function.Bijective (positionFactorMap e v u) := by
  have hi : Function.Injective (cyclicImageMap (positionTensorIntertwiner e) (v ⊗ₜ[ℂ] u)) := by
    intro x y h
    apply Subtype.ext
    exact (OAI.Saxl.positionTensor e).injective (congrArg Subtype.val h)
  have hf := cyclicTensorMap_bijective (OAI.Saxl.wordRep a d) (OAI.Saxl.wordRep b d) v u
  constructor
  · intro x y h
    exact hf.1 (hi h)
  · intro z
    obtain ⟨y,hy⟩ := cyclicImageMap_surjective (positionTensorIntertwiner e) (v ⊗ₜ[ℂ] u) z
    obtain ⟨x,hx⟩ := hf.2 y
    refine ⟨x,?_⟩
    change cyclicImageMap (positionTensorIntertwiner e) (v ⊗ₜ[ℂ] u)
      (cyclicTensorMap (OAI.Saxl.wordRep a d) (OAI.Saxl.wordRep b d) v u x) = z
    rw [hx,hy]

/-- Every permutation preserving the blocks comes from independent block permutations. -/
theorem sumPermHom_sector_iff {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (g : Equiv.Perm (Fin n)) :
    g ∈ OAI.Saxl.sectorGroup (fun i => (e i).isLeft = true) ↔
    ∃ gh, sumPermHom e gh = g := by
  constructor
  · intro hg
    let k : OAI.Saxl.sectorGroup (fun i => (e i).isLeft = true) := ⟨g,hg⟩
    exact ⟨(OAI.Saxl.leftRestriction e k,OAI.Saxl.rightRestriction e k),
      OAI.Saxl.sumPerm_restrictions e k⟩
  · rintro ⟨⟨g,h⟩,rfl⟩ i
    obtain ⟨j,rfl⟩ := e.symm.surjective i
    cases j <;> simp [sumPermHom,OAI.Saxl.sumPerm,Equiv.permCongr_apply]

/-- Product-block orbits are exactly the sector-stabilizer orbits. -/
theorem blockSpan_eq_sectorSpan {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (z : OAI.Saxl.WordSpace n d) :
    cyclicSpan ((OAI.Saxl.wordRep n d).comp (sumPermHom e)) z =
    cyclicSpan ((OAI.Saxl.wordRep n d).comp
      (OAI.Saxl.sectorGroup (fun i => (e i).isLeft = true)).subtype) z := by
  unfold cyclicSpan
  apply congrArg (Submodule.span ℂ)
  ext x
  constructor
  · rintro ⟨gh,rfl⟩
    have hg := (sumPermHom_sector_iff e (sumPermHom e gh)).mpr ⟨gh,rfl⟩
    exact ⟨⟨sumPermHom e gh,hg⟩,rfl⟩
  · rintro ⟨g,rfl⟩
    obtain ⟨gh,hg⟩ := (sumPermHom_sector_iff e g.val).mp g.property
    refine ⟨gh,?_⟩
    change OAI.Saxl.wordRep n d (sumPermHom e gh) z = OAI.Saxl.wordRep n d g.val z
    rw [hg]


/-- Independent block permutations land in the position stabilizer. -/
def positionBlockGroupHom {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b) :
    (Equiv.Perm (Fin a) × Equiv.Perm (Fin b)) →*
      OAI.Saxl.sectorGroup (fun i => (e i).isLeft = true) where
  toFun gh := ⟨sumPermHom e gh,(sumPermHom_sector_iff e _).mpr ⟨gh,rfl⟩⟩
  map_one' := Subtype.ext (sumPermHom e).map_one
  map_mul' x y := Subtype.ext ((sumPermHom e).map_mul x y)

theorem positionBlockGroupHom_bijective {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b) :
    Function.Bijective (positionBlockGroupHom e) := by
  constructor
  · intro x y h
    exact sumPermHom_injective e (congrArg Subtype.val h)
  · intro g
    obtain ⟨gh,hgh⟩ := (sumPermHom_sector_iff e g.val).mp g.property
    exact ⟨gh,Subtype.ext hgh⟩

/-- Group identification, proved directly rather than by an index or dimension count. -/
noncomputable def positionBlockGroupEquiv {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b) :
    (Equiv.Perm (Fin a) × Equiv.Perm (Fin b)) ≃*
      OAI.Saxl.sectorGroup (fun i => (e i).isLeft = true) :=
  MulEquiv.ofBijective (positionBlockGroupHom e) (positionBlockGroupHom_bijective e)

@[simp] theorem positionBlockGroupEquiv_val {n a b : ℕ}
    (e : Fin n ≃ Fin a ⊕ Fin b) (gh : Equiv.Perm (Fin a) × Equiv.Perm (Fin b)) :
    (positionBlockGroupEquiv e gh).val = sumPermHom e gh := rfl

end HSTZ
#print axioms HSTZ.sumPermHom_injective
#print axioms HSTZ.positionTensorIntertwiner_bijective
#print axioms HSTZ.positionTensor_cyclic_image
#print axioms HSTZ.positionTensor_factor_range
#print axioms HSTZ.positionFactorMap_bijective
#print axioms HSTZ.sumPermHom_sector_iff
#print axioms HSTZ.blockSpan_eq_sectorSpan

#print axioms HSTZ.positionBlockGroupHom_bijective
#print axioms HSTZ.positionBlockGroupEquiv_val
