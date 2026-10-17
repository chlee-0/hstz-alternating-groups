import HSTZ.PieriSupport
import HSTZ.StaircaseBlockCarrier

/-! Compatible position pairs are independent block permutations. This reuses the
block/sector bijection and preserves both the ambient and the core maps. -/
namespace HSTZ

/-- The core positions for a given position decomposition. -/
def blockInclusion {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b) : Fin a ↪ Fin n where
  toFun k := e.symm (Sum.inl k)
  inj' := fun _ _ h => Sum.inl_injective (e.symm.injective h)

theorem blockInclusion_range {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b) (k : Fin n) :
    k ∈ Set.range (blockInclusion e) ↔ (e k).isLeft = true := by
  obtain ⟨j, rfl⟩ := e.symm.surjective k
  cases j with
  | inl j =>
    constructor
    · intro _; simp
    · intro _; exact ⟨j, rfl⟩
  | inr j =>
    constructor
    · rintro ⟨x, h⟩
      have hn : Sum.inl x = Sum.inr j := e.symm.injective h
      cases hn
    · intro h
      simp at h

theorem positionPairAmbient_mem_sector {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (g : positionPairGroup (blockInclusion e)) :
    positionPairAmbient (blockInclusion e) g ∈
      OAI.Saxl.sectorGroup (fun k => (e k).isLeft = true) := by
  intro k
  change (e (g.val.1 k)).isLeft = true ↔ (e k).isLeft = true
  rw [← blockInclusion_range e, ← blockInclusion_range e]
  constructor
  · rintro ⟨j, hj⟩
    refine ⟨g.val.2⁻¹ j, ?_⟩
    apply g.val.1.injective
    rw [g.property]
    simpa using hj
  · rintro ⟨j, rfl⟩
    exact ⟨g.val.2 j, (g.property j).symm⟩

/-- Independent block permutations as compatible pairs. -/
def positionBlockPairHom {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b) :
    (Equiv.Perm (Fin a) × Equiv.Perm (Fin b)) →*
      positionPairGroup (blockInclusion e) where
  toFun gh := ⟨(sumPermHom e gh, gh.1), fun k => OAI.Saxl.sumPerm_left e gh.1 gh.2 k⟩
  map_one' := Subtype.ext (Prod.ext (sumPermHom e).map_one rfl)
  map_mul' gh ij := Subtype.ext (Prod.ext ((sumPermHom e).map_mul gh ij) rfl)

theorem positionBlockPairHom_bijective {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b) :
    Function.Bijective (positionBlockPairHom e) := by
  constructor
  · intro gh ij h
    exact sumPermHom_injective e (congrArg (fun g => g.val.1) h)
  · intro g
    let k : OAI.Saxl.sectorGroup (fun p => (e p).isLeft = true) :=
      ⟨positionPairAmbient (blockInclusion e) g, positionPairAmbient_mem_sector e g⟩
    obtain ⟨gh, hgh⟩ := (positionBlockGroupHom_bijective e).2 k
    have he : sumPermHom e gh = g.val.1 := congrArg Subtype.val hgh
    refine ⟨gh, Subtype.ext (Prod.ext he ?_)⟩
    apply Equiv.ext
    intro j
    apply (blockInclusion e).injective
    rw [← g.property]
    change e.symm (Sum.inl (gh.1 j)) = g.val.1 (e.symm (Sum.inl j))
    rw [← he]
    exact (OAI.Saxl.sumPerm_left e gh.1 gh.2 j).symm

/-- Group equivalence, preserving the ambient and core permutations. -/
noncomputable def positionBlockPairEquiv {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b) :
    (Equiv.Perm (Fin a) × Equiv.Perm (Fin b)) ≃*
      positionPairGroup (blockInclusion e) :=
  MulEquiv.ofBijective (positionBlockPairHom e) (positionBlockPairHom_bijective e)

@[simp] theorem positionBlockPairEquiv_ambient {n a b : ℕ}
    (e : Fin n ≃ Fin a ⊕ Fin b) (gh : Equiv.Perm (Fin a) × Equiv.Perm (Fin b)) :
    positionPairAmbient (blockInclusion e) (positionBlockPairEquiv e gh) =
      sumPermHom e gh := rfl

@[simp] theorem positionBlockPairEquiv_core {n a b : ℕ}
    (e : Fin n ≃ Fin a ⊕ Fin b) (gh : Equiv.Perm (Fin a) × Equiv.Perm (Fin b)) :
    positionPairCore (blockInclusion e) (positionBlockPairEquiv e gh) = gh.1 := rfl

/-- Compatible core-position pairs and the staircase label stabilizer. -/
noncomputable def staircasePairLabelEquiv (h s : ℕ) :
    positionPairGroup (blockInclusion (OAI.Saxl.cutPositions h s)) ≃*
      staircaseLabelStabilizer h s :=
  (positionBlockPairEquiv (OAI.Saxl.cutPositions h s)).symm.trans
    (staircaseLabelBlockEquiv h s)

@[simp] theorem staircasePairLabelEquiv_val (h s : ℕ)
    (g : positionPairGroup (blockInclusion (OAI.Saxl.cutPositions h s))) :
    (staircasePairLabelEquiv h s g).val =
      positionPairAmbient (blockInclusion (OAI.Saxl.cutPositions h s)) g := by
  change sumPermHom (OAI.Saxl.cutPositions h s)
    ((positionBlockPairEquiv (OAI.Saxl.cutPositions h s)).symm g) = _
  have he := congrArg (positionPairAmbient (blockInclusion (OAI.Saxl.cutPositions h s)))
    ((positionBlockPairEquiv (OAI.Saxl.cutPositions h s)).apply_symm_apply g)
  exact he

end HSTZ
#print axioms HSTZ.positionBlockPairHom_bijective
#print axioms HSTZ.positionBlockPairEquiv_ambient
#print axioms HSTZ.positionBlockPairEquiv_core
#print axioms HSTZ.staircasePairLabelEquiv_val
