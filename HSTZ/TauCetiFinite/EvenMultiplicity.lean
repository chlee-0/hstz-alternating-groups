import HSTZ.TauCetiFinite.ClassSums
import TauCeti.RepresentationTheory.FDRep
import TauCeti.RepresentationTheory.Simple.Basic
import Mathlib.RepresentationTheory.FinGroupCharZero

/-!
Shows that `evenCoverNumerator lam nu` is n! times the dimension of the space of
intertwiners from S^nu into X ⊕ (sgn ⊗ X), where X = S^lam ⊗ S^lam.
The sign twist is represented on the same carrier by scalar multiplication, and the
direct sum is the product of the two carriers. In particular, a nonzero numerator embeds
the irreducible symmetric-group Specht module before restriction to A_n.

Uses TauCeti's Specht character theorem.
-/
namespace HSTZ.TauCetiFinite
noncomputable section
open scoped Classical TensorProduct

/-- The tensor square of the complex Specht representation. -/
def spechtSquare {n : ℕ} (lam : Nat.Partition n) :=
  Representation.tprod (TauCeti.spechtModuleℂ lam).ρ (TauCeti.spechtModuleℂ lam).ρ

/-- The scalar model of tensoring by the one-dimensional sign representation. -/
def signTwist {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) :
    Representation ℂ (Equiv.Perm (Fin n)) V where
  toFun g := (((Equiv.Perm.sign g : ℤ) : ℂ)) • ρ g
  map_one' := by simp
  map_mul' g h := by
    ext v
    simp [map_mul, Module.End.mul_apply, smul_smul, mul_comm]

/-- The finite direct sum X ⊕ (sgn ⊗ X), in the scalar model of the sign twist. -/
def evenSquareCover {n : ℕ} (lam : Nat.Partition n) :=
  (spechtSquare lam).prod (signTwist (spechtSquare lam))

theorem character_signTwist {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ (Equiv.Perm (Fin n)) V)
    (g : Equiv.Perm (Fin n)) :
    (signTwist ρ).character g = (((Equiv.Perm.sign g : ℤ) : ℂ)) * ρ.character g := by
  simp [Representation.character, signTwist]

theorem character_spechtSquare {n : ℕ} (lam : Nat.Partition n)
    (g : Equiv.Perm (Fin n)) :
    (spechtSquare lam).character g = (TauCeti.spechtModuleℂ lam).character g ^ 2 := by
  simp [spechtSquare, Representation.char_tensor, FDRep.character, pow_two]

theorem character_evenSquareCover {n : ℕ} (lam : Nat.Partition n)
    (g : Equiv.Perm (Fin n)) :
    (evenSquareCover lam).character g =
      if EvenCycleShape (permPartition g) then
        2 * (TauCeti.spechtModuleℂ lam).character g ^ 2 else 0 := by
  rw [evenSquareCover, Representation.char_prod, character_signTwist,
    character_spechtSquare]
  by_cases hg : g ∈ alternatingGroup (Fin n)
  · have hs := Equiv.Perm.mem_alternatingGroup.mp hg
    simp [← mem_alternating_iff_evenCycleShape, hg, hs, two_mul]
  · have hs : Equiv.Perm.sign g = -1 :=
      (Int.units_eq_one_or (Equiv.Perm.sign g)).resolve_left
        (fun h => hg (Equiv.Perm.mem_alternatingGroup.mpr h))
    simp [← mem_alternating_iff_evenCycleShape, hg, hs]

/-- The inverse in the character pairing is retained until the symmetric-group
conjugacy-to-inverse theorem `specht_character_inv` is applied. -/
theorem evenCoverNumerator_eq_character_pairing_sum {n : ℕ}
    (lam nu : Nat.Partition n) :
    (evenCoverNumerator lam nu : ℂ) =
      ∑ g : Equiv.Perm (Fin n),
        (evenSquareCover lam).character g *
          (TauCeti.spechtModuleℂ nu).character g⁻¹ := by
  have hs : (∑ g : Equiv.Perm (Fin n),
      (evenSquareCover lam).character g *
        (TauCeti.spechtModuleℂ nu).character g⁻¹) =
      ∑ rho : Nat.Partition n, ((n.factorial / TauCeti.zPart rho : ℕ) : ℂ) *
        (if EvenCycleShape rho then
          2 * (TauCeti.spechtCharValue lam rho : ℂ) ^ 2 *
            (TauCeti.spechtCharValue nu rho : ℂ) else 0) := by
    calc
      _ = ∑ g : Equiv.Perm (Fin n),
          if EvenCycleShape (permPartition g) then
            2 * (TauCeti.spechtCharValue lam (permPartition g) : ℂ) ^ 2 *
              (TauCeti.spechtCharValue nu (permPartition g) : ℂ) else 0 := by
        apply Finset.sum_congr rfl
        intro g _
        rw [character_evenSquareCover, specht_character_inv,
          specht_character_eq_value, specht_character_eq_value]
        split_ifs <;> simp
      _ = _ := sum_perm_partition (n := n) (fun rho : Nat.Partition n =>
        if EvenCycleShape rho then
          2 * (TauCeti.spechtCharValue lam rho : ℂ) ^ 2 *
            (TauCeti.spechtCharValue nu rho : ℂ) else 0)
  rw [hs]
  simp only [evenCoverNumerator, Int.cast_mul, Int.cast_ofNat,
    Int.cast_sum, Int.cast_ite, Int.cast_natCast, Int.cast_pow, Int.cast_zero]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro rho _
  split_ifs <;> ring

/-- The multiplicity of S^nu in the cover, as the dimension of an intertwiner space. -/
def evenSquareMultiplicity {n : ℕ} (lam nu : Nat.Partition n) : ℕ :=
  Module.finrank ℂ (Representation.IntertwiningMap
    (TauCeti.spechtModuleℂ nu).ρ (evenSquareCover lam))

/-- The cover numerator equals n! times the multiplicity. -/
theorem evenCoverNumerator_eq_factorial_mul_multiplicity {n : ℕ}
    (lam nu : Nat.Partition n) :
    evenCoverNumerator lam nu = (n.factorial : ℤ) *
      (evenSquareMultiplicity lam nu : ℤ) := by
  letI : Invertible (Nat.card (Equiv.Perm (Fin n)) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hc : Nat.card (Equiv.Perm (Fin n)) = n.factorial := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  have hp := Representation.card_inv_mul_sum_char_mul_char_eq_finrank
    (TauCeti.spechtModuleℂ nu).ρ (evenSquareCover lam)
  change (Nat.card (Equiv.Perm (Fin n)) : ℂ)⁻¹ *
      (∑ g, (evenSquareCover lam).character g *
        (TauCeti.spechtModuleℂ nu).character g⁻¹) =
      (evenSquareMultiplicity lam nu : ℂ) at hp
  rw [← evenCoverNumerator_eq_character_pairing_sum, hc] at hp
  have hn : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have he : (evenCoverNumerator lam nu : ℂ) =
      (n.factorial : ℂ) * (evenSquareMultiplicity lam nu : ℂ) := by
    rw [← hp]
    field_simp [hn]
  exact_mod_cast he

/-- A nonzero residue gives an injection of the whole simple S_n Specht module into the
cover. No statement about constituents of a reducible restriction is used. -/
theorem whole_specht_embedding_of_cover_residue {n : ℕ}
    (lam nu : Nat.Partition n) (modulus : ℤ)
    (hE : evenCoverNumerator lam nu % modulus ≠ 0) :
    ∃ f : Representation.IntertwiningMap
        (TauCeti.spechtModuleℂ nu).ρ (evenSquareCover lam),
      Function.Injective f ∧ f ≠ 0 := by
  have hm : 0 < evenSquareMultiplicity lam nu :=
    positive_of_scaled_residue n (evenSquareMultiplicity lam nu) _ modulus
      (evenCoverNumerator_eq_factorial_mul_multiplicity lam nu) hE
  obtain ⟨f, hf⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := ℂ)).mp hm
  haveI := FDRep.isIrreducible_of_simple (TauCeti.spechtModuleℂ nu)
  exact ⟨f, (Representation.IsIrreducible.injective_or_eq_zero f).resolve_right hf, hf⟩

end
end HSTZ.TauCetiFinite

#print axioms HSTZ.TauCetiFinite.evenCoverNumerator_eq_factorial_mul_multiplicity
#print axioms HSTZ.TauCetiFinite.whole_specht_embedding_of_cover_residue
