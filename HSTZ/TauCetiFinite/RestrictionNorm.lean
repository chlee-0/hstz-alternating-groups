import HSTZ.TauCetiFinite.ClassSums
import TauCeti.RepresentationTheory.FDRep
import Mathlib.RepresentationTheory.FinGroupCharZero
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
The restriction-norm bridge for the finite HSTZ witness: if `evenNormNumerator lam = n!`,
then the restriction of the Specht module S^lam to A_n is simple. The hypothesis is the
integer numerator itself, so the finite certificate checks can discharge it separately.
-/
namespace HSTZ.TauCetiFinite
noncomputable section
open CategoryTheory
open scoped Classical

/-- Restrict TauCeti's complex Specht representation to `A_n`. -/
def restrictedSpecht {n : ℕ} (lam : Nat.Partition n) :
    FDRep ℂ (alternatingGroup (Fin n)) :=
  (Action.res (FGModuleCat ℂ) (alternatingGroup (Fin n)).subtype).obj
    (TauCeti.spechtModuleℂ lam)

theorem character_restrictedSpecht {n : ℕ} (lam : Nat.Partition n)
    (g : alternatingGroup (Fin n)) :
    (restrictedSpecht lam).character g =
      (TauCeti.spechtModuleℂ lam).character g.val := by
  exact FDRep.character_actionRes _ _ _

/-- The unnormalized restriction pairing is half of `evenNormNumerator`. -/
theorem evenNormNumerator_eq_twice_restriction_pairing {n : ℕ}
    (lam : Nat.Partition n) :
    (evenNormNumerator lam : ℂ) =
      2 * ∑ g : alternatingGroup (Fin n),
        (restrictedSpecht lam).character g *
          (restrictedSpecht lam).character g⁻¹ := by
  have hs : (∑ g : alternatingGroup (Fin n),
      (restrictedSpecht lam).character g *
        (restrictedSpecht lam).character g⁻¹) =
      ∑ ρ : Nat.Partition n, if EvenCycleShape ρ then
        (n.factorial / TauCeti.zPart ρ : ℕ) *
          (TauCeti.spechtCharValue lam ρ : ℂ) ^ 2 else 0 := by
    calc
      _ = ∑ g : alternatingGroup (Fin n),
          (TauCeti.spechtCharValue lam (permPartition g.val) : ℂ) ^ 2 := by
        apply Finset.sum_congr rfl
        intro g _
        simp only [character_restrictedSpecht]
        change (TauCeti.spechtModuleℂ lam).character g.val *
          (TauCeti.spechtModuleℂ lam).character g.val⁻¹ = _
        simp only [specht_character_eq_value, permPartition_inv, pow_two]
      _ = _ := sum_even_perm_partition
        (fun ρ : Nat.Partition n => (TauCeti.spechtCharValue lam ρ : ℂ) ^ 2)
  rw [hs]
  simp only [evenNormNumerator, Int.cast_mul, Int.cast_ofNat,
    Int.cast_sum, Int.cast_ite, Int.cast_natCast, Int.cast_pow, Int.cast_zero]

/-- The factor two is the index of `A_n`, which requires `n ≥ 2`. -/
theorem twice_card_alternating {n : ℕ} (hn : 2 ≤ n) :
    (2 : ℂ) * (Nat.card (alternatingGroup (Fin n)) : ℂ) = (n.factorial : ℂ) := by
  letI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  have hc := two_mul_nat_card_alternatingGroup (α := Fin n)
  have hc' : 2 * Nat.card (alternatingGroup (Fin n)) = n.factorial := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin] using hc
  exact_mod_cast hc'

/-- If `evenNormNumerator lam = n!`, the restricted Specht representation is simple. -/
theorem simple_restrictedSpecht_of_evenNormNumerator {n : ℕ} (hn : 2 ≤ n)
    (lam : Nat.Partition n) (hD : evenNormNumerator lam = (n.factorial : ℤ)) :
    Simple (restrictedSpecht lam) := by
  apply (FDRep.simple_iff_char_is_norm_one (restrictedSpecht lam)).mpr
  apply mul_left_cancel₀ (show (2 : ℂ) ≠ 0 by norm_num)
  rw [← evenNormNumerator_eq_twice_restriction_pairing,
    twice_card_alternating hn, hD]
  norm_cast

end
end HSTZ.TauCetiFinite

#print axioms HSTZ.TauCetiFinite.evenNormNumerator_eq_twice_restriction_pairing
#print axioms HSTZ.TauCetiFinite.simple_restrictedSpecht_of_evenNormNumerator
