import HSTZ.TauCetiFinite.EvenMoments
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.Algebra.Order.BigOperators.Group.Multiset

/-!
Regroups sums over permutations by cycle type, for TauCeti's complex Specht characters.
The partition map keeps all fixed-point parts. Invariance under inversion is proved in
the symmetric group; it is not assumed that an alternating conjugacy class is closed
under inversion.

Uses TauCeti's class-size and Specht-character theorems.
-/
namespace HSTZ.TauCetiFinite
noncomputable section
open scoped Classical

/-- The full cycle partition, including fixed points, with degree transport. -/
def permPartition {n : ℕ} (g : Equiv.Perm (Fin n)) : Nat.Partition n :=
  (TauCeti.partitionEquivConjClasses n).symm (ConjClasses.mk g)

theorem permPartition_parts {n : ℕ} (g : Equiv.Perm (Fin n)) :
    (permPartition g).parts = g.partition.parts :=
  TauCeti.parts_partitionEquivConjClasses_symm_mk n g

theorem permPartition_inv {n : ℕ} (g : Equiv.Perm (Fin n)) :
    permPartition g⁻¹ = permPartition g := by
  apply Nat.Partition.ext
  simp only [permPartition_parts, Equiv.Perm.parts_partition,
    Equiv.Perm.cycleType_inv, Equiv.Perm.support_inv]

theorem card_permPartition_fiber {n : ℕ} (ρ : Nat.Partition n) :
    Nat.card {g : Equiv.Perm (Fin n) // permPartition g = ρ} =
      n.factorial / TauCeti.zPart ρ := by
  have he : Nat.card {g : Equiv.Perm (Fin n) // permPartition g = ρ} =
      Nat.card {g : Equiv.Perm (Fin n) // g.partition.parts = ρ.parts} := by
    apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro g
    rw [← permPartition_parts]
    exact ⟨fun h => congrArg Nat.Partition.parts h, Nat.Partition.ext⟩
  rw [he]
  exact TauCeti.card_partition_parts_div_zPart_fin n ρ

/-- Sum over every permutation, regrouped by its full cycle partition. -/
theorem sum_perm_partition {n : ℕ} (f : Nat.Partition n → ℂ) :
    (∑ g : Equiv.Perm (Fin n), f (permPartition g)) =
      ∑ ρ : Nat.Partition n, (n.factorial / TauCeti.zPart ρ : ℕ) * f ρ := by
  rw [← Fintype.sum_fiberwise' (permPartition (n := n)) f]
  apply Finset.sum_congr rfl
  intro ρ _
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, ← Nat.card_eq_fintype_card,
    card_permPartition_fiber]

/-- Parity uses the full partition; dropping its ones would change this formula. -/
theorem mem_alternating_iff_evenCycleShape {n : ℕ} (g : Equiv.Perm (Fin n)) :
    g ∈ alternatingGroup (Fin n) ↔ EvenCycleShape (permPartition g) := by
  have hpartsBound : ∀ s : Multiset ℕ, (∀ a ∈ s, 0 < a) → s.card ≤ s.sum := by
    intro s
    induction s using Multiset.induction_on with
    | empty => simp
    | @cons a s ih =>
      intro hpos
      have ha := hpos a (by simp)
      have hs := ih (fun b hb => hpos b (by simp [hb]))
      simp only [Multiset.card_cons, Multiset.sum_cons]
      omega
  have hcard : (permPartition g).parts.card ≤ n := by
    simpa only [(permPartition g).parts_sum] using
      hpartsBound (permPartition g).parts (fun a ha => (permPartition g).parts_pos ha)
  have hparts : (permPartition g).parts.card =
      g.cycleType.card + (n - g.support.card) := by
    rw [permPartition_parts, Equiv.Perm.parts_partition, Multiset.card_add,
      Multiset.card_replicate, Fintype.card_fin]
  have hs := Equiv.Perm.sum_cycleType g
  have hsupport : g.support.card ≤ n := by
    simpa only [Fintype.card_fin] using g.support.card_le_univ
  rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_of_cycleType,
    neg_one_pow_eq_one_iff_even (by decide), Nat.even_iff]
  unfold EvenCycleShape
  omega

/-- Sum over the alternating group, with symmetric-group class weights. -/
theorem sum_even_perm_partition {n : ℕ} (f : Nat.Partition n → ℂ) :
    (∑ g : alternatingGroup (Fin n), f (permPartition g.val)) =
      ∑ ρ : Nat.Partition n,
        if EvenCycleShape ρ then
          (n.factorial / TauCeti.zPart ρ : ℕ) * f ρ else 0 := by
  calc
    _ = ∑ g : Equiv.Perm (Fin n),
        if g ∈ alternatingGroup (Fin n) then f (permPartition g) else 0 := by
      rw [← Finset.sum_subtype (Finset.univ.filter
        (fun g : Equiv.Perm (Fin n) => g ∈ alternatingGroup (Fin n)))
        (by simp) (fun g => f (permPartition g)), Finset.sum_filter]
    _ = ∑ g : Equiv.Perm (Fin n),
        if EvenCycleShape (permPartition g) then f (permPartition g) else 0 := by
      simp only [mem_alternating_iff_evenCycleShape]
    _ = _ := by
      rw [sum_perm_partition (fun ρ => if EvenCycleShape ρ then f ρ else 0)]
      apply Finset.sum_congr rfl
      intro ρ _
      split_ifs <;> simp

theorem specht_character_eq_value {n : ℕ} (lam : Nat.Partition n)
    (g : Equiv.Perm (Fin n)) :
    (TauCeti.spechtModuleℂ lam).character g =
      (TauCeti.spechtCharValue lam (permPartition g) : ℂ) := by
  change (TauCeti.spechtModuleℂ lam).character g =
    (TauCeti.spechtCharValue lam
      ((TauCeti.partitionEquivConjClasses n).symm (ConjClasses.mk g)) : ℂ)
  rw [TauCeti.character_spechtModuleℂ_intCast, TauCeti.spechtChar_eq_value]

/-- Inversion preserves the symmetric-group class, hence every Specht character. -/
theorem specht_character_inv {n : ℕ} (lam : Nat.Partition n)
    (g : Equiv.Perm (Fin n)) :
    (TauCeti.spechtModuleℂ lam).character g⁻¹ =
      (TauCeti.spechtModuleℂ lam).character g := by
  simp only [specht_character_eq_value, permPartition_inv]

end
end HSTZ.TauCetiFinite

#print axioms HSTZ.TauCetiFinite.sum_perm_partition
#print axioms HSTZ.TauCetiFinite.sum_even_perm_partition
#print axioms HSTZ.TauCetiFinite.specht_character_inv
