import HSTZ.TauCetiFinite.CanonicalMoves
import TauCeti.RepresentationTheory.Symmetric.Specht.Extremes

/-!
Proves that the executable Murnaghan–Nakayama recurrence `mn` agrees with TauCeti's
Specht character values on canonical partitions of every degree at most 15.
The proof uses TauCeti's Murnaghan–Nakayama rule and its value on the empty partition.
Fixed points, repeated parts and removal down to the empty partition are included.
-/
namespace HSTZ.TauCetiFinite
open HSTZ.MurnaghanNakayama
open scoped Classical
noncomputable section

theorem partitionRows_zero (p : Nat.Partition 0) : partitionRows p = [] := by
  have hs := partitionRows_sum p
  have hp := partitionRows_isShape p
  cases he : partitionRows p with
  | nil => rfl
  | cons a xs =>
    have ha : 0 < a := hp.2 a (by rw [he]; simp)
    rw [he, List.sum_cons] at hs
    omega

/-- In degree zero both sides equal `1`, the value of the trivial Specht character. -/
theorem canonical_agreement_zero (lam rho : Nat.Partition 0) :
    mn (partitionRows lam) (partitionRows rho) = TauCeti.spechtCharValue lam rho := by
  have he : lam = Nat.Partition.indiscrete 0 := partitionRows_injective
    ((partitionRows_zero lam).trans (partitionRows_zero _).symm)
  calc
    mn (partitionRows lam) (partitionRows rho) = 1 := by
      rw [partitionRows_zero lam, partitionRows_zero rho]; rfl
    1 = TauCeti.spechtCharValue lam rho := by
      rw [he, TauCeti.spechtCharValue_indiscrete]

/-- The recurrence agrees with TauCeti's Specht character values in every degree at most 15. -/
theorem agreementThrough15 : AgreementThrough 15 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn lam rho
    by_cases hzero : n = 0
    · subst n
      exact canonical_agreement_zero lam rho
    cases hc : partitionRows rho with
    | nil =>
      have hs := partitionRows_sum rho
      rw [hc, List.sum_nil] at hs
      exact False.elim (hzero hs.symm)
    | cons r xs =>
      have hshape : IsShape (r :: xs) := hc ▸ partitionRows_isShape rho
      have hr : 0 < r := hshape.2 r (by simp)
      have hx : IsShape xs := ⟨(List.pairwise_cons.mp hshape.1).2,
        fun a ha => hshape.2 a (List.mem_cons_of_mem r ha)⟩
      let nu : Nat.Partition xs.sum := rowsPartition xs hx rfl
      have hnu : partitionRows nu = xs := rowsPartition_rows _ _ _
      have hcycle : partitionRows rho = r :: partitionRows nu :=
        hc.trans (congrArg (List.cons r) hnu.symm)
      have hparts : rho.parts = r ::ₘ nu.parts := by
        have hh := congrArg (fun zs : List ℕ => (zs : Multiset ℕ)) hcycle
        change (partitionRows rho : Multiset ℕ) =
          r ::ₘ (partitionRows nu : Multiset ℕ) at hh
        simpa only [partitionRows_parts] using hh
      have hs := partitionRows_sum rho
      rw [hc, List.sum_cons] at hs
      have hdegree : n = xs.sum + r := by omega
      have hsmall : xs.sum < n := by omega
      rw [← hc]
      calc
        mn (partitionRows lam) (partitionRows rho) =
            ∑ eta : Nat.Partition xs.sum with
                (YoungDiagram.ofPartition lam).IsRimHook (YoungDiagram.ofPartition eta),
              (-1 : ℤ) ^ (YoungDiagram.ofPartition lam).rimHookHeight
                (YoungDiagram.ofPartition eta) * mn (partitionRows eta) (partitionRows nu) := by
          rw [hcycle, mn_cons]
          exact canonical_move_sum lam hdegree hr _
        _ = ∑ eta : Nat.Partition xs.sum with
                (YoungDiagram.ofPartition lam).IsRimHook (YoungDiagram.ofPartition eta),
              (-1 : ℤ) ^ (YoungDiagram.ofPartition lam).rimHookHeight
                (YoungDiagram.ofPartition eta) * TauCeti.spechtCharValue eta nu := by
          apply Finset.sum_congr rfl
          intro eta heta
          rw [ih xs.sum hsmall (by omega) eta nu]
        _ = TauCeti.spechtCharValue lam rho :=
          (TauCeti.spechtCharValue_eq_sum_rimHook lam rho nu hparts).symm

/-- Every query of a verified batch in degree at most 15 is a Specht character value. -/
theorem certified_batch_character {n : ℕ} (hn : n ≤ 15)
    (cert queries : Certificate) (lam rho : Nat.Partition n) (value : ℤ)
    (h : checkBatch cert queries = true)
    (hq : (⟨partitionRows lam,partitionRows rho,value⟩ : Entry) ∈ queries) :
    TauCeti.spechtCharValue lam rho = value :=
  certified_batch_value_of_agreement agreementThrough15 hn cert queries lam rho value h hq

/-- A checked value in degree at most 15 is the trace of `g` on the complex Specht module. -/
theorem certified_complex_character {n : ℕ} (hn : n ≤ 15)
    (cert : Certificate) (lam : Nat.Partition n) (g : Equiv.Perm (Fin n)) (value : ℤ)
    (h : checkValue cert (partitionRows lam)
      (partitionRows ((TauCeti.partitionEquivConjClasses n).symm (ConjClasses.mk g)))
      value = true) :
    (TauCeti.spechtModuleℂ lam).character g = (value : ℂ) :=
  certified_complex_trace_of_agreement agreementThrough15 hn cert lam g value h

end
end HSTZ.TauCetiFinite
#print axioms HSTZ.TauCetiFinite.partitionRows_zero
#print axioms HSTZ.TauCetiFinite.canonical_agreement_zero
#print axioms HSTZ.TauCetiFinite.agreementThrough15
#print axioms HSTZ.TauCetiFinite.certified_batch_character

#print axioms HSTZ.TauCetiFinite.certified_complex_character
