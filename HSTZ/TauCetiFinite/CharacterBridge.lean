import HSTZ.TauCetiFinite.BatchCertificate
import TauCeti.RepresentationTheory.Symmetric.Specht.MurnaghanNakayama
import TauCeti.RepresentationTheory.Symmetric.Specht.Complex

/-!
Connects the executable Murnaghan–Nakayama certificate to TauCeti's Specht characters.
`AgreementThrough` states the comparison between the recurrence and the character
values; `Agreement.agreementThrough15` proves it for degrees at most 15. The generic
`of_agreement` lemmas take the agreement as an explicit argument so that they can be
reused. Canonical cycle lists keep repeated parts and fixed points.
-/
namespace HSTZ.TauCetiFinite
open HSTZ.MurnaghanNakayama
noncomputable section

/-- Positive, descending parts, including all fixed points in cycle partitions. -/
def partitionRows {n : ℕ} (p : Nat.Partition n) : List ℕ :=
  p.parts.sort (· ≥ ·)

theorem partitionRows_parts {n : ℕ} (p : Nat.Partition n) :
    (partitionRows p : Multiset ℕ) = p.parts := Multiset.sort_eq _ _

/-- Agreement of the recurrence with Specht character values in all degrees up to `bound`;
proved for `bound = 15` in `Agreement`. -/
def AgreementThrough (bound : ℕ) : Prop :=
  ∀ (n : ℕ), n ≤ bound → ∀ (lam ρ : Nat.Partition n),
    mn (partitionRows lam) (partitionRows ρ) = TauCeti.spechtCharValue lam ρ

open scoped Classical in
/-- TauCeti's Murnaghan–Nakayama rule, allowing repeated parts, fixed points and an empty
remainder. -/
theorem tauCeti_character_step {n m r : ℕ} (lam ρ : Nat.Partition n)
    (ν : Nat.Partition m) (hρ : ρ.parts = r ::ₘ ν.parts) :
    TauCeti.spechtCharValue lam ρ =
      ∑ τ : Nat.Partition m with
          (YoungDiagram.ofPartition lam).IsRimHook (YoungDiagram.ofPartition τ),
        (-1) ^ (YoungDiagram.ofPartition lam).rimHookHeight (YoungDiagram.ofPartition τ) *
          TauCeti.spechtCharValue τ ν :=
  TauCeti.spechtCharValue_eq_sum_rimHook lam ρ ν hρ

/-- Given agreement, a checked integer is a Specht character value. -/
theorem certified_value_of_agreement {bound n : ℕ}
    (agreement : AgreementThrough bound) (hn : n ≤ bound)
    (cert : Certificate) (lam ρ : Nat.Partition n) (value : ℤ)
    (h : checkValue cert (partitionRows lam) (partitionRows ρ) value = true) :
    TauCeti.spechtCharValue lam ρ = value := by
  exact (agreement n hn lam ρ).symm.trans (checkValue_sound cert _ _ value h)

/-- The same conclusion for each query of a verified batch. -/
theorem certified_batch_value_of_agreement {bound n : ℕ}
    (agreement : AgreementThrough bound) (hn : n ≤ bound)
    (cert queries : Certificate) (lam ρ : Nat.Partition n) (value : ℤ)
    (h : checkBatch cert queries = true)
    (hq : (⟨partitionRows lam, partitionRows ρ, value⟩ : Entry) ∈ queries) :
    TauCeti.spechtCharValue lam ρ = value := by
  exact (agreement n hn lam ρ).symm.trans (checkBatch_sound cert queries h _ hq)

/-- Given agreement, a checked integer is the trace of `g` on the complex Specht module. -/
theorem certified_complex_trace_of_agreement {bound n : ℕ}
    (agreement : AgreementThrough bound) (hn : n ≤ bound)
    (cert : Certificate) (lam : Nat.Partition n) (g : Equiv.Perm (Fin n)) (value : ℤ)
    (h : checkValue cert (partitionRows lam)
      (partitionRows ((TauCeti.partitionEquivConjClasses n).symm (ConjClasses.mk g)))
      value = true) :
    (TauCeti.spechtModuleℂ lam).character g = (value : ℂ) := by
  rw [TauCeti.character_spechtModuleℂ_intCast, TauCeti.spechtChar_eq_value,
    certified_value_of_agreement agreement hn cert lam _ value h]

end
end HSTZ.TauCetiFinite
#print axioms HSTZ.TauCetiFinite.tauCeti_character_step
#print axioms HSTZ.TauCetiFinite.certified_batch_value_of_agreement
#print axioms HSTZ.TauCetiFinite.certified_complex_trace_of_agreement
