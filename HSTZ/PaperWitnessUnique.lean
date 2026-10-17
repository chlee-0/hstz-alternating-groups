import HSTZ.WitnessBalancePackingSupport

/-! The parameters of a guarded witness are determined by its size |λ|. Together
with `paperWitness_parameters` this shows that the existential statements
`paperWitness_statementA` and `paperWitness_alternating` are about the canonical
witness λ_n. -/
namespace HSTZ
open OAI.Saxl

private theorem tri_succ' (k : ℕ) : (k+1)*(k+1+1)/2 = k*(k+1)/2 + (k+1) := by
  have h : (k+1)*(k+1+1) = k*(k+1) + (k+1)*2 := by ring
  rw [h, Nat.add_mul_div_right _ _ (by norm_num)]

private theorem tri_mono {a c : ℕ} (h : a ≤ c) : a*(a+1)/2 ≤ c*(c+1)/2 :=
  Nat.div_le_div_right (Nat.mul_le_mul h (by omega))

/-- Two guarded witnesses of the same size have the same parameters. -/
theorem paperWitness_parameters_unique {k b delta k' b' delta' : ℕ}
    (hp : PaperWitnessGuard k b delta) (hp' : PaperWitnessGuard k' b' delta')
    (h : (witnessDiagram k b delta hp.staircase_bound).card =
      (witnessDiagram k' b' delta' hp'.staircase_bound).card) :
    k = k' ∧ b = b' ∧ delta = delta' := by
  rw [witnessDiagram_card, witnessDiagram_card] at h
  have hr := hp.positive_remainder
  have hR := hp.remainder_bound
  have hr' := hp'.positive_remainder
  have hR' := hp'.remainder_bound
  have hd := hp.parity
  have hd' := hp'.parity
  have hk : k = k' := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have h1 := tri_succ' k
      have h2 := tri_mono (show k + 1 ≤ k' by omega)
      omega
    · have h1 := tri_succ' k'
      have h2 := tri_mono (show k' + 1 ≤ k by omega)
      omega
  subst hk
  exact ⟨rfl, by omega, by omega⟩

end HSTZ
#print axioms HSTZ.paperWitness_parameters_unique
