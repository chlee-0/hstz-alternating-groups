import HSTZ.ContainedMovedWitnessPositions

/-! Elimination of nonmixed terms of the moved full source, using cleared target slots.
Reuses source geometry and `wordMap` from OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
The covectors remain explicitly separated; existence and a nonzero total sum are not
proved in this file. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
section
variable {h e : ℕ → ℕ} (hh : Antitone h) (he : Antitone e)
    {d m t : ℕ} (k b delta : ℕ) (hp : PaperWitnessGuard k b delta)
    (htm : t ≤ m) (hroom : ∀ c < t, d+e c≤h c)
    (hclear : t*d+4≤witnessPathSize k)
    (hcapacity : witnessPathSize k≤prefixSum (capacity h d) m)
    (hsize : prefixSum e m=2*b+delta) (hzero : ∀ c, t ≤ c → e c=0)
    (s : Tableau (witnessComplementSize k b delta)
      (containedWhole h e hh he d (witnessPathSize k) m))
    (sigma : Equiv.Perm (Fin (containedAttachment e he m).card))
    {n : ℕ} (z : Tableau n (witnessDiagram k b delta hp.staircase_bound))
    (L : Fin ((containedWhole h e hh he d (witnessPathSize k) m).colLen 0) → Fin
      ((witnessDiagram k b delta hp.staircase_bound).transpose.colLen 0 *
        (witnessDiagram k b delta hp.staircase_bound).colLen 0) → ℂ)
    (hL : witnessFlagSeparated k b delta hp (fun j => j.val < d) L)
include hzero hL
local notation "P" => containedMovedWitnessPositions hh he k b delta htm hroom hclear hcapacity hsize s sigma

/-- Every nonzero single-word term of the full source has a matching target assignment.
Prefix support discharges the reserved-row invariance hypothesis. -/
theorem containedMovedWitness_nonzero_term_matches (g : columnGroup s)
    (w : Fin (witnessComplementSize k b delta) → Fin
      ((witnessDiagram k b delta hp.staircase_bound).transpose.colLen 0 *
        (witnessDiagram k b delta hp.staircase_bound).colLen 0))
    (hw : witnessComplementPairWord k b delta hp.staircase_bound z w≠0)
    (hmap : wordMap L (Pi.single (rowWord s ∘ g.val.symm ∘ P) 1) w≠0) :
    witnessFlagMatches k b delta (fun j => j.val < d) (rowWord s ∘ g.val.symm ∘ P) := by
  classical
  have hr (p : Fin t × Fin d) :
      (rowWord s (g.val.symm (containedFactorPositions hh he htm hroom hclear hcapacity s
        (.inl ((containedPathPrefixOrder hh htm hroom hclear hcapacity).symm
          (containedReservedCell hh htm hroom hclear p)))))).val < d := by
    let j := (containedPathPrefixOrder hh htm hroom hclear hcapacity).symm
      (containedReservedCell hh htm hroom hclear p)
    let i := witnessComplementOrder k b delta (.inl j)
    have hs := containedReservedSource_low hh k b delta hp.staircase_bound htm hroom hclear hcapacity z w hw p
    have hv : P i=containedFactorPositions hh he htm hroom hclear hcapacity s (.inl j) :=
      containedMovedWitnessPositions_path hh he k b delta htm hroom hclear hcapacity hsize s sigma j
    by_contra hn
    have ha : ¬((rowWord s ∘ g.val.symm ∘ P) i).val < d := by
      simpa only [Function.comp_apply,hv] using hn
    have hl : L ((rowWord s ∘ g.val.symm ∘ P) i) (w i)=0 := by
      apply hL _ _ hs.2
      intro heq
      exact ha (heq.mp hs.1)
    apply hmap
    rw [wordMap_single]
    exact Finset.prod_eq_zero (Finset.mem_univ i) hl
  intro i
  exact (containedColumn_reserved_flag hh he htm hroom hclear hcapacity s hzero g hr (P i)).trans
    (containedMovedWitnessPositions_flag hh he k b delta htm hroom hclear hcapacity hsize s sigma hzero i)

/-- Unmatched full-source terms vanish before sector projection. The full column
group, the inverse precomposition and the asymmetric clearance are kept. -/
theorem containedMovedWitness_unmatched_term_zero (g : columnGroup s)
    (ha : ¬witnessFlagMatches k b delta (fun j => j.val < d) (rowWord s ∘ g.val.symm ∘ P)) :
    dotProduct (wordMap L (Pi.single (rowWord s ∘ g.val.symm ∘ P) 1))
      (witnessComplementPairWord k b delta hp.staircase_bound z)=0 := by
  classical
  unfold dotProduct
  apply Finset.sum_eq_zero
  intro w hw
  by_cases hz : witnessComplementPairWord k b delta hp.staircase_bound z w=0
  · rw [hz,mul_zero]
  · have hm : wordMap L (Pi.single (rowWord s ∘ g.val.symm ∘ P) 1) w=0 := by
      by_contra hn
      exact ha (containedMovedWitness_nonzero_term_matches hh he k b delta hp htm hroom hclear hcapacity hsize hzero s sigma z L hL g w hz hn)
    rw [hm,zero_mul]

end
end
end HSTZ
#print axioms HSTZ.containedMovedWitness_nonzero_term_matches
#print axioms HSTZ.containedMovedWitness_unmatched_term_zero

