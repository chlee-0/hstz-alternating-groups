import HSTZ.ContainedSeparatedCoefficients
import HSTZ.ContainedMovedWitnessProduct

/-! Both prescribed factor coefficients under one separated matrix, and nonvanishing of
the full complement coefficient with the attachment placement retained.
Reuses declarations from OpenAI's `math` repository (commit adc7f1241, Apache-2.0). -/
namespace HSTZ
noncomputable section
open OAI.Saxl
section
variable {h e : ℕ → ℕ} (hh : Antitone h) (he : Antitone e)
    {d m t : ℕ} (k b delta : ℕ) (hp : PaperWitnessGuard k b delta)
    (htm : t ≤ m) (hroom : ∀ c < t, d+e c≤h c)
    (hclear : t*d+4≤witnessPathSize k)
    (hcapacity : witnessPathSize k≤prefixSum (capacity h d) m)
    (hsize : prefixSum e m=2*b+delta) (hzero : ∀ c, t≤c → e c=0)
local notation "pi" => containedPath h hh d (witnessPathSize k) m
local notation "E" => containedAttachment e he m
local notation "theta" => containedWhole h e hh he d (witnessPathSize k) m
local notation "T" => containedPathPrefixOrder hh htm hroom hclear hcapacity

theorem contained_both_lifted_coefficients
    (hpi : (pi).colLen 0≤4) (hc : ColumnParity (E).colLen delta)
    (hE : (E).rowLen 0≤4) :
    ∃ sigma : Equiv.Perm (Fin (E).card), ∃ L : Fin ((theta).colLen 0) → Fin ((witnessDiagram k b delta hp.staircase_bound).transpose.colLen 0 *
        (witnessDiagram k b delta hp.staircase_bound).colLen 0) → ℂ,
      witnessFlagSeparated k b delta hp (fun j => j.val < d) L ∧
      dotProduct (wordMap L (letterLift (rowLetterInclusion
        (containedPath_le_whole h e hh he d (witnessPathSize k) m)) (polytabloid T)))
        (witnessSelectedPathPairWord k b delta hp)≠0 ∧
      dotProduct (wordMap L (letterLift (containedAttachmentRowLetter hh he hroom hclear hzero)
        (polytabloid (containedAttachmentPlacedTableau he sigma))))
        (containedAttachmentFactorSource he k b delta hp hsize)≠0 := by
  obtain ⟨sigma,N,hN⟩ := containedAttachment_high_low_matrix_coefficient he k b delta m hp hsize hc hE
  refine ⟨sigma,containedCombinedTargetDual hh he k b delta hp N,
    containedCombinedTargetDual_separated hh he k b delta hp N,?_,?_⟩
  · rw [containedCombinedTargetDual_path_pair hh he k b delta hp N htm hroom hclear hcapacity]
    exact containedPath_selected_coefficient_nonzero hh he k b delta hp htm hroom hclear hcapacity hpi
  · rw [containedCombinedTargetDual_attachment_pair hh he k b delta hp N hroom hclear hzero hsize sigma]
    exact hN

include hzero in
theorem containedMovedWitness_contraction_nonzero
    (s : Tableau (witnessComplementSize k b delta) (theta))
    (hpi : (pi).colLen 0≤4) (hc : ColumnParity (E).colLen delta)
    (hE : (E).rowLen 0≤4) {n : ℕ}
    (z : Tableau n (witnessDiagram k b delta hp.staircase_bound)) :
    ∃ sigma : Equiv.Perm (Fin (E).card), ∃ L : Fin ((theta).colLen 0) → Fin ((witnessDiagram k b delta hp.staircase_bound).transpose.colLen 0 *
        (witnessDiagram k b delta hp.staircase_bound).colLen 0) → ℂ,
      witnessFlagSeparated k b delta hp (fun j => j.val < d) L ∧
      dotProduct (wordMap L (wordRep _ _
        (containedMovedWitnessPositions hh he k b delta htm hroom hclear hcapacity hsize s sigma).symm
        (polytabloid s))) (witnessComplementPairWord k b delta hp.staircase_bound z)≠0 := by
  obtain ⟨sigma,L,hL,hpL,hEL⟩ := contained_both_lifted_coefficients hh he k b delta hp
    htm hroom hclear hcapacity hsize hzero hpi hc hE
  refine ⟨sigma,L,hL,?_⟩
  rw [containedMovedWitness_lifted_polytabloid_product hh he k b delta hp
    htm hroom hclear hcapacity hsize s sigma hzero z L hL]
  exact neg_ne_zero.mpr (mul_ne_zero hpL hEL)
end
end
end HSTZ
#print axioms HSTZ.contained_both_lifted_coefficients
#print axioms HSTZ.containedMovedWitness_contraction_nonzero
