import HSTZ.ContainedMovedWitnessSurvivorSum

/-! Factorization of the moved selected source and the product over the full
complement. Uses interfaces adapted from OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
The matrix separation hypothesis stays explicit; no coefficient, common flag or
nonvanishing statement is supplied here. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
section
variable {h e : ℕ → ℕ} (hh : Antitone h) (he : Antitone e)
    {d m t : ℕ} (k b delta : ℕ) (hp : PaperWitnessGuard k b delta)
    (htm : t ≤ m) (hroom : ∀ c < t, d+e c≤h c)
    (hclear : t*d+4≤witnessPathSize k)
    (hcapacity : witnessPathSize k≤prefixSum (capacity h d) m)
    (hsize : prefixSum e m=2*b+delta)
    (s : Tableau (witnessComplementSize k b delta)
      (containedWhole h e hh he d (witnessPathSize k) m))
variable (sigma : Equiv.Perm (Fin (containedAttachment e he m).card))
local notation "P" => containedMovedWitnessPositions hh he k b delta htm hroom hclear hcapacity hsize s sigma
local notation "Q" => containedAttachmentPlacedPositions hh he htm hroom hclear hcapacity s sigma
local notation "T" => containedPathPrefixOrder hh htm hroom hclear hcapacity
local notation "A" => canonicalTableau (containedAttachment e he m) rfl

theorem containedMovedWitness_selected_source_factor :
    wordRep _ ((witnessDiagram k b delta hp.staircase_bound).transpose.colLen 0 * (witnessDiagram k b delta hp.staircase_bound).colLen 0) (P) (witnessSelectedComplementPairWord k b delta hp)=
      positionProduct (Q).symm (witnessSelectedPathPairWord k b delta hp)
        (containedAttachmentFactorSource he k b delta hp hsize) := by
  rw [witness_selected_pair_factor]
  funext w
  have hl : leftWord (witnessComplementOrder k b delta).symm (w ∘ P)=leftWord (Q).symm w := by
    funext i
    change w ((P) (witnessComplementOrder k b delta (.inl i)))=w ((Q) (.inl i))
    rw [containedAttachmentPlacedPositions_path]
    exact congrArg w (containedMovedWitnessPositions_path hh he k b delta htm hroom hclear hcapacity hsize s sigma i)
  have hr : rightWord (witnessComplementOrder k b delta).symm (w ∘ P)=
      rightWord (Q).symm w ∘ finCongr (containedAttachment_witness_card he b delta m hsize) := by
    funext i
    exact congrArg w (containedMovedWitnessPositions_attachment hh he k b delta htm hroom hclear hcapacity hsize s sigma i)
  change witnessSelectedPathPairWord k b delta hp (leftWord (witnessComplementOrder k b delta).symm (w ∘ P)) *
    witnessSelectedAttachmentPairWord k b delta hp (rightWord (witnessComplementOrder k b delta).symm (w ∘ P))=_
  rw [hl,hr]
  rfl


theorem containedMovedWitness_lifted_polytabloid_product (hzero : ∀ c, t ≤ c → e c=0)
    {n : ℕ} (z : Tableau n (witnessDiagram k b delta hp.staircase_bound))
    (L : Fin ((containedWhole h e hh he d (witnessPathSize k) m).colLen 0) →
      Fin ((witnessDiagram k b delta hp.staircase_bound).transpose.colLen 0 *
        (witnessDiagram k b delta hp.staircase_bound).colLen 0) → ℂ)
    (hL : witnessFlagSeparated k b delta hp (fun j => j.val < d) L) :
    dotProduct (wordMap L (wordRep _ _ (P).symm (polytabloid s)))
      (witnessComplementPairWord k b delta hp.staircase_bound z)=
    -(dotProduct (wordMap L
      (letterLift (rowLetterInclusion
        (containedPath_le_whole h e hh he d (witnessPathSize k) m)) (polytabloid T)))
      (witnessSelectedPathPairWord k b delta hp) *
      dotProduct (wordMap L
        (letterLift (containedAttachmentRowLetter hh he hroom hclear hzero)
          (polytabloid (containedAttachmentPlacedTableau he sigma))))
        (containedAttachmentFactorSource he k b delta hp hsize)) := by
  rw [containedMovedWitness_selected_survivor_contraction hh he k b delta hp htm hroom hclear hcapacity hsize hzero s sigma z L hL,
    containedAttachmentPlacedSurvivor_lifted hh he htm hroom hclear hcapacity s sigma hzero,
    containedMovedWitness_selected_source_factor hh he k b delta hp htm hroom hclear hcapacity hsize s sigma]
  congr 1
  exact containedWitness_moved_selected_pair_product hh he k b delta hp htm hroom hclear hcapacity hsize s sigma L _ _
end
end
end HSTZ
#print axioms HSTZ.containedMovedWitness_selected_source_factor

#print axioms HSTZ.containedMovedWitness_lifted_polytabloid_product
