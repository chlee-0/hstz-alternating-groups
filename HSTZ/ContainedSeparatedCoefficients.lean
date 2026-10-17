import HSTZ.ContainedSeparatedDual

/-! Disjoint target-row extensions preserve both prescribed coefficients.
Reuses the `wordMap` and placement APIs, building on OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
Neither invertibility nor a common nondegenerate ordered basis is asserted. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
section
variable {h e : ℕ → ℕ} (hh : Antitone h) (he : Antitone e)
    {d m t : ℕ} (k b delta : ℕ) (hp : PaperWitnessGuard k b delta)
local notation "pi" => containedPath h hh d (witnessPathSize k) m
local notation "E" => containedAttachment e he m
local notation "theta" => containedWhole h e hh he d (witnessPathSize k) m
variable (N : Fin ((containedAttachment e he m).colLen 0) → Fin ((witnessDiagram k b delta hp.staircase_bound).transpose.colLen 0 *
        (witnessDiagram k b delta hp.staircase_bound).colLen 0) → ℂ)

variable (htm : t ≤ m) (hroom : ∀ c < t, d+e c≤h c)
    (hclear : t*d+4≤witnessPathSize k)
    (hcapacity : witnessPathSize k≤prefixSum (capacity h d) m)
    (hzero : ∀ c, t≤c → e c=0)
local notation "T" => containedPathPrefixOrder hh htm hroom hclear hcapacity

theorem containedCombinedTargetDual_path_pair :
    dotProduct (wordMap (containedCombinedTargetDual hh he k b delta hp N)
      (letterLift (rowLetterInclusion
        (containedPath_le_whole h e hh he d (witnessPathSize k) m)) (polytabloid T)))
      (witnessSelectedPathPairWord k b delta hp) =
    dotProduct (wordMap (containedPathTargetDual hh he k b delta hp)
      (letterLift (rowLetterInclusion
        (containedPath_le_whole h e hh he d (witnessPathSize k) m)) (polytabloid T)))
      (witnessSelectedPathPairWord k b delta hp) := by
  have hl := containedPath_lifted_pair_restrict (d := d) (m := m)
    (n := witnessPathSize k) hh he k b delta hp
    (containedCombinedTargetDual hh he k b delta hp N)
    (polytabloid T) (witnessSelectedPathPairWord k b delta hp)
  have hp' := containedPath_lifted_pair_restrict (d := d) (m := m)
    (n := witnessPathSize k) hh he k b delta hp
    (containedPathTargetDual hh he k b delta hp)
    (polytabloid T) (witnessSelectedPathPairWord k b delta hp)
  rw [hl, hp']
  have hr : (fun r v => containedCombinedTargetDual hh he k b delta hp N
      (rowLetterInclusion (containedPath_le_whole h e hh he d (witnessPathSize k) m) r) v) =
      (fun r v => containedPathTargetDual hh he k b delta hp
      (rowLetterInclusion (containedPath_le_whole h e hh he d (witnessPathSize k) m) r) v) := by
    funext r v
    exact containedCombinedTargetDual_path hh he k b delta hp N r v
  rw [hr]

theorem containedCombinedTargetDual_attachment_pair
    (hsize : prefixSum e m=2*b+delta)
    (sigma : Equiv.Perm (Fin (E).card)) :
    dotProduct (wordMap (containedCombinedTargetDual hh he k b delta hp N)
      (letterLift (containedAttachmentRowLetter hh he hroom hclear hzero)
        (polytabloid (containedAttachmentPlacedTableau he sigma))))
      (containedAttachmentFactorSource he k b delta hp hsize) =
    dotProduct (wordMap (containedAttachmentMatrixCut N)
      (polytabloid (containedAttachmentPlacedTableau he sigma)))
      (containedAttachmentFactorSource he k b delta hp hsize) := by
  have hl := containedAttachment_lifted_pair_restrict (d := d) (m := m) (t := t)
    hh he k b delta hp hroom hclear hzero
    (containedCombinedTargetDual hh he k b delta hp N)
    (polytabloid (containedAttachmentPlacedTableau he sigma))
    (containedAttachmentFactorSource he k b delta hp hsize)
  rw [hl]
  have hr : (fun r v => containedCombinedTargetDual hh he k b delta hp N
      (containedAttachmentRowLetter hh he hroom hclear hzero r) v)=
      containedAttachmentMatrixCut N := by
    funext r v
    exact containedCombinedTargetDual_attachment hh he k b delta hp N hroom hclear hzero r v
  rw [hr]
end
end
end HSTZ
#print axioms HSTZ.containedCombinedTargetDual_path_pair
#print axioms HSTZ.containedCombinedTargetDual_attachment_pair
