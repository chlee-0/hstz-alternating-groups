import HSTZ.ContainedTargetFactorGroups

/-! The full-source contraction written as a product of ordered factor
contractions. Reuses `wordMap` and `positionProduct` from OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
The private finite-word packaging follows the existing contraction implementation.
No common flag, nonzero factors or shuffle sign of the paper are supplied. -/
namespace HSTZ
noncomputable section
open OAI.Saxl

private def productWords {n a b D : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b) :
    (Fin n → Fin D) ≃ (Fin a → Fin D) × (Fin b → Fin D) where
  toFun w := (leftWord e w,rightWord e w)
  invFun p := joinPositions e p.1 p.2
  left_inv w := joinPositions_parts e w
  right_inv p := by simp

private theorem productLetters {n a b c D : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (L : Fin c → Fin D → ℂ) (u : Fin a → Fin c) (v : Fin b → Fin c)
    (w : Fin n → Fin D) :
    (∏ i, L (joinPositions e u v i) (w i))=
      (∏ i, L (u i) (leftWord e w i))*(∏ i, L (v i) (rightWord e w i)) := by
  calc
    _ = ∏ j : Fin a ⊕ Fin b, L (joinPositions e u v (e.symm j)) (w (e.symm j)) :=
      (e.symm.prod_comp _).symm
    _ = _ := by rw [Fintype.prod_sum_type]; simp [joinPositions,leftWord,rightWord]

private theorem productMap {n a b c D : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (L : Fin c → Fin D → ℂ) (u : WordSpace a c) (v : WordSpace b c) :
    wordMap L (positionProduct e u v)=positionProduct e (wordMap L u) (wordMap L v) := by
  classical
  funext w
  change (∑ z, (u (leftWord e z)*v (rightWord e z)) * ∏ i, L (z i) (w i))=
    (∑ z, u z*∏ i, L (z i) (leftWord e w i)) *
      (∑ z, v z*∏ i, L (z i) (rightWord e w i))
  rw [← (productWords e).symm.sum_comp]
  simp only [productWords,Equiv.coe_fn_symm_mk,leftWord_join,rightWord_join,productLetters]
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  exact mul_mul_mul_comm _ _ _ _

private theorem productPair {n a b D : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (u x : WordSpace a D) (v y : WordSpace b D) :
    dotProduct (positionProduct e u v) (positionProduct e x y)=dotProduct u x*dotProduct v y := by
  classical
  unfold dotProduct
  simp only [positionProduct]
  rw [← (productWords e).symm.sum_comp]
  simp only [productWords,Equiv.coe_fn_symm_mk,leftWord_join,rightWord_join]
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  exact mul_mul_mul_comm _ _ _ _

section
variable {h e : ℕ → ℕ} (hh : Antitone h) (he : Antitone e)
    {d m t : ℕ} (k b delta : ℕ) (hp : PaperWitnessGuard k b delta)
    (htm : t ≤ m) (hroom : ∀ c < t, d+e c≤h c)
    (hclear : t*d+4≤witnessPathSize k)
    (hcapacity : witnessPathSize k≤prefixSum (capacity h d) m)
    (hsize : prefixSum e m=2*b+delta)
    (s : Tableau (witnessComplementSize k b delta)
      (containedWhole h e hh he d (witnessPathSize k) m))
local notation "P" => containedWitnessPositions hh he k b delta htm hroom hclear hcapacity hsize s
local notation "Q" => containedFactorPositions hh he htm hroom hclear hcapacity s
local notation "T" => containedPathPrefixOrder hh htm hroom hclear hcapacity
local notation "A" => canonicalTableau (containedAttachment e he m) rfl

/-- Attachment position transport in exact degree, keeping the same letters. -/
def containedAttachmentFactorSource : WordSpace (containedAttachment e he m).card ((witnessDiagram k b delta hp.staircase_bound).transpose.colLen 0 * (witnessDiagram k b delta hp.staircase_bound).colLen 0) :=
  fun w => witnessSelectedAttachmentPairWord k b delta hp
    (w ∘ finCongr (containedAttachment_witness_card he b delta m hsize))

theorem containedWitness_selected_source_factor :
    wordRep _ ((witnessDiagram k b delta hp.staircase_bound).transpose.colLen 0 * (witnessDiagram k b delta hp.staircase_bound).colLen 0) (P) (witnessSelectedComplementPairWord k b delta hp)=
      positionProduct (Q).symm (witnessSelectedPathPairWord k b delta hp)
        (containedAttachmentFactorSource he k b delta hp hsize) := by
  rw [witness_selected_pair_factor]
  funext w
  have hl : leftWord (witnessComplementOrder k b delta).symm (w ∘ P)=leftWord (Q).symm w := by
    funext i
    exact congrArg w (containedWitnessPositions_path hh he k b delta htm hroom hclear hcapacity hsize s i)
  have hr : rightWord (witnessComplementOrder k b delta).symm (w ∘ P)=
      rightWord (Q).symm w ∘ finCongr (containedAttachment_witness_card he b delta m hsize) := by
    funext i
    exact congrArg w (containedWitnessPositions_attachment hh he k b delta htm hroom hclear hcapacity hsize s i)
  change witnessSelectedPathPairWord k b delta hp (leftWord (witnessComplementOrder k b delta).symm (w ∘ P)) *
    witnessSelectedAttachmentPairWord k b delta hp (rightWord (witnessComplementOrder k b delta).symm (w ∘ P))=_
  rw [hl,hr]
  rfl

/-- Pairing of the selected factors after moving positions. This exposes only
this consumer of the private finite word product API. -/
theorem containedWitness_moved_selected_pair_product
    (sigma : Equiv.Perm (Fin (containedAttachment e he m).card))
    (L : Fin ((containedWhole h e hh he d (witnessPathSize k) m).colLen 0) → Fin
      ((witnessDiagram k b delta hp.staircase_bound).transpose.colLen 0 *
        (witnessDiagram k b delta hp.staircase_bound).colLen 0) → ℂ)
    (u : WordSpace (witnessPathSize k)
      ((containedWhole h e hh he d (witnessPathSize k) m).colLen 0))
    (v : WordSpace (containedAttachment e he m).card
      ((containedWhole h e hh he d (witnessPathSize k) m).colLen 0)) :
    let M := ((Equiv.sumCongr (Equiv.refl _) sigma).trans (Q)).symm
    dotProduct (wordMap L (positionProduct M u v))
      (positionProduct M (witnessSelectedPathPairWord k b delta hp)
        (containedAttachmentFactorSource he k b delta hp hsize))=
      dotProduct (wordMap L u) (witnessSelectedPathPairWord k b delta hp) *
        dotProduct (wordMap L v) (containedAttachmentFactorSource he k b delta hp hsize) := by
  dsimp only
  rw [productMap,productPair]

end
end
end HSTZ
#print axioms HSTZ.containedAttachmentFactorSource
#print axioms HSTZ.containedWitness_selected_source_factor

#print axioms HSTZ.containedWitness_moved_selected_pair_product
