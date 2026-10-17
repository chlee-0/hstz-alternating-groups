import HSTZ.WitnessAttachmentMatrixDetection
import HSTZ.ContainedAttachmentPlacement

/-! A nonzero matrix coefficient for the contained attachment, with the degree
transport handled internally. The canonical tableau is moved by a permutation of the
attachment positions only; the selected source and its cardinality reindexing are
kept unchanged. Uses `tableauMove` and `wordMap` from OpenAI's `math` repository
(commit adc7f1241, Apache-2.0). -/
namespace HSTZ
noncomputable section
open OAI.Saxl

private theorem attachment_card_pair {n N a : ℕ} {mu : YoungDiagram}
    (hn : n = N) (A : Tableau N mu) (sigma : Equiv.Perm (Fin n))
    (L : Fin (mu.colLen 0) → Fin a → ℂ) (u : WordSpace n a) :
    dotProduct (wordMap L (polytabloid
      (((finCongr hn).symm.trans sigma |>.trans (finCongr hn)).trans A)))
      (fun w => u (w ∘ finCongr hn)) =
    dotProduct (wordMap L (wordRep n _ sigma.symm
      (polytabloid ((finCongr hn).trans A)))) u := by
  subst N
  simp only [finCongr_refl,Equiv.refl_trans,Equiv.trans_refl,
    Equiv.refl_apply,Function.comp_def]
  change dotProduct (wordMap L (polytabloid (sigma.trans A))) u =
    dotProduct (wordMap L (wordRep n _ sigma.symm (polytabloid A))) u
  have ht : tableauMove A (sigma.trans A) = sigma.symm := by
    apply Equiv.ext
    intro i
    simp [tableauMove]
  rw [polytabloid_move A (sigma.trans A),ht]

/-- Some placement of the canonical contained target that permutes only
attachment positions has a nonzero matrix coefficient against the unchanged selected
factor source. -/
theorem containedAttachment_matrix_coefficient {e : ℕ → ℕ}
    (he : Antitone e) (k b delta m : ℕ) (hp : PaperWitnessGuard k b delta)
    (hsize : prefixSum e m = 2*b+delta)
    (hc : ColumnParity (containedAttachment e he m).colLen delta)
    (ht : (containedAttachment e he m).rowLen 0 ≤ 4) :
    ∃ sigma : Equiv.Perm (Fin (containedAttachment e he m).card),
      ∃ L : Fin ((containedAttachment e he m).colLen 0) →
        Fin ((witnessDiagram k b delta hp.staircase_bound).transpose.colLen 0 *
          (witnessDiagram k b delta hp.staircase_bound).colLen 0) → ℂ,
      dotProduct (wordMap L (polytabloid (containedAttachmentPlacedTableau he sigma)))
        (containedAttachmentFactorSource he k b delta hp hsize) ≠ 0 := by
  let hn := containedAttachment_witness_card he b delta m hsize
  let A := canonicalTableau (containedAttachment e he m) rfl
  let t : Tableau (witnessAttachment b delta).card (containedAttachment e he m) :=
    (finCongr hn).trans A
  obtain ⟨sigma,L,hpair⟩ :=
    witnessSelectedAttachment_matrix_translate_pair k b delta hp t hc ht
  let sigmaE := ((finCongr hn).symm.trans sigma).trans (finCongr hn)
  refine ⟨sigmaE,L,?_⟩
  change dotProduct (wordMap L (polytabloid (sigmaE.trans A)))
    (fun w => witnessSelectedAttachmentPairWord k b delta hp (w ∘ finCongr hn)) ≠ 0
  rw [attachment_card_pair hn A sigma L (witnessSelectedAttachmentPairWord k b delta hp)]
  exact hpair

/-- High-low cut of a dual letter matrix: keep the entries whose letter has first
coordinate at least `2` and second coordinate below `2`. -/
def containedAttachmentMatrixCut {R D H : ℕ} (L : Fin R → Fin (D*H) → ℂ) :
    Fin R → Fin (D*H) → ℂ := fun r v =>
  if 2 ≤ (finProdFinEquiv.symm v).1.val ∧ (finProdFinEquiv.symm v).2.val < 2
    then L r v else 0

theorem containedAttachment_matrix_cut_pair {e : ℕ → ℕ}
    (he : Antitone e) (k b delta m : ℕ) (hp : PaperWitnessGuard k b delta)
    (hsize : prefixSum e m = 2*b+delta) {R : ℕ}
    (L : Fin R → Fin ((witnessDiagram k b delta hp.staircase_bound).transpose.colLen 0 *
      (witnessDiagram k b delta hp.staircase_bound).colLen 0) → ℂ)
    (x : WordSpace (containedAttachment e he m).card R) :
    dotProduct (wordMap (containedAttachmentMatrixCut L) x)
      (containedAttachmentFactorSource he k b delta hp hsize) =
    dotProduct (wordMap L x) (containedAttachmentFactorSource he k b delta hp hsize) := by
  classical
  unfold dotProduct
  apply Finset.sum_congr rfl
  intro w hw
  by_cases hz : containedAttachmentFactorSource he k b delta hp hsize w = 0
  · rw [hz,mul_zero,mul_zero]
  · have hs := witnessAttachmentCyclic_letters k b delta hp
      ⟨_,generator_mem_cyclicSpan _ _⟩
      (w ∘ finCongr (containedAttachment_witness_card he b delta m hsize)) hz
    congr 1
    change (∑ a, x a * ∏ i, containedAttachmentMatrixCut L (a i) (w i)) =
      ∑ a, x a * ∏ i, L (a i) (w i)
    apply Finset.sum_congr rfl
    intro a ha
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    have hg := hs ((finCongr (containedAttachment_witness_card he b delta m hsize)).symm i)
    simp only [splitLeft,splitRight,Function.comp_apply,Equiv.apply_symm_apply] at hg
    exact if_pos hg

/-- The extracted coefficient remains nonzero after the high-low restriction. -/
theorem containedAttachment_high_low_matrix_coefficient {e : ℕ → ℕ}
    (he : Antitone e) (k b delta m : ℕ) (hp : PaperWitnessGuard k b delta)
    (hsize : prefixSum e m = 2*b+delta)
    (hc : ColumnParity (containedAttachment e he m).colLen delta)
    (ht : (containedAttachment e he m).rowLen 0 ≤ 4) :
    ∃ sigma : Equiv.Perm (Fin (containedAttachment e he m).card),
      ∃ L : Fin ((containedAttachment e he m).colLen 0) →
        Fin ((witnessDiagram k b delta hp.staircase_bound).transpose.colLen 0 *
          (witnessDiagram k b delta hp.staircase_bound).colLen 0) → ℂ,
      dotProduct (wordMap (containedAttachmentMatrixCut L)
        (polytabloid (containedAttachmentPlacedTableau he sigma)))
        (containedAttachmentFactorSource he k b delta hp hsize) ≠ 0 := by
  obtain ⟨sigma,L,hL⟩ := containedAttachment_matrix_coefficient he k b delta m hp hsize hc ht
  refine ⟨sigma,L,?_⟩
  rw [containedAttachment_matrix_cut_pair he k b delta m hp hsize]
  exact hL
end
end HSTZ
#print axioms HSTZ.containedAttachment_matrix_coefficient

#print axioms HSTZ.containedAttachment_matrix_cut_pair
#print axioms HSTZ.containedAttachment_high_low_matrix_coefficient
