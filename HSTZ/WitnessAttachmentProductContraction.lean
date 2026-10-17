import HSTZ.WitnessAttachmentTargetSum
import HSTZ.BalanceOutputTwoTensor

/-! Single-word contractions of paper H factors of the same order. Uses interfaces
from OpenAI's `math` repository (commit adc7f1241, Apache-2.0),
and reuses the existing position splits, `wordMap_single` and the H pair contractions.
Private coordinate packaging supplies only the needed finite sum factorization;
noncancellation over the full target column group is a separate question. -/
namespace HSTZ
noncomputable section
open OAI.Saxl

private def hSplitWords {n a b D : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b) :
    (Fin n → Fin D) ≃ (Fin a → Fin D) × (Fin b → Fin D) where
  toFun w := (leftWord e w,rightWord e w)
  invFun p := joinPositions e p.1 p.2
  left_inv w := joinPositions_parts e w
  right_inv p := by simp

private theorem hLetterProduct {n a b d D : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (L : Fin d → Fin D → ℂ) (w : Fin n → Fin d)
    (u : Fin a → Fin D) (v : Fin b → Fin D) :
    (∏ i, L (w i) (joinPositions e u v i)) =
      (∏ i, L (leftWord e w i) (u i)) * (∏ i, L (rightWord e w i) (v i)) := by
  calc
    _ = ∏ j : Fin a ⊕ Fin b, L (w (e.symm j)) (joinPositions e u v (e.symm j)) :=
      (e.symm.prod_comp _).symm
    _ = _ := by rw [Fintype.prod_sum_type]; simp [joinPositions,leftWord,rightWord]

private theorem hContractionSplit {n a b d D : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (L : Fin d → Fin D → ℂ) (w : Fin n → Fin d)
    (x : WordSpace a D) (y : WordSpace b D) :
    dotProduct (wordMap L (Pi.single w 1)) (positionProduct e x y) =
      dotProduct (wordMap L (Pi.single (leftWord e w) 1)) x *
        dotProduct (wordMap L (Pi.single (rightWord e w) 1)) y := by
  classical
  unfold dotProduct
  simp only [wordMap_single,positionProduct]
  rw [← (hSplitWords e).symm.sum_comp]
  simp only [hSplitWords,Equiv.coe_fn_symm_mk,leftWord_join,rightWord_join,hLetterProduct]
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  exact mul_mul_mul_comm _ _ _ _

theorem attachmentHPower_contraction_zero {d : ℕ}
    (L : Fin d → Fin 4 → ℂ) (w : Fin (2*0) → Fin d) :
    dotProduct (wordMap L (Pi.single w 1)) (attachmentHPower 0) = 1 := by
  classical
  simp [attachmentHPower,wordMap_single]

theorem attachmentHPower_contraction_step {d : ℕ} (b : ℕ)
    (L : Fin d → Fin 4 → ℂ) (w : Fin (2*(b+1)) → Fin d) :
    dotProduct (wordMap L (Pi.single w 1)) (attachmentHPower (b+1)) =
      dotProduct (wordMap L (Pi.single (leftWord (attachmentAppendColumn b) w) 1))
        (attachmentHPower b) *
      dotProduct (wordMap L (Pi.single (rightWord (attachmentAppendColumn b) w) 1))
        attachmentPaperH :=
  hContractionSplit (attachmentAppendColumn b) L w _ _

theorem attachmentHTensor_contraction_split {d : ℕ} (b delta : ℕ)
    (L : Fin d → Fin 4 → ℂ) (w : Fin (witnessAttachment b delta).card → Fin d) :
    dotProduct (wordMap L (Pi.single w 1)) (attachmentHTensor b delta) =
      dotProduct (wordMap L (Pi.single (leftWord (attachmentColumnSplit b delta) w) 1))
        (attachmentHPower b) *
      ∏ j : Fin delta, L (rightWord (attachmentColumnSplit b delta) w j) 0 := by
  rw [show attachmentHTensor b delta = positionProduct (attachmentColumnSplit b delta)
      (attachmentHPower b) (Pi.single (fun _ => 0) 1) from rfl,hContractionSplit]
  simp [wordMap_single]

def attachmentHPairIndex (b : ℕ) (j : Fin b) (r : Fin 2) : Fin (2*b) :=
  ⟨2*j.val+r.val, by have hj := j.isLt; have hr := r.isLt; omega⟩

theorem attachmentHPower_contraction_product {d : ℕ} (b : ℕ)
    (L : Fin d → Fin 4 → ℂ) (w : Fin (2*b) → Fin d) :
    dotProduct (wordMap L (Pi.single w 1)) (attachmentHPower b) =
      ∏ j : Fin b, dotProduct (wordMap L (Pi.single
        (![w (attachmentHPairIndex b j 0),w (attachmentHPairIndex b j 1)] : Fin 2 → Fin d) 1))
        attachmentPaperH := by
  induction b with
  | zero => rw [attachmentHPower_contraction_zero]; simp
  | succ b ih =>
    rw [attachmentHPower_contraction_step,ih,Fin.prod_univ_castSucc]
    congr 1
    have hw : rightWord (attachmentAppendColumn b) w =
          (![w (attachmentHPairIndex (b+1) (Fin.last b) 0),
            w (attachmentHPairIndex (b+1) (Fin.last b) 1)] : Fin 2 → Fin d) := by
      funext r
      fin_cases r <;> rfl
    rw [hw]

theorem attachmentHTensor_contraction_product {d : ℕ} (b delta : ℕ)
    (L : Fin d → Fin 4 → ℂ) (w : Fin (witnessAttachment b delta).card → Fin d) :
    dotProduct (wordMap L (Pi.single w 1)) (attachmentHTensor b delta) =
      (∏ j : Fin b, dotProduct (wordMap L (Pi.single
        (![leftWord (attachmentColumnSplit b delta) w (attachmentHPairIndex b j 0),
           leftWord (attachmentColumnSplit b delta) w (attachmentHPairIndex b j 1)] : Fin 2 → Fin d) 1))
        attachmentPaperH) *
      ∏ j : Fin delta, L (rightWord (attachmentColumnSplit b delta) w j) 0 := by
  rw [attachmentHTensor_contraction_split,attachmentHPower_contraction_product]


/-- Concrete output-two consumer of the existing private split calculation.
The same target letters give delta for the two-letter symmetric pair and for H. -/
theorem balanceOutputTwoPower_target_single_pair {n : ℕ} {mu : YoungDiagram}
    (t : Tableau n mu) (ht : mu.colLen 0≤2) (m : ℕ)
    (w : Fin (2*m) → Fin (mu.colLen 0)) :
    dotProduct (wordMap (balanceOutputTwoTargetLetters t ht) (Pi.single w 1))
      (balanceOutputTwoPower m)=
    dotProduct (wordMap (attachmentTargetLetters t (ht.trans (by omega : 2≤4)) 0)
      (Pi.single w 1)) (attachmentHPower m) := by
  classical
  induction m with
  | zero => simp [balanceOutputTwoPower,attachmentHPower,wordMap_single]
  | succ m ih =>
    change dotProduct (wordMap _ (Pi.single w 1))
      (positionProduct (attachmentAppendColumn m) (balanceOutputTwoPower m)
        balanceOutputTwoPair)=_
    rw [hContractionSplit,attachmentHPower_contraction_step,ih]
    congr 1
    have hw : rightWord (attachmentAppendColumn m) w=
        (![w ((attachmentAppendColumn m).symm (.inr 0)),
           w ((attachmentAppendColumn m).symm (.inr 1))] : Fin 2 → Fin (mu.colLen 0)) := by
      ext i
      fin_cases i <;> rfl
    rw [hw,balanceOutputTwoTargetLetters_pair,attachmentTargetLetters_pair]

/-- All original target coordinates, with the same source cut and degree. -/
theorem balanceOutputTwo_target_single_pair {n : ℕ} {mu : YoungDiagram}
    (t : Tableau n mu) (ht : mu.colLen 0≤2) (m : ℕ)
    (w : Fin (witnessAttachment m 0).card → Fin (mu.colLen 0)) :
    dotProduct (wordMap (balanceOutputTwoTargetLetters t ht) (Pi.single w 1))
      (balanceOutputTwoOrdered m)=
    dotProduct (wordMap (attachmentTargetLetters t (ht.trans (by omega : 2≤4)) 0)
      (Pi.single w 1)) (attachmentHTensor m 0) := by
  classical
  change dotProduct (wordMap _ (Pi.single w 1))
    (positionProduct (attachmentColumnSplit m 0) (balanceOutputTwoPower m)
      (Pi.single (fun _ : Fin 0 => (0 : Fin 2)) 1))=_
  rw [hContractionSplit,attachmentHTensor_contraction_split,
    balanceOutputTwoPower_target_single_pair,dotProduct_single_one,wordMap_single]
  simp

/-- Basis expansion and the concrete split consumer compare the two source
contractions for every target vector. -/
theorem balanceOutputTwo_target_pair {n : ℕ} {mu : YoungDiagram}
    (t : Tableau n mu) (ht : mu.colLen 0≤2) (m : ℕ)
    (x : WordSpace (witnessAttachment m 0).card (mu.colLen 0)) :
    dotProduct (wordMap (balanceOutputTwoTargetLetters t ht) x)
      (balanceOutputTwoOrdered m)=
    dotProduct (wordMap (attachmentTargetLetters t (ht.trans (by omega : 2≤4)) 0) x)
      (attachmentHTensor m 0) := by
  classical
  change dotProduct ((wordMap (balanceOutputTwoTargetLetters t ht)).toLinearMap x)
      (balanceOutputTwoOrdered m)=
    dotProduct ((wordMap (attachmentTargetLetters t (ht.trans (by omega : 2≤4)) 0)).toLinearMap x)
      (attachmentHTensor m 0)
  rw [← (Pi.basisFun ℂ (Fin (witnessAttachment m 0).card → Fin (mu.colLen 0))).sum_repr x]
  simp only [map_sum,map_smul,sum_dotProduct,smul_dotProduct,Pi.basisFun_apply]
  apply Finset.sum_congr rfl
  intro a ha
  congr 1
  exact balanceOutputTwo_target_single_pair t ht m a

end
end HSTZ
#print axioms HSTZ.attachmentHPower_contraction_zero
#print axioms HSTZ.attachmentHPower_contraction_step
#print axioms HSTZ.attachmentHTensor_contraction_split

#print axioms HSTZ.attachmentHPower_contraction_product
#print axioms HSTZ.attachmentHTensor_contraction_product

#print axioms HSTZ.balanceOutputTwoPower_target_single_pair
#print axioms HSTZ.balanceOutputTwo_target_single_pair
#print axioms HSTZ.balanceOutputTwo_target_pair
