import HSTZ.WitnessPathLetterTransport
import HSTZ.ContainedPathCoefficient

/-! Selected-path source dual and prescribed coefficient transport.
Reuses word/letter pairing interfaces from OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
This is a private finite pairing calculation; no common flag or attachment
coefficient is computed here. -/
namespace HSTZ
noncomputable section
open OAI.Saxl

private theorem finite_basis_sum {I : Type*} [Fintype I] [DecidableEq I] (x : I → ℂ) :
    x=∑ a : I, x a • (Pi.single (M := fun _ => ℂ) a 1) := by
  funext w
  simp [Pi.smul_apply,Pi.single_apply]

private theorem map_lift_eval {n d D e E : ℕ} (phi : Fin d → Fin D)
    (psi : Fin e → Fin E) (L : Fin D → Fin E → ℂ)
    (x : WordSpace n d) (w : Fin n → Fin e) :
    wordMap L (letterLift phi x) (psi ∘ w)=
      wordMap (fun i a=>L (phi i) (psi a)) x w := by
  classical
  rw [finite_basis_sum x]
  change (wordMap L).toLinearMap ((letterLift phi).toLinearMap _ ) _=
    (wordMap (fun i a=>L (phi i) (psi a))).toLinearMap _ _
  simp only [map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro a ha
  change x a * wordMap L (letterLift phi (Pi.single a 1)) (psi ∘ w)=
    x a * wordMap (fun i z => L (phi i) (psi z)) (Pi.single a 1) w
  rw [letterLift_single,wordMap_single,wordMap_single]
  rfl

private theorem pair_lift_source {n e E : ℕ} (psi : Fin e → Fin E)
    (v : WordSpace n E) (y : WordSpace n e) :
    dotProduct v (letterLift psi y)=∑ a : Fin n → Fin e, y a*v (psi ∘ a) := by
  classical
  conv_lhs => rw [finite_basis_sum y]
  change dotProduct v ((letterLift psi).toLinearMap _)=_
  simp only [map_sum,map_smul,dotProduct_sum,dotProduct_smul,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro a ha
  change y a * dotProduct v (letterLift psi (Pi.single a 1))=y a*v (psi ∘ a)
  rw [letterLift_single,dotProduct_single_one]

private theorem lifted_pair {n d D e E : ℕ} (phi : Fin d → Fin D)
    (psi : Fin e → Fin E) (L : Fin D → Fin E → ℂ)
    (x : WordSpace n d) (y : WordSpace n e) :
    dotProduct (wordMap L (letterLift phi x)) (letterLift psi y)=
      dotProduct (wordMap (fun i a=>L (phi i) (psi a)) x) y := by
  rw [pair_lift_source]
  simp_rw [map_lift_eval]
  unfold dotProduct
  apply Finset.sum_congr rfl
  intro a ha
  exact mul_comm _ _

private def binaryDual {D E : ℕ} (L : Fin 4 → ℂ) (v : Fin (D*E)) : ℂ :=
  if hv : ((finProdFinEquiv : Fin D × Fin E ≃ Fin (D*E)).symm v).1.val<2 ∧
      ((finProdFinEquiv : Fin D × Fin E ≃ Fin (D*E)).symm v).2.val<2 then
    L ((finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4)
      (⟨((finProdFinEquiv : Fin D × Fin E ≃ Fin (D*E)).symm v).1.val,hv.1⟩,
        ⟨((finProdFinEquiv : Fin D × Fin E ≃ Fin (D*E)).symm v).2.val,hv.2⟩))
  else 0

section Source
variable {h : ℕ → ℕ} (hh : Antitone h) {d m : ℕ} (k b delta : ℕ) (hk : 5 ≤ k)
local notation "pi" => containedPath h hh d (witnessPathSize k) m

def containedPathSourceDual : Fin ((pi).colLen 0) →
    Fin ((witnessDiagram k b delta hk).transpose.colLen 0 *
      (witnessDiagram k b delta hk).colLen 0) → ℂ :=
  fun i v => binaryDual (containedPathNativeLetters hh k i) v

 theorem containedPathSourceDual_native (i : Fin ((pi).colLen 0)) (a : Fin 4) :
    containedPathSourceDual hh k b delta hk i (witnessPathPairLetter k b delta hk a)=
      containedPathNativeLetters hh k i a := by
  have hp := witnessPathPairLetter_parts k b delta hk a
  have hl : ((finProdFinEquiv :
      Fin ((witnessDiagram k b delta hk).transpose.colLen 0) ×
      Fin ((witnessDiagram k b delta hk).colLen 0) ≃ Fin
      ((witnessDiagram k b delta hk).transpose.colLen 0 *
        (witnessDiagram k b delta hk).colLen 0)).symm
        (witnessPathPairLetter k b delta hk a)).1.val<2 ∧
      ((finProdFinEquiv :
      Fin ((witnessDiagram k b delta hk).transpose.colLen 0) ×
      Fin ((witnessDiagram k b delta hk).colLen 0) ≃ Fin
      ((witnessDiagram k b delta hk).transpose.colLen 0 *
        (witnessDiagram k b delta hk).colLen 0)).symm
        (witnessPathPairLetter k b delta hk a)).2.val<2 := by
    rw [hp]
    exact ⟨((finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4).symm a).1.isLt,
      ((finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4).symm a).2.isLt⟩
  unfold containedPathSourceDual binaryDual
  rw [dif_pos hl]
  congr 1
  apply (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4).symm.injective
  simp only [Equiv.symm_apply_apply]
  apply Prod.ext
  · apply Fin.ext
    exact congrArg (fun p => p.1.val) hp
  · apply Fin.ext
    exact congrArg (fun p => p.2.val) hp

 theorem containedPathSourceDual_zero (i : Fin ((pi).colLen 0))
    (v : Fin ((witnessDiagram k b delta hk).transpose.colLen 0 *
      (witnessDiagram k b delta hk).colLen 0))
    (hv : ¬(((finProdFinEquiv :
      Fin ((witnessDiagram k b delta hk).transpose.colLen 0) ×
      Fin ((witnessDiagram k b delta hk).colLen 0) ≃ Fin
      ((witnessDiagram k b delta hk).transpose.colLen 0 *
        (witnessDiagram k b delta hk).colLen 0)).symm v).1.val<2 ∧
      ((finProdFinEquiv :
      Fin ((witnessDiagram k b delta hk).transpose.colLen 0) ×
      Fin ((witnessDiagram k b delta hk).colLen 0) ≃ Fin
      ((witnessDiagram k b delta hk).transpose.colLen 0 *
        (witnessDiagram k b delta hk).colLen 0)).symm v).2.val<2)) :
    containedPathSourceDual hh k b delta hk i v=0 := by
  exact dif_neg hv
end Source

section Target
variable {h e : ℕ → ℕ} (hh : Antitone h) (he : Antitone e)
    {d m t : ℕ} (k b delta : ℕ) (hp : PaperWitnessGuard k b delta)
    (htm : t ≤ m) (hroom : ∀ c < t, d+e c≤h c)
    (hclear : t*d+4≤witnessPathSize k)
    (hcapacity : witnessPathSize k≤prefixSum (capacity h d) m)
local notation "pi" => containedPath h hh d (witnessPathSize k) m
local notation "theta" => containedWhole h e hh he d (witnessPathSize k) m
local notation "T" => containedPathPrefixOrder hh htm hroom hclear hcapacity

def containedPathTargetDual : Fin ((theta).colLen 0) →
    Fin ((witnessDiagram k b delta hp.staircase_bound).transpose.colLen 0 *
      (witnessDiagram k b delta hp.staircase_bound).colLen 0) → ℂ :=
  fun i v => if hi : i.val < (pi).colLen 0 then
    containedPathSourceDual hh k b delta hp.staircase_bound ⟨i.val,hi⟩ v else 0

 theorem containedPathTargetDual_path (i : Fin ((pi).colLen 0))
    (v : Fin ((witnessDiagram k b delta hp.staircase_bound).transpose.colLen 0 *
      (witnessDiagram k b delta hp.staircase_bound).colLen 0)) :
    containedPathTargetDual hh he k b delta hp
      (rowLetterInclusion (containedPath_le_whole h e hh he d (witnessPathSize k) m) i) v=
      containedPathSourceDual hh k b delta hp.staircase_bound i v := by
  unfold containedPathTargetDual
  change (if hi : i.val < (pi).colLen 0 then
    containedPathSourceDual hh k b delta hp.staircase_bound ⟨i.val,hi⟩ v else 0)=
      containedPathSourceDual hh k b delta hp.staircase_bound i v
  rw [dif_pos i.isLt]

 theorem containedPath_selected_coefficient_eq :
    dotProduct (wordMap (containedPathTargetDual hh he k b delta hp)
      (letterLift (rowLetterInclusion
        (containedPath_le_whole h e hh he d (witnessPathSize k) m)) (polytabloid T)))
      (witnessSelectedPathPairWord k b delta hp)=
    dotProduct (wordMap (containedPathNativeLetters hh k) (polytabloid T))
      (pathPairWord ((k-2)+1)) := by
  rw [witnessSelectedPathPairWord_letter]
  rw [lifted_pair]
  have hm : (fun i a => containedPathTargetDual hh he k b delta hp
      (rowLetterInclusion (containedPath_le_whole h e hh he d (witnessPathSize k) m) i)
      (witnessPathPairLetter k b delta hp.staircase_bound a))=
      containedPathNativeLetters hh k := by
    funext i a
    rw [containedPathTargetDual_path,containedPathSourceDual_native]
  rw [hm]

 theorem containedPath_selected_coefficient_nonzero
    (hmu : (pi).colLen 0≤4) :
    dotProduct (wordMap (containedPathTargetDual hh he k b delta hp)
      (letterLift (rowLetterInclusion
        (containedPath_le_whole h e hh he d (witnessPathSize k) m)) (polytabloid T)))
      (witnessSelectedPathPairWord k b delta hp) ≠ 0 := by
  rw [containedPath_selected_coefficient_eq]
  exact containedPath_native_coefficient hh k htm hroom hclear hcapacity hmu
/-- Same-source restriction for the path row inclusion. -/
theorem containedPath_lifted_pair_restrict {n : ℕ}
    (L : Fin ((theta).colLen 0) →
      Fin ((witnessDiagram k b delta hp.staircase_bound).transpose.colLen 0 *
        (witnessDiagram k b delta hp.staircase_bound).colLen 0) → ℂ)
    (x : WordSpace n ((pi).colLen 0))
    (y : WordSpace n
      ((witnessDiagram k b delta hp.staircase_bound).transpose.colLen 0 *
        (witnessDiagram k b delta hp.staircase_bound).colLen 0)) :
    dotProduct (wordMap L (letterLift (rowLetterInclusion
      (containedPath_le_whole h e hh he d (witnessPathSize k) m)) x)) y =
    dotProduct (wordMap (fun r v => L (rowLetterInclusion
      (containedPath_le_whole h e hh he d (witnessPathSize k) m) r) v) x) y := by
  congr 1
  funext w
  exact map_lift_eval _ id L x w

/-- Same-source restriction for the attachment row embedding. -/
theorem containedAttachment_lifted_pair_restrict
    (hzero : ∀ c, t ≤ c → e c=0)
    (L : Fin ((theta).colLen 0) →
      Fin ((witnessDiagram k b delta hp.staircase_bound).transpose.colLen 0 *
        (witnessDiagram k b delta hp.staircase_bound).colLen 0) → ℂ)
    (x : WordSpace (containedAttachment e he m).card
      ((containedAttachment e he m).colLen 0))
    (y : WordSpace (containedAttachment e he m).card
      ((witnessDiagram k b delta hp.staircase_bound).transpose.colLen 0 *
        (witnessDiagram k b delta hp.staircase_bound).colLen 0)) :
    dotProduct (wordMap L
      (letterLift (containedAttachmentRowLetter hh he hroom hclear hzero) x)) y =
    dotProduct (wordMap (fun r v => L
      (containedAttachmentRowLetter hh he hroom hclear hzero r) v) x) y := by
  congr 1
  funext w
  exact map_lift_eval _ id L x w
end Target
end
end HSTZ
#print axioms HSTZ.containedPathSourceDual
#print axioms HSTZ.containedPathSourceDual_native
#print axioms HSTZ.containedPathSourceDual_zero
#print axioms HSTZ.containedPathTargetDual
#print axioms HSTZ.containedPathTargetDual_path
#print axioms HSTZ.containedPath_selected_coefficient_eq
#print axioms HSTZ.containedPath_selected_coefficient_nonzero

#print axioms HSTZ.containedPath_lifted_pair_restrict
#print axioms HSTZ.containedAttachment_lifted_pair_restrict
