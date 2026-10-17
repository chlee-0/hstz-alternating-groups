import HSTZ.WitnessNativeAttachment

/-! Letter support of the selected factors on the full diagonal cyclic carriers.
Reuses letter/cyclic interfaces from OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
The witness width and height and the original ordered cuts are kept separate. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped TensorProduct

private theorem lifted_letter_support {n d D : ℕ} (phi : Fin d → Fin D)
    (P : Fin D → Prop) (hP : ∀ j, P (phi j)) (x : WordSpace n d)
    (w : Fin n → Fin D) (hw : letterLift phi x w ≠ 0) : ∀ i, P (w i) := by
  intro i
  by_contra hi
  apply hw
  change (∑ a : Fin n → Fin d, x a * ∏ j : Fin n,
    if phi (a j)=w j then (1:ℂ) else 0)=0
  apply Finset.sum_eq_zero
  intro a ha
  have hn : phi (a i)≠w i := fun he => hi (he ▸ hP (a i))
  rw [Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hn),mul_zero]

private theorem encoded_letter_support {n d e D E : ℕ}
    (phi : Fin d → Fin D) (psi : Fin e → Fin E)
    (P : Fin D → Prop) (Q : Fin E → Prop)
    (hP : ∀ j, P (phi j)) (hQ : ∀ j, Q (psi j))
    (x : WordSpace n (d*e)) (w : Fin n → Fin (D*E))
    (hw : encodedLetterLift phi psi x w≠0) :
    ∀ i, P (splitLeft w i) ∧ Q (splitRight w i) := by
  have hz : ∀ z : WordSpace n d ⊗[ℂ] WordSpace n e,
      ¬(∀ i, P (splitLeft w i) ∧ Q (splitRight w i)) →
        encodedLetterLift phi psi (wordTensor n d e z) w=0 := by
    intro z hn
    induction z using TensorProduct.induction_on with
    | zero =>
      rw [map_zero]
      change ((encodedLetterLift phi psi).toLinearMap 0) w=0
      rw [map_zero]
      rfl
    | add x y hx hy =>
      rw [map_add]
      change ((encodedLetterLift phi psi).toLinearMap (_+_)) w=0
      rw [map_add]
      change encodedLetterLift phi psi (wordTensor n d e x) w +
        encodedLetterLift phi psi (wordTensor n d e y) w=0
      rw [hx,hy,add_zero]
    | tmul u v =>
      rw [encodedLetterLift_tensor,wordTensor_tmul]
      by_cases hu : letterLift phi u (splitLeft w)=0
      · rw [hu,zero_mul]
      · have hp := lifted_letter_support phi P hP u (splitLeft w) hu
        have hv : letterLift psi v (splitRight w)=0 := by
          by_contra hv
          exact hn (fun i => ⟨hp i,lifted_letter_support psi Q hQ v (splitRight w) hv i⟩)
        rw [hv,mul_zero]
  by_contra hn
  apply hw
  simpa only [LinearEquiv.apply_symm_apply] using hz ((wordTensor n d e).symm x) hn

theorem witnessAttachmentRowLetter_high (k b delta : ℕ) (hk : 5 ≤ k)
    (i : Fin ((witnessAttachment b delta).transpose.colLen 0)) :
    2≤(witnessAttachmentRowLetter k b delta hk i).val := by
  change 2≤witnessAttachmentHighValue k b delta i.val
  unfold witnessAttachmentHighValue
  split_ifs <;> omega

theorem witnessAttachmentColumnLetter_low (k b delta : ℕ) (hk : 5 ≤ k)
    (i : Fin ((witnessAttachment b delta).colLen 0)) :
    (witnessAttachmentColumnLetter k b delta hk i).val<2 := by
  change i.val<2
  exact lt_of_lt_of_le i.isLt (witnessAttachment_rows b delta)

/-- Every vector in the selected path cyclic module uses low-low letters. -/
theorem witnessPathCyclic_letters (k b delta : ℕ) (hp : PaperWitnessGuard k b delta)
    (x : witnessPathCyclic k b delta hp)
    (w : Fin (witnessPathSize k) → Fin
      ((witnessDiagram k b delta hp.staircase_bound).transpose.colLen 0 *
        (witnessDiagram k b delta hp.staircase_bound).colLen 0)) (hw : x.val w≠0) :
    ∀ i, (splitLeft w i).val<2 ∧ (splitRight w i).val<2 := by
  obtain ⟨y,hy⟩ := (witnessNativePathCyclicMap_bijective k b delta hp).surjective x
  have he := witnessNativePathCyclicMap_encoding k b delta hp y
  rw [hy] at he
  rw [he] at hw
  exact encoded_letter_support (witnessLowRowLetter k b delta hp.staircase_bound)
    (witnessLowColumnLetter k b delta hp.staircase_bound)
    (fun j => j.val<2) (fun j => j.val<2) (fun j => j.isLt) (fun j => j.isLt) y.val w hw

/-- Every vector in the selected attachment cyclic module uses high-low letters. -/
theorem witnessAttachmentCyclic_letters (k b delta : ℕ) (hp : PaperWitnessGuard k b delta)
    (x : witnessAttachmentCyclic k b delta hp)
    (w : Fin (witnessAttachment b delta).card → Fin
      ((witnessDiagram k b delta hp.staircase_bound).transpose.colLen 0 *
        (witnessDiagram k b delta hp.staircase_bound).colLen 0)) (hw : x.val w≠0) :
    ∀ i, 2≤(splitLeft w i).val ∧ (splitRight w i).val<2 := by
  obtain ⟨y,hy⟩ := (witnessNativeAttachmentCyclicMap_bijective k b delta hp).surjective x
  have he := witnessNativeAttachmentCyclicMap_encoding k b delta hp y
  rw [hy] at he
  rw [he] at hw
  have hz : encodedLetterLift (witnessAttachmentRowLetter k b delta hp.staircase_bound)
      (witnessAttachmentColumnLetter k b delta hp.staircase_bound) y.val w≠0 := by
    intro hz
    apply hw
    change signC (witnessAttachmentCyclePositions b delta) *
      encodedLetterLift _ _ y.val w=0
    rw [hz,mul_zero]
  exact encoded_letter_support (witnessAttachmentRowLetter k b delta hp.staircase_bound)
    (witnessAttachmentColumnLetter k b delta hp.staircase_bound)
    (fun j => 2≤j.val) (fun j => j.val<2)
    (witnessAttachmentRowLetter_high k b delta hp.staircase_bound)
    (witnessAttachmentColumnLetter_low k b delta hp.staircase_bound) y.val w hz

end
end HSTZ
#print axioms HSTZ.witnessAttachmentRowLetter_high
#print axioms HSTZ.witnessAttachmentColumnLetter_low
#print axioms HSTZ.witnessPathCyclic_letters
#print axioms HSTZ.witnessAttachmentCyclic_letters
