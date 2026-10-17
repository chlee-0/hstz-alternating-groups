import HSTZ.WitnessFirstRowCarrier

/-! First-row width permutation for the asymmetric witness.
Uses witness interfaces from OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
The exceptional core letter is kept; this is not a permutation between the unequal
width and height alphabets. -/
namespace HSTZ

theorem witnessFirstRowRotation_value (k b delta : ℕ) (hk : 5 ≤ k)
    (c : Fin (k+b+delta)) :
    (witnessFirstRowRotation k b delta hk c).val=witnessFirstRowForward k b c.val := rfl

theorem witnessFirstRowRotation_symm_value (k b delta : ℕ) (hk : 5 ≤ k)
    (a : Fin (k+b+delta)) :
    ((witnessFirstRowRotation k b delta hk).symm a).val=witnessFirstRowBackward k b a.val := rfl

theorem witnessFirstRowRotation_core (k b delta : ℕ) (hk : 5 ≤ k)
    (i : Fin (k-2)) :
    witnessFirstRowRotation k b delta hk ⟨i.val,by have hi:=i.isLt; omega⟩ =
      witnessMarkedRowLetter k b delta hk i := by
  have hi:=i.isLt
  apply Fin.ext
  change witnessFirstRowForward k b i.val=(if i.val=k-3 then k+b-1 else i.val+2)
  unfold witnessFirstRowForward
  split_ifs <;> omega

theorem witnessFirstRowRotation_marked (k b delta : ℕ) (hk : 5 ≤ k)
    (c : Fin (k+b+delta)) :
    witnessRowMarked k b (witnessFirstRowRotation k b delta hk c).val ↔ c.val<k-2 := by
  have hc:=c.isLt
  change witnessRowMarked k b (witnessFirstRowForward k b c.val) ↔ _
  unfold witnessFirstRowForward witnessRowMarked
  split_ifs <;> omega

theorem witnessFirstRowRotation_inverse (k b delta : ℕ) (hk : 5 ≤ k) :
    Function.LeftInverse (witnessFirstRowUnrotate k b delta hk) (witnessFirstRowRotate k b delta hk) ∧
    Function.RightInverse (witnessFirstRowUnrotate k b delta hk) (witnessFirstRowRotate k b delta hk) :=
  ⟨(witnessFirstRowRotation k b delta hk).left_inv,(witnessFirstRowRotation k b delta hk).right_inv⟩

theorem witnessFirstRowRotation_bijective (k b delta : ℕ) (hk : 5 ≤ k) :
    Function.Bijective (witnessFirstRowRotate k b delta hk) :=
  (witnessFirstRowRotation k b delta hk).bijective

end HSTZ
#print axioms HSTZ.witnessFirstRowRotation_value
#print axioms HSTZ.witnessFirstRowRotation_symm_value
#print axioms HSTZ.witnessFirstRowRotation_core
#print axioms HSTZ.witnessFirstRowRotation_marked
#print axioms HSTZ.witnessFirstRowRotation_inverse
#print axioms HSTZ.witnessFirstRowRotation_bijective
