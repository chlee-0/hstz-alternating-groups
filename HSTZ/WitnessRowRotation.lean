import HSTZ.WitnessRowCarrier

/-! Restriction to the marked core of the row-preserving cell rotation of the
asymmetric witness. The proof is new and uses interfaces adapted from
OpenAI's `math` repository (commit adc7f1241, Apache-2.0). -/
namespace HSTZ
open OAI.Saxl

theorem witnessRowRotation_row (k b delta : ℕ) (hk : 5 ≤ k)
    (x : (witnessDiagram k b delta hk).cells) :
    (witnessRowRotation k b delta hk x).val.1=x.val.1 := rfl

theorem witnessRowRotation_core (k b delta : ℕ) (hk : 5 ≤ k)
    (x : (staircase (k-2)).cells) :
    witnessRowRotation k b delta hk (witnessCoreCell k b delta hk x)=
      (witnessRowMarkedCell k b delta hk x).val := by
  have hx : x.val.1+x.val.2<k-2 := mem_staircase.mp x.property
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change witnessRowForward k b x.val.1 x.val.2=
      (if x.val.2=k-3 then k+b-1 else x.val.2+2)
    by_cases hr : x.val.1=0
    · have he := congrArg Fin.val (witnessFirstRowRotation_core k b delta hk
        ⟨x.val.2,by omega⟩)
      change witnessFirstRowForward k b x.val.2 =
        (if x.val.2=k-3 then k+b-1 else x.val.2+2) at he
      simpa only [witnessRowForward,if_pos hr] using he
    · unfold witnessRowForward witnessRowTailForward
      rw [if_neg hr,if_pos (by omega),if_neg (by omega)]

theorem witnessRowRotation_marked (k b delta : ℕ) (hk : 5 ≤ k)
    (x : (witnessDiagram k b delta hk).cells) :
    witnessRowMarked k b (witnessRowRotation k b delta hk x).val.2 ↔
      x.val.1+x.val.2<k-2 := by
  change witnessRowMarked k b (witnessRowForward k b x.val.1 x.val.2) ↔ _
  have hx : x.val.2<witnessRow k b delta x.val.1 := by
    simpa only [witnessDiagram_row_length] using YoungDiagram.mem_iff_lt_rowLen.mp x.property
  by_cases hr : x.val.1=0
  · have hc : x.val.2<k+b+delta := by simpa [witnessRow,hr,Nat.add_assoc] using hx
    have he := witnessFirstRowRotation_marked k b delta hk ⟨x.val.2,hc⟩
    change witnessRowMarked k b (witnessFirstRowForward k b x.val.2) ↔ x.val.2<k-2 at he
    simpa only [witnessRowForward,if_pos hr,hr,zero_add,if_true] using he
  · unfold witnessRow at hx
    unfold witnessRowForward witnessRowTailForward witnessRowMarked
    simp only [if_neg hr] at hx ⊢
    split_ifs at hx ⊢ <;> omega

theorem witnessRowRotation_inverse (k b delta : ℕ) (hk : 5 ≤ k) :
    Function.LeftInverse (witnessRowUnrotateCell k b delta hk) (witnessRowRotateCell k b delta hk) ∧
    Function.RightInverse (witnessRowUnrotateCell k b delta hk) (witnessRowRotateCell k b delta hk) :=
  ⟨(witnessRowRotation k b delta hk).left_inv,(witnessRowRotation k b delta hk).right_inv⟩
theorem witnessRowRotation_bijective (k b delta : ℕ) (hk : 5 ≤ k) :
    Function.Bijective (witnessRowRotateCell k b delta hk) := (witnessRowRotation k b delta hk).bijective

theorem witnessRowRotation_value (k b delta : ℕ) (hk : 5 ≤ k)
    (x : (witnessDiagram k b delta hk).cells) :
    (witnessRowRotation k b delta hk x).val=
      (x.val.1,witnessRowForward k b x.val.1 x.val.2) := rfl
theorem witnessRowRotation_symm_value (k b delta : ℕ) (hk : 5 ≤ k)
    (x : (witnessDiagram k b delta hk).cells) :
    ((witnessRowRotation k b delta hk).symm x).val=
      (x.val.1,witnessRowBackward k b x.val.1 x.val.2) := rfl

theorem witnessRowRotation_empty_core_row (k b delta : ℕ) (hk : 5 ≤ k)
    (x : (witnessDiagram k b delta hk).cells) (hr : k-2≤x.val.1) :
    witnessRowRotation k b delta hk x=x := by
  have hn : x.val.1≠0 := by omega
  have hq : k-2-x.val.1=0 := by omega
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change witnessRowForward k b x.val.1 x.val.2=x.val.2
    simp [witnessRowForward,hn,witnessRowTailForward,hq]

theorem witnessRowRotation_tail (k b delta : ℕ) (hk : 5 ≤ k)
    (x : (witnessDiagram k b delta hk).cells) (hr : x.val.1≠0)
    (hc : k-2-x.val.1+2≤x.val.2) : witnessRowRotation k b delta hk x=x := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change witnessRowForward k b x.val.1 x.val.2=x.val.2
    simp only [witnessRowForward,if_neg hr,witnessRowTailForward,
      if_neg (by omega : ¬ x.val.2<k-2-x.val.1),
      if_neg (by omega : ¬ x.val.2<k-2-x.val.1+2)]

end HSTZ
#print axioms HSTZ.witnessRowRotation_row
#print axioms HSTZ.witnessRowRotation_core
#print axioms HSTZ.witnessRowRotation_marked
#print axioms HSTZ.witnessRowRotation_inverse
#print axioms HSTZ.witnessRowRotation_bijective
#print axioms HSTZ.witnessRowRotation_value
#print axioms HSTZ.witnessRowRotation_symm_value
#print axioms HSTZ.witnessRowRotation_empty_core_row
#print axioms HSTZ.witnessRowRotation_tail
