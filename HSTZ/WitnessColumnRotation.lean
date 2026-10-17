import HSTZ.WitnessMarkedCells

/-! A rotation of the cells within each column of the asymmetric witness. Uses the
staircase and marked-cell declarations from OpenAI's `math` repository
(commit adc7f1241, Apache-2.0). -/
namespace HSTZ
open OAI.Saxl

theorem witness_column_core_mem (k b delta r c : ℕ) (hk : 5 ≤ k)
    (hc : c<k-2) :
    (r,c)∈witnessDiagram k b delta hk ↔ r+c<k := by
  rw [YoungDiagram.mem_iff_lt_rowLen,witnessDiagram_row_length]
  unfold witnessRow
  split_ifs <;> omega

theorem witness_cell_column_bound (k b delta : ℕ) (hk : 5 ≤ k)
    (x : (witnessDiagram k b delta hk).cells) :
    x.val.1<k-2-x.val.2+2 := by
  have hx : x.val.2<witnessRow k b delta x.val.1 := by
    simpa only [witnessDiagram_row_length] using
      (YoungDiagram.mem_iff_lt_rowLen.mp x.property)
  unfold witnessRow at hx
  split_ifs at hx <;> omega

theorem witness_cell_row_bound (k b delta : ℕ) (hk : 5 ≤ k)
    (x : (witnessDiagram k b delta hk).cells) : x.val.1<k := by
  have hx : x.val.2<witnessRow k b delta x.val.1 := by
    simpa only [witnessDiagram_row_length] using
      (YoungDiagram.mem_iff_lt_rowLen.mp x.property)
  unfold witnessRow at hx
  split_ifs at hx <;> omega

def witnessColumnRotateCell (k b delta : ℕ) (hk : 5 ≤ k)
    (x : (witnessDiagram k b delta hk).cells) :
    (witnessDiagram k b delta hk).cells :=
  ⟨(if x.val.1<k-2-x.val.2 then x.val.1+2 else x.val.1-(k-2-x.val.2),x.val.2),by
    have hx := witness_cell_column_bound k b delta hk x
    by_cases hc : x.val.2<k-2
    · apply (witness_column_core_mem k b delta _ _ hk hc).mpr
      split_ifs <;> omega
    · have he : k-2-x.val.2=0 := by omega
      simpa only [he,Nat.not_lt_zero,if_false,Nat.sub_zero] using x.property⟩

def witnessColumnUnrotateCell (k b delta : ℕ) (hk : 5 ≤ k)
    (x : (witnessDiagram k b delta hk).cells) :
    (witnessDiagram k b delta hk).cells :=
  ⟨(if x.val.1<2 then x.val.1+(k-2-x.val.2) else x.val.1-2,x.val.2),by
    have hx := witness_cell_column_bound k b delta hk x
    by_cases hc : x.val.2<k-2
    · apply (witness_column_core_mem k b delta _ _ hk hc).mpr
      split_ifs <;> omega
    · have he : k-2-x.val.2=0 := by omega
      have hr : x.val.1<2 := by omega
      simpa only [if_pos hr,he,Nat.add_zero] using x.property⟩

def witnessColumnRotation (k b delta : ℕ) (hk : 5 ≤ k) :
    Equiv.Perm (witnessDiagram k b delta hk).cells where
  toFun := witnessColumnRotateCell k b delta hk
  invFun := witnessColumnUnrotateCell k b delta hk
  left_inv x := by
    have hx := witness_cell_column_bound k b delta hk x
    apply Subtype.ext
    apply Prod.ext
    · change (if (if x.val.1<k-2-x.val.2 then x.val.1+2 else x.val.1-(k-2-x.val.2))<2
        then (if x.val.1<k-2-x.val.2 then x.val.1+2 else x.val.1-(k-2-x.val.2))+(k-2-x.val.2)
        else (if x.val.1<k-2-x.val.2 then x.val.1+2 else x.val.1-(k-2-x.val.2))-2)=x.val.1
      split_ifs <;> omega
    · rfl
  right_inv x := by
    have hx := witness_cell_column_bound k b delta hk x
    apply Subtype.ext
    apply Prod.ext
    · change (if (if x.val.1<2 then x.val.1+(k-2-x.val.2) else x.val.1-2)<k-2-x.val.2
        then (if x.val.1<2 then x.val.1+(k-2-x.val.2) else x.val.1-2)+2
        else (if x.val.1<2 then x.val.1+(k-2-x.val.2) else x.val.1-2)-(k-2-x.val.2))=x.val.1
      split_ifs <;> omega
    · rfl

theorem witnessColumnRotation_column (k b delta : ℕ) (hk : 5 ≤ k)
    (x : (witnessDiagram k b delta hk).cells) :
    (witnessColumnRotation k b delta hk x).val.2=x.val.2 := rfl

theorem witnessColumnRotation_core (k b delta : ℕ) (hk : 5 ≤ k)
    (x : (staircase (k-2)).cells) :
    witnessColumnRotation k b delta hk (witnessCoreCell k b delta hk x) =
      (witnessColumnMarkedCell k b delta hk x).val := by
  have hx : x.val.1+x.val.2<k-2 := mem_staircase.mp x.property
  apply Subtype.ext
  change (if x.val.1<k-2-x.val.2 then x.val.1+2 else x.val.1-(k-2-x.val.2),x.val.2)=
    (x.val.1+2,x.val.2)
  rw [if_pos (by omega)]

theorem witnessColumnRotation_marked (k b delta : ℕ) (hk : 5 ≤ k)
    (x : (witnessDiagram k b delta hk).cells) :
    witnessColumnMarked k (witnessColumnRotation k b delta hk x).val.1 ↔
      x.val.1+x.val.2<k-2 := by
  have hx := witness_cell_column_bound k b delta hk x
  have hr := witness_cell_row_bound k b delta hk (witnessColumnRotation k b delta hk x)
  change (if x.val.1<k-2-x.val.2 then x.val.1+2 else x.val.1-(k-2-x.val.2))<k at hr
  change (2≤(if x.val.1<k-2-x.val.2 then x.val.1+2 else x.val.1-(k-2-x.val.2)) ∧
    (if x.val.1<k-2-x.val.2 then x.val.1+2 else x.val.1-(k-2-x.val.2))<k) ↔ _
  split_ifs <;> omega

theorem witnessColumnRotation_value (k b delta : ℕ) (hk : 5 ≤ k)
    (x : (witnessDiagram k b delta hk).cells) :
    (witnessColumnRotation k b delta hk x).val =
      (if x.val.1<k-2-x.val.2 then x.val.1+2 else x.val.1-(k-2-x.val.2),x.val.2) := rfl

theorem witnessColumnRotation_symm_value (k b delta : ℕ) (hk : 5 ≤ k)
    (x : (witnessDiagram k b delta hk).cells) :
    ((witnessColumnRotation k b delta hk).symm x).val =
      (if x.val.1<2 then x.val.1+(k-2-x.val.2) else x.val.1-2,x.val.2) := rfl

theorem witnessColumnRotation_inverse (k b delta : ℕ) (hk : 5 ≤ k) :
    Function.LeftInverse (witnessColumnUnrotateCell k b delta hk)
      (witnessColumnRotateCell k b delta hk) ∧
    Function.RightInverse (witnessColumnUnrotateCell k b delta hk)
      (witnessColumnRotateCell k b delta hk) :=
  ⟨(witnessColumnRotation k b delta hk).left_inv,
    (witnessColumnRotation k b delta hk).right_inv⟩

theorem witnessColumnRotation_bijective (k b delta : ℕ) (hk : 5 ≤ k) :
    Function.Bijective (witnessColumnRotation k b delta hk) :=
  (witnessColumnRotation k b delta hk).bijective

theorem witnessColumnRotation_empty_core_column (k b delta : ℕ) (hk : 5 ≤ k)
    (x : (witnessDiagram k b delta hk).cells) (hc : k-2≤x.val.2) :
    witnessColumnRotation k b delta hk x=x := by
  have he : k-2-x.val.2=0 := by omega
  apply Subtype.ext
  rw [witnessColumnRotation_value]
  simp only [he,Nat.not_lt_zero,if_false,Nat.sub_zero]

end HSTZ
#print axioms HSTZ.witness_column_core_mem
#print axioms HSTZ.witness_cell_column_bound
#print axioms HSTZ.witness_cell_row_bound
#print axioms HSTZ.witnessColumnRotation
#print axioms HSTZ.witnessColumnRotation_column
#print axioms HSTZ.witnessColumnRotation_core
#print axioms HSTZ.witnessColumnRotation_marked
#print axioms HSTZ.witnessColumnRotation_value
#print axioms HSTZ.witnessColumnRotation_symm_value
#print axioms HSTZ.witnessColumnRotation_inverse
#print axioms HSTZ.witnessColumnRotation_bijective
#print axioms HSTZ.witnessColumnRotation_empty_core_column
