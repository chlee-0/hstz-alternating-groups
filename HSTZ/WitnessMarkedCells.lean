import HSTZ.WitnessMarkedCounts
import HSTZ.WitnessCutCells

/-! Marked-cell carriers and coordinate-preserving equivalences. These
maps do not infer a common mask from polytabloid coefficients. The masks use the
staircase geometry of OpenAI's `math` repository (Apache-2.0). -/
namespace HSTZ
open OAI.Saxl

abbrev WitnessRowMarkedCells (k b delta : ℕ) (hk : 5 ≤ k) :=
  {x : (witnessDiagram k b delta hk).cells // witnessRowMarked k b x.val.2}
abbrev WitnessColumnMarkedCells (k b delta : ℕ) (hk : 5 ≤ k) :=
  {x : (witnessDiagram k b delta hk).cells // witnessColumnMarked k x.val.1}

def witnessRowMarkedCell (k b delta : ℕ) (hk : 5 ≤ k)
    (x : (staircase (k-2)).cells) : WitnessRowMarkedCells k b delta hk := by
  have hx : x.val.1+x.val.2<k-2 := mem_staircase.mp x.property
  let i : Fin (k-2) := ⟨x.val.2,by omega⟩
  let a := witnessMarkedRowLetter k b delta hk i
  refine ⟨⟨(x.val.1,a.val),?_⟩,?_⟩
  · apply YoungDiagram.mem_iff_lt_rowLen.mpr
    exact (witnessMarkedRowLetter_in_row k b delta hk x.val.1 i).mpr (by change x.val.2<k-2-x.val.1; omega)
  · exact (witnessMarkedRowLetter_range k b delta hk a).mp ⟨i,rfl⟩

def witnessColumnMarkedCell (k b delta : ℕ) (hk : 5 ≤ k)
    (x : (staircase (k-2)).cells) : WitnessColumnMarkedCells k b delta hk := by
  have hx : x.val.1+x.val.2<k-2 := mem_staircase.mp x.property
  let i : Fin (k-2) := ⟨x.val.1,by omega⟩
  refine ⟨⟨(x.val.1+2,x.val.2),?_⟩,?_⟩
  · apply YoungDiagram.mem_iff_lt_colLen.mpr
    exact (witnessMarkedColumnLetter_in_column k b delta hk x.val.2 i).mpr (by change x.val.1<k-2-x.val.2; omega)
  · change 2≤x.val.1+2 ∧ x.val.1+2<k
    omega

theorem witnessRowMarkedCell_bijective (k b delta : ℕ) (hk : 5 ≤ k) :
    Function.Bijective (witnessRowMarkedCell k b delta hk) := by
  constructor
  · intro x y he
    have hr := congrArg (fun z : WitnessRowMarkedCells k b delta hk => z.val.val.1) he
    have hc := congrArg (fun z : WitnessRowMarkedCells k b delta hk => z.val.val.2) he
    change x.val.1=y.val.1 at hr
    have hx : x.val.1+x.val.2<k-2 := mem_staircase.mp x.property
    have hy : y.val.1+y.val.2<k-2 := mem_staircase.mp y.property
    have hi : (⟨x.val.2,by omega⟩ : Fin (k-2))=⟨y.val.2,by omega⟩ :=
      witnessMarkedRowLetter_injective k b delta hk (Fin.ext hc)
    exact Subtype.ext (Prod.ext hr (congrArg Fin.val hi))
  · intro y
    have hy : y.val.val.2 < (witnessDiagram k b delta hk).rowLen y.val.val.1 :=
      YoungDiagram.mem_iff_lt_rowLen.mp y.val.property
    have hbound : y.val.val.2<k+b+delta := by
      rw [witnessDiagram_row_length] at hy
      unfold witnessRow at hy
      split_ifs at hy <;> omega
    let a : Fin (k+b+delta) := ⟨y.val.val.2,hbound⟩
    obtain ⟨i,hi⟩ := (witnessMarkedRowLetter_range k b delta hk a).mpr y.property
    have hv : (witnessMarkedRowLetter k b delta hk i).val=y.val.val.2 := congrArg Fin.val hi
    have hsmall : i.val<k-2-y.val.val.1 :=
      (witnessMarkedRowLetter_in_row k b delta hk y.val.val.1 i).mp (by rw [hv];exact hy)
    let x : (staircase (k-2)).cells := ⟨(y.val.val.1,i.val),mem_staircase.mpr (by omega)⟩
    refine ⟨x,Subtype.ext (Subtype.ext (Prod.ext rfl ?_))⟩
    exact hv

theorem witnessColumnMarkedCell_bijective (k b delta : ℕ) (hk : 5 ≤ k) :
    Function.Bijective (witnessColumnMarkedCell k b delta hk) := by
  constructor
  · intro x y he
    have hr := congrArg (fun z : WitnessColumnMarkedCells k b delta hk => z.val.val.1) he
    have hc := congrArg (fun z : WitnessColumnMarkedCells k b delta hk => z.val.val.2) he
    change x.val.1+2=y.val.1+2 at hr
    change x.val.2=y.val.2 at hc
    exact Subtype.ext (Prod.ext (by omega) hc)
  · intro y
    have hm : 2≤y.val.val.1 ∧ y.val.val.1<k := y.property
    have hy : y.val.val.1 < (witnessDiagram k b delta hk).colLen y.val.val.2 :=
      YoungDiagram.mem_iff_lt_colLen.mp y.val.property
    let i : Fin (k-2) := ⟨y.val.val.1-2,by omega⟩
    have hv : (witnessMarkedColumnLetter k hk i).val=y.val.val.1 := by
      change y.val.val.1-2+2=y.val.val.1
      omega
    have hsmall : i.val<k-2-y.val.val.2 :=
      (witnessMarkedColumnLetter_in_column k b delta hk y.val.val.2 i).mp (by rw [hv];exact hy)
    let x : (staircase (k-2)).cells := ⟨(i.val,y.val.val.2),mem_staircase.mpr (by omega)⟩
    refine ⟨x,Subtype.ext (Subtype.ext (Prod.ext ?_ rfl))⟩
    exact hv

noncomputable def witnessMarkedRowEquiv (k b delta : ℕ) (hk : 5 ≤ k) :
    WitnessRowMarkedCells k b delta hk ≃ (staircase (k-2)).cells :=
  (Equiv.ofBijective _ (witnessRowMarkedCell_bijective k b delta hk)).symm
noncomputable def witnessMarkedColumnEquiv (k b delta : ℕ) (hk : 5 ≤ k) :
    WitnessColumnMarkedCells k b delta hk ≃ (staircase (k-2)).cells :=
  (Equiv.ofBijective _ (witnessColumnMarkedCell_bijective k b delta hk)).symm

theorem witnessMarkedRowEquiv_row (k b delta : ℕ) (hk : 5 ≤ k)
    (x : WitnessRowMarkedCells k b delta hk) :
    (witnessMarkedRowEquiv k b delta hk x).val.1=x.val.val.1 := by
  have he := (witnessMarkedRowEquiv k b delta hk).symm_apply_apply x
  exact congrArg (fun z : WitnessRowMarkedCells k b delta hk => z.val.val.1) he

theorem witnessMarkedColumnEquiv_column (k b delta : ℕ) (hk : 5 ≤ k)
    (x : WitnessColumnMarkedCells k b delta hk) :
    (witnessMarkedColumnEquiv k b delta hk x).val.2=x.val.val.2 := by
  have he := (witnessMarkedColumnEquiv k b delta hk).symm_apply_apply x
  exact congrArg (fun z : WitnessColumnMarkedCells k b delta hk => z.val.val.2) he

theorem witnessMarkedRowEquiv_symm_value (k b delta : ℕ) (hk : 5 ≤ k)
    (x : (staircase (k-2)).cells) :
    ((witnessMarkedRowEquiv k b delta hk).symm x).val.val =
      (x.val.1,(witnessMarkedRowLetter k b delta hk
        ⟨x.val.2,by have hx : x.val.1+x.val.2<k-2 := mem_staircase.mp x.property; omega⟩).val) := rfl

theorem witnessMarkedColumnEquiv_symm_value (k b delta : ℕ) (hk : 5 ≤ k)
    (x : (staircase (k-2)).cells) :
    ((witnessMarkedColumnEquiv k b delta hk).symm x).val.val =
      (x.val.1+2,x.val.2) := rfl

theorem witnessMarkedRowEquiv_inverse (k b delta : ℕ) (hk : 5 ≤ k) :
    Function.LeftInverse (witnessMarkedRowEquiv k b delta hk)
      (witnessRowMarkedCell k b delta hk) ∧
    Function.RightInverse (witnessMarkedRowEquiv k b delta hk)
      (witnessRowMarkedCell k b delta hk) :=
  ⟨(witnessMarkedRowEquiv k b delta hk).apply_symm_apply,
    (witnessMarkedRowEquiv k b delta hk).symm_apply_apply⟩

theorem witnessMarkedColumnEquiv_inverse (k b delta : ℕ) (hk : 5 ≤ k) :
    Function.LeftInverse (witnessMarkedColumnEquiv k b delta hk)
      (witnessColumnMarkedCell k b delta hk) ∧
    Function.RightInverse (witnessMarkedColumnEquiv k b delta hk)
      (witnessColumnMarkedCell k b delta hk) :=
  ⟨(witnessMarkedColumnEquiv k b delta hk).apply_symm_apply,
    (witnessMarkedColumnEquiv k b delta hk).symm_apply_apply⟩

end HSTZ
#print axioms HSTZ.witnessRowMarkedCell_bijective
#print axioms HSTZ.witnessColumnMarkedCell_bijective
#print axioms HSTZ.witnessMarkedRowEquiv
#print axioms HSTZ.witnessMarkedColumnEquiv
#print axioms HSTZ.witnessMarkedRowEquiv_row
#print axioms HSTZ.witnessMarkedColumnEquiv_column
#print axioms HSTZ.witnessMarkedRowEquiv_symm_value
#print axioms HSTZ.witnessMarkedColumnEquiv_symm_value
#print axioms HSTZ.witnessMarkedRowEquiv_inverse
#print axioms HSTZ.witnessMarkedColumnEquiv_inverse
