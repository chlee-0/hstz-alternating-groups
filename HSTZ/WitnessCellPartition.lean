import HSTZ.WitnessCutCells
import HSTZ.WitnessPathPositions

/-! Partition of the witness cells into three pieces: core, path and attachment.
This file is purely geometric. -/
namespace HSTZ
open OAI.Saxl

theorem witnessCore_path_disjoint (k b delta : ℕ) (hk : 5 ≤ k)
    (x : (staircase (k-2)).cells) (y : WitnessNativeBandCells k) :
    witnessCoreCell k b delta hk x ≠ witnessPathCell k b delta hk y := by
  intro he
  have hx : x.val.1+x.val.2<k-2 := mem_staircase.mp x.property
  have hy := y.property
  have he' := congrArg (fun z : (witnessDiagram k b delta hk).cells => z.val) he
  change x.val = (y.val.1, if y.val.2=k-1 then k+b+delta-1 else y.val.2) at he'
  have hr := congrArg (fun z : ℕ × ℕ => z.1) he'
  have hc := congrArg (fun z : ℕ × ℕ => z.2) he'
  dsimp at hr hc
  split_ifs at hc <;> omega

theorem witnessCore_attachment_disjoint (k b delta : ℕ) (hk : 5 ≤ k)
    (x : (staircase (k-2)).cells) (y : (witnessAttachment b delta).cells) :
    witnessCoreCell k b delta hk x ≠ witnessAttachmentCell k b delta hk y := by
  intro he
  have hx : x.val.1+x.val.2<k-2 := mem_staircase.mp x.property
  have he' := congrArg (fun z : (witnessDiagram k b delta hk).cells => z.val.2) he
  change x.val.2=k-1+y.val.2 at he'
  omega

theorem witnessPath_attachment_disjoint (k b delta : ℕ) (hk : 5 ≤ k)
    (x : WitnessNativeBandCells k) (y : (witnessAttachment b delta).cells) :
    witnessPathCell k b delta hk x ≠ witnessAttachmentCell k b delta hk y := by
  intro he
  have hx := witnessNativeBandCell_bounds k hk x
  have hy := (mem_witnessAttachment b delta y.val.1 y.val.2).mp y.property
  have he' := congrArg (fun z : (witnessDiagram k b delta hk).cells => z.val) he
  change (x.val.1, if x.val.2=k-1 then k+b+delta-1 else x.val.2) =
    (y.val.1,k-1+y.val.2) at he'
  have hr := congrArg (fun z : ℕ × ℕ => z.1) he'
  have hc := congrArg (fun z : ℕ × ℕ => z.2) he'
  dsimp at hr hc
  rcases hy with ⟨hy,hc'⟩ | ⟨hy,hc'⟩ <;> split_ifs at hc <;> omega

theorem witnessCell_coverage (k b delta : ℕ) (hk : 5 ≤ k)
    (z : (witnessDiagram k b delta hk).cells) :
    (∃ x, witnessCoreCell k b delta hk x=z) ∨
    (∃ x, witnessPathCell k b delta hk x=z) ∨
    (∃ x, witnessAttachmentCell k b delta hk x=z) := by
  rcases z with ⟨⟨i,c⟩,hz⟩
  have hz' : c<witnessRow k b delta i := by
    simpa only [witnessDiagram_row_length] using YoungDiagram.mem_iff_lt_rowLen.mp hz
  by_cases hcore : i+c<k-2
  · left
    exact ⟨⟨(i,c),mem_staircase.mpr hcore⟩,rfl⟩
  · by_cases hcol : c<k-1
    · right; left
      have hh : i+c<k := by unfold witnessRow at hz'; split_ifs at hz' <;> omega
      let x : WitnessNativeBandCells k := ⟨(i,c),by constructor <;> omega⟩
      refine ⟨x,Subtype.ext ?_⟩
      change (i, if c=k-1 then k+b+delta-1 else c)=(i,c)
      rw [if_neg (by omega)]
    · by_cases hend : i=0 ∧ c=k+b+delta-1
      · right; left
        refine ⟨witnessNativeBandEndpoint k hk,Subtype.ext ?_⟩
        rw [witnessPathCell_endpoint]
        rcases hend with ⟨rfl,rfl⟩
        rfl
      · right; right
        have ha : (i,c-(k-1)) ∈ witnessAttachment b delta := by
          rw [mem_witnessAttachment]
          unfold witnessRow at hz'
          split_ifs at hz' <;> omega
        refine ⟨⟨(i,c-(k-1)),ha⟩,Subtype.ext ?_⟩
        change (i,k-1+(c-(k-1)))=(i,c)
        congr 1
        omega

abbrev WitnessCutCells (k b delta : ℕ) :=
  (staircase (k-2)).cells ⊕ (WitnessNativeBandCells k ⊕ (witnessAttachment b delta).cells)

def witnessCutCellMap (k b delta : ℕ) (hk : 5 ≤ k) :
    WitnessCutCells k b delta → (witnessDiagram k b delta hk).cells
  | .inl x => witnessCoreCell k b delta hk x
  | .inr (.inl x) => witnessPathCell k b delta hk x
  | .inr (.inr x) => witnessAttachmentCell k b delta hk x

theorem witnessCutCellMap_bijective (k b delta : ℕ) (hk : 5 ≤ k) :
    Function.Bijective (witnessCutCellMap k b delta hk) := by
  constructor
  · intro x y he
    rcases x with x | (x | x) <;> rcases y with y | (y | y)
    · exact congrArg Sum.inl (witnessCoreCell_injective k b delta hk he)
    · exact False.elim (witnessCore_path_disjoint k b delta hk x y he)
    · exact False.elim (witnessCore_attachment_disjoint k b delta hk x y he)
    · exact False.elim (witnessCore_path_disjoint k b delta hk y x he.symm)
    · exact congrArg (fun z => Sum.inr (Sum.inl z)) (witnessPathCell_injective k b delta hk he)
    · exact False.elim (witnessPath_attachment_disjoint k b delta hk x y he)
    · exact False.elim (witnessCore_attachment_disjoint k b delta hk y x he.symm)
    · exact False.elim (witnessPath_attachment_disjoint k b delta hk y x he.symm)
    · exact congrArg (fun z => Sum.inr (Sum.inr z)) (witnessAttachmentCell_injective k b delta hk he)
  · intro z
    rcases witnessCell_coverage k b delta hk z with ⟨x,hx⟩ | ⟨x,hx⟩ | ⟨x,hx⟩
    · exact ⟨.inl x,hx⟩
    · exact ⟨.inr (.inl x),hx⟩
    · exact ⟨.inr (.inr x),hx⟩

noncomputable def witnessCutCellEquiv (k b delta : ℕ) (hk : 5 ≤ k) :
    WitnessCutCells k b delta ≃ (witnessDiagram k b delta hk).cells :=
  Equiv.ofBijective (witnessCutCellMap k b delta hk) (witnessCutCellMap_bijective k b delta hk)

end HSTZ
#print axioms HSTZ.witnessCore_path_disjoint
#print axioms HSTZ.witnessCore_attachment_disjoint
#print axioms HSTZ.witnessPath_attachment_disjoint
#print axioms HSTZ.witnessCell_coverage
#print axioms HSTZ.witnessCutCellMap_bijective
