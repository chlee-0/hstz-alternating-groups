import HSTZ.WitnessAttachmentWords
import HSTZ.BalanceProjectedCoordinate
import HSTZ.FourRowSupport

/-! Neighboring-column positions in the witness attachment. Adapts
`UniversalSquare/Support/Neighboring` from OpenAI's `math` repository (commit adc7f1241, Apache-2.0),
using the `witnessAttachment` cells. -/
namespace HSTZ
noncomputable section
open OAI.Saxl

def balanceNeighborColumn (r : ℕ) (i : Fin (2*r+1)) : ℕ :=
  if i.val=0 then r else r-1-(i.val-1)/2

def balanceNeighborLayer (r : ℕ) : Tableau (2*r+1) (witnessAttachment r 1) where
  toFun i := ⟨((PathLayer.base i).val,balanceNeighborColumn r i), by
    apply (mem_witnessAttachment r 1 _ _).mpr
    have hi := i.isLt
    by_cases hz : i.val=0
    · simp [PathLayer.base,balanceNeighborColumn,hz]
    · simp only [PathLayer.base,balanceNeighborColumn,if_neg hz,Fin.val_mk]
      omega⟩
  invFun c := ⟨if c.val.2=r then 0 else 1+2*(r-1-c.val.2)+c.val.1, by
    rcases c with ⟨⟨a,b⟩,hc⟩
    have hc := (mem_witnessAttachment r 1 a b).mp hc
    change (if b=r then 0 else 1+2*(r-1-b)+a)<2*r+1
    split_ifs <;> omega⟩
  left_inv i := by
    apply Fin.ext
    have hi := i.isLt
    change (if balanceNeighborColumn r i=r then 0 else
      1+2*(r-1-balanceNeighborColumn r i)+(PathLayer.base i).val)=i.val
    by_cases hz : i.val=0
    · simp [balanceNeighborColumn,hz]
    · simp only [balanceNeighborColumn,PathLayer.base,if_neg hz,Fin.val_mk]
      split_ifs <;> omega
  right_inv c := by
    rcases c with ⟨⟨a,b⟩,hc⟩
    have hc := (mem_witnessAttachment r 1 a b).mp hc
    apply Subtype.ext
    apply Prod.ext
    · change (PathLayer.base (⟨if b=r then 0 else 1+2*(r-1-b)+a, _⟩ : Fin (2*r+1))).val=a
      by_cases hb : b=r
      · have ha : a=0 := by omega
        simp [hb,ha,PathLayer.base]
      · have hn : 1+2*(r-1-b)+a≠0 := by omega
        simp only [PathLayer.base,if_neg hb,Fin.val_mk,if_neg hn]
        omega
    · change balanceNeighborColumn r (⟨if b=r then 0 else 1+2*(r-1-b)+a, _⟩ : Fin (2*r+1))=b
      simp only [balanceNeighborColumn,Fin.val_mk]
      split_ifs <;> omega

theorem balanceNeighborLayer_row (r : ℕ) (i : Fin (2*r+1)) :
    (balanceNeighborLayer r i).val.1=(PathLayer.base i).val := rfl

theorem balanceNeighborLayer_col (r : ℕ) (i : Fin (2*r+1)) :
    (balanceNeighborLayer r i).val.2=if i.val=0 then r else r-1-(i.val-1)/2 := rfl

theorem balanceNeighborLayer_col_iff (r : ℕ) (i j : Fin (2*r+1)) :
    (balanceNeighborLayer r i).val.2=(balanceNeighborLayer r j).val.2 ↔
      PathLayer.tag i=PathLayer.tag j := by
  have hi := i.isLt
  have hj := j.isLt
  rw [balanceNeighborLayer_col,balanceNeighborLayer_col]
  simp only [PathLayer.tag]
  split_ifs <;> omega

theorem balanceNeighborLayer_group (r : ℕ) :
    columnGroup (balanceNeighborLayer r)=fiberGroup (@PathLayer.tag r) := by
  apply Subgroup.ext
  intro g
  change (∀ i, _=_) ↔ (∀ i, _=_)
  simp only [balanceNeighborLayer_col_iff]

/-- Explicit change of enumeration to the canonical attachment carrier. -/
def balanceNeighborCanonicalPositions (r : ℕ) :
    Fin (2*r+1) ≃ Fin (witnessAttachment r 1).card :=
  (balanceNeighborLayer r).trans (witnessCanonicalAttachment r 1).symm

theorem balanceNeighborCanonicalPositions_cell (r : ℕ) (i : Fin (2*r+1)) :
    witnessCanonicalAttachment r 1 (balanceNeighborCanonicalPositions r i)=
      balanceNeighborLayer r i := by
  exact (witnessCanonicalAttachment r 1).apply_symm_apply _

theorem balanceNeighborCanonicalPositions_inverse (r : ℕ)
    (i : Fin (witnessAttachment r 1).card) :
    balanceNeighborLayer r ((balanceNeighborCanonicalPositions r).symm i)=
      witnessCanonicalAttachment r 1 i := by
  exact (balanceNeighborLayer r).apply_symm_apply _

def balanceNeighborTableau (r : ℕ) :
    Tableau (2*r+1) (witnessAttachment r 1).transpose :=
  transposeTableau (balanceNeighborLayer r)

def balanceNeighborRight (r : ℕ) :
    Tableau (2*r+1) (witnessAttachment r 1).transpose :=
  Fin.revPerm.trans (balanceNeighborTableau r)

def balancePairOutput {d e : ℕ} (a : Fin (d*e)) : ℕ :=
  ((finProdFinEquiv : Fin d × Fin e ≃ Fin (d*e)).symm a).1.val+
  ((finProdFinEquiv : Fin d × Fin e ≃ Fin (d*e)).symm a).2.val+1

def balanceInOutputs {n d e : ℕ} (I : Set ℕ) (w : Fin n → Fin (d*e)) : Prop :=
  ∀ i, balancePairOutput (w i) ∈ I

theorem balanceInOutputs_invariant {n d e : ℕ} (I : Set ℕ)
    (g : Equiv.Perm (Fin n)) (w : Fin n → Fin (d*e)) :
    balanceInOutputs I (w ∘ g) ↔ balanceInOutputs I w := by
  constructor
  · intro h i
    simpa only [Function.comp_apply,Equiv.apply_symm_apply] using h (g.symm i)
  · intro h i
    exact h (g i)

theorem balanceNeighbor_outputs (r : ℕ) :
    balanceInOutputs (Set.Icc r (r+1))
      (mergeWords (rowWord (balanceNeighborTableau r))
        (rowWord (balanceNeighborRight r))) := by
  intro i
  simp only [balancePairOutput,mergeWords,Equiv.symm_apply_apply]
  change (balanceNeighborLayer r i).val.2+
    (balanceNeighborLayer r i.rev).val.2+1 ∈ Set.Icc r (r+1)
  rw [balanceNeighborLayer_col,balanceNeighborLayer_col]
  simp only [Set.mem_Icc,Fin.val_rev]
  have hi := i.isLt
  split_ifs <;> omega

end
end HSTZ
#print axioms HSTZ.balanceNeighborLayer
#print axioms HSTZ.balanceNeighborLayer_row
#print axioms HSTZ.balanceNeighborLayer_col
#print axioms HSTZ.balanceNeighborLayer_col_iff
#print axioms HSTZ.balanceNeighborLayer_group
#print axioms HSTZ.balanceInOutputs_invariant
#print axioms HSTZ.balanceNeighbor_outputs

#print axioms HSTZ.balanceNeighborCanonicalPositions_cell
#print axioms HSTZ.balanceNeighborCanonicalPositions_inverse
