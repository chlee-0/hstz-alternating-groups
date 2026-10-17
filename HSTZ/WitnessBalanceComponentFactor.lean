import HSTZ.WitnessBalanceGlobal
import HSTZ.PositionBlock
import Mathlib.Data.Fintype.EquivFin

/-! Splitting the witness positions into one column component (positions with
label `a`) and all remaining positions, and factoring the polytabloid accordingly.
The remaining factor is kept whole. Local packing support is not addressed here.
Uses `altWord_fiber_split` and `positionTensor` from OpenAI's `math` repository
(commit adc7f1241, Apache-2.0). -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped Classical TensorProduct

section
variable {k b delta n : ℕ} (hk : 5 ≤ k)
    (z : Tableau n (witnessDiagram k b delta hk)) (a : ℕ)

abbrev witnessBalanceComponentSize := Fintype.card {i : Fin n // witnessBalanceLabel hk z i=a}
abbrev witnessBalanceOtherSize := Fintype.card {i : Fin n // witnessBalanceLabel hk z i≠a}

def witnessBalanceComponentCut : Fin n ≃
    Fin (witnessBalanceComponentSize hk z a) ⊕ Fin (witnessBalanceOtherSize hk z a) :=
  (Equiv.sumCompl (fun i : Fin n => witnessBalanceLabel hk z i=a)).symm.trans
    (Equiv.sumCongr (Fintype.equivFin _) (Fintype.equivFin _))

theorem witnessBalanceComponentCut_left (i : Fin (witnessBalanceComponentSize hk z a)) :
    witnessBalanceLabel hk z ((witnessBalanceComponentCut hk z a).symm (.inl i))=a :=
  ((Fintype.equivFin {i : Fin n // witnessBalanceLabel hk z i=a}).symm i).property

theorem witnessBalanceComponentCut_right (i : Fin (witnessBalanceOtherSize hk z a)) :
    witnessBalanceLabel hk z ((witnessBalanceComponentCut hk z a).symm (.inr i))≠a :=
  ((Fintype.equivFin {i : Fin n // witnessBalanceLabel hk z i≠a}).symm i).property

theorem witnessBalanceComponentCut_mask (i : Fin n) :
    (witnessBalanceComponentCut hk z a i).isLeft=true ↔ witnessBalanceLabel hk z i=a := by
  obtain ⟨j,rfl⟩ := (witnessBalanceComponentCut hk z a).symm.surjective i
  cases j with
  | inl j => simp [witnessBalanceComponentCut_left hk z a j]
  | inr j => simp [witnessBalanceComponentCut_right hk z a j]

theorem witnessBalanceComponentCut_card :
    witnessBalanceComponentSize hk z a+witnessBalanceOtherSize hk z a=n := by
  simpa using (Fintype.card_congr (witnessBalanceComponentCut hk z a)).symm

def witnessBalanceComponentWord : WordSpace (witnessBalanceComponentSize hk z a)
    ((witnessDiagram k b delta hk).colLen 0) :=
  altWord (fiberGroup (fun i => (z ((witnessBalanceComponentCut hk z a).symm (.inl i))).val.2))
    (leftWord (witnessBalanceComponentCut hk z a) (rowWord z))

def witnessBalanceOtherWord : WordSpace (witnessBalanceOtherSize hk z a)
    ((witnessDiagram k b delta hk).colLen 0) :=
  altWord (fiberGroup (fun i => (z ((witnessBalanceComponentCut hk z a).symm (.inr i))).val.2))
    (rightWord (witnessBalanceComponentCut hk z a) (rowWord z))

theorem witnessBalance_component_polytabloid : polytabloid z=
    positionProduct (witnessBalanceComponentCut hk z a)
      (witnessBalanceComponentWord hk z a) (witnessBalanceOtherWord hk z a) := by
  have hs : columnGroup z ≤ sectorGroup (fun i => (witnessBalanceComponentCut hk z a i).isLeft=true) := by
    intro g hg i
    change (witnessBalanceComponentCut hk z a (g i)).isLeft=true ↔
      (witnessBalanceComponentCut hk z a i).isLeft=true
    rw [witnessBalanceComponentCut_mask,witnessBalanceComponentCut_mask]
    have he := witnessBalance_column_mem hk z ⟨g,hg⟩ i
    change witnessBalanceLabel hk z (g i)=witnessBalanceLabel hk z i at he
    rw [he]
  rw [polytabloid_eq_altWord,←inf_eq_left.mpr hs]
  exact altWord_fiber_split (witnessBalanceComponentCut hk z a)
    (fun i => (z i).val.2) (rowWord z)

/-- The polytabloid is the position tensor of the component word and the word on
the remaining positions. -/
theorem witnessBalance_component_tensor :
    positionTensor (witnessBalanceComponentCut hk z a)
      (witnessBalanceComponentWord hk z a ⊗ₜ[ℂ] witnessBalanceOtherWord hk z a)=polytabloid z := by
  rw [positionTensor_tmul]
  exact (witnessBalance_component_polytabloid hk z a).symm

end
end
end HSTZ
#print axioms HSTZ.witnessBalanceComponentCut_left
#print axioms HSTZ.witnessBalanceComponentCut_right
#print axioms HSTZ.witnessBalanceComponentCut_mask
#print axioms HSTZ.witnessBalanceComponentCut_card
#print axioms HSTZ.witnessBalance_component_polytabloid
#print axioms HSTZ.witnessBalance_component_tensor
