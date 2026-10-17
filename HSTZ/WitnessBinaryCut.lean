import HSTZ.WitnessFilteredCore

/-! The ordered binary cut of the witness into core and complement. The
three-piece order is kept through the `Fin` sum equivalence. The proof is new and
uses position interfaces adapted from OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
The complement is enumerated in a fixed order, with no shuffle phase. -/
namespace HSTZ
noncomputable section
open OAI.Saxl

abbrev witnessPathSize (k : ℕ) := 2*((k-2)+1)+1
abbrev witnessComplementSize (k b delta : ℕ) :=
  witnessPathSize k + (witnessAttachment b delta).card

def witnessComplementOrder (k b delta : ℕ) :
    Fin (witnessPathSize k) ⊕ Fin (witnessAttachment b delta).card ≃
      Fin (witnessComplementSize k b delta) := finSumFinEquiv

def witnessBinaryCut (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hk)) :
    Fin n ≃ Fin (staircase (k-2)).card ⊕ Fin (witnessComplementSize k b delta) :=
  (witnessCutPositionEquiv k b delta hk t).trans
    (Equiv.sumCongr (Equiv.refl _) (witnessComplementOrder k b delta))

theorem witnessComplementOrder_path_value (k b delta : ℕ)
    (i : Fin (witnessPathSize k)) :
    (witnessComplementOrder k b delta (.inl i)).val=i.val := rfl

theorem witnessComplementOrder_attachment_value (k b delta : ℕ)
    (i : Fin (witnessAttachment b delta).card) :
    (witnessComplementOrder k b delta (.inr i)).val=witnessPathSize k+i.val := rfl

theorem witnessBinaryCut_core (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hk))
    (i : Fin (staircase (k-2)).card) :
    (witnessBinaryCut k b delta hk t).symm (.inl i)=
      (witnessCutPositionEquiv k b delta hk t).symm (.inl i) := rfl

theorem witnessBinaryCut_path (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hk)) (i : Fin (witnessPathSize k)) :
    (witnessBinaryCut k b delta hk t).symm
      (.inr (witnessComplementOrder k b delta (.inl i)))=
      (witnessCutPositionEquiv k b delta hk t).symm (.inr (.inl i)) := by
  simp [witnessBinaryCut,Equiv.symm_trans_apply]

theorem witnessBinaryCut_attachment (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hk))
    (i : Fin (witnessAttachment b delta).card) :
    (witnessBinaryCut k b delta hk t).symm
      (.inr (witnessComplementOrder k b delta (.inr i)))=
      (witnessCutPositionEquiv k b delta hk t).symm (.inr (.inr i)) := by
  simp [witnessBinaryCut,Equiv.symm_trans_apply]

theorem witnessBinaryCut_mask (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hk)) (i : Fin n) :
    (witnessBinaryCut k b delta hk t i).isLeft=true ↔
      i∈Set.range (witnessCorePositionEmbedding k b delta hk t) := by
  have hcore (j : Fin (staircase (k-2)).card) :
      (witnessBinaryCut k b delta hk t).symm (.inl j)=
        witnessCorePositionEmbedding k b delta hk t j := witnessBinaryCut_core k b delta hk t j
  constructor
  · intro hi
    obtain ⟨p,rfl⟩ := (witnessBinaryCut k b delta hk t).symm.surjective i
    cases p with
    | inl j => exact ⟨j,(hcore j).symm⟩
    | inr j => simp at hi
  · rintro ⟨j,rfl⟩
    rw [← hcore]
    simp

theorem witnessBinaryCut_card (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hk)) :
    (staircase (k-2)).card+witnessComplementSize k b delta=n := by
  have he := Fintype.card_congr (witnessBinaryCut k b delta hk t)
  simpa using he.symm

theorem witnessBinaryCut_inverse (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hk)) :
    Function.LeftInverse (witnessBinaryCut k b delta hk t).symm (witnessBinaryCut k b delta hk t) ∧
    Function.RightInverse (witnessBinaryCut k b delta hk t).symm (witnessBinaryCut k b delta hk t) :=
  ⟨(witnessBinaryCut k b delta hk t).left_inv,(witnessBinaryCut k b delta hk t).right_inv⟩

theorem witnessBinaryCut_bijective (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hk)) :
    Function.Bijective (witnessBinaryCut k b delta hk t) := (witnessBinaryCut k b delta hk t).bijective

end
end HSTZ
#print axioms HSTZ.witnessComplementOrder_path_value
#print axioms HSTZ.witnessComplementOrder_attachment_value
#print axioms HSTZ.witnessBinaryCut_core
#print axioms HSTZ.witnessBinaryCut_path
#print axioms HSTZ.witnessBinaryCut_attachment
#print axioms HSTZ.witnessBinaryCut_mask
#print axioms HSTZ.witnessBinaryCut_card
#print axioms HSTZ.witnessBinaryCut_inverse
#print axioms HSTZ.witnessBinaryCut_bijective
