import HSTZ.WitnessCellPartition

/-! Ordered core, path and attachment positions in any tableau of the witness
shape. The path positions use the native path order. -/
namespace HSTZ
open OAI.Saxl

theorem witnessAttachment_rows (b delta : ℕ) :
    (witnessAttachment b delta).colLen 0 ≤ 2 := by
  by_contra hn
  have hh : (2,0) ∈ witnessAttachment b delta :=
    YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
  simp [mem_witnessAttachment] at hh

theorem witnessAttachment_card (b delta : ℕ) :
    (witnessAttachment b delta).card=2*b+delta := by
  have h0 : (witnessAttachment b delta).rowLen 0=b+delta :=
    YoungDiagram.rowLen_ofRowLens (w := [b+delta,b]) (hw := by rw [List.sortedGE_iff_pairwise]; simp) ⟨0,by simp⟩
  have h1 : (witnessAttachment b delta).rowLen 1=b :=
    YoungDiagram.rowLen_ofRowLens (w := [b+delta,b]) (hw := by rw [List.sortedGE_iff_pairwise]; simp) ⟨1,by simp⟩
  have hh := row_prefix_full (witnessAttachment b delta) (witnessAttachment_rows b delta)
  simp only [prefix_succ,prefix_zero,h0,h1] at hh
  omega

theorem witnessAttachment_zero : witnessAttachment 0 0 = ⊥ := by
  ext ⟨i,c⟩
  simp [mem_witnessAttachment]

abbrev WitnessCutPositions (k b delta : ℕ) :=
  Fin (staircase (k-2)).card ⊕
    (Fin (2*((k-2)+1)+1) ⊕ Fin (witnessAttachment b delta).card)

noncomputable def witnessCutOrderedCells (k b delta : ℕ) (hk : 5 ≤ k) :
    WitnessCutPositions k b delta ≃ (witnessDiagram k b delta hk).cells :=
  (Equiv.sumCongr (canonicalTableau (staircase (k-2)) rfl)
    (Equiv.sumCongr (pathCellsEquiv (k-2))
      (canonicalTableau (witnessAttachment b delta) rfl))).trans
        (witnessCutCellEquiv k b delta hk)

noncomputable def witnessCutPositionEquiv (k b delta : ℕ) (hk : 5 ≤ k)
    {n : ℕ} (t : Tableau n (witnessDiagram k b delta hk)) :
    Fin n ≃ WitnessCutPositions k b delta :=
  t.trans (witnessCutOrderedCells k b delta hk).symm

theorem witnessCutPosition_core (k b delta : ℕ) (hk : 5 ≤ k)
    {n : ℕ} (t : Tableau n (witnessDiagram k b delta hk))
    (i : Fin (staircase (k-2)).card) :
    t ((witnessCutPositionEquiv k b delta hk t).symm (.inl i)) =
      witnessCoreCell k b delta hk (canonicalTableau (staircase (k-2)) rfl i) := by
  simp only [witnessCutPositionEquiv,Equiv.symm_trans_apply,Equiv.apply_symm_apply]
  rfl

theorem witnessCutPosition_path (k b delta : ℕ) (hk : 5 ≤ k)
    {n : ℕ} (t : Tableau n (witnessDiagram k b delta hk))
    (i : Fin (2*((k-2)+1)+1)) :
    t ((witnessCutPositionEquiv k b delta hk t).symm (.inr (.inl i))) =
      witnessPathPositionCell k b delta hk i := by
  simp only [witnessCutPositionEquiv,Equiv.symm_trans_apply,Equiv.apply_symm_apply]
  rfl

theorem witnessCutPosition_attachment (k b delta : ℕ) (hk : 5 ≤ k)
    {n : ℕ} (t : Tableau n (witnessDiagram k b delta hk))
    (i : Fin (witnessAttachment b delta).card) :
    t ((witnessCutPositionEquiv k b delta hk t).symm (.inr (.inr i))) =
      witnessAttachmentCell k b delta hk (canonicalTableau (witnessAttachment b delta) rfl i) := by
  simp only [witnessCutPositionEquiv,Equiv.symm_trans_apply,Equiv.apply_symm_apply]
  rfl

theorem witnessCutPosition_bijective (k b delta : ℕ) (hk : 5 ≤ k)
    {n : ℕ} (t : Tableau n (witnessDiagram k b delta hk)) :
    Function.Bijective (witnessCutPositionEquiv k b delta hk t) :=
  (witnessCutPositionEquiv k b delta hk t).bijective

theorem witnessCutPosition_left_inverse (k b delta : ℕ) (hk : 5 ≤ k)
    {n : ℕ} (t : Tableau n (witnessDiagram k b delta hk)) :
    Function.LeftInverse (witnessCutPositionEquiv k b delta hk t).symm
      (witnessCutPositionEquiv k b delta hk t) :=
  (witnessCutPositionEquiv k b delta hk t).left_inv

theorem witnessCutPosition_right_inverse (k b delta : ℕ) (hk : 5 ≤ k)
    {n : ℕ} (t : Tableau n (witnessDiagram k b delta hk)) :
    Function.RightInverse (witnessCutPositionEquiv k b delta hk t).symm
      (witnessCutPositionEquiv k b delta hk t) :=
  (witnessCutPositionEquiv k b delta hk t).right_inv

end HSTZ
#print axioms HSTZ.witnessAttachment_rows
#print axioms HSTZ.witnessAttachment_card
#print axioms HSTZ.witnessCutPosition_core
#print axioms HSTZ.witnessCutPosition_path
#print axioms HSTZ.witnessCutPosition_attachment
#print axioms HSTZ.witnessCutPosition_bijective

#print axioms HSTZ.witnessAttachment_zero
#print axioms HSTZ.witnessCutPosition_left_inverse
#print axioms HSTZ.witnessCutPosition_right_inverse
