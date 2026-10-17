import HSTZ.ContainedFactorLetters

/-! Placement freedom for the attachment alone, as needed by the dual test for
the contained witness. Reuses the geometry and `tableauMove`/`polytabloid_move` from
OpenAI's `math` repository (commit adc7f1241, Apache-2.0). No fixed coefficient and no converse of the
dual test is asserted.
-/
namespace HSTZ
noncomputable section
open OAI.Saxl
section
variable {h e : ℕ → ℕ} (hh : Antitone h) (he : Antitone e)
    {d K m t n : ℕ} (htm : t ≤ m) (hroom : ∀ c < t, d+e c≤h c)
    (hclear : t*d+4≤K) (hcapacity : K≤prefixSum (capacity h d) m)
    (s : Tableau n (containedWhole h e hh he d K m))
local notation "Q" => containedFactorPositions hh he htm hroom hclear hcapacity s
local notation "A" => canonicalTableau (containedAttachment e he m) rfl
variable (sigma : Equiv.Perm (Fin (containedAttachment e he m).card))

/-- An attachment tableau; the source remains in its original order. -/
def containedAttachmentPlacedTableau :
    Tableau (containedAttachment e he m).card (containedAttachment e he m) :=
  sigma.trans A

/-- The target position equivalence that moves only attachment slots. -/
def containedAttachmentPlacedPositions :
    (Fin K ⊕ Fin (containedAttachment e he m).card) ≃ Fin n :=
  (Equiv.sumCongr (Equiv.refl _) sigma).trans (Q)

theorem containedAttachmentPlacedPositions_path (i : Fin K) :
    containedAttachmentPlacedPositions hh he htm hroom hclear hcapacity s sigma (.inl i)=
      (Q) (.inl i) := rfl

theorem containedAttachmentPlacedPositions_attachment
    (i : Fin (containedAttachment e he m).card) :
    containedAttachmentPlacedPositions hh he htm hroom hclear hcapacity s sigma (.inr i)=
      (Q) (.inr (sigma i)) := rfl

theorem containedAttachmentPlacedPositions_inverse_path (i : Fin K) :
    (containedAttachmentPlacedPositions hh he htm hroom hclear hcapacity s sigma).symm
      ((Q) (.inl i))=.inl i := by
  rw [← containedAttachmentPlacedPositions_path hh he htm hroom hclear hcapacity s sigma i]
  exact Equiv.symm_apply_apply _ _

theorem containedAttachmentPlacedPositions_inverse_attachment
    (i : Fin (containedAttachment e he m).card) :
    (containedAttachmentPlacedPositions hh he htm hroom hclear hcapacity s sigma).symm
      ((Q) (.inr i))=.inr (sigma.symm i) := by
  have hv := containedAttachmentPlacedPositions_attachment
    hh he htm hroom hclear hcapacity s sigma (sigma.symm i)
  rw [sigma.apply_symm_apply] at hv
  rw [← hv]
  exact Equiv.symm_apply_apply _ _

/-- Each attachment position lies at its attachment cell translated by `d` in
the row coordinate. -/
theorem containedAttachmentPlacedPositions_cell (hzero : ∀ c, t ≤ c → e c=0)
    (i : Fin (containedAttachment e he m).card) :
    (s (containedAttachmentPlacedPositions hh he htm hroom hclear hcapacity s sigma
      (.inr i))).val=(d+(A (sigma i)).val.1,(A (sigma i)).val.2) := by
  rw [containedAttachmentPlacedPositions_attachment]
  exact containedFactorPositions_attachment_reserved hh he htm hroom hclear hcapacity s
    (sigma i) (containedAttachment_col_lt he m t hzero (A (sigma i)))

/-- The row flag of the full tableau is preserved, including for an empty
attachment. -/
theorem containedAttachmentPlacedPositions_flag (hzero : ∀ c, t ≤ c → e c=0)
    (j : Fin K ⊕ Fin (containedAttachment e he m).card) :
    (rowWord s (containedAttachmentPlacedPositions hh he htm hroom hclear hcapacity s sigma j)).val<d
      ↔ j.isLeft=true := by
  cases j with
  | inl i =>
    simpa only [containedAttachmentPlacedPositions_path,Sum.isLeft_inl,Bool.true_eq,iff_true]
      using containedFactorPositions_path_flag hh he htm hroom hclear hcapacity s i
  | inr i =>
    simpa only [containedAttachmentPlacedPositions_attachment,Sum.isLeft_inr,
      Bool.false_eq_true,iff_false] using
      (not_lt.mpr (containedFactorPositions_attachment_flag hh he htm hroom hclear hcapacity s hzero (sigma i)))

theorem containedAttachmentPlaced_rowWord (hzero : ∀ c, t ≤ c → e c=0) :
    rightWord (containedAttachmentPlacedPositions hh he htm hroom hclear hcapacity s sigma).symm
      (rowWord s)=containedAttachmentRowLetter hh he hroom hclear hzero ∘
        rowWord (containedAttachmentPlacedTableau he sigma) := by
  funext i
  apply Fin.ext
  change (s (containedAttachmentPlacedPositions hh he htm hroom hclear hcapacity s sigma (.inr i))).val.1=
    d+(A (sigma i)).val.1
  rw [containedAttachmentPlacedPositions_cell hh he htm hroom hclear hcapacity s sigma hzero]

theorem containedAttachmentPlaced_path_rowWord :
    leftWord (containedAttachmentPlacedPositions hh he htm hroom hclear hcapacity s sigma).symm
      (rowWord s)=leftWord (Q).symm (rowWord s) := rfl

/-- The moved prescribed polytabloid, with the inverse direction explicit. -/
theorem containedAttachmentPlaced_polytabloid_move :
    polytabloid (containedAttachmentPlacedTableau he sigma)=
      wordRep _ _ sigma.symm (polytabloid A) := by
  rw [polytabloid_move A (containedAttachmentPlacedTableau he sigma)]
  have hp : tableauMove A (containedAttachmentPlacedTableau he sigma)=sigma.symm := by
    apply Equiv.ext
    intro i
    simp [tableauMove,containedAttachmentPlacedTableau]
  rw [hp]

theorem containedAttachmentPlaced_polytabloid_lift (hzero : ∀ c, t ≤ c → e c=0) :
    altWord (columnGroup (containedAttachmentPlacedTableau he sigma))
      (rightWord (containedAttachmentPlacedPositions hh he htm hroom hclear hcapacity s sigma).symm (rowWord s))=
    letterLift (containedAttachmentRowLetter hh he hroom hclear hzero)
      (polytabloid (containedAttachmentPlacedTableau he sigma)) := by
  rw [polytabloid_eq_altWord,letterLift_altWord,containedAttachmentPlaced_rowWord]

/-- Reuses the exhaustive survivor equivalence with the moved columns. -/
def containedAttachmentPlacedColumnSplit (hzero : ∀ c, t ≤ c → e c=0) :
    (columnGroup (containedPathPrefixOrder hh htm hroom hclear hcapacity) ×
      columnGroup (containedAttachmentPlacedTableau he sigma)) ≃
        containedTargetSurvivorGroup hh he s (d:=d) :=
  (Equiv.prodCongr (Equiv.refl _)
    (columnMove (containedAttachmentPlacedTableau he sigma) A)).trans
      (containedTargetColumnSplit hh he htm hroom hclear hcapacity s hzero)

theorem containedAttachmentPlacedColumnSplit_value (hzero : ∀ c, t ≤ c → e c=0)
    (p : columnGroup (containedPathPrefixOrder hh htm hroom hclear hcapacity) ×
      columnGroup (containedAttachmentPlacedTableau he sigma)) :
    (containedAttachmentPlacedColumnSplit hh he htm hroom hclear hcapacity s sigma hzero p).val=
      sumPerm (containedAttachmentPlacedPositions hh he htm hroom hclear hcapacity s sigma).symm
        p.1.val p.2.val := by
  apply Equiv.ext
  intro i
  obtain ⟨j,rfl⟩ := (containedAttachmentPlacedPositions hh he htm hroom hclear hcapacity s sigma).surjective i
  cases j with
  | inl j =>
    have hv := sumPerm_left
      (containedAttachmentPlacedPositions hh he htm hroom hclear hcapacity s sigma).symm
        p.1.val p.2.val j
    simp only [Equiv.symm_symm] at hv
    rw [hv,containedAttachmentPlacedPositions_path,containedAttachmentPlacedPositions_path]
    change (containedTargetColumnSplit hh he htm hroom hclear hcapacity s hzero
      (p.1,columnMove (containedAttachmentPlacedTableau he sigma) A p.2)).val
        ((Q) (.inl j))=(Q) (.inl (p.1.val j))
    exact containedTargetColumnSplit_left hh he htm hroom hclear hcapacity s hzero _ j
  | inr j =>
    have hv := sumPerm_right
      (containedAttachmentPlacedPositions hh he htm hroom hclear hcapacity s sigma).symm
        p.1.val p.2.val j
    simp only [Equiv.symm_symm] at hv
    rw [hv,containedAttachmentPlacedPositions_attachment,
      containedAttachmentPlacedPositions_attachment]
    change (containedTargetColumnSplit hh he htm hroom hclear hcapacity s hzero
      (p.1,columnMove (containedAttachmentPlacedTableau he sigma) A p.2)).val
        ((Q) (.inr (sigma j)))=(Q) (.inr (sigma (p.2.val j)))
    rw [containedTargetColumnSplit_right]
    congr 2
    change (tableauMove (containedAttachmentPlacedTableau he sigma) A * p.2.val *
      (tableauMove (containedAttachmentPlacedTableau he sigma) A)⁻¹) (sigma j) = sigma (p.2.val j)
    have hmove : tableauMove (containedAttachmentPlacedTableau he sigma) A = sigma := by
      ext i
      simp [tableauMove,containedAttachmentPlacedTableau]
    rw [hmove]
    simp [Equiv.Perm.mul_apply,Equiv.Perm.inv_def]

theorem containedAttachmentPlacedColumnSplit_sign (hzero : ∀ c, t ≤ c → e c=0)
    (p : columnGroup (containedPathPrefixOrder hh htm hroom hclear hcapacity) ×
      columnGroup (containedAttachmentPlacedTableau he sigma)) :
    signC (containedAttachmentPlacedColumnSplit hh he htm hroom hclear hcapacity s sigma hzero p).val=
      signC p.1.val*signC p.2.val := by
  rw [containedAttachmentPlacedColumnSplit_value,signC_sumPerm]

/-- The whole survivor alternant in the new order; the full caller group is
retained. -/
theorem containedAttachmentPlacedSurvivor_alternant (hzero : ∀ c, t ≤ c → e c=0) :
    altWord (containedTargetSurvivorGroup hh he s (d:=d)) (rowWord s)=
      positionProduct (containedAttachmentPlacedPositions hh he htm hroom hclear hcapacity s sigma).symm
        (altWord (columnGroup (containedPathPrefixOrder hh htm hroom hclear hcapacity))
          (leftWord (containedAttachmentPlacedPositions hh he htm hroom hclear hcapacity s sigma).symm (rowWord s)))
        (letterLift (containedAttachmentRowLetter hh he hroom hclear hzero)
          (polytabloid (containedAttachmentPlacedTableau he sigma))) := by
  rw [← containedAttachmentPlaced_polytabloid_lift hh he htm hroom hclear hcapacity s sigma hzero]
  apply altWord_split _ _ _ _
    (containedAttachmentPlacedColumnSplit hh he htm hroom hclear hcapacity s sigma hzero).symm
  intro g
  exact (congrArg Subtype.val
    ((containedAttachmentPlacedColumnSplit hh he htm hroom hclear hcapacity s sigma hzero).apply_symm_apply g)).symm.trans
      (containedAttachmentPlacedColumnSplit_value hh he htm hroom hclear hcapacity s sigma hzero _)

theorem containedAttachmentPlacedSurvivor_lifted (hzero : ∀ c, t ≤ c → e c=0) :
    altWord (containedTargetSurvivorGroup hh he s (d:=d)) (rowWord s)=
      positionProduct (containedAttachmentPlacedPositions hh he htm hroom hclear hcapacity s sigma).symm
        (letterLift (rowLetterInclusion (containedPath_le_whole h e hh he d K m))
          (polytabloid (containedPathPrefixOrder hh htm hroom hclear hcapacity)))
        (letterLift (containedAttachmentRowLetter hh he hroom hclear hzero)
          (polytabloid (containedAttachmentPlacedTableau he sigma))) := by
  rw [containedAttachmentPlacedSurvivor_alternant,
    containedAttachmentPlaced_path_rowWord,containedFactor_path_polytabloid]
end
end
end HSTZ
#print axioms HSTZ.containedAttachmentPlacedTableau
#print axioms HSTZ.containedAttachmentPlacedPositions
#print axioms HSTZ.containedAttachmentPlacedPositions_path
#print axioms HSTZ.containedAttachmentPlacedPositions_attachment
#print axioms HSTZ.containedAttachmentPlacedPositions_inverse_path
#print axioms HSTZ.containedAttachmentPlacedPositions_inverse_attachment
#print axioms HSTZ.containedAttachmentPlacedPositions_cell
#print axioms HSTZ.containedAttachmentPlacedPositions_flag
#print axioms HSTZ.containedAttachmentPlaced_rowWord
#print axioms HSTZ.containedAttachmentPlaced_path_rowWord
#print axioms HSTZ.containedAttachmentPlaced_polytabloid_move
#print axioms HSTZ.containedAttachmentPlaced_polytabloid_lift
#print axioms HSTZ.containedAttachmentPlacedColumnSplit
#print axioms HSTZ.containedAttachmentPlacedColumnSplit_value
#print axioms HSTZ.containedAttachmentPlacedColumnSplit_sign
#print axioms HSTZ.containedAttachmentPlacedSurvivor_alternant
#print axioms HSTZ.containedAttachmentPlacedSurvivor_lifted
