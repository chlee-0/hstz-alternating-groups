import HSTZ.ContainedTargetColumns

/-! The capacity survivor column group and its two-factor bijection.
Reuses `fiberSplit` and `sumPerm` from OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
The original callers, prefix/tail and row flag are retained. This group normalization
alone gives neither a common covector nor a global nonzero coefficient. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
section
variable {h e : ℕ → ℕ} (hh : Antitone h) (he : Antitone e)
    {d K m t n : ℕ} (htm : t ≤ m) (hroom : ∀ c < t, d+e c≤h c)
    (hclear : t*d+4≤K) (hcapacity : K≤prefixSum (capacity h d) m)
    (s : Tableau n (containedWhole h e hh he d K m))
local notation "Q" => containedFactorPositions hh he htm hroom hclear hcapacity s
local notation "T" => containedPathPrefixOrder hh htm hroom hclear hcapacity
local notation "A" => canonicalTableau (containedAttachment e he m) rfl

/-- Row-flag preserving members of the full original column group. -/
def containedTargetSurvivorGroup := columnGroup s ⊓ sectorGroup (fun i => (rowWord s i).val < d)

theorem containedFactorPositions_flag (hzero : ∀ c, t ≤ c → e c=0) (i : Fin n) :
    ((Q).symm i).isLeft=true ↔ (rowWord s i).val < d := by
  obtain ⟨j,rfl⟩ := (Q).surjective i
  cases j with
  | inl j =>
    have hr := containedFactorPositions_path_flag hh he htm hroom hclear hcapacity s j
    simpa only [Equiv.symm_apply_apply,Sum.isLeft_inl,Bool.true_eq,true_iff] using hr
  | inr j =>
    have hr := containedFactorPositions_attachment_flag hh he htm hroom hclear hcapacity s hzero j
    simpa only [Equiv.symm_apply_apply,Sum.isLeft_inr,Bool.false_eq_true,false_iff] using (not_lt.mpr hr)

private def pathColumnTransport : columnGroup T ≃
    fiberGroup (fun i => (s ((Q) (.inl i))).val.2) :=
  Equiv.subtypeEquivRight (fun g => by
    change (∀ i, (T (g i)).val.2=(T i).val.2) ↔
      (∀ i, (s ((Q) (.inl (g i)))).val.2=(s ((Q) (.inl i))).val.2)
    simp only [containedFactorPositions_path])

private def attachmentColumnTransport : columnGroup A ≃
    fiberGroup (fun i => (s ((Q) (.inr i))).val.2) :=
  Equiv.subtypeEquivRight (fun g => by
    change (∀ i, (A (g i)).val.2=(A i).val.2) ↔
      (∀ i, (s ((Q) (.inr (g i)))).val.2=(s ((Q) (.inr i))).val.2)
    simp only [containedFactorPositions_attachment])

private def survivorColumnTransport (hzero : ∀ c, t ≤ c → e c=0) :
    ↥(fiberGroup (fun i => (s i).val.2) ⊓ sectorGroup (fun i => ((Q).symm i).isLeft=true)) ≃
      containedTargetSurvivorGroup hh he s (d:=d) :=
  Equiv.subtypeEquivRight (fun g => by
    change ((∀ i, (s (g i)).val.2=(s i).val.2) ∧
      (∀ i, ((Q).symm (g i)).isLeft=true ↔ ((Q).symm i).isLeft=true)) ↔
      ((∀ i, (s (g i)).val.2=(s i).val.2) ∧
      (∀ i, (rowWord s (g i)).val < d ↔ (rowWord s i).val < d))
    simp only [containedFactorPositions_flag hh he htm hroom hclear hcapacity s hzero])

/-- The factor groups extend to exactly the row-flag survivors. -/
def containedTargetColumnSplit (hzero : ∀ c, t ≤ c → e c=0) :
    (columnGroup T × columnGroup A) ≃ containedTargetSurvivorGroup hh he s (d:=d) :=
  ((Equiv.prodCongr (pathColumnTransport hh he htm hroom hclear hcapacity s)
    (attachmentColumnTransport hh he htm hroom hclear hcapacity s)).trans
      (fiberSplit (Q).symm (fun i => (s i).val.2))).trans
        (survivorColumnTransport hh he htm hroom hclear hcapacity s hzero)

theorem containedTargetColumnSplit_value (hzero : ∀ c, t ≤ c → e c=0)
    (p : columnGroup T × columnGroup A) :
    (containedTargetColumnSplit hh he htm hroom hclear hcapacity s hzero p).val=
      sumPerm (Q).symm p.1.val p.2.val := rfl

theorem containedTargetColumnSplit_left (hzero : ∀ c, t ≤ c → e c=0)
    (p : columnGroup T × columnGroup A) (i : Fin K) :
    (containedTargetColumnSplit hh he htm hroom hclear hcapacity s hzero p).val ((Q) (.inl i))=
      (Q) (.inl (p.1.val i)) := by
  rw [containedTargetColumnSplit_value]
  exact sumPerm_left (Q).symm _ _ i

theorem containedTargetColumnSplit_right (hzero : ∀ c, t ≤ c → e c=0)
    (p : columnGroup T × columnGroup A) (i : Fin (containedAttachment e he m).card) :
    (containedTargetColumnSplit hh he htm hroom hclear hcapacity s hzero p).val ((Q) (.inr i))=
      (Q) (.inr (p.2.val i)) := by
  rw [containedTargetColumnSplit_value]
  exact sumPerm_right (Q).symm _ _ i

theorem containedTargetColumnSplit_inverse_left (hzero : ∀ c, t ≤ c → e c=0)
    (g : containedTargetSurvivorGroup hh he s (d:=d)) (i : Fin K) :
    g.val.symm ((Q) (.inl i))=(Q) (.inl
      (((containedTargetColumnSplit hh he htm hroom hclear hcapacity s hzero).symm g).1.val.symm i)) := by
  apply g.val.injective
  rw [Equiv.apply_symm_apply]
  have hv := containedTargetColumnSplit_left hh he htm hroom hclear hcapacity s hzero
    ((containedTargetColumnSplit hh he htm hroom hclear hcapacity s hzero).symm g)
    (((containedTargetColumnSplit hh he htm hroom hclear hcapacity s hzero).symm g).1.val.symm i)
  simpa only [Equiv.apply_symm_apply] using hv.symm

theorem containedTargetColumnSplit_inverse_right (hzero : ∀ c, t ≤ c → e c=0)
    (g : containedTargetSurvivorGroup hh he s (d:=d)) (i : Fin (containedAttachment e he m).card) :
    g.val.symm ((Q) (.inr i))=(Q) (.inr
      (((containedTargetColumnSplit hh he htm hroom hclear hcapacity s hzero).symm g).2.val.symm i)) := by
  apply g.val.injective
  rw [Equiv.apply_symm_apply]
  have hv := containedTargetColumnSplit_right hh he htm hroom hclear hcapacity s hzero
    ((containedTargetColumnSplit hh he htm hroom hclear hcapacity s hzero).symm g)
    (((containedTargetColumnSplit hh he htm hroom hclear hcapacity s hzero).symm g).2.val.symm i)
  simpa only [Equiv.apply_symm_apply] using hv.symm

theorem containedTargetColumnSplit_sign (hzero : ∀ c, t ≤ c → e c=0)
    (p : columnGroup T × columnGroup A) :
    signC (containedTargetColumnSplit hh he htm hroom hclear hcapacity s hzero p).val=
      signC p.1.val*signC p.2.val := by
  rw [containedTargetColumnSplit_value,signC_sumPerm]

/-- The entire survivor alternant in the original caller's factor order. -/
theorem containedTargetSurvivor_alternant (hzero : ∀ c, t ≤ c → e c=0) :
    altWord (containedTargetSurvivorGroup hh he s (d:=d)) (rowWord s)=
      positionProduct (Q).symm
        (altWord (columnGroup T) (leftWord (Q).symm (rowWord s)))
        (altWord (columnGroup A) (rightWord (Q).symm (rowWord s))) := by
  apply altWord_split (Q).symm _ _ _
    (containedTargetColumnSplit hh he htm hroom hclear hcapacity s hzero).symm
  intro g
  exact (congrArg Subtype.val
    ((containedTargetColumnSplit hh he htm hroom hclear hcapacity s hzero).apply_symm_apply g)).symm.trans
      (containedTargetColumnSplit_value hh he htm hroom hclear hcapacity s hzero _)
end
end
end HSTZ
#print axioms HSTZ.containedFactorPositions_flag
#print axioms HSTZ.containedTargetColumnSplit
#print axioms HSTZ.containedTargetColumnSplit_value
#print axioms HSTZ.containedTargetColumnSplit_left
#print axioms HSTZ.containedTargetColumnSplit_right
#print axioms HSTZ.containedTargetColumnSplit_sign
#print axioms HSTZ.containedTargetSurvivor_alternant

#print axioms HSTZ.containedTargetColumnSplit_inverse_left
#print axioms HSTZ.containedTargetColumnSplit_inverse_right
