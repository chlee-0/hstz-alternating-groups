import HSTZ.WitnessAttachmentEvenNoncancellation

/-! Inverse paired coordinates for odd survivors, with exclusion of the orphan cell.
Uses interfaces from OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
Only the original column membership, row matching and target cells are used. -/
namespace HSTZ
noncomputable section
open OAI.Saxl

private theorem oddColumn_inverse_one {b : ℕ} {mu : YoungDiagram}
    (t : Tableau (witnessAttachment b 1).card mu) (a : ℕ)
    (ho : AttachmentOneOddRow mu a) (g : attachmentTargetOddColumnGroup t a ho)
    (j : Fin b) :
    ∃ q : Fin b, g.val.symm (witnessAttachmentColumnOrderFin b 1 (.inl (j,1))) =
      witnessAttachmentColumnOrderFin b 1 (.inl (q,1)) ∧
      (attachmentTargetOddHalfTableau t a ho q).val.2 =
        (attachmentTargetOddHalfTableau t a ho j).val.2 := by
  have hc := (g⁻¹).property (witnessAttachmentColumnOrderFin b 1 (.inl (j,1)))
  change (t (attachmentTargetOddMatching t a ho
    (g.val.symm (witnessAttachmentColumnOrderFin b 1 (.inl (j,1)))))).val.2 =
    (t (attachmentTargetOddMatching t a ho
      (witnessAttachmentColumnOrderFin b 1 (.inl (j,1))))).val.2 at hc
  obtain ⟨p,hp⟩ := (witnessAttachmentColumnOrderFin b 1).surjective
    (g.val.symm (witnessAttachmentColumnOrderFin b 1 (.inl (j,1))))
  cases p with
  | inr z =>
    rw [← hp,attachmentTargetOddMatching_order,attachmentTargetOddMatching_order,
      attachmentTargetOddPositions_single,attachmentTargetOddPositions_pair] at hc
    change mu.rowLen a-1 = 2*(attachmentTargetOddHalfTableau t a ho j).val.2+1 at hc
    have hm := ho.1
    omega
  | inl p =>
    rcases p with ⟨q,u⟩
    rw [← hp,attachmentTargetOddMatching_order,attachmentTargetOddMatching_order,
      attachmentTargetOddPositions_pair,attachmentTargetOddPositions_pair] at hc
    change 2*(attachmentTargetOddHalfTableau t a ho q).val.2+u.val =
      2*(attachmentTargetOddHalfTableau t a ho j).val.2+1 at hc
    have hu : u=1 := by
      apply Fin.ext
      have hh := u.isLt
      omega
    subst u
    exact ⟨q,hp.symm,by omega⟩

theorem attachmentTargetOdd_survivor_inverse_pair {b : ℕ} {mu : YoungDiagram}
    (t : Tableau (witnessAttachment b 1).card mu) (a : ℕ)
    (ho : AttachmentOneOddRow mu a) (g : attachmentTargetOddColumnGroup t a ho)
    (hm : attachmentTargetOddPairMatches t a ho g) (j : Fin b) :
    ∃ q : Fin b, (attachmentTargetOddHalfTableau t a ho q).val.2 =
      (attachmentTargetOddHalfTableau t a ho j).val.2 ∧
      ∀ s : Fin 2, g.val.symm (witnessAttachmentColumnOrderFin b 1 (.inl (j,s))) =
        witnessAttachmentColumnOrderFin b 1 (.inl (q,s)) := by
  obtain ⟨q1,h1,c1⟩ := oddColumn_inverse_one t a ho g j
  have hr := congrArg (fun x : Fin (mu.colLen 0) => x.val) (hm j)
  change (t (attachmentTargetOddMatching t a ho
    (g.val.symm (witnessAttachmentColumnOrderFin b 1 (.inl (j,0)))))).val.1 =
    (t (attachmentTargetOddMatching t a ho
      (g.val.symm (witnessAttachmentColumnOrderFin b 1 (.inl (j,1)))))).val.1 at hr
  rw [h1,attachmentTargetOddMatching_order,attachmentTargetOddPositions_pair] at hr
  have hc := (g⁻¹).property (witnessAttachmentColumnOrderFin b 1 (.inl (j,0)))
  change (t (attachmentTargetOddMatching t a ho
    (g.val.symm (witnessAttachmentColumnOrderFin b 1 (.inl (j,0)))))).val.2 =
    (t (attachmentTargetOddMatching t a ho
      (witnessAttachmentColumnOrderFin b 1 (.inl (j,0))))).val.2 at hc
  obtain ⟨p,hp⟩ := (witnessAttachmentColumnOrderFin b 1).surjective
    (g.val.symm (witnessAttachmentColumnOrderFin b 1 (.inl (j,0))))
  cases p with
  | inr z =>
    rw [← hp,attachmentTargetOddMatching_order,attachmentTargetOddPositions_single] at hr
    rw [← hp,attachmentTargetOddMatching_order,attachmentTargetOddMatching_order,
      attachmentTargetOddPositions_single,attachmentTargetOddPositions_pair] at hc
    change mu.rowLen a-1 = 2*(attachmentTargetOddHalfTableau t a ho j).val.2 at hc
    have hcMem := (t (attachmentTargetOddPositions t a ho (.inl (q1,1)))).property
    change (t (attachmentTargetOddPositions t a ho (.inl (q1,1)))).val ∈ mu at hcMem
    rw [attachmentTargetOddPositions_pair] at hcMem
    have hb := YoungDiagram.mem_iff_lt_rowLen.mp hcMem
    change 2*(attachmentTargetOddHalfTableau t a ho q1).val.2+1 <
      mu.rowLen (attachmentTargetOddHalfTableau t a ho q1).val.1 at hb
    change a = (attachmentTargetOddHalfTableau t a ho q1).val.1 at hr
    rw [← hr] at hb
    have hodd := ho.1
    omega
  | inl p =>
    rcases p with ⟨q0,u⟩
    rw [← hp,attachmentTargetOddMatching_order,attachmentTargetOddMatching_order,
      attachmentTargetOddPositions_pair,attachmentTargetOddPositions_pair] at hc
    change 2*(attachmentTargetOddHalfTableau t a ho q0).val.2+u.val =
      2*(attachmentTargetOddHalfTableau t a ho j).val.2 at hc
    have hu : u=0 := by
      apply Fin.ext
      have hh := u.isLt
      omega
    subst u
    rw [← hp,attachmentTargetOddMatching_order,attachmentTargetOddPositions_pair] at hr
    have hq : q0=q1 := (attachmentTargetOddHalfTableau t a ho).injective
      (Subtype.ext (Prod.ext hr (by omega)))
    subst q1
    refine ⟨q0,c1,?_⟩
    intro s
    fin_cases s
    · exact hp.symm
    · exact h1

end
end HSTZ
#print axioms HSTZ.attachmentTargetOdd_survivor_inverse_pair
