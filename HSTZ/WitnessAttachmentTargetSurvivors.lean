import HSTZ.WitnessAttachmentTargetDiagonal

/-! Inverse coordinates of even-target survivors; no global sign or value is
claimed. Uses interfaces adapted from OpenAI's `math` repository (commit adc7f1241, Apache-2.0). -/
namespace HSTZ
noncomputable section
open OAI.Saxl

private theorem evenColumn_inverse_side {b : ℕ} {mu : YoungDiagram}
    (t : Tableau (witnessAttachment b 0).card mu) (he : AttachmentEvenRows mu)
    (g : attachmentTargetEvenColumnGroup t he) (j : Fin b) (s : Fin 2) :
    ∃ q : Fin b, g.val.symm (witnessAttachmentColumnOrderFin b 0 (.inl (j,s))) =
      witnessAttachmentColumnOrderFin b 0 (.inl (q,s)) ∧
      (attachmentTargetEvenHalfTableau t he q).val.2 =
        (attachmentTargetEvenHalfTableau t he j).val.2 := by
  have hc := (g⁻¹).property (witnessAttachmentColumnOrderFin b 0 (.inl (j,s)))
  change (t (attachmentTargetEvenMatching t he
    (g.val.symm (witnessAttachmentColumnOrderFin b 0 (.inl (j,s)))))).val.2 =
    (t (attachmentTargetEvenMatching t he
      (witnessAttachmentColumnOrderFin b 0 (.inl (j,s))))).val.2 at hc
  obtain ⟨p,hp⟩ := (witnessAttachmentColumnOrderFin b 0).surjective
    (g.val.symm (witnessAttachmentColumnOrderFin b 0 (.inl (j,s))))
  cases p with
  | inr z => exact Fin.elim0 z
  | inl p =>
    rcases p with ⟨q,u⟩
    rw [← hp,attachmentTargetEvenMatching_order,attachmentTargetEvenMatching_order,
      attachmentTargetEvenPositions_pair,attachmentTargetEvenPositions_pair] at hc
    change 2*(attachmentTargetEvenHalfTableau t he q).val.2+u.val =
      2*(attachmentTargetEvenHalfTableau t he j).val.2+s.val at hc
    have hu : u=s := by
      apply Fin.ext
      have hh := u.isLt
      have hh' := s.isLt
      omega
    subst u
    exact ⟨q,hp.symm,by omega⟩

theorem attachmentTargetEven_survivor_inverse_pair {b : ℕ} {mu : YoungDiagram}
    (t : Tableau (witnessAttachment b 0).card mu) (he : AttachmentEvenRows mu)
    (g : attachmentTargetEvenColumnGroup t he)
    (hm : attachmentTargetEvenPairMatches t he g) (j : Fin b) :
    ∃ q : Fin b, (attachmentTargetEvenHalfTableau t he q).val.2 =
      (attachmentTargetEvenHalfTableau t he j).val.2 ∧
      ∀ s : Fin 2, g.val.symm (witnessAttachmentColumnOrderFin b 0 (.inl (j,s))) =
        witnessAttachmentColumnOrderFin b 0 (.inl (q,s)) := by
  obtain ⟨q0,h0,c0⟩ := evenColumn_inverse_side t he g j 0
  obtain ⟨q1,h1,c1⟩ := evenColumn_inverse_side t he g j 1
  have hr := congrArg (fun x : Fin (mu.colLen 0) => x.val) (hm j)
  change (t (attachmentTargetEvenMatching t he
    (g.val.symm (witnessAttachmentColumnOrderFin b 0 (.inl (j,0)))))).val.1 =
    (t (attachmentTargetEvenMatching t he
      (g.val.symm (witnessAttachmentColumnOrderFin b 0 (.inl (j,1)))))).val.1 at hr
  rw [h0,h1,attachmentTargetEvenMatching_order,attachmentTargetEvenMatching_order,
    attachmentTargetEvenPositions_pair,attachmentTargetEvenPositions_pair] at hr
  have hq : q0=q1 := (attachmentTargetEvenHalfTableau t he).injective
    (Subtype.ext (Prod.ext hr (c0.trans c1.symm)))
  subst q1
  refine ⟨q0,c0,?_⟩
  intro s
  fin_cases s <;> assumption

end
end HSTZ
#print axioms HSTZ.attachmentTargetEven_survivor_inverse_pair
