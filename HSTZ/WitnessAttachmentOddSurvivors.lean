import HSTZ.WitnessAttachmentOddSurvivorCoordinates

/-! Odd survivors duplicate half-columns and fix the orphan cell.
Uses interfaces adapted from OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
Evaluation of the full sum is done separately. -/
namespace HSTZ
noncomputable section
open OAI.Saxl

theorem attachmentTargetOdd_survivor_duplicate {b : ℕ} {mu : YoungDiagram}
    (t : Tableau (witnessAttachment b 1).card mu) (a : ℕ) (ho : AttachmentOneOddRow mu a)
    (g : attachmentTargetOddColumnGroup t a ho)
    (hm : attachmentTargetOddPairMatches t a ho g) :
    ∃ h : columnGroup (attachmentTargetOddHalfTableau t a ho),
      g.val.symm = (attachmentTargetOddDiagonal t a ho h).val := by
  classical
  let f : Fin b → Fin b := fun j => Classical.choose
    (attachmentTargetOdd_survivor_inverse_pair t a ho g hm j)
  have hc (j : Fin b) : (attachmentTargetOddHalfTableau t a ho (f j)).val.2 =
      (attachmentTargetOddHalfTableau t a ho j).val.2 :=
    (Classical.choose_spec (attachmentTargetOdd_survivor_inverse_pair t a ho g hm j)).1
  have hv (j : Fin b) (s : Fin 2) :
      g.val.symm (witnessAttachmentColumnOrderFin b 1 (.inl (j,s))) =
        witnessAttachmentColumnOrderFin b 1 (.inl (f j,s)) :=
    (Classical.choose_spec (attachmentTargetOdd_survivor_inverse_pair t a ho g hm j)).2 s
  have hi : Function.Injective f := by
    intro j k hh
    have hh' : witnessAttachmentColumnOrderFin b 1 (.inl (j,0)) =
        witnessAttachmentColumnOrderFin b 1 (.inl (k,0)) := by
      apply g.val.symm.injective
      rw [hv j 0,hv k 0,hh]
    exact congrArg Prod.fst (Sum.inl.inj ((witnessAttachmentColumnOrderFin b 1).injective hh'))
  let h : columnGroup (attachmentTargetOddHalfTableau t a ho) :=
    ⟨Equiv.ofBijective f ⟨hi,Finite.surjective_of_injective hi⟩,hc⟩
  have hsingle : g.val.symm (witnessAttachmentColumnOrderFin b 1 (.inr 0)) =
      witnessAttachmentColumnOrderFin b 1 (.inr 0) := by
    obtain ⟨p,hp⟩ := (witnessAttachmentColumnOrderFin b 1).surjective
      (g.val.symm (witnessAttachmentColumnOrderFin b 1 (.inr 0)))
    cases p with
    | inr z =>
      have hz : z=0 := Subsingleton.elim _ _
      subst z
      exact hp.symm
    | inl p =>
      obtain ⟨j,hj⟩ := Finite.surjective_of_injective hi p.1
      have hh : g.val.symm (witnessAttachmentColumnOrderFin b 1 (.inl (j,p.2))) =
          g.val.symm (witnessAttachmentColumnOrderFin b 1 (.inr 0)) := by
        rw [hv j p.2,hj]
        exact hp
      have hh' := (witnessAttachmentColumnOrderFin b 1).injective (g.val.symm.injective hh)
      cases hh'
  refine ⟨h,?_⟩
  apply Equiv.ext
  intro i
  obtain ⟨p,rfl⟩ := (witnessAttachmentColumnOrderFin b 1).surjective i
  cases p with
  | inr z =>
    have hz : z=0 := Subsingleton.elim _ _
    subst z
    change g.val.symm (witnessAttachmentColumnOrderFin b 1 (.inr 0)) =
      attachmentTargetDiagonal b 1 h.val (witnessAttachmentColumnOrderFin b 1 (.inr 0))
    rw [attachmentTargetDiagonal_single]
    exact hsingle
  | inl p =>
    change g.val.symm (witnessAttachmentColumnOrderFin b 1 (.inl p)) =
      attachmentTargetDiagonal b 1 h.val (witnessAttachmentColumnOrderFin b 1 (.inl p))
    rw [attachmentTargetDiagonal_pair]
    exact hv p.1 p.2

theorem attachmentTargetOdd_survivor_sign {b : ℕ} {mu : YoungDiagram}
    (t : Tableau (witnessAttachment b 1).card mu) (a : ℕ) (ho : AttachmentOneOddRow mu a)
    (g : attachmentTargetOddColumnGroup t a ho)
    (hm : attachmentTargetOddPairMatches t a ho g) : signC g.val = 1 := by
  obtain ⟨h,hh⟩ := attachmentTargetOdd_survivor_duplicate t a ho g hm
  have hs : signC g.val = signC g.val.symm := by
    simpa only [Equiv.Perm.inv_def] using (signC_inv g.val).symm
  rw [hs,hh]
  exact attachmentTargetDiagonal_sign b 1 h.val

theorem attachmentTargetOdd_survivor_single {b : ℕ} {mu : YoungDiagram}
    (t : Tableau (witnessAttachment b 1).card mu) (a : ℕ)
    (ho : AttachmentOneOddRow mu a) (g : attachmentTargetOddColumnGroup t a ho)
    (hm : attachmentTargetOddPairMatches t a ho g) (z : Fin 1) :
    g.val.symm (witnessAttachmentColumnOrderFin b 1 (.inr z)) =
      witnessAttachmentColumnOrderFin b 1 (.inr z) := by
  obtain ⟨h,hh⟩ := attachmentTargetOdd_survivor_duplicate t a ho g hm
  rw [hh]
  exact attachmentTargetDiagonal_single b 1 h.val z

end
end HSTZ
#print axioms HSTZ.attachmentTargetOdd_survivor_duplicate
#print axioms HSTZ.attachmentTargetOdd_survivor_sign
#print axioms HSTZ.attachmentTargetOdd_survivor_single
