import HSTZ.WitnessAttachmentTargetSurvivors

/-! The even survivors are exactly the duplicated half-column permutations. Uses
interfaces from OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
The classification of odd orphans and the full sum evaluation are not done here. -/
namespace HSTZ
noncomputable section
open OAI.Saxl

theorem attachmentTargetEven_survivor_duplicate {b : ℕ} {mu : YoungDiagram}
    (t : Tableau (witnessAttachment b 0).card mu) (he : AttachmentEvenRows mu)
    (g : attachmentTargetEvenColumnGroup t he)
    (hm : attachmentTargetEvenPairMatches t he g) :
    ∃ h : columnGroup (attachmentTargetEvenHalfTableau t he),
      g.val.symm = (attachmentTargetEvenDiagonal t he h).val := by
  classical
  let f : Fin b → Fin b := fun j => Classical.choose
    (attachmentTargetEven_survivor_inverse_pair t he g hm j)
  have hc (j : Fin b) : (attachmentTargetEvenHalfTableau t he (f j)).val.2 =
      (attachmentTargetEvenHalfTableau t he j).val.2 :=
    (Classical.choose_spec (attachmentTargetEven_survivor_inverse_pair t he g hm j)).1
  have hv (j : Fin b) (s : Fin 2) :
      g.val.symm (witnessAttachmentColumnOrderFin b 0 (.inl (j,s))) =
        witnessAttachmentColumnOrderFin b 0 (.inl (f j,s)) :=
    (Classical.choose_spec (attachmentTargetEven_survivor_inverse_pair t he g hm j)).2 s
  have hi : Function.Injective f := by
    intro j k hh
    have hh' : witnessAttachmentColumnOrderFin b 0 (.inl (j,0)) =
        witnessAttachmentColumnOrderFin b 0 (.inl (k,0)) := by
      apply g.val.symm.injective
      rw [hv j 0,hv k 0,hh]
    exact congrArg Prod.fst (Sum.inl.inj ((witnessAttachmentColumnOrderFin b 0).injective hh'))
  let h : columnGroup (attachmentTargetEvenHalfTableau t he) :=
    ⟨Equiv.ofBijective f ⟨hi,Finite.surjective_of_injective hi⟩,hc⟩
  refine ⟨h,?_⟩
  apply Equiv.ext
  intro i
  obtain ⟨p,rfl⟩ := (witnessAttachmentColumnOrderFin b 0).surjective i
  cases p with
  | inr z => exact Fin.elim0 z
  | inl p =>
    change g.val.symm (witnessAttachmentColumnOrderFin b 0 (.inl p)) =
      attachmentTargetDiagonal b 0 h.val (witnessAttachmentColumnOrderFin b 0 (.inl p))
    rw [attachmentTargetDiagonal_pair]
    exact hv p.1 p.2

theorem attachmentTargetEven_survivor_sign {b : ℕ} {mu : YoungDiagram}
    (t : Tableau (witnessAttachment b 0).card mu) (he : AttachmentEvenRows mu)
    (g : attachmentTargetEvenColumnGroup t he)
    (hm : attachmentTargetEvenPairMatches t he g) : signC g.val = 1 := by
  obtain ⟨h,hh⟩ := attachmentTargetEven_survivor_duplicate t he g hm
  have hs : signC g.val = signC g.val.symm := by
    simpa only [Equiv.Perm.inv_def] using (signC_inv g.val).symm
  rw [hs,hh]
  exact attachmentTargetDiagonal_sign b 0 h.val

end
end HSTZ
#print axioms HSTZ.attachmentTargetEven_survivor_duplicate
#print axioms HSTZ.attachmentTargetEven_survivor_sign
