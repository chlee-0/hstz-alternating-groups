import HSTZ.WitnessAttachmentProductContraction

/-! Products over all coordinates in the matched target column-group sum.
Builds on OpenAI's `math` repository (commit adc7f1241, Apache-2.0) and reuses the target letters
and source cuts. These product expressions do not by themselves establish
noncancellation over the full group or unconditional target support. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped Classical

private theorem targetIteInstances (p : Prop) (d e : Decidable p) (x y : ℂ) :
    @ite ℂ p d x y = @ite ℂ p e x y := by
  have hh : d = e := Subsingleton.elim _ _
  cases hh
  rfl

theorem attachmentHPairIndex_order (b delta : ℕ) (j : Fin b) (s : Fin 2) :
    (attachmentColumnSplit b delta).symm (.inl (attachmentHPairIndex b j s)) =
      witnessAttachmentColumnOrderFin b delta (.inl (j,s)) := by
  apply (attachmentColumnSplit b delta).injective
  rw [Equiv.apply_symm_apply]
  unfold attachmentColumnSplit
  simp only [Equiv.trans_apply,Equiv.symm_apply_apply,Equiv.sumCongr_apply,Sum.map_inl]
  congr 1
  apply Fin.ext
  change 2*j.val+s.val = s.val+2*j.val
  omega

theorem attachmentHSingleton_order (b delta : ℕ) (j : Fin delta) :
    (attachmentColumnSplit b delta).symm (.inr j) =
      witnessAttachmentColumnOrderFin b delta (.inr j) := by
  apply (attachmentColumnSplit b delta).injective
  simp [attachmentColumnSplit]

theorem attachmentHTensor_target_product {n : ℕ} {mu : YoungDiagram}
    (t : Tableau n mu) (ht : mu.colLen 0 ≤ 4) (a : Fin 4) (b delta : ℕ)
    (w : Fin (witnessAttachment b delta).card → Fin (mu.colLen 0)) :
    dotProduct (wordMap (attachmentTargetLetters t ht a) (Pi.single w 1))
      (attachmentHTensor b delta) =
    (∏ j : Fin b, if w (witnessAttachmentColumnOrderFin b delta (.inl (j,0))) =
      w (witnessAttachmentColumnOrderFin b delta (.inl (j,1))) then (1:ℂ) else 0) *
    ∏ j : Fin delta, attachmentTargetLetters t ht a
      (w (witnessAttachmentColumnOrderFin b delta (.inr j))) 0 := by
  rw [attachmentHTensor_contraction_product]
  congr 1
  · apply Finset.prod_congr rfl
    intro j hj
    rw [attachmentTargetLetters_pair]
    simp only [leftWord,attachmentHPairIndex_order]

def attachmentTargetEvenPairMatches {b : ℕ} {mu : YoungDiagram}
    (t : Tableau (witnessAttachment b 0).card mu) (he : AttachmentEvenRows mu)
    (g : attachmentTargetEvenColumnGroup t he) : Prop :=
  ∀ j : Fin b, rowWord t (attachmentTargetEvenMatching t he
    (g.val.symm (witnessAttachmentColumnOrderFin b 0 (.inl (j,0))))) =
    rowWord t (attachmentTargetEvenMatching t he
    (g.val.symm (witnessAttachmentColumnOrderFin b 0 (.inl (j,1)))))

def attachmentTargetOddPairMatches {b : ℕ} {mu : YoungDiagram}
    (t : Tableau (witnessAttachment b 1).card mu) (a : ℕ)
    (ho : AttachmentOneOddRow mu a) (g : attachmentTargetOddColumnGroup t a ho) : Prop :=
  ∀ j : Fin b, rowWord t (attachmentTargetOddMatching t a ho
    (g.val.symm (witnessAttachmentColumnOrderFin b 1 (.inl (j,0))))) =
    rowWord t (attachmentTargetOddMatching t a ho
    (g.val.symm (witnessAttachmentColumnOrderFin b 1 (.inl (j,1)))))

theorem attachmentTargetEven_term {b : ℕ} {mu : YoungDiagram}
    (t : Tableau (witnessAttachment b 0).card mu) (he : AttachmentEvenRows mu)
    (ht : mu.colLen 0 ≤ 4) (a : Fin 4) (g : attachmentTargetEvenColumnGroup t he) :
    dotProduct (wordMap (attachmentTargetLetters t ht a) (Pi.single
      ((rowWord t ∘ attachmentTargetEvenMatching t he) ∘ g.val.symm) 1))
      (attachmentHTensor b 0) = if attachmentTargetEvenPairMatches t he g then 1 else 0 := by
  classical
  rw [attachmentHTensor_target_product]
  simp only [Fintype.prod_empty,mul_one,Fintype.prod_boole,Function.comp_apply,
    attachmentTargetEvenPairMatches]
  exact targetIteInstances _ _ _ _ _

theorem attachmentTargetOdd_term {b : ℕ} {mu : YoungDiagram}
    (t : Tableau (witnessAttachment b 1).card mu) (a : ℕ)
    (ho : AttachmentOneOddRow mu a) (ht : mu.colLen 0 ≤ 4)
    (g : attachmentTargetOddColumnGroup t a ho) :
    dotProduct (wordMap (attachmentTargetOddLetters t a ho ht) (Pi.single
      ((rowWord t ∘ attachmentTargetOddMatching t a ho) ∘ g.val.symm) 1))
      (attachmentHTensor b 1) =
    (if attachmentTargetOddPairMatches t a ho g then (1:ℂ) else 0) *
      attachmentTargetOddLetters t a ho ht
        (rowWord t (attachmentTargetOddMatching t a ho
          (g.val.symm (witnessAttachmentColumnOrderFin b 1 (.inr 0))))) 0 := by
  classical
  unfold attachmentTargetOddLetters
  rw [attachmentHTensor_target_product]
  simp only [Fintype.prod_boole,Fin.prod_univ_one,Function.comp_apply,
    attachmentTargetOddPairMatches]
  congr 1
  exact targetIteInstances _ _ _ _ _

end
end HSTZ
#print axioms HSTZ.attachmentHPairIndex_order
#print axioms HSTZ.attachmentHSingleton_order
#print axioms HSTZ.attachmentHTensor_target_product
#print axioms HSTZ.attachmentTargetEven_term
#print axioms HSTZ.attachmentTargetOdd_term
