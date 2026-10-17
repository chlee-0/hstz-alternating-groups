import HSTZ.IntertwiningCompat
import HSTZ.WitnessAttachmentTargetPositions

/-! Full target column groups and polytabloids in the H matching.
Reuses `fiberRelabel`, `altWord_fiber_relabel` and `wordPair_move` from
OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
No independent-column contraction or target noncancellation is assumed. -/
namespace HSTZ
noncomputable section
open OAI.Saxl

def attachmentTargetEvenColumnGroup {b : ℕ} {mu : YoungDiagram}
    (t : Tableau (witnessAttachment b 0).card mu) (he : AttachmentEvenRows mu) :=
  fiberGroup (fun i => (t (attachmentTargetEvenMatching t he i)).val.2)

def attachmentTargetOddColumnGroup {b : ℕ} {mu : YoungDiagram}
    (t : Tableau (witnessAttachment b 1).card mu) (a : ℕ)
    (ho : AttachmentOneOddRow mu a) :=
  fiberGroup (fun i => (t (attachmentTargetOddMatching t a ho i)).val.2)

def attachmentTargetEvenColumnEquiv {b : ℕ} {mu : YoungDiagram}
    (t : Tableau (witnessAttachment b 0).card mu) (he : AttachmentEvenRows mu) :
    attachmentTargetEvenColumnGroup t he ≃ columnGroup t :=
  fiberRelabel (attachmentTargetEvenMatching t he) (fun i => (t i).val.2)

def attachmentTargetOddColumnEquiv {b : ℕ} {mu : YoungDiagram}
    (t : Tableau (witnessAttachment b 1).card mu) (a : ℕ)
    (ho : AttachmentOneOddRow mu a) :
    attachmentTargetOddColumnGroup t a ho ≃ columnGroup t :=
  fiberRelabel (attachmentTargetOddMatching t a ho) (fun i => (t i).val.2)

theorem attachmentTargetEvenColumnEquiv_value {b : ℕ} {mu : YoungDiagram}
    (t : Tableau (witnessAttachment b 0).card mu) (he : AttachmentEvenRows mu)
    (g : attachmentTargetEvenColumnGroup t he) (i : Fin (witnessAttachment b 0).card) :
    (attachmentTargetEvenColumnEquiv t he g).val i =
      attachmentTargetEvenMatching t he (g.val ((attachmentTargetEvenMatching t he).symm i)) := rfl

theorem attachmentTargetOddColumnEquiv_value {b : ℕ} {mu : YoungDiagram}
    (t : Tableau (witnessAttachment b 1).card mu) (a : ℕ)
    (ho : AttachmentOneOddRow mu a) (g : attachmentTargetOddColumnGroup t a ho)
    (i : Fin (witnessAttachment b 1).card) :
    (attachmentTargetOddColumnEquiv t a ho g).val i =
      attachmentTargetOddMatching t a ho
        (g.val ((attachmentTargetOddMatching t a ho).symm i)) := rfl

def attachmentTargetEvenAlternant {b : ℕ} {mu : YoungDiagram}
    (t : Tableau (witnessAttachment b 0).card mu) (he : AttachmentEvenRows mu) :=
  altWord (attachmentTargetEvenColumnGroup t he) (rowWord t ∘ attachmentTargetEvenMatching t he)

def attachmentTargetOddAlternant {b : ℕ} {mu : YoungDiagram}
    (t : Tableau (witnessAttachment b 1).card mu) (a : ℕ)
    (ho : AttachmentOneOddRow mu a) :=
  altWord (attachmentTargetOddColumnGroup t a ho) (rowWord t ∘ attachmentTargetOddMatching t a ho)

theorem attachmentTargetEvenAlternant_original {b : ℕ} {mu : YoungDiagram}
    (t : Tableau (witnessAttachment b 0).card mu) (he : AttachmentEvenRows mu) :
    wordRep _ _ (attachmentTargetEvenMatching t he).symm (polytabloid t) =
      attachmentTargetEvenAlternant t he := by
  funext w
  rw [polytabloid_eq_altWord]
  change altWord (fiberGroup (fun i => (t i).val.2)) (rowWord t)
    (w ∘ (attachmentTargetEvenMatching t he).symm) = _
  exact altWord_fiber_relabel (attachmentTargetEvenMatching t he)
    (fun i => (t i).val.2) (rowWord t) w

theorem attachmentTargetOddAlternant_original {b : ℕ} {mu : YoungDiagram}
    (t : Tableau (witnessAttachment b 1).card mu) (a : ℕ)
    (ho : AttachmentOneOddRow mu a) :
    wordRep _ _ (attachmentTargetOddMatching t a ho).symm (polytabloid t) =
      attachmentTargetOddAlternant t a ho := by
  funext w
  rw [polytabloid_eq_altWord]
  change altWord (fiberGroup (fun i => (t i).val.2)) (rowWord t)
    (w ∘ (attachmentTargetOddMatching t a ho).symm) = _
  exact altWord_fiber_relabel (attachmentTargetOddMatching t a ho)
    (fun i => (t i).val.2) (rowWord t) w

theorem attachmentTargetEvenContraction_original {b : ℕ} {mu : YoungDiagram}
    (t : Tableau (witnessAttachment b 0).card mu) (he : AttachmentEvenRows mu)
    (L : Fin (mu.colLen 0) → Fin 4 → ℂ) :
    dotProduct (wordMap L (attachmentTargetEvenAlternant t he)) (attachmentHTensor b 0) =
      dotProduct (wordMap L (polytabloid t))
        (wordRep _ 4 (attachmentTargetEvenMatching t he) (attachmentHTensor b 0)) := by
  rw [← attachmentTargetEvenAlternant_original]
  have hi : wordMap L (wordRep _ _ (attachmentTargetEvenMatching t he).symm (polytabloid t)) =
      wordRep _ 4 (attachmentTargetEvenMatching t he).symm (wordMap L (polytabloid t)) :=
    (wordMap L).map_action (attachmentTargetEvenMatching t he).symm (polytabloid t)
  rw [hi]
  simpa only [Equiv.Perm.inv_def, Equiv.symm_symm] using
    wordPair_move (attachmentTargetEvenMatching t he).symm
      (wordMap L (polytabloid t)) (attachmentHTensor b 0)

theorem attachmentTargetOddContraction_original {b : ℕ} {mu : YoungDiagram}
    (t : Tableau (witnessAttachment b 1).card mu) (a : ℕ)
    (ho : AttachmentOneOddRow mu a) (L : Fin (mu.colLen 0) → Fin 4 → ℂ) :
    dotProduct (wordMap L (attachmentTargetOddAlternant t a ho)) (attachmentHTensor b 1) =
      dotProduct (wordMap L (polytabloid t))
        (wordRep _ 4 (attachmentTargetOddMatching t a ho) (attachmentHTensor b 1)) := by
  rw [← attachmentTargetOddAlternant_original]
  have hi : wordMap L (wordRep _ _ (attachmentTargetOddMatching t a ho).symm (polytabloid t)) =
      wordRep _ 4 (attachmentTargetOddMatching t a ho).symm (wordMap L (polytabloid t)) :=
    (wordMap L).map_action (attachmentTargetOddMatching t a ho).symm (polytabloid t)
  rw [hi]
  simpa only [Equiv.Perm.inv_def, Equiv.symm_symm] using
    wordPair_move (attachmentTargetOddMatching t a ho).symm
      (wordMap L (polytabloid t)) (attachmentHTensor b 1)

def attachmentTargetOddRowLetter (mu : YoungDiagram) (a : ℕ)
    (ho : AttachmentOneOddRow mu a) : Fin (mu.colLen 0) :=
  ⟨a, by
    have hp : 0 < mu.rowLen a := by have hh := ho.1; omega
    exact YoungDiagram.mem_iff_lt_colLen.mp (YoungDiagram.mem_iff_lt_rowLen.mpr hp)⟩

/-- The unique odd row chooses the singleton covector internally. -/
def attachmentTargetOddLetters {b : ℕ} {mu : YoungDiagram}
    (t : Tableau (witnessAttachment b 1).card mu) (a : ℕ)
    (ho : AttachmentOneOddRow mu a) (ht : mu.colLen 0 ≤ 4) :
    Fin (mu.colLen 0) → Fin 4 → ℂ :=
  attachmentTargetLetters t ht (Fin.castLE ht (attachmentTargetOddRowLetter mu a ho))

theorem attachmentTargetOddLetters_single {b : ℕ} {mu : YoungDiagram}
    (t : Tableau (witnessAttachment b 1).card mu) (a : ℕ)
    (ho : AttachmentOneOddRow mu a) (ht : mu.colLen 0 ≤ 4) (j : Fin 1) :
    attachmentTargetOddLetters t a ho ht
      (rowWord t (attachmentTargetOddMatching t a ho
        (witnessAttachmentColumnOrderFin b 1 (.inr j)))) 0 = attachmentHScale := by
  have hr : rowWord t (attachmentTargetOddMatching t a ho
      (witnessAttachmentColumnOrderFin b 1 (.inr j))) = attachmentTargetOddRowLetter mu a ho := by
    apply Fin.ext
    change (t (attachmentTargetOddMatching t a ho
      (witnessAttachmentColumnOrderFin b 1 (.inr j)))).val.1 = a
    rw [attachmentTargetOddMatching_order]
    exact congrArg Prod.fst (attachmentTargetOddPositions_single t a ho j)
  rw [hr]
  exact attachmentHLettersAt_singleton _

theorem attachmentTargetOddLetters_single_ne_zero {b : ℕ} {mu : YoungDiagram}
    (t : Tableau (witnessAttachment b 1).card mu) (a : ℕ)
    (ho : AttachmentOneOddRow mu a) (ht : mu.colLen 0 ≤ 4) (j : Fin 1) :
    attachmentTargetOddLetters t a ho ht
      (rowWord t (attachmentTargetOddMatching t a ho
        (witnessAttachmentColumnOrderFin b 1 (.inr j)))) 0 ≠ 0 := by
  rw [attachmentTargetOddLetters_single]
  exact attachmentHScale_ne_zero

end
end HSTZ
#print axioms HSTZ.attachmentTargetEvenColumnEquiv
#print axioms HSTZ.attachmentTargetOddColumnEquiv
#print axioms HSTZ.attachmentTargetEvenColumnEquiv_value
#print axioms HSTZ.attachmentTargetOddColumnEquiv_value
#print axioms HSTZ.attachmentTargetEvenAlternant_original
#print axioms HSTZ.attachmentTargetOddAlternant_original
#print axioms HSTZ.attachmentTargetEvenContraction_original
#print axioms HSTZ.attachmentTargetOddContraction_original
#print axioms HSTZ.attachmentTargetOddLetters_single
#print axioms HSTZ.attachmentTargetOddLetters_single_ne_zero
