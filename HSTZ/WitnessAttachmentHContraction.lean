import HSTZ.WitnessAttachmentHLetters

/-! The H and singleton contractions and their Specht consumer. Reuses `wordMap`
and `hom_to_cyclic_of_pair` from OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
Parity matching and the nonzero polytabloid contraction are separate obligations,
not proved in this file. -/
namespace HSTZ
noncomputable section
open OAI.Saxl

theorem attachmentPaperH_contraction {d : ℕ} (L : Fin d → Fin 4 → ℂ)
    (r s : Fin d) :
    dotProduct (wordMap L (Pi.single (![r,s] : Fin 2 → Fin d) 1)) attachmentPaperH =
      L r 0 * L s 3 + L r 3 * L s 0 - L r 1 * L s 2 - L r 2 * L s 1 := by
  classical
  simp [attachmentPaperH, dotProduct_sub, dotProduct_add,
    wordMap_single, Fin.prod_univ_succ]

theorem attachmentHForm_bilinear (L : Fin 4 → Fin 4 → ℂ) (r s : Fin 4) :
    (∑ x : Fin 4, ∑ y : Fin 4, L r x * attachmentHForm x y * L s y) =
      L r 0 * L s 3 + L r 3 * L s 0 - L r 1 * L s 2 - L r 2 * L s 1 := by
  simp [attachmentHForm, Fin.sum_univ_succ]
  ring

theorem attachmentHLettersAt_pair_contraction (a r s : Fin 4) :
    dotProduct (wordMap (attachmentHLettersAt a)
      (Pi.single (![r,s] : Fin 2 → Fin 4) 1)) attachmentPaperH =
      if r = s then 1 else 0 := by
  erw [attachmentPaperH_contraction]
  exact (attachmentHForm_bilinear (fun i j => attachmentHLettersAt a i j) r s).symm.trans
    (attachmentHLettersAt_orthonormal a r s)

theorem attachmentHLettersAt_singleton_contraction (a : Fin 4) :
    dotProduct (wordMap (attachmentHLettersAt a)
      (Pi.single (fun _ : Fin 1 => a) 1))
      (Pi.single (fun _ : Fin 1 => (0 : Fin 4)) 1) = attachmentHScale := by
  classical
  rw [dotProduct_single_one]
  erw [wordMap_single]
  simp [attachmentHLettersAt_singleton]

theorem attachmentHLettersAt_singleton_contraction_ne_zero (a : Fin 4) :
    dotProduct (wordMap (attachmentHLettersAt a)
      (Pi.single (fun _ : Fin 1 => a) 1))
      (Pi.single (fun _ : Fin 1 => (0 : Fin 4)) 1) ≠ 0 := by
  rw [attachmentHLettersAt_singleton_contraction]
  exact attachmentHScale_ne_zero

/-- Covectors on the original target alphabet, not on a new tableau. -/
def attachmentTargetLetters {n : ℕ} {mu : YoungDiagram} (_t : Tableau n mu)
    (ht : mu.colLen 0 ≤ 4) (a : Fin 4) : Fin (mu.colLen 0) → Fin 4 → ℂ :=
  fun r => attachmentHLettersAt a (Fin.castLE ht r)

theorem attachmentTargetLetters_pair {n : ℕ} {mu : YoungDiagram}
    (t : Tableau n mu) (ht : mu.colLen 0 ≤ 4) (a : Fin 4)
    (r s : Fin (mu.colLen 0)) :
    dotProduct (wordMap (attachmentTargetLetters t ht a)
      (Pi.single (![r,s] : Fin 2 → Fin (mu.colLen 0)) 1)) attachmentPaperH =
      if r = s then 1 else 0 := by
  rw [attachmentPaperH_contraction]
  have he := attachmentHLettersAt_pair_contraction a (Fin.castLE ht r) (Fin.castLE ht s)
  erw [attachmentPaperH_contraction] at he
  simpa [attachmentTargetLetters] using he

theorem attachmentTargetLetters_singleton {n : ℕ} {mu : YoungDiagram}
    (t : Tableau n mu) (ht : mu.colLen 0 ≤ 4) (r : Fin (mu.colLen 0)) :
    attachmentTargetLetters t ht (Fin.castLE ht r) r 0 ≠ 0 := by
  change attachmentHLettersAt (Fin.castLE ht r) (Fin.castLE ht r) 0 ≠ 0
  rw [attachmentHLettersAt_singleton]
  exact attachmentHScale_ne_zero

theorem attachmentPaperH_real : star attachmentPaperH = attachmentPaperH := by
  classical
  funext w
  simp [attachmentPaperH, Pi.single_apply]

theorem attachmentHPower_real (b : ℕ) : star (attachmentHPower b) = attachmentHPower b := by
  classical
  induction b with
  | zero => funext w; simp [attachmentHPower, Pi.single_apply]
  | succ b ih =>
    funext w
    change star ((attachmentHPower b) (leftWord (attachmentAppendColumn b) w) *
      attachmentPaperH (rightWord (attachmentAppendColumn b) w)) = _
    rw [star_mul]
    rw [show star ((attachmentHPower b) (leftWord (attachmentAppendColumn b) w)) =
        (attachmentHPower b) (leftWord (attachmentAppendColumn b) w) from congrFun ih _,
      show star (attachmentPaperH (rightWord (attachmentAppendColumn b) w)) =
        attachmentPaperH (rightWord (attachmentAppendColumn b) w) from
          congrFun attachmentPaperH_real _]
    exact mul_comm _ _

theorem attachmentHTensor_real (b delta : ℕ) :
    star (attachmentHTensor b delta) = attachmentHTensor b delta := by
  classical
  funext w
  change star ((attachmentHPower b) (leftWord (attachmentColumnSplit b delta) w) *
    (Pi.single (fun _ : Fin delta => (0 : Fin 4)) (1:ℂ) : WordSpace delta 4)
      (rightWord (attachmentColumnSplit b delta) w)) = _
  rw [star_mul]
  have hr := congrFun (attachmentHPower_real b) (leftWord (attachmentColumnSplit b delta) w)
  simp only [Pi.star_apply] at hr
  rw [hr]
  simp [attachmentHTensor, positionProduct, Pi.single_apply, mul_comm]

/-- Conditional consumer: the nonzero full column alternation is a hypothesis. It
must be proved from parity and target matching, not from H being nonzero. -/
theorem attachmentHTensor_contraction_embedding (b delta : ℕ) {mu : YoungDiagram}
    (t : Tableau (witnessAttachment b delta).card mu)
    (L : Fin (mu.colLen 0) → Fin 4 → ℂ)
    (hnz : dotProduct (wordMap L (polytabloid t)) (attachmentHTensor b delta) ≠ 0) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (attachmentHCyclic b delta).toRepresentation, Function.Injective F := by
  obtain ⟨F,hF⟩ := hom_to_cyclic_of_pair L (spechtSub t)
    ⟨polytabloid t, mem_cyclic _ _⟩ (attachmentHTensor b delta)
    (attachmentHTensor_real b delta) hnz
  change Representation.IntertwiningMap (spechtRep t)
    (attachmentHCyclic b delta).toRepresentation at F
  letI := specht_irreducible t
  exact ⟨F,(Representation.IsIrreducible.injective_or_eq_zero F).resolve_right hF⟩

end
end HSTZ
#print axioms HSTZ.attachmentPaperH_contraction
#print axioms HSTZ.attachmentHLettersAt_pair_contraction
#print axioms HSTZ.attachmentHLettersAt_singleton_contraction_ne_zero
#print axioms HSTZ.attachmentTargetLetters_pair
#print axioms HSTZ.attachmentTargetLetters_singleton
#print axioms HSTZ.attachmentPaperH_real
#print axioms HSTZ.attachmentHPower_real
#print axioms HSTZ.attachmentHTensor_real
#print axioms HSTZ.attachmentHTensor_contraction_embedding
