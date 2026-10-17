import HSTZ.WitnessAttachmentTargetProductSum

/-! Duplicated half-tableau column permutations in the full target group.
Builds on OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
This proves a surviving family, not the converse or global noncancellation. -/
namespace HSTZ
noncomputable section
open OAI.Saxl

def attachmentTargetDiagonal (b delta : ℕ) (h : Equiv.Perm (Fin b)) :
    Equiv.Perm (Fin (witnessAttachment b delta).card) :=
  (witnessAttachmentColumnOrderFin b delta).permCongr
    (Equiv.sumCongr (Equiv.prodCongr h (Equiv.refl (Fin 2))) (Equiv.refl (Fin delta)))

theorem attachmentTargetDiagonal_pair (b delta : ℕ) (h : Equiv.Perm (Fin b))
    (j : Fin b) (s : Fin 2) :
    attachmentTargetDiagonal b delta h (witnessAttachmentColumnOrderFin b delta (.inl (j,s))) =
      witnessAttachmentColumnOrderFin b delta (.inl (h j,s)) := by
  simp [attachmentTargetDiagonal,Equiv.permCongr_apply]

theorem attachmentTargetDiagonal_single (b delta : ℕ) (h : Equiv.Perm (Fin b))
    (j : Fin delta) :
    attachmentTargetDiagonal b delta h (witnessAttachmentColumnOrderFin b delta (.inr j)) =
      witnessAttachmentColumnOrderFin b delta (.inr j) := by
  simp [attachmentTargetDiagonal,Equiv.permCongr_apply]

theorem attachmentTargetDiagonal_symm_pair (b delta : ℕ) (h : Equiv.Perm (Fin b))
    (j : Fin b) (s : Fin 2) :
    (attachmentTargetDiagonal b delta h).symm
      (witnessAttachmentColumnOrderFin b delta (.inl (j,s))) =
      witnessAttachmentColumnOrderFin b delta (.inl (h.symm j,s)) := by
  apply (attachmentTargetDiagonal b delta h).injective
  rw [Equiv.apply_symm_apply,attachmentTargetDiagonal_pair,Equiv.apply_symm_apply]

theorem attachmentTargetDiagonal_symm_single (b delta : ℕ) (h : Equiv.Perm (Fin b))
    (j : Fin delta) :
    (attachmentTargetDiagonal b delta h).symm
      (witnessAttachmentColumnOrderFin b delta (.inr j)) =
      witnessAttachmentColumnOrderFin b delta (.inr j) := by
  apply (attachmentTargetDiagonal b delta h).injective
  rw [Equiv.apply_symm_apply,attachmentTargetDiagonal_single]

theorem attachmentTargetDiagonal_injective (b delta : ℕ) :
    Function.Injective (attachmentTargetDiagonal b delta) := by
  intro h h' he
  apply Equiv.ext
  intro j
  have hh := congrArg (fun e : Equiv.Perm (Fin (witnessAttachment b delta).card) =>
    e (witnessAttachmentColumnOrderFin b delta (.inl (j,0)))) he
  rw [attachmentTargetDiagonal_pair,attachmentTargetDiagonal_pair] at hh
  exact congrArg Prod.fst (Sum.inl.inj ((witnessAttachmentColumnOrderFin b delta).injective hh))

theorem attachmentTargetDiagonal_sign (b delta : ℕ) (h : Equiv.Perm (Fin b)) :
    signC (attachmentTargetDiagonal b delta h) = 1 := by
  have hp : Equiv.prodCongr h (Equiv.refl (Fin 2)) =
      Equiv.prodCongrLeft (fun _ : Fin 2 => h) := by
    apply Equiv.ext
    intro p
    rfl
  simp only [signC_def,attachmentTargetDiagonal,Equiv.Perm.sign_permCongr,
    Equiv.Perm.sign_sumCongr,hp,Equiv.Perm.sign_prodCongrLeft,Fin.prod_univ_two,
    Equiv.Perm.sign_refl,mul_one]
  simpa only [signC_def,Units.val_mul,Int.cast_mul] using signC_mul_self h

def attachmentTargetEvenDiagonal {b : ℕ} {mu : YoungDiagram}
    (t : Tableau (witnessAttachment b 0).card mu) (he : AttachmentEvenRows mu)
    (h : columnGroup (attachmentTargetEvenHalfTableau t he)) :
    attachmentTargetEvenColumnGroup t he :=
  ⟨attachmentTargetDiagonal b 0 h.val, by
    intro i
    obtain ⟨p,rfl⟩ := (witnessAttachmentColumnOrderFin b 0).surjective i
    cases p with
    | inl p =>
      change (t (attachmentTargetEvenMatching t he
        (attachmentTargetDiagonal b 0 h.val
          (witnessAttachmentColumnOrderFin b 0 (.inl p))))).val.2 =
        (t (attachmentTargetEvenMatching t he
          (witnessAttachmentColumnOrderFin b 0 (.inl p)))).val.2
      rw [attachmentTargetDiagonal_pair,attachmentTargetEvenMatching_order,
        attachmentTargetEvenMatching_order,attachmentTargetEvenPositions_pair,
        attachmentTargetEvenPositions_pair]
      exact congrArg (fun c : ℕ => 2*c+p.2.val) (h.property p.1)
    | inr j =>
      exact Fin.elim0 j⟩

theorem attachmentTargetEvenDiagonal_matches {b : ℕ} {mu : YoungDiagram}
    (t : Tableau (witnessAttachment b 0).card mu) (he : AttachmentEvenRows mu)
    (h : columnGroup (attachmentTargetEvenHalfTableau t he)) :
    attachmentTargetEvenPairMatches t he (attachmentTargetEvenDiagonal t he h) := by
  intro j
  apply Fin.ext
  change (t (attachmentTargetEvenMatching t he
    ((attachmentTargetDiagonal b 0 h.val).symm
      (witnessAttachmentColumnOrderFin b 0 (.inl (j,0)))))).val.1 =
    (t (attachmentTargetEvenMatching t he
    ((attachmentTargetDiagonal b 0 h.val).symm
      (witnessAttachmentColumnOrderFin b 0 (.inl (j,1)))))).val.1
  rw [attachmentTargetDiagonal_symm_pair,attachmentTargetDiagonal_symm_pair,
    attachmentTargetEvenMatching_order,attachmentTargetEvenMatching_order,
    attachmentTargetEvenPositions_pair,attachmentTargetEvenPositions_pair]

def attachmentTargetOddDiagonal {b : ℕ} {mu : YoungDiagram}
    (t : Tableau (witnessAttachment b 1).card mu) (a : ℕ) (ho : AttachmentOneOddRow mu a)
    (h : columnGroup (attachmentTargetOddHalfTableau t a ho)) :
    attachmentTargetOddColumnGroup t a ho :=
  ⟨attachmentTargetDiagonal b 1 h.val, by
    intro i
    obtain ⟨p,rfl⟩ := (witnessAttachmentColumnOrderFin b 1).surjective i
    cases p with
    | inl p =>
      change (t (attachmentTargetOddMatching t a ho
        (attachmentTargetDiagonal b 1 h.val
          (witnessAttachmentColumnOrderFin b 1 (.inl p))))).val.2 =
        (t (attachmentTargetOddMatching t a ho
          (witnessAttachmentColumnOrderFin b 1 (.inl p)))).val.2
      rw [attachmentTargetDiagonal_pair,attachmentTargetOddMatching_order,
        attachmentTargetOddMatching_order,attachmentTargetOddPositions_pair,
        attachmentTargetOddPositions_pair]
      exact congrArg (fun c : ℕ => 2*c+p.2.val) (h.property p.1)
    | inr j =>
      rw [attachmentTargetDiagonal_single]⟩

theorem attachmentTargetOddDiagonal_matches {b : ℕ} {mu : YoungDiagram}
    (t : Tableau (witnessAttachment b 1).card mu) (a : ℕ) (ho : AttachmentOneOddRow mu a)
    (h : columnGroup (attachmentTargetOddHalfTableau t a ho)) :
    attachmentTargetOddPairMatches t a ho (attachmentTargetOddDiagonal t a ho h) := by
  intro j
  apply Fin.ext
  change (t (attachmentTargetOddMatching t a ho
    ((attachmentTargetDiagonal b 1 h.val).symm
      (witnessAttachmentColumnOrderFin b 1 (.inl (j,0)))))).val.1 =
    (t (attachmentTargetOddMatching t a ho
    ((attachmentTargetDiagonal b 1 h.val).symm
      (witnessAttachmentColumnOrderFin b 1 (.inl (j,1)))))).val.1
  rw [attachmentTargetDiagonal_symm_pair,attachmentTargetDiagonal_symm_pair,
    attachmentTargetOddMatching_order,attachmentTargetOddMatching_order,
    attachmentTargetOddPositions_pair,attachmentTargetOddPositions_pair]

theorem attachmentTargetEvenDiagonal_injective {b : ℕ} {mu : YoungDiagram}
    (t : Tableau (witnessAttachment b 0).card mu) (he : AttachmentEvenRows mu) :
    Function.Injective (attachmentTargetEvenDiagonal t he) := by
  intro h h' hh
  apply Subtype.ext
  exact attachmentTargetDiagonal_injective b 0 (congrArg Subtype.val hh)

theorem attachmentTargetOddDiagonal_injective {b : ℕ} {mu : YoungDiagram}
    (t : Tableau (witnessAttachment b 1).card mu) (a : ℕ) (ho : AttachmentOneOddRow mu a) :
    Function.Injective (attachmentTargetOddDiagonal t a ho) := by
  intro h h' hh
  apply Subtype.ext
  exact attachmentTargetDiagonal_injective b 1 (congrArg Subtype.val hh)

theorem attachmentTargetEvenDiagonal_contraction {b : ℕ} {mu : YoungDiagram}
    (t : Tableau (witnessAttachment b 0).card mu) (he : AttachmentEvenRows mu)
    (ht : mu.colLen 0 ≤ 4) (a : Fin 4)
    (h : columnGroup (attachmentTargetEvenHalfTableau t he)) :
    dotProduct (wordMap (attachmentTargetLetters t ht a) (Pi.single
      ((rowWord t ∘ attachmentTargetEvenMatching t he) ∘
        (attachmentTargetEvenDiagonal t he h).val.symm) 1)) (attachmentHTensor b 0) = 1 := by
  rw [attachmentTargetEven_term,if_pos (attachmentTargetEvenDiagonal_matches t he h)]

theorem attachmentTargetOddDiagonal_contraction {b : ℕ} {mu : YoungDiagram}
    (t : Tableau (witnessAttachment b 1).card mu) (a : ℕ)
    (ho : AttachmentOneOddRow mu a) (ht : mu.colLen 0 ≤ 4)
    (h : columnGroup (attachmentTargetOddHalfTableau t a ho)) :
    dotProduct (wordMap (attachmentTargetOddLetters t a ho ht) (Pi.single
      ((rowWord t ∘ attachmentTargetOddMatching t a ho) ∘
        (attachmentTargetOddDiagonal t a ho h).val.symm) 1)) (attachmentHTensor b 1) =
      attachmentHScale := by
  rw [attachmentTargetOdd_term,if_pos (attachmentTargetOddDiagonal_matches t a ho h),one_mul]
  change attachmentTargetOddLetters t a ho ht
    (rowWord t (attachmentTargetOddMatching t a ho
      ((attachmentTargetDiagonal b 1 h.val).symm
        (witnessAttachmentColumnOrderFin b 1 (.inr 0))))) 0 = _
  rw [attachmentTargetDiagonal_symm_single,attachmentTargetOddLetters_single]

end
end HSTZ
#print axioms HSTZ.attachmentTargetDiagonal_pair
#print axioms HSTZ.attachmentTargetDiagonal_single
#print axioms HSTZ.attachmentTargetDiagonal_symm_pair
#print axioms HSTZ.attachmentTargetDiagonal_symm_single
#print axioms HSTZ.attachmentTargetDiagonal_injective
#print axioms HSTZ.attachmentTargetDiagonal_sign
#print axioms HSTZ.attachmentTargetEvenDiagonal
#print axioms HSTZ.attachmentTargetOddDiagonal
#print axioms HSTZ.attachmentTargetEvenDiagonal_matches
#print axioms HSTZ.attachmentTargetOddDiagonal_matches
#print axioms HSTZ.attachmentTargetEvenDiagonal_injective
#print axioms HSTZ.attachmentTargetOddDiagonal_injective
#print axioms HSTZ.attachmentTargetEvenDiagonal_contraction
#print axioms HSTZ.attachmentTargetOddDiagonal_contraction
