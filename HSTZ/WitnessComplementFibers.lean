import HSTZ.WitnessComplementCoordinates

/-! Complement columns never mix path and attachment cells, while row fibers can
cross. Uses interfaces from OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
These are full subgroup statements, not a support or contraction theorem. -/
namespace HSTZ
noncomputable section
open OAI.Saxl

theorem witness_path_attachment_column_ne (k b delta : ℕ) (hk : 5 ≤ k)
    (i : Fin (witnessPathSize k)) (x : (witnessAttachment b delta).cells) :
    (witnessPathPositionCell k b delta hk i).val.2≠
      (witnessAttachmentCell k b delta hk x).val.2 := by
  intro he
  change (if i.val/2=k-1 then k+b+delta-1 else i.val/2)=k-1+x.val.2 at he
  have hi : i.val<2*((k-2)+1)+1 := i.isLt
  have hdiv : i.val/2≤k-1 := by omega
  have hc : x.val.2<b+delta := by
    rcases (mem_witnessAttachment b delta _ _).mp x.property with ⟨_,h⟩ | ⟨_,h⟩
    · exact h
    · exact lt_of_lt_of_le h (Nat.le_add_right b delta)
  by_cases h : i.val/2=k-1
  · rw [if_pos h] at he
    omega
  · rw [if_neg h] at he
    omega

def witnessComplementPathMask (k b delta : ℕ)
    (i : Fin (witnessComplementSize k b delta)) : Prop :=
  ((witnessComplementOrder k b delta).symm i).isLeft=true

theorem witness_complement_column_sector (k b delta : ℕ) (hk : 5 ≤ k) :
    witnessComplementColumnGroup k b delta hk ≤
      sectorGroup (witnessComplementPathMask k b delta) := by
  have hsep (i j : Fin (witnessComplementSize k b delta))
      (he : (witnessComplementCell k b delta hk i).val.2=
        (witnessComplementCell k b delta hk j).val.2) :
      witnessComplementPathMask k b delta i ↔ witnessComplementPathMask k b delta j := by
    obtain ⟨a,rfl⟩ := (witnessComplementOrder k b delta).surjective i
    obtain ⟨b',rfl⟩ := (witnessComplementOrder k b delta).surjective j
    cases a with
    | inl a =>
      cases b' with
      | inl b' => simp [witnessComplementPathMask]
      | inr b' =>
        have hn := witness_path_attachment_column_ne k b delta hk a (witnessCanonicalAttachment b delta b')
        simp only [witnessComplementCell_path,witnessComplementCell_attachment] at he
        exact (hn he).elim
    | inr a =>
      cases b' with
      | inl b' =>
        have hn := witness_path_attachment_column_ne k b delta hk b' (witnessCanonicalAttachment b delta a)
        simp only [witnessComplementCell_path,witnessComplementCell_attachment] at he
        exact (hn he.symm).elim
      | inr b' => simp [witnessComplementPathMask]
  intro g hg
  change ∀ i, witnessComplementPathMask k b delta (g i) ↔ witnessComplementPathMask k b delta i
  change ∀ i, (witnessComplementCell k b delta hk (g i)).val.2=
    (witnessComplementCell k b delta hk i).val.2 at hg
  exact fun i => hsep (g i) i (hg i)

theorem witness_complement_row_cross_swap (k b delta : ℕ) (hk : 5 ≤ k)
    (p : Fin (witnessPathSize k)) (a : Fin (witnessAttachment b delta).card)
    (he : (witnessPathPositionCell k b delta hk p).val.1=
      (witnessCanonicalAttachment b delta a).val.1) :
    Equiv.swap (witnessComplementOrder k b delta (.inl p))
      (witnessComplementOrder k b delta (.inr a)) ∈ witnessComplementRowGroup k b delta hk := by
  change ∀ i, (witnessComplementCell k b delta hk
    (Equiv.swap (witnessComplementOrder k b delta (.inl p))
      (witnessComplementOrder k b delta (.inr a)) i)).val.1=
    (witnessComplementCell k b delta hk i).val.1
  intro i
  have ht : (witnessComplementCell k b delta hk (witnessComplementOrder k b delta (.inl p))).val.1=
      (witnessComplementCell k b delta hk (witnessComplementOrder k b delta (.inr a))).val.1 := by
    simpa only [witnessComplementCell_path,witnessComplementCell_attachment,witnessAttachmentCell_value,witnessCanonicalAttachment] using he
  rw [Equiv.swap_apply_def]
  split_ifs <;> subst_vars <;> first | exact ht | exact ht.symm | rfl

theorem witness_complement_cross_swap_not_sector (k b delta : ℕ)
    (p : Fin (witnessPathSize k)) (a : Fin (witnessAttachment b delta).card) :
    Equiv.swap (witnessComplementOrder k b delta (.inl p))
      (witnessComplementOrder k b delta (.inr a)) ∉
        sectorGroup (witnessComplementPathMask k b delta) := by
  intro hg
  have hh := hg (witnessComplementOrder k b delta (.inl p))
  simp [Equiv.swap_apply_left,witnessComplementPathMask] at hh

end
end HSTZ
#print axioms HSTZ.witness_path_attachment_column_ne
#print axioms HSTZ.witness_complement_column_sector
#print axioms HSTZ.witness_complement_row_cross_swap
#print axioms HSTZ.witness_complement_cross_swap_not_sector
