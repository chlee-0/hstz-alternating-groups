import HSTZ.YoungDiagramCompat
import HSTZ.WitnessSelectedNonmixed

/-! Full complement letters before low-sector selection.
Reuses fiber, rotation and alternant interfaces from OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
No path/attachment tensor or changed endpoint base is used. -/
namespace HSTZ
noncomputable section
open OAI.Saxl

private theorem alt_supported_word {n d : ℕ} (G : Subgroup (Equiv.Perm (Fin n)))
    (a w : Fin n → Fin d) (hw : altWord G a w≠0) :
    ∃ g : G, w=a ∘ (g.val.symm : Equiv.Perm (Fin n)) := by
  classical
  letI := Fintype.ofFinite G
  by_contra hn
  push_neg at hn
  apply hw
  unfold altWord
  rw [Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro g hg
  rw [wordRep_single]
  change signC g.val * (Pi.single (M := fun _ => ℂ) (a ∘ g.val.symm) (1:ℂ) w)=0
  simp only [Pi.single_apply,if_neg (hn g),mul_zero]

/-- The original row>=2 fibers contain no attachment or exceptional endpoint. -/
theorem witnessComplementRowBase_low_of_row_ge_two (k b delta : ℕ) (hk : 5 ≤ k)
    (i : Fin (witnessComplementSize k b delta))
    (hi : 2≤(witnessComplementCell k b delta hk i).val.1) :
    (witnessComplementRowBase k b delta hk i).val<2 := by
  obtain ⟨s,rfl⟩ := (witnessComplementOrder k b delta).surjective i
  cases s with
  | inl j =>
    rw [witnessComplementCell_path] at hi
    have hn : j≠witnessPathEndpoint k := by
      intro he
      subst j
      rw [witnessPathPositionCell_endpoint] at hi
      change 2≤0 at hi
      omega
    rw [witnessComplementRowBase_path,witnessPathRowBase_nonendpoint k b delta hk j hn]
    split_ifs <;> omega
  | inr j =>
    rw [witnessComplementCell_attachment] at hi
    change 2≤(witnessCanonicalAttachment b delta j).val.1 at hi
    have hr : (witnessCanonicalAttachment b delta j).val.1<2 :=
      lt_of_lt_of_le (YoungDiagram.mem_iff_lt_colLen.mp (witnessCanonicalAttachment b delta j).property)
        (((witnessAttachment b delta).colLen_anti 0 _ (Nat.zero_le _)).trans
          (witnessAttachment_rows b delta))
    omega

/-- All original full complement column letters are low, including the attachment. -/
theorem witnessComplementColumnBase_low (k b delta : ℕ) (hk : 5 ≤ k)
    (i : Fin (witnessComplementSize k b delta)) :
    (witnessComplementColumnBase k b delta hk i).val<2 := by
  obtain ⟨s,rfl⟩ := (witnessComplementOrder k b delta).surjective i
  cases s with
  | inl j =>
    rw [witnessComplementColumnBase_path,witnessPathColumnBase_all]
    split_ifs <;> omega
  | inr j =>
    change (witnessColumnRotation k b delta hk (witnessComplementCell k b delta hk
      (witnessComplementOrder k b delta (.inr j)))).val.1<2
    rw [witnessComplementCell_attachment]
    have hz : k-2-(k-1+(witnessCanonicalAttachment b delta j).val.2)=0 := by omega
    change (if (witnessCanonicalAttachment b delta j).val.1<k-2-(k-1+_)
      then (witnessCanonicalAttachment b delta j).val.1+2
      else (witnessCanonicalAttachment b delta j).val.1-(k-2-(k-1+_)))<2
    rw [hz]
    simp only [Nat.not_lt_zero,if_false,Nat.sub_zero]
    have hr : (witnessCanonicalAttachment b delta j).val.1<2 :=
      lt_of_lt_of_le (YoungDiagram.mem_iff_lt_colLen.mp (witnessCanonicalAttachment b delta j).property)
        (((witnessAttachment b delta).colLen_anti 0 _ (Nat.zero_le _)).trans
          (witnessAttachment_rows b delta))
    omega

/-- A supported coefficient of the original full row alternant stays low on every
row>=2 position, despite full row cross-swaps elsewhere. -/
theorem witnessComplementRowWord_low_of_row_ge_two (k b delta : ℕ) (hk : 5 ≤ k)
    {n : ℕ} (t : Tableau n (witnessDiagram k b delta hk))
    (a : Fin (witnessComplementSize k b delta) → Fin
      ((witnessDiagram k b delta hk).transpose.colLen 0))
    (ha : witnessComplementRowWord k b delta hk t a≠0)
    (i : Fin (witnessComplementSize k b delta))
    (hi : 2≤(witnessComplementCell k b delta hk i).val.1) : (a i).val<2 := by
  rw [witness_complement_row_alternant] at ha
  obtain ⟨g,hg⟩ := alt_supported_word _ _ a ha
  rw [hg]
  apply witnessComplementRowBase_low_of_row_ge_two
  have he := (g⁻¹).property i
  change (witnessComplementCell k b delta hk (g.val.symm i)).val.1=
    (witnessComplementCell k b delta hk i).val.1 at he
  rw [he]
  exact hi

theorem witnessComplementColumnWord_low (k b delta : ℕ) (hk : 5 ≤ k)
    {n : ℕ} (t : Tableau n (witnessDiagram k b delta hk))
    (a : Fin (witnessComplementSize k b delta) → Fin ((witnessDiagram k b delta hk).colLen 0))
    (ha : witnessComplementColumnWord k b delta hk t a≠0) : ∀ i, (a i).val<2 := by
  rw [witness_complement_column_alternant] at ha
  obtain ⟨g,hg⟩ := alt_supported_word _ _ a ha
  rw [hg]
  intro i
  exact witnessComplementColumnBase_low k b delta hk _

end
end HSTZ
#print axioms HSTZ.witnessComplementRowBase_low_of_row_ge_two
#print axioms HSTZ.witnessComplementColumnBase_low
#print axioms HSTZ.witnessComplementRowWord_low_of_row_ge_two
#print axioms HSTZ.witnessComplementColumnWord_low
