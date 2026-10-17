import HSTZ.ContainedWitnessPlacement

/-! The capacity row flag, keeping the original order of the target and witness
data. Reuses geometry from OpenAI's `math` repository (commit adc7f1241, Apache-2.0). -/
namespace HSTZ
noncomputable section
open OAI.Saxl

theorem containedPath_row_lt {h : ℕ → ℕ} (hh : Antitone h) (d K m : ℕ)
    (x : (containedPath h hh d K m).cells) : x.val.1 < d := by
  have hr := ((mem_fromColumns _ _ _ _ _).mp x.property).2
  exact hr.trans_le (greedy_le_depth h d K x.val.2)

theorem containedAttachment_col_lt {e : ℕ → ℕ} (he : Antitone e) (m t : ℕ)
    (hzero : ∀ c, t ≤ c → e c=0) (x : (containedAttachment e he m).cells) :
    x.val.2 < t := by
  have hr := ((mem_fromColumns _ _ _ _ _).mp x.property).2
  change x.val.1 < e x.val.2 at hr
  by_contra hc
  have hz := hzero x.val.2 (by omega)
  omega

section Positions
variable {h e : ℕ → ℕ} (hh : Antitone h) (he : Antitone e)
    {d K m t : ℕ} (htm : t ≤ m) (hroom : ∀ c < t, d+e c≤h c)
    (hclear : t*d+4≤K) (hcapacity : K≤prefixSum (capacity h d) m)
    {n : ℕ} (s : Tableau n (containedWhole h e hh he d K m))

theorem containedFactorPositions_path_flag (i : Fin K) :
    (rowWord s (containedFactorPositions hh he htm hroom hclear hcapacity s (.inl i))).val < d := by
  change (s _).val.1 < d
  rw [containedFactorPositions_path]
  exact containedPath_row_lt hh d K m _

theorem containedFactorPositions_attachment_flag
    (hzero : ∀ c, t ≤ c → e c=0) (i : Fin (containedAttachment e he m).card) :
    d ≤ (rowWord s (containedFactorPositions hh he htm hroom hclear hcapacity s (.inr i))).val := by
  have hc := containedAttachment_col_lt he m t hzero
    (canonicalTableau (containedAttachment e he m) rfl i)
  change d ≤ (s _).val.1
  rw [containedFactorPositions_attachment_reserved hh he htm hroom hclear hcapacity s i hc]
  exact Nat.le_add_right _ _
end Positions

section Witness
variable {h e : ℕ → ℕ} (hh : Antitone h) (he : Antitone e)
    {d m t : ℕ} (k b delta : ℕ) (htm : t ≤ m)
    (hroom : ∀ c < t, d+e c≤h c) (hclear : t*d+4≤witnessPathSize k)
    (hcapacity : witnessPathSize k≤prefixSum (capacity h d) m)
    (hsize : prefixSum e m=2*b+delta)
    (s : Tableau (witnessComplementSize k b delta)
      (containedWhole h e hh he d (witnessPathSize k) m))

theorem containedWitnessPositions_attachment (i : Fin (witnessAttachment b delta).card) :
    containedWitnessPositions hh he k b delta htm hroom hclear hcapacity hsize s
      (witnessComplementOrder k b delta (.inr i))=
        containedFactorPositions hh he htm hroom hclear hcapacity s
          (.inr (finCongr (containedAttachment_witness_card he b delta m hsize) i)) := by
  simp only [containedWitnessPositions,Equiv.trans_apply,Equiv.symm_apply_apply,
    Equiv.sumCongr_apply,Sum.map_inr]

theorem containedWitnessPositions_flag (hzero : ∀ c, t ≤ c → e c=0)
    (i : Fin (witnessComplementSize k b delta)) :
    (rowWord s (containedWitnessPositions hh he k b delta htm hroom hclear hcapacity hsize s i)).val < d ↔
      witnessComplementPathMask k b delta i := by
  obtain ⟨j,rfl⟩ := (witnessComplementOrder k b delta).surjective i
  cases j with
  | inl j =>
    rw [containedWitnessPositions_path]
    have hr := containedFactorPositions_path_flag hh he htm hroom hclear hcapacity s j
    simpa [witnessComplementPathMask] using hr
  | inr j =>
    rw [containedWitnessPositions_attachment]
    have hr := containedFactorPositions_attachment_flag hh he htm hroom hclear hcapacity s hzero
      (finCongr (containedAttachment_witness_card he b delta m hsize) j)
    simpa only [witnessComplementPathMask, Equiv.symm_apply_apply, Sum.isLeft_inr,
      Bool.false_eq_true, iff_false, finCongr_apply] using (not_lt.mpr hr)
end Witness
end
end HSTZ
#print axioms HSTZ.containedPath_row_lt
#print axioms HSTZ.containedAttachment_col_lt
#print axioms HSTZ.containedFactorPositions_path_flag
#print axioms HSTZ.containedFactorPositions_attachment_flag
#print axioms HSTZ.containedWitnessPositions_attachment
#print axioms HSTZ.containedWitnessPositions_flag
