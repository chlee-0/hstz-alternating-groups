import HSTZ.ContainedTargetPrefix

/-! Placement of the capacity target in the original tableau and the literal
witness path order. Uses interfaces adapted from OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
No common flag, vanishing of unmatched full-source terms or nonvanishing of the
full sum is assumed. -/
namespace HSTZ
noncomputable section
open OAI.Saxl

/-- Two-factor positions, preserving the reserved prefix and the
consecutive-column tail. The attachment uses its canonical cells. -/
def containedFactorPositions {h e : ℕ → ℕ} (hh : Antitone h) (he : Antitone e)
    {d K m t : ℕ} (htm : t ≤ m) (hroom : ∀ c < t, d+e c≤h c)
    (hclear : t*d+4≤K) (hcapacity : K≤prefixSum (capacity h d) m) {n : ℕ}
    (s : Tableau n (containedWhole h e hh he d K m)) :
    (Fin K ⊕ Fin (containedAttachment e he m).card) ≃ Fin n :=
  ((Equiv.sumCongr (containedPathPrefixOrder hh htm hroom hclear hcapacity)
    (canonicalTableau (containedAttachment e he m) rfl)).trans
      (containedCellSplit h e hh he d K m)).trans s.symm

theorem containedFactorPositions_path {h e : ℕ → ℕ} (hh : Antitone h) (he : Antitone e)
    {d K m t : ℕ} (htm : t ≤ m) (hroom : ∀ c < t, d+e c≤h c)
    (hclear : t*d+4≤K) (hcapacity : K≤prefixSum (capacity h d) m) {n : ℕ}
    (s : Tableau n (containedWhole h e hh he d K m)) (i : Fin K) :
    (s (containedFactorPositions hh he htm hroom hclear hcapacity s (.inl i))).val=
      (containedPathPrefixOrder hh htm hroom hclear hcapacity i).val := by
  simp only [containedFactorPositions,Equiv.trans_apply,Equiv.sumCongr_apply,
    Sum.map_inl,Equiv.apply_symm_apply]
  rfl

theorem containedFactorPositions_attachment {h e : ℕ → ℕ} (hh : Antitone h) (he : Antitone e)
    {d K m t : ℕ} (htm : t ≤ m) (hroom : ∀ c < t, d+e c≤h c)
    (hclear : t*d+4≤K) (hcapacity : K≤prefixSum (capacity h d) m) {n : ℕ}
    (s : Tableau n (containedWhole h e hh he d K m)) (i : Fin (containedAttachment e he m).card) :
    (s (containedFactorPositions hh he htm hroom hclear hcapacity s (.inr i))).val=
      (greedy h d K (canonicalTableau (containedAttachment e he m) rfl i).val.2+
        (canonicalTableau (containedAttachment e he m) rfl i).val.1,
        (canonicalTableau (containedAttachment e he m) rfl i).val.2) := by
  simp only [containedFactorPositions,Equiv.trans_apply,Equiv.sumCongr_apply,
    Sum.map_inr,Equiv.apply_symm_apply]
  rfl

/-- Every reserved long-column path cell occupies its original target
position, with literal row and column coordinates. -/
theorem containedFactorPositions_reserved {h e : ℕ → ℕ} (hh : Antitone h) (he : Antitone e)
    {d K m t : ℕ} (htm : t ≤ m) (hroom : ∀ c < t, d+e c≤h c)
    (hclear : t*d+4≤K) (hcapacity : K≤prefixSum (capacity h d) m) {n : ℕ}
    (s : Tableau n (containedWhole h e hh he d K m)) (p : Fin t × Fin d) :
    (s (containedFactorPositions hh he htm hroom hclear hcapacity s
      (.inl ((containedPathPrefixOrder hh htm hroom hclear hcapacity).symm
        (containedReservedCell hh htm hroom hclear p))))).val=(p.2.val,p.1.val) := by
  rw [containedFactorPositions_path,Equiv.apply_symm_apply]
  rfl

/-- In the first `t` columns the attachment translation is exactly `d`. -/
theorem containedFactorPositions_attachment_reserved {h e : ℕ → ℕ} (hh : Antitone h) (he : Antitone e)
    {d K m t : ℕ} (htm : t ≤ m) (hroom : ∀ c < t, d+e c≤h c)
    (hclear : t*d+4≤K) (hcapacity : K≤prefixSum (capacity h d) m) {n : ℕ}
    (s : Tableau n (containedWhole h e hh he d K m)) (i : Fin (containedAttachment e he m).card)
    (hc : (canonicalTableau (containedAttachment e he m) rfl i).val.2 < t) :
    (s (containedFactorPositions hh he htm hroom hclear hcapacity s (.inr i))).val=
      (d+(canonicalTableau (containedAttachment e he m) rfl i).val.1,
        (canonicalTableau (containedAttachment e he m) rfl i).val.2) := by
  rw [containedFactorPositions_attachment,greedy_eq_depth hroom (by omega) hc]

/-- The reserved target index equals the literal cleared prefix in the witness
path order, preserving `c*d+r`. -/
theorem containedReservedIndex_witness {h e : ℕ → ℕ} (hh : Antitone h)
    {d m t : ℕ} (k : ℕ) (htm : t ≤ m)
    (hroom : ∀ c < t, d+e c≤h c) (hclear : t*d+4≤witnessPathSize k)
    (hcapacity : witnessPathSize k≤prefixSum (capacity h d) m) (p : Fin t × Fin d) :
    (containedPathPrefixOrder hh htm hroom hclear hcapacity).symm
      (containedReservedCell hh htm hroom hclear p)=
      witnessClearedPathPrefix k (t*d) hclear (finProdFinEquiv p) := by
  apply Fin.ext
  rw [containedPathPrefixOrder_reserved]
  change p.1.val*d+p.2.val=p.2.val+d*p.1.val
  rw [Nat.mul_comm d p.1.val]
  omega

/-- Reserved cells of the capacity target use low-low source letters before
selection, for every witness tableau. -/
theorem containedReservedSource_low {h e : ℕ → ℕ} (hh : Antitone h)
    {d m t : ℕ} (k b delta : ℕ) (hk : 5 ≤ k) (htm : t ≤ m)
    (hroom : ∀ c < t, d+e c≤h c) (hclear : t*d+4≤witnessPathSize k)
    (hcapacity : witnessPathSize k≤prefixSum (capacity h d) m) {n : ℕ}
    (s : Tableau n (witnessDiagram k b delta hk))
    (w : Fin (witnessComplementSize k b delta) → Fin
      ((witnessDiagram k b delta hk).transpose.colLen 0*(witnessDiagram k b delta hk).colLen 0))
    (hw : witnessComplementPairWord k b delta hk s w≠0) (p : Fin t × Fin d) :
    let j := (containedPathPrefixOrder hh htm hroom hclear hcapacity).symm
      (containedReservedCell hh htm hroom hclear p)
    (splitLeft w (witnessComplementOrder k b delta (.inl j))).val<2 ∧
      (splitRight w (witnessComplementOrder k b delta (.inl j))).val<2 := by
  dsimp only
  rw [containedReservedIndex_witness hh k htm hroom hclear hcapacity p]
  exact witnessComplementPairWord_cleared_prefix k b delta (t*d) hk hclear s w hw _

/-- The attachment size comes from the capacity height sum. -/
theorem containedAttachment_witness_card {e : ℕ → ℕ} (he : Antitone e)
    (b delta m : ℕ) (hsize : prefixSum e m=2*b+delta) :
    (witnessAttachment b delta).card=(containedAttachment e he m).card := by
  rw [witnessAttachment_card,fromColumns_card,hsize]

/-- The full complement position permutation into the contained target, with
the exact attachment size. -/
def containedWitnessPositions {h e : ℕ → ℕ} (hh : Antitone h) (he : Antitone e)
    {d m t : ℕ} (k b delta : ℕ) (htm : t ≤ m)
    (hroom : ∀ c < t, d+e c≤h c) (hclear : t*d+4≤witnessPathSize k)
    (hcapacity : witnessPathSize k≤prefixSum (capacity h d) m)
    (hsize : prefixSum e m=2*b+delta)
    (s : Tableau (witnessComplementSize k b delta)
      (containedWhole h e hh he d (witnessPathSize k) m)) :
    Equiv.Perm (Fin (witnessComplementSize k b delta)) :=
  (witnessComplementOrder k b delta).symm.trans
    ((Equiv.sumCongr (Equiv.refl _) (finCongr (containedAttachment_witness_card he b delta m hsize))).trans
      (containedFactorPositions hh he htm hroom hclear hcapacity s))

theorem containedWitnessPositions_path {h e : ℕ → ℕ} (hh : Antitone h) (he : Antitone e)
    {d m t : ℕ} (k b delta : ℕ) (htm : t ≤ m)
    (hroom : ∀ c < t, d+e c≤h c) (hclear : t*d+4≤witnessPathSize k)
    (hcapacity : witnessPathSize k≤prefixSum (capacity h d) m)
    (hsize : prefixSum e m=2*b+delta)
    (s : Tableau (witnessComplementSize k b delta)
      (containedWhole h e hh he d (witnessPathSize k) m)) (i : Fin (witnessPathSize k)) :
    containedWitnessPositions hh he k b delta htm hroom hclear hcapacity hsize s
      (witnessComplementOrder k b delta (.inl i))=
        containedFactorPositions hh he htm hroom hclear hcapacity s (.inl i) := by
  simp only [containedWitnessPositions,Equiv.trans_apply,Equiv.symm_apply_apply,
    Equiv.sumCongr_apply,Sum.map_inl,Equiv.refl_apply]

end
end HSTZ
#print axioms HSTZ.containedFactorPositions
#print axioms HSTZ.containedFactorPositions_path
#print axioms HSTZ.containedFactorPositions_attachment
#print axioms HSTZ.containedFactorPositions_reserved
#print axioms HSTZ.containedFactorPositions_attachment_reserved
#print axioms HSTZ.containedReservedIndex_witness
#print axioms HSTZ.containedReservedSource_low

#print axioms HSTZ.containedAttachment_witness_card
#print axioms HSTZ.containedWitnessPositions
#print axioms HSTZ.containedWitnessPositions_path
