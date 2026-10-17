import HSTZ.ContainedTargetFlags

/-! Pullback of the full column group along the witness positions, and invariance
of the reserved-prefix flag under column permutations. The reserved-row condition is
an explicit hypothesis. Uses `fiberRelabel` from OpenAI's `math` repository
(commit adc7f1241, Apache-2.0). -/
namespace HSTZ
noncomputable section
open OAI.Saxl

section Witness
variable {h e : ℕ → ℕ} (hh : Antitone h) (he : Antitone e)
    {d m t : ℕ} (k b delta : ℕ) (htm : t ≤ m)
    (hroom : ∀ c < t, d+e c≤h c) (hclear : t*d+4≤witnessPathSize k)
    (hcapacity : witnessPathSize k≤prefixSum (capacity h d) m)
    (hsize : prefixSum e m=2*b+delta)
    (s : Tableau (witnessComplementSize k b delta)
      (containedWhole h e hh he d (witnessPathSize k) m))

def containedWitnessColumnGroup :=
  fiberGroup (fun i => (s (containedWitnessPositions hh he k b delta htm hroom hclear hcapacity hsize s i)).val.2)

def containedWitnessColumnEquiv :
    containedWitnessColumnGroup hh he k b delta htm hroom hclear hcapacity hsize s ≃ columnGroup s :=
  fiberRelabel (containedWitnessPositions hh he k b delta htm hroom hclear hcapacity hsize s)
    (fun i => (s i).val.2)

theorem containedWitnessColumnEquiv_value
    (g : containedWitnessColumnGroup hh he k b delta htm hroom hclear hcapacity hsize s)
    (i : Fin (witnessComplementSize k b delta)) :
    (containedWitnessColumnEquiv hh he k b delta htm hroom hclear hcapacity hsize s g).val i =
      containedWitnessPositions hh he k b delta htm hroom hclear hcapacity hsize s
        (g.val ((containedWitnessPositions hh he k b delta htm hroom hclear hcapacity hsize s).symm i)) := rfl

theorem containedWitnessColumnEquiv_inverse
    (g : columnGroup s) (i : Fin (witnessComplementSize k b delta)) :
    ((containedWitnessColumnEquiv hh he k b delta htm hroom hclear hcapacity hsize s).symm g).val.symm i =
      (containedWitnessPositions hh he k b delta htm hroom hclear hcapacity hsize s).symm
        (g.val.symm (containedWitnessPositions hh he k b delta htm hroom hclear hcapacity hsize s i)) := rfl

theorem containedWitnessPolytabloid_reindex :
    wordRep _ _ (containedWitnessPositions hh he k b delta htm hroom hclear hcapacity hsize s).symm
      (polytabloid s) =
      altWord (containedWitnessColumnGroup hh he k b delta htm hroom hclear hcapacity hsize s)
        (rowWord s ∘ containedWitnessPositions hh he k b delta htm hroom hclear hcapacity hsize s) := by
  funext w
  rw [polytabloid_eq_altWord]
  change altWord (fiberGroup (fun i => (s i).val.2)) (rowWord s)
    (w ∘ (containedWitnessPositions hh he k b delta htm hroom hclear hcapacity hsize s).symm) = _
  exact altWord_fiber_relabel _ _ _ w
end Witness

section Flag
variable {h e : ℕ → ℕ} (hh : Antitone h) (he : Antitone e)
    {d K m t n : ℕ} (htm : t ≤ m) (hroom : ∀ c < t, d+e c≤h c)
    (hclear : t*d+4≤K) (hcapacity : K≤prefixSum (capacity h d) m)
    (s : Tableau n (containedWhole h e hh he d K m))

/-- A column permutation preserves the flag "row below `d`" once the inverse images
of the reserved cleared slots have low target rows; finite injectivity supplies the
converse direction. -/
theorem containedColumn_reserved_flag (hzero : ∀ c, t ≤ c → e c=0)
    (g : columnGroup s)
    (hp : ∀ p : Fin t × Fin d,
      (rowWord s (g.val.symm (containedFactorPositions hh he htm hroom hclear hcapacity s
        (.inl ((containedPathPrefixOrder hh htm hroom hclear hcapacity).symm
          (containedReservedCell hh htm hroom hclear p)))))).val < d)
    (i : Fin n) : (rowWord s (g.val.symm i)).val < d ↔ (rowWord s i).val < d := by
  classical
  let S : Set (Fin n) := {j | (s j).val.2 < t ∧ (s j).val.1 < d}
  have hc (j : Fin n) : (s (g.val.symm j)).val.2=(s j).val.2 := by
    exact (g⁻¹).property j
  have hm : Set.MapsTo g.val.symm S S := by
    intro j hj
    change (s j).val.2 < t ∧ (s j).val.1 < d at hj
    let p : Fin t × Fin d := (⟨(s j).val.2,hj.1⟩,⟨(s j).val.1,hj.2⟩)
    have hjp : containedFactorPositions hh he htm hroom hclear hcapacity s
        (.inl ((containedPathPrefixOrder hh htm hroom hclear hcapacity).symm
          (containedReservedCell hh htm hroom hclear p)))=j := by
      apply s.injective
      apply Subtype.ext
      rw [containedFactorPositions_reserved]
    change (s (g.val.symm j)).val.2 < t ∧ (s (g.val.symm j)).val.1 < d
    exact ⟨by rw [hc]; exact hj.1, by simpa only [hjp,rowWord] using hp p⟩
  have hb := ((Set.toFinite S).injOn_iff_bijOn_of_mapsTo hm).mp g.val.symm.injective.injOn
  have hs (j : Fin n) : g.val.symm j ∈ S ↔ j ∈ S := by
    constructor
    · intro hj
      obtain ⟨v,hv,heq⟩ := hb.surjOn hj
      have hvj : v=j := g.val.symm.injective heq
      simpa only [hvj] using hv
    · exact fun hj => hm hj
  by_cases hci : (s i).val.2 < t
  · have hh := hs i
    change (_ ∧ _) ↔ (_ ∧ _) at hh
    rw [hc] at hh
    simpa only [hci,true_and,rowWord] using hh
  · have hl (j : Fin n) (hj : t ≤ (s j).val.2) : (s j).val.1 < d := by
      have hr := ((mem_fromColumns _ _ _ _ _).mp (s j).property).2
      change (s j).val.1 < greedy h d K (s j).val.2+e (s j).val.2 at hr
      rw [hzero _ hj,add_zero] at hr
      exact hr.trans_le (greedy_le_depth h d K _)
    exact iff_of_true (hl _ (by rw [hc]; omega)) (hl i (by omega))
end Flag
end
end HSTZ
#print axioms HSTZ.containedWitnessColumnEquiv
#print axioms HSTZ.containedWitnessColumnEquiv_value
#print axioms HSTZ.containedWitnessColumnEquiv_inverse
#print axioms HSTZ.containedWitnessPolytabloid_reindex
#print axioms HSTZ.containedColumn_reserved_flag
