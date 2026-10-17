import HSTZ.WitnessPreselectionLetters

/-! Prefix clearance before the low-sector projection, in the original path order.
Reuses geometry/`wordTensor` interfaces from OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
The base is unchanged, and no independent unprojected attachment tensor is assumed. -/
namespace HSTZ
noncomputable section
open OAI.Saxl

/-- Path coordinate criterion: a position lies in row at least 2 exactly when it is
not among the last four positions. -/
theorem witnessPath_row_ge_two_iff_clearance (k b delta : ℕ) (hk : 5 ≤ k)
    (i : Fin (witnessPathSize k)) :
    2≤(witnessPathPositionCell k b delta hk i).val.1 ↔ i.val+4<witnessPathSize k := by
  rw [witnessPathPositionCell_coordinates]
  change 2≤(k-2)+1-(i.val+1)/2 ↔ i.val+4<2*((k-2)+1)+1
  have hi : i.val<2*((k-2)+1)+1 := i.isLt
  omega

/-- The unprojected pair coefficients have low columns everywhere and low rows at
every position in row at least 2, for every tableau of the witness. -/
theorem witnessComplementPairWord_preselection_letters (k b delta : ℕ) (hk : 5 ≤ k)
    {n : ℕ} (t : Tableau n (witnessDiagram k b delta hk))
    (w : Fin (witnessComplementSize k b delta) → Fin
      ((witnessDiagram k b delta hk).transpose.colLen 0 * (witnessDiagram k b delta hk).colLen 0))
    (hw : witnessComplementPairWord k b delta hk t w≠0) :
    ∀ i, (splitRight w i).val<2 ∧
      (2≤(witnessComplementCell k b delta hk i).val.1 → (splitLeft w i).val<2) := by
  unfold witnessComplementPairWord at hw
  rw [wordTensor_tmul] at hw
  have hr := left_ne_zero_of_mul hw
  have hc := right_ne_zero_of_mul hw
  intro i
  exact ⟨witnessComplementColumnWord_low k b delta hk t _ hc i,
    witnessComplementRowWord_low_of_row_ge_two k b delta hk t _ hr i⟩

/-- The canonical prefix inclusion, retaining literal source indices. -/
def witnessClearedPathPrefix (k m : ℕ) (hm : m+4≤witnessPathSize k) : Fin m ↪ Fin (witnessPathSize k) where
  toFun i := ⟨i.val,by have hi := i.isLt; omega⟩
  inj' := by
    intro i j he
    have hv := congrArg (fun z : Fin (witnessPathSize k) => z.val) he
    exact Fin.ext (show i.val=j.val from hv)

/-- Complement and original tableau cell coordinates, not an enumeration choice. -/
theorem witnessClearedPathPrefix_original_row (k b delta m : ℕ) (hk : 5 ≤ k)
    (hm : m+4≤witnessPathSize k) {n : ℕ} (t : Tableau n (witnessDiagram k b delta hk))
    (i : Fin m) :
    2≤(t ((witnessBinaryCut k b delta hk t).symm
      (.inr (witnessComplementOrder k b delta (.inl (witnessClearedPathPrefix k m hm i)))))).val.1 := by
  rw [witnessComplementCell_original,witnessComplementCell_path]
  apply (witnessPath_row_ge_two_iff_clearance k b delta hk _).mpr
  change i.val+4<witnessPathSize k
  have hi := i.isLt
  omega

/-- The selected capacity prefix is low-low before selection when K - m ≥ 4. -/
theorem witnessComplementPairWord_cleared_prefix (k b delta m : ℕ) (hk : 5 ≤ k)
    (hm : m+4≤witnessPathSize k) {n : ℕ} (t : Tableau n (witnessDiagram k b delta hk))
    (w : Fin (witnessComplementSize k b delta) → Fin
      ((witnessDiagram k b delta hk).transpose.colLen 0 * (witnessDiagram k b delta hk).colLen 0))
    (hw : witnessComplementPairWord k b delta hk t w≠0) (i : Fin m) :
    (splitLeft w (witnessComplementOrder k b delta (.inl (witnessClearedPathPrefix k m hm i)))).val<2 ∧
    (splitRight w (witnessComplementOrder k b delta (.inl (witnessClearedPathPrefix k m hm i)))).val<2 := by
  have hs := witnessComplementPairWord_preselection_letters k b delta hk t w hw
    (witnessComplementOrder k b delta (.inl (witnessClearedPathPrefix k m hm i)))
  refine ⟨hs.2 ?_,hs.1⟩
  rw [witnessComplementCell_path]
  apply (witnessPath_row_ge_two_iff_clearance k b delta hk _).mpr
  change i.val+4<witnessPathSize k
  have hi := i.isLt
  omega

/-- Capacity clearance at the chosen t is used directly, without replacing it by d*q. -/
theorem witnessComplementPairWord_chosen_prefix (k b delta d tcount : ℕ) (hk : 5 ≤ k)
    (hclear : d*tcount+4≤witnessPathSize k) {n : ℕ}
    (t : Tableau n (witnessDiagram k b delta hk))
    (w : Fin (witnessComplementSize k b delta) → Fin
      ((witnessDiagram k b delta hk).transpose.colLen 0 * (witnessDiagram k b delta hk).colLen 0))
    (hw : witnessComplementPairWord k b delta hk t w≠0) (i : Fin (d*tcount)) :
    (splitLeft w (witnessComplementOrder k b delta (.inl
      (witnessClearedPathPrefix k (d*tcount) hclear i)))).val<2 ∧
    (splitRight w (witnessComplementOrder k b delta (.inl
      (witnessClearedPathPrefix k (d*tcount) hclear i)))).val<2 :=
  witnessComplementPairWord_cleared_prefix k b delta (d*tcount) hk hclear t w hw i

end
end HSTZ
#print axioms HSTZ.witnessPath_row_ge_two_iff_clearance
#print axioms HSTZ.witnessComplementPairWord_preselection_letters
#print axioms HSTZ.witnessClearedPathPrefix
#print axioms HSTZ.witnessClearedPathPrefix_original_row
#print axioms HSTZ.witnessComplementPairWord_cleared_prefix
#print axioms HSTZ.witnessComplementPairWord_chosen_prefix
