import HSTZ.FinsuppAction
import HSTZ.SpechtTensorWords
import OAI.RepresentationTheory.Saxl.CoordinateSector

/-! The native staircase high cut in paired-word coordinates.
The selector keeps pair letters; the label only indexes supported sectors.
No constituent embedding or asymmetric witness support is assumed. -/
namespace HSTZ
open scoped Classical TensorProduct

/-- The two high/low colors must agree at every position. -/
def sameHighWords (n d e s : ℕ) : Set (PositionWord (Fin n) (Fin d × Fin e)) :=
  {w | ∀ i, s ≤ (w.letters i).1.val ↔ s ≤ (w.letters i).2.val}

theorem sameHighWords_invariant (n d e s : ℕ) (g : Equiv.Perm (Fin n))
    (w : PositionWord (Fin n) (Fin d × Fin e)) :
    g • w ∈ sameHighWords n d e s ↔ w ∈ sameHighWords n d e s := by
  change (∀ i, s ≤ (w.letters (g⁻¹ i)).1.val ↔ s ≤ (w.letters (g⁻¹ i)).2.val) ↔
    (∀ i, s ≤ (w.letters i).1.val ↔ s ≤ (w.letters i).2.val)
  constructor
  · intro hw i
    simpa only [Equiv.Perm.inv_def, Equiv.symm_apply_apply] using hw (g i)
  · intro hw i
    exact hw (g⁻¹ i)

/-- Entire coordinate projections agree, not only one coefficient. -/
theorem encodedPair_sameHighFilter (n d e s : ℕ)
    (f : PositionWord (Fin n) (Fin d × Fin e) →₀ ℂ) :
    encodedPairModelEquiv n d e (coordinateFilter (sameHighWords n d e s) f) =
      OAI.Saxl.sameHighProjection n d e s (encodedPairModelEquiv n d e f) := by
  funext a
  by_cases ha : ∀ i, s ≤ (a i).val / e ↔ s ≤ (a i).val % e
  <;> simp [encodedPairModelEquiv_apply,coordinateFilter_apply,sameHighWords,
    OAI.Saxl.sameHighProjection,OAI.Saxl.splitLeft,OAI.Saxl.splitRight,ha]

/-- The native staircase generator in the original pair-word basis. -/
noncomputable def staircasePairGenerator (m : ℕ) :
    PositionWord (Fin (OAI.Saxl.staircase m).card)
      (Fin ((OAI.Saxl.staircase m).colLen 0) × Fin ((OAI.Saxl.staircase m).colLen 0)) →₀ ℂ :=
  pairWordTensorEquiv (wordPolytabloid (OAI.Saxl.stairRowTableau m) ⊗ₜ[ℂ]
    wordPolytabloid (OAI.Saxl.stairTableau m))

theorem encodedPair_staircaseGenerator (m : ℕ) :
    encodedPairModelEquiv _ _ _ (staircasePairGenerator m) = OAI.Saxl.staircaseWord m := by
  rw [staircasePairGenerator,encodedPair_tensor_tmul]
  simp only [wordPolytabloid,LinearEquiv.apply_symm_apply,OAI.Saxl.staircaseWord]

noncomputable def staircasePairCut (h s : ℕ) :=
  coordinateFilter (sameHighWords (OAI.Saxl.staircase (h+s)).card
    ((OAI.Saxl.staircase (h+s)).colLen 0) ((OAI.Saxl.staircase (h+s)).colLen 0) s)
    (staircasePairGenerator (h+s))

theorem encodedPair_staircaseCut (h s : ℕ) :
    encodedPairModelEquiv _ _ _ (staircasePairCut h s) =
      OAI.Saxl.sameHighProjection _ _ _ s (OAI.Saxl.staircaseWord (h+s)) := by
  rw [staircasePairCut,encodedPair_sameHighFilter,encodedPair_staircaseGenerator]

theorem staircasePairCut_ne_zero (h s : ℕ) : staircasePairCut h s ≠ 0 := by
  intro hz
  apply OAI.Saxl.staircase_projected_ne_zero h s
  rw [← encodedPair_staircaseCut,hz,map_zero]

/-- Layer factorization, with the native shuffle signs cancelled. -/
theorem staircasePairCut_layers (h s : ℕ) :
    staircasePairCut h s = pairWordTensorEquiv
      ((wordModelEquiv _ _).symm (OAI.Saxl.cutRowWord h s) ⊗ₜ[ℂ]
        (wordModelEquiv _ _).symm (OAI.Saxl.cutColumnWord h s)) := by
  apply (encodedPairModelEquiv _ _ _).injective
  rw [encodedPair_staircaseCut,OAI.Saxl.staircase_cut_layers,encodedPair_tensor_tmul]
  simp only [LinearEquiv.apply_symm_apply]

/-- Label remembers the high positions; coefficients remain indexed by pair words. -/
def highPairLabel {n d e : ℕ} (s : ℕ)
    (w : PositionWord (Fin n) (Fin d × Fin e)) : PositionWord (Fin n) Bool :=
  PositionWord.mapLetters (fun ab => decide (s ≤ ab.1.val)) w

theorem highPairLabel_equivariant {n d e : ℕ} (s : ℕ)
    (g : Equiv.Perm (Fin n)) (w : PositionWord (Fin n) (Fin d × Fin e)) :
    highPairLabel s (g • w) = g • highPairLabel s w := rfl

noncomputable def staircaseHighLabel (h s : ℕ) :
    PositionWord (Fin (OAI.Saxl.staircase (h+s)).card) Bool :=
  ⟨fun i => decide (OAI.Saxl.stairHigh h s i)⟩

/-- The filtered vector is supported in a single label fiber. -/
theorem staircasePairCut_sector (h s : ℕ) :
    staircasePairCut h s ∈ labelSector (highPairLabel s) (staircaseHighLabel h s) := by
  rw [labelSector,Finsupp.mem_supported]
  intro w hw
  have hcoeff : staircasePairCut h s w ≠ 0 := Finsupp.mem_support_iff.mp hw
  change highPairLabel s w = staircaseHighLabel h s
  apply PositionWord.ext
  intro i
  have hc : OAI.Saxl.sameHighProjection _ _ _ s (OAI.Saxl.staircaseWord (h+s))
      (fun j => finProdFinEquiv (w.letters j)) ≠ 0 := by
    rw [← encodedPair_staircaseCut,encodedPairModelEquiv_apply]
    simpa only [Equiv.symm_apply_apply] using hcoeff
  have hpos := OAI.Saxl.staircase_projected_high_positions h s _ hc i
  change decide (s ≤ (w.letters i).1.val) = decide (OAI.Saxl.stairHigh h s i)
  have he : s ≤ (w.letters i).1.val ↔ OAI.Saxl.stairHigh h s i := by
    simpa only [OAI.Saxl.splitLeft,Equiv.symm_apply_apply,OAI.Saxl.stairHigh] using hpos
  by_cases hi : s ≤ (w.letters i).1.val
  · simp only [hi,he.mp hi,decide_true]
  · simp only [hi,mt he.mpr hi,decide_false]

/-- This cut is the equivariant image of the original prescribed orbit. -/
theorem staircasePairCut_cyclic_image (h s : ℕ) :
    (cyclicSpan (finsuppAction ℂ
      (Equiv.Perm (Fin (OAI.Saxl.staircase (h+s)).card)) _) (staircasePairGenerator (h+s))).map
      (coordinateFilter (sameHighWords (OAI.Saxl.staircase (h+s)).card
        ((OAI.Saxl.staircase (h+s)).colLen 0) ((OAI.Saxl.staircase (h+s)).colLen 0) s)) =
    cyclicSpan (finsuppAction ℂ
      (Equiv.Perm (Fin (OAI.Saxl.staircase (h+s)).card)) _) (staircasePairCut h s) :=
  coordinateFilter_cyclic_image _ (sameHighWords_invariant _ _ _ s) _

/-- Ordinary induction of the stabilizer cyclic space, with all sector
hypotheses discharged by the concrete selected generator. -/
theorem staircasePairCut_induction_bijective (h s : ℕ) :
    Function.Bijective (sectorInductionMap
      (finsuppAction ℂ (Equiv.Perm (Fin (OAI.Saxl.staircase (h+s)).card)) _)
      (labelOrbitBase (Equiv.Perm (Fin (OAI.Saxl.staircase (h+s)).card))
        (staircaseHighLabel h s)) (staircasePairCut h s)) :=
  labelOrbit_sectorInduction_bijective (highPairLabel s) (highPairLabel_equivariant s)
    (staircasePairCut h s) (staircaseHighLabel h s) (staircasePairCut_sector h s)

end HSTZ
#print axioms OAI.Saxl.high_positions_rigidity
#print axioms OAI.Saxl.staircase_projected_ne_zero
#print axioms OAI.Saxl.altWord_sector
#print axioms OAI.Saxl.staircase_cut_layers
#print axioms HSTZ.encodedPair_sameHighFilter
#print axioms HSTZ.staircasePairCut_ne_zero
#print axioms HSTZ.staircasePairCut_layers
#print axioms HSTZ.staircasePairCut_sector
#print axioms HSTZ.staircasePairCut_induction_bijective

#print axioms HSTZ.staircasePairCut_cyclic_image
