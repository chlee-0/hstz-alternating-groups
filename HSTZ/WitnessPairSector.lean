import HSTZ.FinsuppAction
import HSTZ.WitnessCorePositionSector
import HSTZ.SpechtTensorWords

/-! The asymmetric common-mask pair-word sector and ordinary induction.
Uses interfaces from OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
Coordinates keep the two original unequal alphabets; labels only index fibers.
Nothing is asserted about a chosen Young target, the full witness or kappa. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped Classical TensorProduct

/-- Common marks select original pair words, without identifying pair letters. -/
def witnessSameMarkedWords (n d e k b : ℕ) :
    Set (PositionWord (Fin n) (Fin d × Fin e)) :=
  {w | ∀ i, witnessRowMarked k b (w.letters i).1.val ↔
    witnessColumnMarked k (w.letters i).2.val}

theorem witnessSameMarkedWords_invariant (n d e k b : ℕ)
    (g : Equiv.Perm (Fin n)) (w : PositionWord (Fin n) (Fin d × Fin e)) :
    g • w∈witnessSameMarkedWords n d e k b ↔ w∈witnessSameMarkedWords n d e k b := by
  change (∀ i, witnessRowMarked k b (w.letters (g⁻¹ i)).1.val ↔
    witnessColumnMarked k (w.letters (g⁻¹ i)).2.val) ↔
    (∀ i, witnessRowMarked k b (w.letters i).1.val ↔
      witnessColumnMarked k (w.letters i).2.val)
  constructor
  · intro hw i
    simpa only [PositionWord.smul_letters,Equiv.Perm.inv_def,
      Equiv.symm_apply_apply] using hw (g i)
  · intro hw i
    exact hw (g⁻¹ i)

/-- All vector coordinates agree with the common-mask projection. -/
theorem encodedPair_witnessMaskFilter (n d e k b : ℕ)
    (f : PositionWord (Fin n) (Fin d × Fin e) →₀ ℂ) :
    encodedPairModelEquiv n d e (coordinateFilter (witnessSameMarkedWords n d e k b) f) =
      witnessMaskProjection n d e k b (encodedPairModelEquiv n d e f) := by
  funext a
  rw [encodedPairModelEquiv_apply,coordinateFilter_apply,witnessMaskProjection_apply,
    encodedPairModelEquiv_apply]
  rfl

def witnessPairLabel {n d e : ℕ} (k b : ℕ)
    (w : PositionWord (Fin n) (Fin d × Fin e)) : PositionWord (Fin n) Bool :=
  PositionWord.mapLetters (fun ab => decide (witnessRowMarked k b ab.1.val)) w

theorem witnessPairLabel_equivariant {n d e : ℕ} (k b : ℕ)
    (g : Equiv.Perm (Fin n)) (w : PositionWord (Fin n) (Fin d × Fin e)) :
    witnessPairLabel k b (g • w)=g • witnessPairLabel k b w := rfl

section Actual
variable (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
  (z : Tableau n (witnessDiagram k b delta hk))

abbrev WitnessPairSpace := PositionWord (Fin n)
    (Fin ((witnessDiagram k b delta hk).transpose.colLen 0) ×
      Fin ((witnessDiagram k b delta hk).colLen 0)) →₀ ℂ

abbrev witnessPairRep : Representation ℂ (Equiv.Perm (Fin n))
    (WitnessPairSpace k b delta hk (n := n)) := finsuppAction ℂ _ _

def witnessPairGenerator : WitnessPairSpace k b delta hk (n := n) :=
  (encodedPairModelEquiv n _ _).symm (witnessMixedWord k b delta hk z)

def witnessPairCut : WitnessPairSpace k b delta hk (n := n) :=
  coordinateFilter (witnessSameMarkedWords n
    ((witnessDiagram k b delta hk).transpose.colLen 0)
    ((witnessDiagram k b delta hk).colLen 0) k b) (witnessPairGenerator k b delta hk z)

def witnessCorePairLabel : PositionWord (Fin n) Bool :=
  ⟨fun i => decide (i∈Set.range (witnessCorePositionEmbedding k b delta hk z))⟩

theorem encodedPair_witnessGenerator :
    encodedPairModelEquiv n _ _ (witnessPairGenerator k b delta hk z) =
      witnessMixedWord k b delta hk z := LinearEquiv.apply_symm_apply _ _

theorem encodedPair_witnessCut :
    encodedPairModelEquiv n _ _ (witnessPairCut k b delta hk z) =
      witnessMaskProjection n _ _ k b (witnessMixedWord k b delta hk z) := by
  rw [witnessPairCut,encodedPair_witnessMaskFilter,encodedPair_witnessGenerator]

/-- The selected vector belongs to its original core-range label fiber. -/
theorem witnessPairCut_sector :
    witnessPairCut k b delta hk z ∈ labelSector (witnessPairLabel k b)
      (witnessCorePairLabel k b delta hk z) := by
  rw [labelSector,Finsupp.mem_supported]
  intro w hw
  have hcoeff : witnessPairCut k b delta hk z w≠0 := Finsupp.mem_support_iff.mp hw
  change witnessPairLabel k b w=witnessCorePairLabel k b delta hk z
  apply PositionWord.ext
  intro i
  have hc : witnessMaskProjection n _ _ k b (witnessMixedWord k b delta hk z)
      (fun j => finProdFinEquiv (w.letters j))≠0 := by
    rw [← encodedPair_witnessCut,encodedPairModelEquiv_apply]
    simpa only [Equiv.symm_apply_apply] using hcoeff
  have hpos := (witness_filtered_core_positions k b delta hk z _ hc i).1
  change decide (witnessRowMarked k b (w.letters i).1.val) =
    decide (i∈Set.range (witnessCorePositionEmbedding k b delta hk z))
  apply decide_eq_decide.mpr
  simpa only [splitLeft,Equiv.symm_apply_apply] using hpos

/-- Equivariant filter image of the original prescribed-vector cyclic space. -/
theorem witnessPairCut_cyclic_image :
    (cyclicSpan (witnessPairRep k b delta hk (n := n))
      (witnessPairGenerator k b delta hk z)).map
      (coordinateFilter (witnessSameMarkedWords n
        ((witnessDiagram k b delta hk).transpose.colLen 0)
        ((witnessDiagram k b delta hk).colLen 0) k b)) =
      cyclicSpan (witnessPairRep k b delta hk (n := n)) (witnessPairCut k b delta hk z) :=
  coordinateFilter_cyclic_image _ (witnessSameMarkedWords_invariant _ _ _ k b) _

abbrev witnessPairOrbitSector := labelOrbitSector (R := ℂ) (G := Equiv.Perm (Fin n))
  (witnessPairLabel (d := (witnessDiagram k b delta hk).transpose.colLen 0)
    (e := (witnessDiagram k b delta hk).colLen 0) k b) (witnessCorePairLabel k b delta hk z)

theorem witnessPairOrbitSector_independent :
    iSupIndep (witnessPairOrbitSector k b delta hk z) := labelOrbitSector_independent _ _

theorem witnessPairOrbitSector_covariant (g : Equiv.Perm (Fin n))
    (i : MulAction.orbit (Equiv.Perm (Fin n)) (witnessCorePairLabel k b delta hk z)) :
    (witnessPairOrbitSector k b delta hk z i).map (witnessPairRep k b delta hk g) ≤
      witnessPairOrbitSector k b delta hk z (g • i) :=
  labelOrbitSector_covariant _ (witnessPairLabel_equivariant k b) _ _ _

theorem witnessPairOrbitRepresentative_spec
    (i : MulAction.orbit (Equiv.Perm (Fin n)) (witnessCorePairLabel k b delta hk z)) :
    labelOrbitRepresentative (witnessCorePairLabel k b delta hk z) i •
      labelOrbitBase (Equiv.Perm (Fin n)) (witnessCorePairLabel k b delta hk z) = i :=
  labelOrbitRepresentative_spec _ _

/-- Ordinary induction over the orbit sector, with all covariance and support
inputs discharged. -/
theorem witnessPairCut_induction_bijective :
    Function.Bijective (sectorInductionMap (witnessPairRep k b delta hk (n := n))
      (labelOrbitBase (Equiv.Perm (Fin n)) (witnessCorePairLabel k b delta hk z))
      (witnessPairCut k b delta hk z)) :=
  labelOrbit_sectorInduction_bijective (witnessPairLabel k b) (witnessPairLabel_equivariant k b)
    (witnessPairCut k b delta hk z) (witnessCorePairLabel k b delta hk z)
    (witnessPairCut_sector k b delta hk z)

abbrev witnessPairLabelStabilizer := MulAction.stabilizer (Equiv.Perm (Fin n))
  (labelOrbitBase (Equiv.Perm (Fin n)) (witnessCorePairLabel k b delta hk z))

/-- The orbit-label stabilizer is the original core-range sector group. -/
theorem witnessPairLabelStabilizer_eq : witnessPairLabelStabilizer k b delta hk z =
    sectorGroup (fun i => i∈Set.range (witnessCorePositionEmbedding k b delta hk z)) := by
  rw [witnessPairLabelStabilizer,labelOrbitBase_stabilizer]
  ext g
  change (g • witnessCorePairLabel k b delta hk z=witnessCorePairLabel k b delta hk z) ↔
    (∀ i, g i∈Set.range (witnessCorePositionEmbedding k b delta hk z) ↔
      i∈Set.range (witnessCorePositionEmbedding k b delta hk z))
  constructor
  · intro hg i
    have he := congrArg (fun w => w.letters (g i)) hg
    change decide (g⁻¹ (g i)∈Set.range (witnessCorePositionEmbedding k b delta hk z)) =
      decide (g i∈Set.range (witnessCorePositionEmbedding k b delta hk z)) at he
    simp only [Equiv.Perm.inv_def, Equiv.symm_apply_apply] at he
    exact (decide_eq_decide.mp he).symm
  · intro hg
    apply PositionWord.ext
    intro i
    change decide (g⁻¹ i∈Set.range (witnessCorePositionEmbedding k b delta hk z)) =
      decide (i∈Set.range (witnessCorePositionEmbedding k b delta hk z))
    apply decide_eq_decide.mpr
    simpa only [Equiv.Perm.inv_def, Equiv.apply_symm_apply] using (hg (g⁻¹ i)).symm

/-- Product of the full factor groups, identified with the label stabilizer. -/
def witnessPairLabelBlockEquiv :
    (Equiv.Perm (Fin (staircase (k-2)).card) ×
      Equiv.Perm (Fin (witnessComplementSize k b delta))) ≃* witnessPairLabelStabilizer k b delta hk z :=
  (witnessCorePositionGroupEquiv k b delta hk z).trans
    (MulEquiv.subgroupCongr (witnessPairLabelStabilizer_eq k b delta hk z).symm)

theorem witnessPairLabelBlockEquiv_val (gh : Equiv.Perm (Fin (staircase (k-2)).card) ×
    Equiv.Perm (Fin (witnessComplementSize k b delta))) :
    (witnessPairLabelBlockEquiv k b delta hk z gh).val =
      sumPermHom (witnessBinaryCut k b delta hk z) gh := rfl
end Actual
end
end HSTZ
#print axioms HSTZ.witnessSameMarkedWords_invariant
#print axioms HSTZ.encodedPair_witnessMaskFilter
#print axioms HSTZ.witnessPairLabel_equivariant
#print axioms HSTZ.encodedPair_witnessGenerator
#print axioms HSTZ.encodedPair_witnessCut
#print axioms HSTZ.witnessPairCut_sector
#print axioms HSTZ.witnessPairCut_cyclic_image
#print axioms HSTZ.witnessPairOrbitSector_independent
#print axioms HSTZ.witnessPairOrbitSector_covariant
#print axioms HSTZ.witnessPairOrbitRepresentative_spec
#print axioms HSTZ.witnessPairCut_induction_bijective
#print axioms HSTZ.witnessPairLabelStabilizer_eq
#print axioms HSTZ.witnessPairLabelBlockEquiv_val
