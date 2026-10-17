import HSTZ.OneBandWords
import HSTZ.OneRowTensor

/-! One-row source embedding into the prescribed one-band cyclic space.
Injectivity is proved by coordinate recovery, not by a dimension count. -/
namespace HSTZ
open OAI.Saxl

abbrev OneBandCarrier (h : ℕ) :=
  ↥(cyclicSpan (wordRep _ _) (bandPairWord h 1))

noncomputable def oneBandRepresentation (h : ℕ) :
    Representation ℂ (Equiv.Perm (Fin (bandSize h 1))) (OneBandCarrier h) :=
  (cyclicSubrepresentation (wordRep _ _) (bandPairWord h 1)).toRepresentation

theorem oneBand_cyclic_line (h : ℕ) :
    cyclicSpan (wordRep _ _) (bandPairWord h 1) =
      Submodule.span ℂ {bandPairWord h 1} := by
  simp [cyclicSpan, oneBand_pair_fixed]

/-- Sends `x` to its row-word coordinate times the band generator. -/
noncomputable def oneBandSourceMap (h : ℕ) {mu : YoungDiagram}
    (u : Tableau (bandSize h 1) mu) (hmu : mu.colLen 0 ≤ 1) :
    Representation.IntertwiningMap (spechtRep u) (oneBandRepresentation h) where
  toLinearMap := {
    toFun x := x.val (rowWord u) •
      (⟨bandPairWord h 1, generator_mem_cyclicSpan (wordRep _ _) _⟩ : OneBandCarrier h)
    map_add' x y := by simp [add_smul]
    map_smul' a x := by simp [smul_smul] }
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (spechtRep u g x).val (rowWord u) • bandPairWord h 1 =
      wordRep _ _ g (x.val (rowWord u) • bandPairWord h 1)
    rw [oneRow_specht_fixed u hmu, map_smul, oneBand_pair_fixed]

theorem oneBandSourceMap_generator (h : ℕ) {mu : YoungDiagram}
    (u : Tableau (bandSize h 1) mu) (hmu : mu.colLen 0 ≤ 1) :
    (oneBandSourceMap h u hmu
      ⟨polytabloid u, mem_cyclic _ _⟩).val = bandPairWord h 1 := by
  change polytabloid u (rowWord u) • bandPairWord h 1 = _
  rw [polytabloid_rowWord, one_smul]

theorem oneBandSourceMap_injective (h : ℕ) {mu : YoungDiagram}
    (u : Tableau (bandSize h 1) mu) (hmu : mu.colLen 0 ≤ 1) :
    Function.Injective (oneBandSourceMap h u hmu) := by
  intro x y he
  have hc := congrArg (fun z : OneBandCarrier h =>
    z.val (mergeWords (fun _ => oneBandLetter h) (fun _ => oneBandLetter h))) he
  change x.val (rowWord u) * bandPairWord h 1 _ =
    y.val (rowWord u) * bandPairWord h 1 _ at hc
  rw [oneBand_pair_coefficient] at hc
  simp only [mul_one] at hc
  letI : Subsingleton (Fin (mu.colLen 0)) := Fin.subsingleton_iff_le_one.mpr hmu
  apply Subtype.ext
  funext w
  have hw : w = rowWord u := Subsingleton.elim _ _
  rw [hw]
  exact hc

end HSTZ
#print axioms HSTZ.oneBand_cyclic_line
#print axioms HSTZ.oneBandSourceMap_generator
#print axioms HSTZ.oneBandSourceMap_injective
