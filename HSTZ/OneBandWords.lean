import HSTZ.OneBandGeometry
import HSTZ.StaircaseBlock

/-! Full-coordinate one-band layers and a fixed nonzero pair generator. -/
namespace HSTZ
open OAI.Saxl
open scoped TensorProduct

noncomputable def oneBandLetter (h : ℕ) : Fin ((staircase (h+1)).colLen 0) :=
  ⟨0, by simp [staircase_colLen]⟩

theorem oneBand_rowLetters (h : ℕ) :
    rightWord (cutPositions h 1)
      (rowWord (stairRowTableau (h+1)) ∘ (rotateRowPositions h 1 : Equiv.Perm _)) =
      fun _ => oneBandLetter h := by
  funext i
  apply Fin.ext
  have hh := rotateRow_high h 1 (bandTableau h 1 i)
  have hd := oneBand_antidiagonal h i
  have hn : ¬ 1 ≤ (rotateRow h 1 (bandTableau h 1 i)).val.2 := by
    intro he
    have hl := hh.mp he
    omega
  simp only [rightWord, Function.comp_apply, rowWord, stairRowTableau,
    rotateRowPositions, Equiv.trans_apply, Equiv.apply_symm_apply, staircaseSwap]
  change (rotateRow h 1 (bandTableau h 1 i)).val.2 = 0
  omega

theorem oneBand_columnLetters (h : ℕ) :
    rightWord (cutPositions h 1)
      (rowWord (stairTableau (h+1)) ∘ (rotateColumnPositions h 1 : Equiv.Perm _)) =
      fun _ => oneBandLetter h := by
  funext i
  apply Fin.ext
  have hh := rotateColumn_high h 1 (bandTableau h 1 i)
  have hd := oneBand_antidiagonal h i
  have hn : ¬ 1 ≤ (rotateColumn h 1 (bandTableau h 1 i)).val.1 := by
    intro he
    have hl := hh.mp he
    omega
  simp only [rightWord, Function.comp_apply, rowWord,
    rotateColumnPositions, Equiv.trans_apply, Equiv.apply_symm_apply]
  change (rotateColumn h 1 (bandTableau h 1 i)).val.1 = 0
  omega

theorem altWord_bot {n d : ℕ} (a : Fin n → Fin d) :
    altWord (⊥ : Subgroup (Equiv.Perm (Fin n))) a = Pi.single a (1 : ℂ) := by
  classical
  letI : Fintype (⊥ : Subgroup (Equiv.Perm (Fin n))) := Fintype.ofFinite _
  unfold altWord
  rw [Finset.sum_eq_single (1 : (⊥ : Subgroup (Equiv.Perm (Fin n))))]
  · simp [signC]
  · intro g _ hne
    exact False.elim (hne (Subsingleton.elim _ _))
  · intro hn
    exact False.elim (hn (Finset.mem_univ _))

theorem oneBand_rowWord (h : ℕ) :
    bandRowWord h 1 = Pi.single (fun _ => oneBandLetter h) (1 : ℂ) := by
  rw [bandRowWord, oneBand_rowGroup, oneBand_rowLetters, altWord_bot]

theorem oneBand_columnWord (h : ℕ) :
    bandColumnWord h 1 = Pi.single (fun _ => oneBandLetter h) (1 : ℂ) := by
  rw [bandColumnWord, oneBand_columnGroup, oneBand_columnLetters, altWord_bot]

theorem oneBand_row_fixed (h : ℕ) (g : Equiv.Perm (Fin (bandSize h 1))) :
    wordRep _ _ g (bandRowWord h 1) = bandRowWord h 1 := by
  rw [oneBand_rowWord, wordRep_single]
  rfl

theorem oneBand_column_fixed (h : ℕ) (g : Equiv.Perm (Fin (bandSize h 1))) :
    wordRep _ _ g (bandColumnWord h 1) = bandColumnWord h 1 := by
  rw [oneBand_columnWord, wordRep_single]
  rfl

theorem oneBand_pair_fixed (h : ℕ) (g : Equiv.Perm (Fin (bandSize h 1))) :
    wordRep _ _ g (bandPairWord h 1) = bandPairWord h 1 := by
  have he := wordTensor_equivariant g (bandRowWord h 1 ⊗ₜ[ℂ] bandColumnWord h 1)
  rw [Representation.tprod_apply, TensorProduct.map_tmul,
    oneBand_row_fixed, oneBand_column_fixed] at he
  exact he.symm

theorem oneBand_pair_coefficient (h : ℕ) :
    bandPairWord h 1
      (mergeWords (fun _ => oneBandLetter h) (fun _ => oneBandLetter h)) = 1 := by
  rw [bandPairWord, wordTensor_tmul, splitLeft_merge, splitRight_merge,
    oneBand_rowWord, oneBand_columnWord]
  simp

theorem oneBand_pair_ne_zero (h : ℕ) : bandPairWord h 1 ≠ 0 := by
  intro hz
  have he := oneBand_pair_coefficient h
  rw [hz] at he
  exact zero_ne_one he

end HSTZ
#print axioms HSTZ.oneBand_rowLetters
#print axioms HSTZ.oneBand_columnLetters
#print axioms HSTZ.altWord_bot
#print axioms HSTZ.oneBand_pair_fixed
#print axioms HSTZ.oneBand_pair_coefficient
#print axioms HSTZ.oneBand_pair_ne_zero
