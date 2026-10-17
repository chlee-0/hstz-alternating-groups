import OAI.RepresentationTheory.Saxl.BandFactorization

/-! One-band cell and fiber geometry. No trivial band action is assumed. -/
namespace HSTZ
open OAI.Saxl

theorem bandSize_one (h : ℕ) : bandSize h 1 = h+1 := by
  have he := bandSize_add h 1
  have hs := staircase_card_succ h
  omega

theorem oneBand_antidiagonal (h : ℕ) (i : Fin (bandSize h 1)) :
    (bandTableau h 1 i).val.1 + (bandTableau h 1 i).val.2 = h := by
  have he := bandTableau_bounds h 1 i
  omega

theorem oneBand_row_injective (h : ℕ) :
    Function.Injective (fun i : Fin (bandSize h 1) => (bandTableau h 1 i).val.1) := by
  intro i j he
  change (bandTableau h 1 i).val.1 = (bandTableau h 1 j).val.1 at he
  apply (bandCellsEquiv h 1).injective
  apply Subtype.ext
  change (bandTableau h 1 i).val = (bandTableau h 1 j).val
  apply Prod.ext he
  have hi := oneBand_antidiagonal h i
  have hj := oneBand_antidiagonal h j
  omega

theorem oneBand_column_injective (h : ℕ) :
    Function.Injective (fun i : Fin (bandSize h 1) => (bandTableau h 1 i).val.2) := by
  intro i j he
  change (bandTableau h 1 i).val.2 = (bandTableau h 1 j).val.2 at he
  apply (bandCellsEquiv h 1).injective
  apply Subtype.ext
  change (bandTableau h 1 i).val = (bandTableau h 1 j).val
  apply Prod.ext
  · have hi := oneBand_antidiagonal h i
    have hj := oneBand_antidiagonal h j
    omega
  · exact he

/-- An injective fiber label has only the identity permutation. -/
theorem fiberGroup_eq_bot_of_injective {n : ℕ} {A : Type*} (f : Fin n → A)
    (hf : Function.Injective f) : fiberGroup f = ⊥ := by
  apply Subgroup.ext
  intro g
  constructor
  · intro hg
    change g = 1
    apply Equiv.ext
    intro i
    exact hf (hg i)
  · intro hg
    have he : g = 1 := hg
    subst g
    exact fun _ => rfl

theorem oneBand_rowGroup (h : ℕ) : bandRowGroup h 1 = ⊥ :=
  fiberGroup_eq_bot_of_injective _ (oneBand_row_injective h)

theorem oneBand_columnGroup (h : ℕ) : bandColumnGroup h 1 = ⊥ :=
  fiberGroup_eq_bot_of_injective _ (oneBand_column_injective h)

end HSTZ
#print axioms HSTZ.bandSize_one
#print axioms HSTZ.oneBand_antidiagonal
#print axioms HSTZ.fiberGroup_eq_bot_of_injective
#print axioms HSTZ.oneBand_rowGroup
#print axioms HSTZ.oneBand_columnGroup
