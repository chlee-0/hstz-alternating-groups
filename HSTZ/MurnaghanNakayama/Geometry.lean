import HSTZ.MurnaghanNakayama.Compute
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Union
import Mathlib.Logic.Relation

/-!
# Geometric specification of the bead enumerator

This is the cell-level definition of a rim hook (edge-connected, with no 2-by-2
square), independent of beta numbers. `MoveEnumerationCorrect` is a proposition;
`BeadReconstruction` proves it as `moveEnumerationCorrect`, including completeness
and absence of duplicate summands.
-/
namespace HSTZ.MurnaghanNakayama

abbrev Cell := ℕ × ℕ

def IsShape (lam : Shape) : Prop :=
  lam.Pairwise (fun a b => b ≤ a) ∧ ∀ a ∈ lam, 0 < a

/-- Zero-based diagram cells, without using Specht/tableau definitions. -/
def cellSet (lam : Shape) : Finset Cell :=
  (Finset.range lam.length).biUnion (fun i =>
    (Finset.range ((lam[i]?).getD 0)).image (fun j => (i, j)))

def EdgeAdjacent (a b : Cell) : Prop :=
  (a.1 = b.1 ∧ (a.2 + 1 = b.2 ∨ b.2 + 1 = a.2)) ∨
  (a.2 = b.2 ∧ (a.1 + 1 = b.1 ∨ b.1 + 1 = a.1))

def ConnectedWithin (d : Finset Cell) : Prop :=
  ∀ a ∈ d, ∀ b ∈ d,
    Relation.ReflTransGen (fun x y => x ∈ d ∧ y ∈ d ∧ EdgeAdjacent x y) a b

def NoTwoByTwo (d : Finset Cell) : Prop :=
  ∀ i j : ℕ, ¬ ((i, j) ∈ d ∧ (i + 1, j) ∈ d ∧
    (i, j + 1) ∈ d ∧ (i + 1, j + 1) ∈ d)

/-- `leg` counts occupied rows minus one; a one-row rim hook has sign +1. -/
def IsRimRemoval (lam mu : Shape) (r leg : ℕ) : Prop :=
  let d := cellSet lam \ cellSet mu
  IsShape lam ∧ IsShape mu ∧ cellSet mu ⊆ cellSet lam ∧
    0 < r ∧ d.card = r ∧ ConnectedWithin d ∧ NoTwoByTwo d ∧
    (d.image Prod.fst).card = leg + 1

/-- Geometric specification: the legal bead moves are in bijection with all rim-hook
removals, with the correct leg lengths. -/
def MoveEnumerationCorrect : Prop :=
  ∀ lam : Shape, IsShape lam → ∀ r : ℕ, 0 < r →
    (moves lam r).Nodup ∧
      ∀ m : Move, m ∈ moves lam r ↔ IsRimRemoval lam m.shape r m.leg

/-- Membership in `moves` characterizes rim-hook removals, given
`MoveEnumerationCorrect` as a hypothesis (it is proved as `moveEnumerationCorrect`
in `BeadReconstruction`). -/
theorem mem_moves_iff_of_correct (hc : MoveEnumerationCorrect)
    (lam : Shape) (hlam : IsShape lam) (r : ℕ) (hr : 0 < r) (m : Move) :
    m ∈ moves lam r ↔ IsRimRemoval lam m.shape r m.leg :=
  (hc lam hlam r hr).2 m

end HSTZ.MurnaghanNakayama

#print axioms HSTZ.MurnaghanNakayama.mem_moves_iff_of_correct
