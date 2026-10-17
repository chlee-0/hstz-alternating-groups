import HSTZ.RightStripDiagram
import OAI.RepresentationTheory.Saxl.PieriRestriction

import OAI.RepresentationTheory.Saxl.Basic

/-! Long-row horizontal-strip extraction and the resulting tableau of smaller
staircase size. This does not identify a one-step support source. -/
namespace HSTZ
open OAI.Saxl

theorem rightStripDiagram_horizontal (mu : YoungDiagram) (m : ℕ) :
    HorizontalStrip (rightStripDiagram mu m) mu :=
  ⟨rightStripDiagram_le mu m, fun _ hx hn _ hy hny hcol =>
    rightStripDiagram_removed_column mu m hx hn hy hny hcol⟩

theorem rightStripDiagram_staircase_card (mu : YoungDiagram) {m : ℕ}
    (hm : m ≤ mu.rowLen 0) (hsize : mu.card = (staircase m).card) :
    (rightStripDiagram mu m).card = (staircase (m-1)).card := by
  have he := rightStripDiagram_card mu hm
  by_cases hz : m = 0
  · subst m
    simpa only [Nat.zero_sub, Nat.add_zero] using he.trans hsize
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hz
    rw [staircase_card_succ] at hsize
    have hs : k+1-1 = k := by omega
    rw [hs]
    omega

/-- A smaller tableau, including the empty case, is chosen internally. -/
noncomputable def rightStripTableau (mu : YoungDiagram) {m : ℕ}
    (hm : m ≤ mu.rowLen 0) (hsize : mu.card = (staircase m).card) :
    Tableau (staircase (m-1)).card (rightStripDiagram mu m) :=
  canonicalTableau (rightStripDiagram mu m)
    (rightStripDiagram_staircase_card mu hm hsize)

/-- One-step geometric interface for the caller's target tableau. -/
theorem exists_staircase_rightStrip (m : ℕ) {mu : YoungDiagram}
    (t : Tableau (staircase m).card mu) (hm : m ≤ mu.rowLen 0) :
    ∃ (nu : YoungDiagram) (_ : Tableau (staircase (m-1)).card nu),
      HorizontalStrip nu mu ∧ nu.card+m = mu.card := by
  have hsize : mu.card = (staircase m).card := by
    simpa [YoungDiagram.card] using (Fintype.card_congr t).symm
  exact ⟨rightStripDiagram mu m, rightStripTableau mu hm hsize,
    rightStripDiagram_horizontal mu m, rightStripDiagram_card mu hm⟩

end HSTZ
#print axioms HSTZ.rightStripDiagram_horizontal
#print axioms HSTZ.rightStripDiagram_staircase_card
#print axioms HSTZ.exists_staircase_rightStrip
