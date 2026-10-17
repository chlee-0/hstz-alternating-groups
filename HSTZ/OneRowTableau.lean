import OAI.RepresentationTheory.Saxl.Model

/-! One-row diagrams and tableaux, including the empty diagram. -/
namespace HSTZ

def oneRowDiagram (n : ℕ) : YoungDiagram where
  cells := Finset.range 1 ×ˢ Finset.range n
  isLowerSet := by
    intro x y hxy hx
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_range] at hx ⊢
    exact ⟨lt_of_le_of_lt hxy.1 hx.1, lt_of_le_of_lt hxy.2 hx.2⟩

@[simp] theorem mem_oneRowDiagram {n i j : ℕ} :
    (i, j) ∈ oneRowDiagram n ↔ i = 0 ∧ j < n := by
  simp [oneRowDiagram, and_comm, eq_comm]

@[simp] theorem oneRowDiagram_card (n : ℕ) : (oneRowDiagram n).card = n := by
  simp [YoungDiagram.card, oneRowDiagram]

theorem oneRowDiagram_rows (n : ℕ) : (oneRowDiagram n).colLen 0 ≤ 1 := by
  by_contra hn
  have hx : (1, 0) ∈ oneRowDiagram n :=
    YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
  simp at hx

@[simp] theorem oneRowDiagram_zero : oneRowDiagram 0 = ⊥ := by
  ext ⟨i, j⟩
  simp

noncomputable def oneRowTableau (n : ℕ) : OAI.Saxl.Tableau n (oneRowDiagram n) :=
  OAI.Saxl.canonicalTableau (oneRowDiagram n) (oneRowDiagram_card n)

theorem exists_oneRowTableau (n : ℕ) :
    ∃ (mu : YoungDiagram) (_ : OAI.Saxl.Tableau n mu), mu.colLen 0 ≤ 1 :=
  ⟨oneRowDiagram n, oneRowTableau n, oneRowDiagram_rows n⟩

end HSTZ
#print axioms HSTZ.oneRowDiagram_card
#print axioms HSTZ.oneRowDiagram_rows
#print axioms HSTZ.exists_oneRowTableau

#print axioms HSTZ.oneRowDiagram_zero
