import HSTZ.YoungDiagramCompat
import HSTZ.WitnessAttachmentHContraction

/-! Target columns for the contraction with the paper's H, via a parity
argument, using OpenAI's `math` repository and Mathlib's `YoungDiagram` API.
These are target geometry identities, not a noncancellation hypothesis. -/
namespace HSTZ
noncomputable section
open OAI.Saxl

def AttachmentEvenRows (mu : YoungDiagram) : Prop := ∀ r, mu.rowLen r % 2 = 0
def AttachmentOneOddRow (mu : YoungDiagram) (a : ℕ) : Prop :=
  mu.rowLen a % 2 = 1 ∧ ∀ r, r ≠ a → mu.rowLen r % 2 = 0

theorem attachmentTarget_even_columns (mu : YoungDiagram) (he : AttachmentEvenRows mu)
    (c : ℕ) : mu.colLen (2*c) = mu.colLen (2*c+1) := by
  apply eq_of_forall_lt_iff
  intro r
  rw [← YoungDiagram.mem_iff_lt_colLen, ← YoungDiagram.mem_iff_lt_colLen,
    YoungDiagram.mem_iff_lt_rowLen, YoungDiagram.mem_iff_lt_rowLen]
  have hp := he r
  omega

theorem attachmentTarget_odd_columns (mu : YoungDiagram) (a : ℕ)
    (ho : AttachmentOneOddRow mu a) (c : ℕ) (hc : 2*c+1 ≠ mu.rowLen a) :
    mu.colLen (2*c) = mu.colLen (2*c+1) := by
  apply eq_of_forall_lt_iff
  intro r
  rw [← YoungDiagram.mem_iff_lt_colLen, ← YoungDiagram.mem_iff_lt_colLen,
    YoungDiagram.mem_iff_lt_rowLen, YoungDiagram.mem_iff_lt_rowLen]
  by_cases hr : r = a
  · subst r; have hp := ho.1; omega
  · have hp := ho.2 r hr; omega

/-- Zero-based odd row a gives the paper's exceptional heights a+1,a.
When a=0 the second height is zero and has no cell. -/
theorem attachmentTarget_odd_heights (mu : YoungDiagram) (a : ℕ)
    (ho : AttachmentOneOddRow mu a) :
    mu.colLen (mu.rowLen a - 1) = a+1 ∧ mu.colLen (mu.rowLen a) = a := by
  have hp := ho.1
  constructor
  · apply eq_of_forall_lt_iff
    intro r
    rw [← YoungDiagram.mem_iff_lt_colLen, YoungDiagram.mem_iff_lt_rowLen]
    by_cases hr : r ≤ a
    · have hb := mu.rowLen_anti r a hr; omega
    · have hb := mu.rowLen_anti a r (by omega)
      have he := ho.2 r (by omega)
      omega
  · apply eq_of_forall_lt_iff
    intro r
    rw [← YoungDiagram.mem_iff_lt_colLen, YoungDiagram.mem_iff_lt_rowLen]
    by_cases hr : r < a
    · have hb := mu.rowLen_anti r a (by omega)
      have he := ho.2 r (by omega)
      omega
    · have hb := mu.rowLen_anti a r (by omega); omega

def attachmentTargetOddCell (mu : YoungDiagram) (a : ℕ)
    (ho : AttachmentOneOddRow mu a) : mu.cells :=
  ⟨(a,mu.rowLen a-1), by
    apply YoungDiagram.mem_iff_lt_rowLen.mpr
    have hp := ho.1
    change mu.rowLen a-1 < mu.rowLen a
    omega⟩

def attachmentTargetOddPosition {n : ℕ} {mu : YoungDiagram} (t : Tableau n mu)
    (a : ℕ) (ho : AttachmentOneOddRow mu a) : Fin n :=
  t.symm (attachmentTargetOddCell mu a ho)

theorem attachmentTargetOddPosition_cell {n : ℕ} {mu : YoungDiagram} (t : Tableau n mu)
    (a : ℕ) (ho : AttachmentOneOddRow mu a) :
    (t (attachmentTargetOddPosition t a ho)).val = (a,mu.rowLen a-1) := by
  simp [attachmentTargetOddPosition, attachmentTargetOddCell]

/-- Local paired-column sum: matching permutations cancel their signs.
The factorization of the global column group is not assumed or supplied here. -/
theorem attachmentEqualColumnSignSum (h : ℕ) :
    (∑ g : Equiv.Perm (Fin h), ∑ k : Equiv.Perm (Fin h),
      signC g * signC k * (if g = k then (1:ℂ) else 0)) =
      (Nat.card (Equiv.Perm (Fin h)) : ℂ) := by
  classical
  calc
    _ = ∑ g : Equiv.Perm (Fin h), signC g * signC g := by
      apply Finset.sum_congr rfl
      intro g hg
      simp [mul_ite]
    _ = _ := by simp only [signC_mul_self]; simp [Nat.card_eq_fintype_card]

theorem attachmentEqualColumnSignSum_ne_zero (h : ℕ) :
    (∑ g : Equiv.Perm (Fin h), ∑ k : Equiv.Perm (Fin h),
      signC g * signC k * (if g = k then (1:ℂ) else 0)) ≠ 0 := by
  rw [attachmentEqualColumnSignSum]
  exact Nat.cast_ne_zero.mpr (by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_ne_zero)

end
end HSTZ
#print axioms HSTZ.attachmentTarget_even_columns
#print axioms HSTZ.attachmentTarget_odd_columns
#print axioms HSTZ.attachmentTarget_odd_heights
#print axioms HSTZ.attachmentTargetOddCell
#print axioms HSTZ.attachmentTargetOddPosition_cell
#print axioms HSTZ.attachmentEqualColumnSignSum
#print axioms HSTZ.attachmentEqualColumnSignSum_ne_zero
