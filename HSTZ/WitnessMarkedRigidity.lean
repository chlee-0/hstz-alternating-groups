import HSTZ.WitnessMarkedCells
import OAI.RepresentationTheory.Saxl.HighProjection

/-! Adapted from `high_positions_rigidity` in OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
The asymmetric masks are transported by coordinate-preserving cell bijections.
Common-mask equality is an explicit hypothesis, not derived from coefficient support. -/
namespace HSTZ
open OAI.Saxl

theorem witness_common_marked_positions (k b delta : ℕ) (hk : 5 ≤ k)
    (g q : Equiv.Perm (witnessDiagram k b delta hk).cells)
    (hg : ∀ x, (g x).val.1=x.val.1)
    (hq : ∀ x, (q x).val.2=x.val.2)
    (hc : ∀ x, witnessRowMarked k b (g x).val.2 ↔
      witnessColumnMarked k (q x).val.1) :
    ∀ x, witnessRowMarked k b (g x).val.2 ↔ x.val.1+x.val.2<k-2 := by
  classical
  let A : Finset (witnessDiagram k b delta hk).cells := Finset.univ.filter (fun x => witnessRowMarked k b (g x).val.2)
  let B : Finset (witnessDiagram k b delta hk).cells := Finset.univ.filter (fun x => x.val.1 + x.val.2 < k-2)
  let eR : A ≃ (staircase (k-2)).cells :=
    (Equiv.subtypeEquiv g (by intro x; simp only [A, Finset.mem_filter, Finset.mem_univ, true_and])).trans
      (witnessMarkedRowEquiv k b delta hk)
  let eC : A ≃ (staircase (k-2)).cells :=
    (Equiv.subtypeEquiv q (by intro x; simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]; exact hc x)).trans
      (witnessMarkedColumnEquiv k b delta hk)
  let eB : B ≃ (staircase (k-2)).cells :=
    { toFun := fun x => ⟨x.val.val, mem_staircase.mpr (by simpa only [B, Finset.mem_filter, Finset.mem_univ, true_and] using x.property)⟩
      invFun := fun x => ⟨witnessCoreCell k b delta hk x, by
        simpa only [B, Finset.mem_filter, Finset.mem_univ, true_and, witnessCoreCell]
          using mem_staircase.mp x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hcard : A.card = B.card := by
    have he := Fintype.card_congr (eR.trans eB.symm)
    simpa using he
  have hrow : ∑ x ∈ A, (x.val.1 : ℤ) = ∑ x ∈ B, (x.val.1 : ℤ) := by
    rw [← Finset.sum_coe_sort A, ← Finset.sum_coe_sort B]
    have hR := Equiv.sum_comp eR (fun x => (x.val.1 : ℤ))
    have hB := Equiv.sum_comp eB (fun x => (x.val.1 : ℤ))
    simp only [eR, Equiv.trans_apply, witnessMarkedRowEquiv_row] at hR
    change (∑ x : A, ((g x.val).val.1 : ℤ)) = _ at hR
    simp_rw [hg] at hR
    exact hR.trans hB.symm
  have hcol : ∑ x ∈ A, (x.val.2 : ℤ) = ∑ x ∈ B, (x.val.2 : ℤ) := by
    rw [← Finset.sum_coe_sort A, ← Finset.sum_coe_sort B]
    have hC := Equiv.sum_comp eC (fun x => (x.val.2 : ℤ))
    have hB := Equiv.sum_comp eB (fun x => (x.val.2 : ℤ))
    simp only [eC, Equiv.trans_apply, witnessMarkedColumnEquiv_column] at hC
    change (∑ x : A, ((q x.val).val.2 : ℤ)) = _ at hC
    simp_rw [hq] at hC
    exact hC.trans hB.symm
  let w := fun x : (witnessDiagram k b delta hk).cells =>
    2 * ((k-2 : ℕ) : ℤ) - 1 - 2 * (x.val.1 : ℤ) - 2 * (x.val.2 : ℤ)
  have he : ∑ x ∈ A, w x = ∑ x ∈ B, w x := by
    simp only [w, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    rw [hcard, hrow, hcol]
  have hab := finset_eq_of_signed_sum A B w
    (fun x hx => by
      have hh : x.val.1 + x.val.2 < k-2 := by simpa only [B, Finset.mem_filter, Finset.mem_univ, true_and] using hx
      dsimp [w]
      omega)
    (fun x hx => by
      have hh : ¬x.val.1 + x.val.2 < k-2 := by simpa only [B, Finset.mem_filter, Finset.mem_univ, true_and] using hx
      dsimp [w]
      omega) he
  intro x
  have := Finset.ext_iff.mp hab x
  simpa [A, B] using this


theorem witnessCoreCell_range (k b delta : ℕ) (hk : 5 ≤ k)
    (x : (witnessDiagram k b delta hk).cells) :
    x∈Set.range (witnessCoreCell k b delta hk) ↔ x.val.1+x.val.2<k-2 := by
  constructor
  · rintro ⟨y,rfl⟩
    exact mem_staircase.mp y.property
  · intro hx
    exact ⟨⟨x.val,mem_staircase.mpr hx⟩,rfl⟩

theorem witness_common_marked_core (k b delta : ℕ) (hk : 5 ≤ k)
    (g q : Equiv.Perm (witnessDiagram k b delta hk).cells)
    (hg : ∀ x, (g x).val.1=x.val.1)
    (hq : ∀ x, (q x).val.2=x.val.2)
    (hc : ∀ x, witnessRowMarked k b (g x).val.2 ↔
      witnessColumnMarked k (q x).val.1) :
    ∀ x, (witnessRowMarked k b (g x).val.2 ↔
      x∈Set.range (witnessCoreCell k b delta hk)) ∧
      (witnessColumnMarked k (q x).val.1 ↔
      x∈Set.range (witnessCoreCell k b delta hk)) := by
  intro x
  have hr := (witness_common_marked_positions k b delta hk g q hg hq hc x).trans
    (witnessCoreCell_range k b delta hk x).symm
  exact ⟨hr,(hc x).symm.trans hr⟩


end HSTZ
#print axioms HSTZ.witness_common_marked_positions
#print axioms HSTZ.witnessCoreCell_range
#print axioms HSTZ.witness_common_marked_core
