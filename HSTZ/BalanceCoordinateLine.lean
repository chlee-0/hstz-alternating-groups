import HSTZ.IntertwiningCompat
import HSTZ.TensorInterfaces
import HSTZ.SpechtSignTransport
import HSTZ.SpechtTableauTransport
import OAI.RepresentationTheory.Saxl.StaircaseSign

import OAI.RepresentationTheory.Saxl.DominatedSupport

import OAI.RepresentationTheory.Saxl.YoungRule

/-! Coordinate-line lemmas for Specht modules, adapted from
`UniversalSquare/Support/CoordinateLine` in OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
The proofs follow the original, except that the older self-duality and
vector-intertwiner API is replaced and the sign map is chosen explicitly. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped TensorProduct

def coordinateRestriction {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (a : Fin n → Fin (μ.colLen 0)) : Module.Dual ℂ (Specht t) :=
  { toFun := fun x => x.val a
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

def projectedCoordinate {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (a : Fin n → Fin (μ.colLen 0)) : Specht t :=
  (spechtSelfDualLinear t).symm (coordinateRestriction t a)

lemma projectedCoordinate_pair {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (a : Fin n → Fin (μ.colLen 0)) (x : Specht t) :
    dotProduct (projectedCoordinate t a).val x.val = x.val a := by
  exact congrArg (fun f : Module.Dual ℂ (Specht t) => f x)
    ((spechtSelfDualLinear t).apply_symm_apply (coordinateRestriction t a))

lemma projectedCoordinate_nonzero {n : ℕ} {μ : YoungDiagram} (t s : Tableau n μ) :
    projectedCoordinate t (rowWord s) ≠ 0 := by
  intro hz
  have h := projectedCoordinate_pair t (rowWord s)
    ⟨polytabloid s, polytabloid_mem_all t s⟩
  rw [hz] at h
  have h0 : (0 : ℂ) = 1 := by
    simpa only [ZeroMemClass.coe_zero, zero_dotProduct, polytabloid_rowWord] using h
  exact zero_ne_one h0

lemma coordinateRestriction_nonzero {n : ℕ} {μ : YoungDiagram} (t s : Tableau n μ) :
    coordinateRestriction t (rowWord s) ≠ 0 := by
  intro hz
  apply projectedCoordinate_nonzero t s
  change (spechtSelfDualLinear t).symm (coordinateRestriction t (rowWord s)) = 0
  rw [hz]
  exact (spechtSelfDualLinear t).symm.toLinearMap.map_zero

lemma coordinateRestriction_fixed {n : ℕ} {μ : YoungDiagram} (t s : Tableau n μ)
    (g : columnGroup (transposeTableau s)) :
    (spechtRep t).dual g.val (coordinateRestriction t (rowWord s)) =
      coordinateRestriction t (rowWord s) := by
  ext x
  change x.val (rowWord s ∘ ((g.val)⁻¹ : Equiv.Perm (Fin n))) = x.val (rowWord s)
  apply congrArg x.val
  funext i
  apply Fin.ext
  exact g⁻¹.property i

lemma projectedCoordinate_fixed {n : ℕ} {μ : YoungDiagram} (t s : Tableau n μ)
    (g : columnGroup (transposeTableau s)) :
    spechtRep t g.val (projectedCoordinate t (rowWord s)) =
      projectedCoordinate t (rowWord s) := by
  apply (spechtSelfDualLinear t).injective
  rw [spechtSelfDualLinear_equivariant]
  simp only [projectedCoordinate,LinearEquiv.apply_symm_apply]
  exact coordinateRestriction_fixed t s g

theorem signEquiv_coordinate_line {n : ℕ} {μ : YoungDiagram} (t s : Tableau n μ)
    :
    ∃ c : ℂ, c ≠ 0 ∧ ((spechtSignMap t) (projectedCoordinate t (rowWord s))).val =
      c • polytabloid (transposeTableau s) := by
  let y : Specht (transposeTableau s) :=
    ⟨((spechtSignMap t) (projectedCoordinate t (rowWord s))).val,
      by change _ ∈ (spechtSub (transposeTableau s)).toSubmodule
         rw [← spechtSub_tableau_independent (transposeTableau t) (transposeTableau s)]
         exact ((spechtSignMap t) (projectedCoordinate t (rowWord s))).property⟩
  have ha (g : columnGroup (transposeTableau s)) :
      spechtRep (transposeTableau s) g.val y = signC g.val • y := by
    have he := (spechtSignMap t).map_action g.val
      (projectedCoordinate t (rowWord s))
    change (spechtSignMap t) (spechtRep t g.val (projectedCoordinate t (rowWord s))) =
      signC g.val • spechtRep (transposeTableau t) g.val
        ((spechtSignMap t) (projectedCoordinate t (rowWord s))) at he
    rw [projectedCoordinate_fixed] at he
    have hh := congrArg (fun x => signC g.val • x.val) he
    change signC g.val • ((spechtSignMap t) (projectedCoordinate t (rowWord s))).val =
      signC g.val • (signC g.val • wordRep _ _ g.val
        ((spechtSignMap t) (projectedCoordinate t (rowWord s))).val) at hh
    apply Subtype.ext
    change wordRep _ _ g.val ((spechtSignMap t) (projectedCoordinate t (rowWord s))).val =
      signC g.val • ((spechtSignMap t) (projectedCoordinate t (rowWord s))).val
    simpa only [Submodule.coe_smul_of_tower, smul_smul, signC_mul_self, one_smul]
      using hh.symm
  obtain ⟨c,hc⟩ := alternating_specht_line (transposeTableau s) y ha
  refine ⟨c, ?_, hc⟩
  intro hz
  rw [hz, zero_smul] at hc
  apply projectedCoordinate_nonzero t s
  apply (spechtSignMap_bijective t).1
  have hz' : (spechtSignMap t).toLinearMap (projectedCoordinate t (rowWord s)) = 0 := by
    apply Subtype.ext
    exact hc
  exact hz'.trans ((spechtSignMap t).toLinearMap.map_zero).symm

lemma exists_tableau_of_row_content {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (a : Fin n → Fin (μ.colLen 0))
    (ha : ∀ j, (Finset.univ.filter (fun i => a i = j)).card = μ.rowLen j.val) :
    ∃ s : Tableau n μ, rowWord s = a := by
  obtain ⟨g,hg⟩ := perm_of_equal_content a (rowWord t)
    (fun j => (ha j).trans (rowWord_content t j).symm)
  exact ⟨g.trans t, hg⟩

theorem coordinateRestriction_ne_zero_of_content {n : ℕ} {μ : YoungDiagram}
    (t : Tableau n μ) (a : Fin n → Fin (μ.colLen 0))
    (ha : ∀ j, (Finset.univ.filter (fun i => a i = j)).card = μ.rowLen j.val) :
    coordinateRestriction t a ≠ 0 := by
  obtain ⟨s, rfl⟩ := exists_tableau_of_row_content t a ha
  exact coordinateRestriction_nonzero t s

end
end HSTZ
#print axioms HSTZ.projectedCoordinate_pair
#print axioms HSTZ.projectedCoordinate_nonzero
#print axioms HSTZ.coordinateRestriction_nonzero
#print axioms HSTZ.coordinateRestriction_fixed
#print axioms HSTZ.projectedCoordinate_fixed
#print axioms HSTZ.signEquiv_coordinate_line
#print axioms HSTZ.exists_tableau_of_row_content
#print axioms HSTZ.coordinateRestriction_ne_zero_of_content
