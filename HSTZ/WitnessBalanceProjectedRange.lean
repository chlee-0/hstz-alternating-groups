import HSTZ.IntertwiningCompat
import HSTZ.TensorInterfaces
import HSTZ.WitnessBalanceTailSupport
import HSTZ.ProjectionLift

/-! Component projection and the target-specific quotient lift.
Adapts `componentProjection` and `rangeQuotient` from `BalanceColumns` in
OpenAI's `math` repository (commit adc7f1241, Apache-2.0), together with the HSTZ Maschke lift and
tensor maps. Allowed pair letters, letter labels and the target map remain explicit
hypotheses. No original packing support or full-group target map is asserted. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped TensorProduct

def witnessBalanceComponentWords {k b delta n : ℕ} (hk : 5 ≤ k)
    (z : Tableau n (witnessDiagram k b delta hk))
    (A : Fin ((witnessDiagram k b delta hk).colLen 0 *
      (witnessDiagram k b delta hk).colLen 0) → Prop)
    (ell : Fin ((witnessDiagram k b delta hk).colLen 0 *
      (witnessDiagram k b delta hk).colLen 0) → ℕ)
    (w : Fin n → Fin ((witnessDiagram k b delta hk).colLen 0 *
      (witnessDiagram k b delta hk).colLen 0)) : Prop :=
  (∀ i, A (w i)) ∧ ∀ i, ell (w i) = witnessBalanceLabel hk z i

theorem witnessBalanceComponentWords_invariant {k b delta n : ℕ} (hk : 5 ≤ k)
    (z : Tableau n (witnessDiagram k b delta hk))
    (A : Fin ((witnessDiagram k b delta hk).colLen 0 *
      (witnessDiagram k b delta hk).colLen 0) → Prop)
    (ell : Fin ((witnessDiagram k b delta hk).colLen 0 *
      (witnessDiagram k b delta hk).colLen 0) → ℕ)
    (g : witnessBalanceGroup hk z) (w) :
    witnessBalanceComponentWords hk z A ell (w ∘ g.val) ↔
      witnessBalanceComponentWords hk z A ell w := by
  constructor
  · rintro ⟨hA,hl⟩
    refine ⟨?_,fun i => ?_⟩
    · intro i
      simpa only [Function.comp_apply,Equiv.apply_symm_apply] using hA (g.val.symm i)
    · have he := hl (g.val.symm i)
      have hc := g.property (g.val.symm i)
      simpa only [Function.comp_apply,Equiv.apply_symm_apply] using he.trans hc.symm
  · rintro ⟨hA,hl⟩
    exact ⟨fun i => hA (g.val i),fun i => (hl (g.val i)).trans (g.property i)⟩

def witnessBalanceComponentProjection {k b delta n : ℕ} (hk : 5 ≤ k)
    (z : Tableau n (witnessDiagram k b delta hk))
    (A : Fin ((witnessDiagram k b delta hk).colLen 0 *
      (witnessDiagram k b delta hk).colLen 0) → Prop)
    (ell : Fin ((witnessDiagram k b delta hk).colLen 0 *
      (witnessDiagram k b delta hk).colLen 0) → ℕ) :
    Representation.IntertwiningMap
      ((wordRep n ((witnessDiagram k b delta hk).colLen 0 *
        (witnessDiagram k b delta hk).colLen 0)).comp (witnessBalanceGroup hk z).subtype)
      ((wordRep n ((witnessDiagram k b delta hk).colLen 0 *
        (witnessDiagram k b delta hk).colLen 0)).comp (witnessBalanceGroup hk z).subtype) where
  toLinearMap := coordinateProjection (witnessBalanceComponentWords hk z A ell)
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    classical
    funext w
    change (if witnessBalanceComponentWords hk z A ell w then x (w ∘ g.val) else 0) =
      (if witnessBalanceComponentWords hk z A ell (w ∘ g.val) then x (w ∘ g.val) else 0)
    rw [witnessBalanceComponentWords_invariant hk z A ell g w]

def witnessBalanceProjectedMap {k b delta n : ℕ} (hk : 5 ≤ k)
    (z : Tableau n (witnessDiagram k b delta hk))
    (A : Fin ((witnessDiagram k b delta hk).colLen 0 *
      (witnessDiagram k b delta hk).colLen 0) → Prop)
    (ell : Fin ((witnessDiagram k b delta hk).colLen 0 *
      (witnessDiagram k b delta hk).colLen 0) → ℕ) :=
  (witnessBalanceComponentProjection hk z A ell).comp (witnessBalanceTensorMap hk z)

def witnessBalanceProjectedRange {k b delta n : ℕ} (hk : 5 ≤ k)
    (z : Tableau n (witnessDiagram k b delta hk))
    (A : Fin ((witnessDiagram k b delta hk).colLen 0 *
      (witnessDiagram k b delta hk).colLen 0) → Prop)
    (ell : Fin ((witnessDiagram k b delta hk).colLen 0 *
      (witnessDiagram k b delta hk).colLen 0) → ℕ) :
    Subrepresentation ((wordRep n ((witnessDiagram k b delta hk).colLen 0 *
      (witnessDiagram k b delta hk).colLen 0)).comp (witnessBalanceGroup hk z).subtype) where
  toSubmodule := (witnessBalanceProjectedMap hk z A ell).toLinearMap.range
  apply_mem_toSubmodule g x hx := by
    obtain ⟨y,rfl⟩ := hx
    exact ⟨((witnessBalanceLocalRows hk z).toRepresentation.tprod
      (witnessBalanceLocalRows hk z).toRepresentation) g y,
      (witnessBalanceProjectedMap hk z A ell).map_action g y⟩

def witnessBalanceProjectedQuotient {k b delta n : ℕ} (hk : 5 ≤ k)
    (z : Tableau n (witnessDiagram k b delta hk))
    (A : Fin ((witnessDiagram k b delta hk).colLen 0 *
      (witnessDiagram k b delta hk).colLen 0) → Prop)
    (ell : Fin ((witnessDiagram k b delta hk).colLen 0 *
      (witnessDiagram k b delta hk).colLen 0) → ℕ) :
    Representation.IntertwiningMap
      ((witnessBalanceLocalRows hk z).toRepresentation.tprod
        (witnessBalanceLocalRows hk z).toRepresentation)
      (witnessBalanceProjectedRange hk z A ell).toRepresentation where
  toLinearMap := (witnessBalanceProjectedMap hk z A ell).toLinearMap.codRestrict
    (witnessBalanceProjectedRange hk z A ell).toSubmodule (fun x => ⟨x,rfl⟩)
  isIntertwining' g := LinearMap.ext fun x =>
    Subtype.ext ((witnessBalanceProjectedMap hk z A ell).map_action g x)

theorem witnessBalanceProjectedQuotient_surjective {k b delta n : ℕ} (hk : 5 ≤ k)
    (z : Tableau n (witnessDiagram k b delta hk))
    (A : Fin ((witnessDiagram k b delta hk).colLen 0 *
      (witnessDiagram k b delta hk).colLen 0) → Prop)
    (ell : Fin ((witnessDiagram k b delta hk).colLen 0 *
      (witnessDiagram k b delta hk).colLen 0) → ℕ) :
    Function.Surjective (witnessBalanceProjectedQuotient hk z A ell) := by
  rintro ⟨y,x,rfl⟩
  exact ⟨x,rfl⟩

/-- Conditional target-specific raw lift. The nonzero map `f` is a hypothesis: no local
placement, packing or full-group constituent follows from this lemma alone. -/
theorem witnessBalance_projected_target_lift {k b delta n : ℕ} (hk : 5 ≤ k)
    (z : Tableau n (witnessDiagram k b delta hk)) {nu : YoungDiagram}
    (target : Tableau n nu)
    (A : Fin ((witnessDiagram k b delta hk).colLen 0 *
      (witnessDiagram k b delta hk).colLen 0) → Prop)
    (ell : Fin ((witnessDiagram k b delta hk).colLen 0 *
      (witnessDiagram k b delta hk).colLen 0) → ℕ)
    (f : Representation.IntertwiningMap
      ((spechtRep target).comp (witnessBalanceGroup hk z).subtype)
      (witnessBalanceProjectedRange hk z A ell).toRepresentation) (hf : f ≠ 0) :
    ∃ L : Representation.IntertwiningMap
      ((spechtRep target).comp (witnessBalanceGroup hk z).subtype)
      ((wordRep n ((witnessDiagram k b delta hk).colLen 0 *
        (witnessDiagram k b delta hk).colLen 0)).comp (witnessBalanceGroup hk z).subtype),
      (∀ x, coordinateProjection (witnessBalanceComponentWords hk z A ell) (L x) = (f x).val) ∧
      (∀ x, L x ∈ witnessBalanceFixedOutputs hk z) ∧
      (∀ x, ∃ q : Specht z ⊗[ℂ] Specht z,
        ((wordTensorIntertwiner n _ _).comp (spechtTensorInclusion z z)) q = L x) ∧
      (coordinateProjection (witnessBalanceComponentWords hk z A ell)).comp L.toLinearMap ≠ 0 := by
  letI : NeZero (Nat.card (witnessBalanceGroup hk z) : ℂ) :=
    ⟨Nat.cast_ne_zero.mpr (Nat.card_pos.ne')⟩
  let Q := witnessBalanceProjectedQuotient hk z A ell
  let idQ : Representation.IntertwiningMap
      (witnessBalanceProjectedRange hk z A ell).toRepresentation
      (witnessBalanceProjectedRange hk z A ell).toRepresentation :=
    { toLinearMap := LinearMap.id
      isIntertwining' := fun _ => LinearMap.ext (fun _ => rfl) }
  obtain ⟨s,_,hs⟩ := equivariant_injective_lift
    (K := ℂ) (G := witnessBalanceGroup hk z)
    (U := (witnessBalanceProjectedRange hk z A ell).toSubmodule)
    (V := (witnessBalanceLocalRows hk z).toSubmodule ⊗[ℂ]
      (witnessBalanceLocalRows hk z).toSubmodule)
    (W := (witnessBalanceProjectedRange hk z A ell).toSubmodule)
    (rho := (witnessBalanceLocalRows hk z).toRepresentation.tprod
      (witnessBalanceLocalRows hk z).toRepresentation)
    (sigma := (witnessBalanceProjectedRange hk z A ell).toRepresentation)
    (tau := (witnessBalanceProjectedRange hk z A ell).toRepresentation) Q
    (witnessBalanceProjectedQuotient_surjective hk z A ell) idQ (fun _ _ h => h)
  let L := (witnessBalanceTensorMap hk z).comp (s.comp f)
  have he (x) : coordinateProjection (witnessBalanceComponentWords hk z A ell) (L x) = (f x).val :=
    congrArg Subtype.val (hs (f x))
  refine ⟨L,he,?_,?_,?_⟩
  · intro x
    exact witnessBalanceTensorMap_output_sums hk z (s (f x))
  · intro x
    exact witnessBalanceTensorMap_full_square hk z (s (f x))
  · intro hz
    apply hf
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact (he x).symm.trans (LinearMap.congr_fun hz x)

end
end HSTZ
#print axioms HSTZ.witnessBalanceComponentWords_invariant
#print axioms HSTZ.witnessBalanceComponentProjection
#print axioms HSTZ.witnessBalanceProjectedQuotient_surjective
#print axioms HSTZ.witnessBalance_projected_target_lift
