import HSTZ.IntertwiningCompat
import HSTZ.WitnessBalancePackingGroup
import Mathlib.LinearAlgebra.PiTensorProduct.Basis

/-! Finite tensor product of all original projected factors and physical paired word
coordinates. Reuses declarations from OpenAI's `math` repository (commit adc7f1241, Apache-2.0)
and Mathlib's `PiTensorProduct`.
No compatible Young support or global nonzero target map is assumed or supplied. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped Classical TensorProduct
section
variable {k b delta n : ℕ} (hk : 5 ≤ k)
  (z : Tableau n (witnessDiagram k b delta hk))

abbrev witnessBalancePackingTensorSpace :=
  ⨂[ℂ] a : witnessBalancePackingLabelIndex k delta,
    (witnessBalanceLocalProjectedFactor hk z a.val).toSubmodule

/-- All original factors, with their independent position actions. -/
def witnessBalancePackingTensorAction : Representation ℂ
    (witnessBalancePackingOriginalGroup hk z) (witnessBalancePackingTensorSpace hk z) where
  toFun g := PiTensorProduct.map fun a => witnessBalancePackingFactorAction hk z a g
  map_one' := by
    simp only [map_one]
    exact PiTensorProduct.map_one
  map_mul' g h := by
    simp only [map_mul]
    exact PiTensorProduct.map_mul _ _

theorem witnessBalancePackingTensorAction_tprod
    (g : witnessBalancePackingOriginalGroup hk z)
    (x : ∀ a : witnessBalancePackingLabelIndex k delta,
      (witnessBalanceLocalProjectedFactor hk z a.val).toSubmodule) :
    witnessBalancePackingTensorAction hk z g (PiTensorProduct.tprod ℂ x)=
      PiTensorProduct.tprod ℂ (fun a => witnessBalancePackingFactorAction hk z a g (x a)) :=
  PiTensorProduct.map_tprod _ _

/-- The same named component positions, obtained from the original all-label cut. -/
def witnessBalancePackingPairRestriction (hd : delta ≤ 1)
    (w : Fin n → Fin (witnessBalancePairDim k b delta hk))
    (a : witnessBalancePackingLabelIndex k delta) :
    Fin (witnessBalanceComponentSize hk z a.val) → Fin (witnessBalancePairDim k b delta hk) :=
  fun i => w ((witnessBalancePackingLabelCut hk z hd).symm ⟨a,i⟩)

private def packingCoefficient (hd : delta ≤ 1) : MultilinearMap ℂ
    (fun a : witnessBalancePackingLabelIndex k delta =>
      (witnessBalanceLocalProjectedFactor hk z a.val).toSubmodule)
    (WordSpace n (witnessBalancePairDim k b delta hk)) :=
  MultilinearMap.pi fun w =>
    (MultilinearMap.mkPiAlgebra ℂ (witnessBalancePackingLabelIndex k delta) ℂ).compLinearMap
      (fun a => (LinearMap.proj (witnessBalancePackingPairRestriction hk z hd w a)).comp
        (witnessBalanceLocalProjectedFactor hk z a.val).toSubmodule.subtype)

/-- Finite product coefficient on paired words, with both square layers retained inside
each prescribed local projected factor. -/
def witnessBalancePackingTensorWords (hd : delta ≤ 1) :
    witnessBalancePackingTensorSpace hk z →ₗ[ℂ] WordSpace n (witnessBalancePairDim k b delta hk) :=
  PiTensorProduct.lift (packingCoefficient hk z hd)

theorem witnessBalancePackingTensorWords_tprod (hd : delta ≤ 1)
    (x : ∀ a : witnessBalancePackingLabelIndex k delta,
      (witnessBalanceLocalProjectedFactor hk z a.val).toSubmodule)
    (w : Fin n → Fin (witnessBalancePairDim k b delta hk)) :
    witnessBalancePackingTensorWords hk z hd (PiTensorProduct.tprod ℂ x) w=
      ∏ a, (x a).val (witnessBalancePackingPairRestriction hk z hd w a) := by
  rw [witnessBalancePackingTensorWords,PiTensorProduct.lift.tprod]
  rfl

theorem witnessBalancePackingPairRestriction_action (hd : delta ≤ 1)
    (g : witnessBalancePackingOriginalGroup hk z)
    (w : Fin n → Fin (witnessBalancePairDim k b delta hk))
    (a : witnessBalancePackingLabelIndex k delta) :
    witnessBalancePackingPairRestriction hk z hd
      (w ∘ (witnessBalancePackingOriginalHom hk z hd g).val) a=
      witnessBalancePackingPairRestriction hk z hd w a ∘ g a := by
  let E : Fin n ≃ Σ a : witnessBalancePackingLabelIndex k delta,
      Fin (witnessBalanceComponentSize hk z a.val) := witnessBalancePackingLabelCut hk z hd
  funext i
  change w ((witnessBalancePackingOriginalHom hk z hd g).val (E.symm ⟨a,i⟩))=
    w (E.symm ⟨a,g a i⟩)
  have hi : E (E.symm ⟨a,i⟩)=⟨a,i⟩ := E.apply_symm_apply ⟨a,i⟩
  have hp := witnessBalancePackingOriginalHom_value hk z hd g (E.symm ⟨a,i⟩)
  change (witnessBalancePackingOriginalHom hk z hd g).val (E.symm ⟨a,i⟩)=
    E.symm ⟨(E (E.symm ⟨a,i⟩)).1,g (E (E.symm ⟨a,i⟩)).1 (E (E.symm ⟨a,i⟩)).2⟩ at hp
  rw [hi] at hp
  exact congrArg w hp

/-- Physical coordinate map, returning to the same original product pullback of `H`. -/
def witnessBalancePackingTensorIntertwiner (hd : delta ≤ 1) : Representation.IntertwiningMap
    (witnessBalancePackingTensorAction hk z)
    (((wordRep n (witnessBalancePairDim k b delta hk)).comp (witnessBalanceGroup hk z).subtype).comp
      (witnessBalancePackingOriginalHom hk z hd)) where
  toLinearMap := witnessBalancePackingTensorWords hk z hd
  isIntertwining' g := by
    apply LinearMap.ext
    intro q
    change witnessBalancePackingTensorWords hk z hd (witnessBalancePackingTensorAction hk z g q)=
      wordRep n (witnessBalancePairDim k b delta hk)
        (witnessBalancePackingOriginalHom hk z hd g).val (witnessBalancePackingTensorWords hk z hd q)
    induction q using PiTensorProduct.induction_on with
    | smul_tprod r x =>
      simp only [map_smul]
      congr 1
      funext w
      rw [witnessBalancePackingTensorAction_tprod,witnessBalancePackingTensorWords_tprod]
      change (∏ a, (x a).val (witnessBalancePackingPairRestriction hk z hd w a ∘ g a))=
        witnessBalancePackingTensorWords hk z hd (PiTensorProduct.tprod ℂ x)
          (w ∘ (witnessBalancePackingOriginalHom hk z hd g).val)
      rw [witnessBalancePackingTensorWords_tprod]
      apply Finset.prod_congr rfl
      intro a _
      rw [witnessBalancePackingPairRestriction_action]
    | add x y hx hy => simp only [map_add,hx,hy]

/-- Reassembly of all physical paired words, using the original label cut. -/
def witnessBalancePackingPairEquiv (hd : delta ≤ 1) :
    (Fin n → Fin (witnessBalancePairDim k b delta hk)) ≃
      (∀ a : witnessBalancePackingLabelIndex k delta,
        Fin (witnessBalanceComponentSize hk z a.val) → Fin (witnessBalancePairDim k b delta hk)) where
  toFun w := witnessBalancePackingPairRestriction hk z hd w
  invFun v i := v (witnessBalancePackingLabelCut hk z hd i).1
    (witnessBalancePackingLabelCut hk z hd i).2
  left_inv w := by
    funext i
    exact congrArg w ((witnessBalancePackingLabelCut hk z hd).symm_apply_apply i)
  right_inv v := by
    funext a i
    exact congrArg (fun t : Σ a : witnessBalancePackingLabelIndex k delta,
      Fin (witnessBalanceComponentSize hk z a.val) => v t.1 t.2)
      ((witnessBalancePackingLabelCut hk z hd).apply_symm_apply ⟨a,i⟩)

private def ambientCoordinates (hd : delta ≤ 1) :
    (⨂[ℂ] a : witnessBalancePackingLabelIndex k delta,
      WordSpace (witnessBalanceComponentSize hk z a.val) (witnessBalancePairDim k b delta hk)) ≃ₗ[ℂ]
        WordSpace n (witnessBalancePairDim k b delta hk) :=
  (Basis.piTensorProduct (fun a : witnessBalancePackingLabelIndex k delta =>
    Pi.basisFun ℂ (Fin (witnessBalanceComponentSize hk z a.val) →
      Fin (witnessBalancePairDim k b delta hk)))).repr.trans
    ((Finsupp.linearEquivFunOnFinite ℂ ℂ _).trans
      (LinearEquiv.funCongrLeft ℂ ℂ (witnessBalancePackingPairEquiv hk z hd)))

private theorem ambientCoordinates_tprod (hd : delta ≤ 1)
    (x : ∀ a : witnessBalancePackingLabelIndex k delta,
      WordSpace (witnessBalanceComponentSize hk z a.val) (witnessBalancePairDim k b delta hk))
    (w : Fin n → Fin (witnessBalancePairDim k b delta hk)) :
    ambientCoordinates hk z hd (PiTensorProduct.tprod ℂ x) w=
      ∏ a, x a (witnessBalancePackingPairRestriction hk z hd w a) := by
  change (Basis.piTensorProduct (fun a : witnessBalancePackingLabelIndex k delta =>
    Pi.basisFun ℂ (Fin (witnessBalanceComponentSize hk z a.val) →
      Fin (witnessBalancePairDim k b delta hk)))).repr
        (PiTensorProduct.tprod ℂ x) (witnessBalancePackingPairRestriction hk z hd w)=_
  simp only [Basis.piTensorProduct_repr_tprod_apply,Pi.basisFun_repr]

private theorem words_eq_ambient (hd : delta ≤ 1) :
    witnessBalancePackingTensorWords hk z hd=
      (ambientCoordinates hk z hd).toLinearMap.comp
        (PiTensorProduct.mapIncl (fun a : witnessBalancePackingLabelIndex k delta =>
          (witnessBalanceLocalProjectedFactor hk z a.val).toSubmodule)) := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  funext w
  rw [LinearMap.compMultilinearMap_apply,LinearMap.compMultilinearMap_apply,
    witnessBalancePackingTensorWords_tprod,LinearMap.comp_apply]
  change _=ambientCoordinates hk z hd
    (PiTensorProduct.map (fun a : witnessBalancePackingLabelIndex k delta =>
      (witnessBalanceLocalProjectedFactor hk z a.val).toSubmodule.subtype)
      (PiTensorProduct.tprod ℂ x)) w
  rw [PiTensorProduct.map_tprod,ambientCoordinates_tprod]
  rfl

/-- Injectivity for all projected factors, without a nonzero-factor or common-basis
hypothesis. The private left inverses are only linear, not equivariant. -/
theorem witnessBalancePackingTensorWords_injective (hd : delta ≤ 1) :
    Function.Injective (witnessBalancePackingTensorWords hk z hd) := by
  let inc := fun a : witnessBalancePackingLabelIndex k delta =>
    (witnessBalanceLocalProjectedFactor hk z a.val).toSubmodule.subtype
  have hi : Function.Injective (PiTensorProduct.map inc) := by
    have hl : (PiTensorProduct.map (fun a => (inc a).leftInverse)).comp
        (PiTensorProduct.map inc)=LinearMap.id := by
      rw [← PiTensorProduct.map_comp]
      have he : (fun a => (inc a).leftInverse.comp (inc a))=(fun a => LinearMap.id) := by
        funext a
        exact LinearMap.leftInverse_comp_of_inj
          (witnessBalanceLocalProjectedFactor hk z a.val).toSubmodule.ker_subtype
      rw [he,PiTensorProduct.map_id]
    intro x y h
    have h' := congrArg (PiTensorProduct.map (fun a => (inc a).leftInverse)) h
    simpa only [← LinearMap.comp_apply,hl,LinearMap.id_apply] using h'
  rw [words_eq_ambient]
  exact (ambientCoordinates hk z hd).injective.comp hi

/-- The span of the all-factor pure-word products. Equality of this image with
`range (P J)` is a further obligation about the original carrier and projector. -/
theorem witnessBalancePackingTensorWords_range (hd : delta ≤ 1) :
    (witnessBalancePackingTensorWords hk z hd).range=
      Submodule.span ℂ (Set.range fun x : ∀ a : witnessBalancePackingLabelIndex k delta,
        (witnessBalanceLocalProjectedFactor hk z a.val).toSubmodule =>
          fun w => ∏ a, (x a).val (witnessBalancePackingPairRestriction hk z hd w a)) := by
  rw [← Submodule.map_top,← PiTensorProduct.span_tprod_eq_top,
    Submodule.map_span,← Set.range_comp]
  congr 1
  apply congrArg Set.range
  funext x w
  exact witnessBalancePackingTensorWords_tprod hk z hd x w

/-- The original selector over all label factors, using physical inverse positions;
joint block labels remain distinct. -/
theorem witnessBalancePackingPairWords_iff (hd : delta ≤ 1)
    (w : Fin n → Fin (witnessBalancePairDim k b delta hk)) :
    witnessBalanceComponentWords hk z
      (witnessBalancePairAllowed (k:=k) (b:=b) (delta:=delta) hk)
      (witnessBalancePairLabel (k:=k) (b:=b) (delta:=delta) hk) w ↔
      ∀ a : witnessBalancePackingLabelIndex k delta,
        witnessBalanceLocalPairWords hk z a.val (witnessBalancePackingPairRestriction hk z hd w a) := by
  let E := witnessBalancePackingLabelCut hk z hd
  constructor
  · rintro ⟨hA,hL⟩ a
    refine ⟨fun j => hA (E.symm ⟨a,j⟩),fun j => ?_⟩
    exact (hL (E.symm ⟨a,j⟩)).trans
      (witnessBalancePackingLabelCut_inverse_label hk z hd a j)
  · intro h
    constructor
    · intro i
      have ht := (h (E i).1).1 (E i).2
      change witnessBalancePairAllowed (k:=k) (b:=b) (delta:=delta) hk
        (w (E.symm (E i))) at ht
      rw [E.symm_apply_apply] at ht
      exact ht
    · intro i
      have ht := (h (E i).1).2 (E i).2
      change witnessBalancePairLabel (k:=k) (b:=b) (delta:=delta) hk
        (w (E.symm (E i)))=(E i).1.val at ht
      rw [E.symm_apply_apply] at ht
      exact ht.trans (witnessBalancePackingLabelCut_label hk z hd i)

abbrev witnessBalancePackingAmbientTensorSpace :=
  ⨂[ℂ] a : witnessBalancePackingLabelIndex k delta,
    WordSpace (witnessBalanceComponentSize hk z a.val) (witnessBalancePairDim k b delta hk)

/-- The all-label positional equivalence, with the original common pair alphabet. -/
def witnessBalancePackingPositionTensor (hd : delta ≤ 1) :
    witnessBalancePackingAmbientTensorSpace hk z ≃ₗ[ℂ]
      WordSpace n (witnessBalancePairDim k b delta hk) := ambientCoordinates hk z hd

theorem witnessBalancePackingPositionTensor_tprod (hd : delta ≤ 1)
    (x : ∀ a : witnessBalancePackingLabelIndex k delta,
      WordSpace (witnessBalanceComponentSize hk z a.val) (witnessBalancePairDim k b delta hk))
    (w : Fin n → Fin (witnessBalancePairDim k b delta hk)) :
    witnessBalancePackingPositionTensor hk z hd (PiTensorProduct.tprod ℂ x) w=
      ∏ a, x a (witnessBalancePackingPairRestriction hk z hd w a) :=
  ambientCoordinates_tprod hk z hd x w

/-- Projection split over all vectors, not a stability statement for the unfiltered square. -/
theorem witnessBalancePackingPositionTensor_projection (hd : delta ≤ 1)
    (q : witnessBalancePackingAmbientTensorSpace hk z) :
    coordinateProjection (witnessBalanceComponentWords hk z
      (witnessBalancePairAllowed (k:=k) (b:=b) (delta:=delta) hk)
      (witnessBalancePairLabel (k:=k) (b:=b) (delta:=delta) hk))
        (witnessBalancePackingPositionTensor hk z hd q)=
    witnessBalancePackingPositionTensor hk z hd
      (PiTensorProduct.map (fun a : witnessBalancePackingLabelIndex k delta =>
        coordinateProjection (witnessBalanceLocalPairWords hk z a.val)) q) := by
  induction q using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    simp only [map_smul]
    congr 1
    funext w
    rw [PiTensorProduct.map_tprod]
    change (if witnessBalanceComponentWords hk z
      (witnessBalancePairAllowed (k:=k) (b:=b) (delta:=delta) hk)
      (witnessBalancePairLabel (k:=k) (b:=b) (delta:=delta) hk) w then
        witnessBalancePackingPositionTensor hk z hd (PiTensorProduct.tprod ℂ x) w else 0)=_
    rw [witnessBalancePackingPositionTensor_tprod,witnessBalancePackingPositionTensor_tprod]
    change (if witnessBalanceComponentWords hk z
      (witnessBalancePairAllowed (k:=k) (b:=b) (delta:=delta) hk)
      (witnessBalancePairLabel (k:=k) (b:=b) (delta:=delta) hk) w then
        ∏ a, x a (witnessBalancePackingPairRestriction hk z hd w a) else 0)=
      ∏ a, if witnessBalanceLocalPairWords hk z a.val
        (witnessBalancePackingPairRestriction hk z hd w a) then
          x a (witnessBalancePackingPairRestriction hk z hd w a) else 0
    rw [Fintype.prod_ite_zero,witnessBalancePackingPairWords_iff hk z hd]
    by_cases h : ∀ a : witnessBalancePackingLabelIndex k delta,
      witnessBalanceLocalPairWords hk z a.val (witnessBalancePackingPairRestriction hk z hd w a)
    · simp only [if_pos h]
    · simp only [if_neg h]
  | add x y hx hy => simp only [map_add,hx,hy]

/-- Tensor action of the original `H`, using the all-label inverse. -/
def witnessBalancePackingTensorHAction (hd : delta ≤ 1) :
    Representation ℂ (witnessBalanceGroup hk z) (witnessBalancePackingTensorSpace hk z) :=
  (witnessBalancePackingTensorAction hk z).comp
    (witnessBalancePackingOriginalEquiv hk z hd).symm.toMonoidHom

/-- Physical coordinate return to `H`; no target or other-factor support is used. -/
def witnessBalancePackingTensorHIntertwiner (hd : delta ≤ 1) : Representation.IntertwiningMap
    (witnessBalancePackingTensorHAction hk z hd)
    ((wordRep n (witnessBalancePairDim k b delta hk)).comp (witnessBalanceGroup hk z).subtype) where
  toLinearMap := witnessBalancePackingTensorWords hk z hd
  isIntertwining' g := by
    apply LinearMap.ext
    intro q
    let E := witnessBalancePackingOriginalEquiv hk z hd
    have h := (witnessBalancePackingTensorIntertwiner hk z hd).map_action (E.symm g) q
    change witnessBalancePackingTensorWords hk z hd (witnessBalancePackingTensorAction hk z (E.symm g) q)=
      wordRep n (witnessBalancePairDim k b delta hk) (E (E.symm g)).val
        (witnessBalancePackingTensorWords hk z hd q) at h
    rw [E.apply_symm_apply] at h
    exact h

def witnessBalancePackingTensorImage (hd : delta ≤ 1) : Subrepresentation
    ((wordRep n (witnessBalancePairDim k b delta hk)).comp (witnessBalanceGroup hk z).subtype) where
  toSubmodule := (witnessBalancePackingTensorWords hk z hd).range
  apply_mem_toSubmodule g v hv := by
    obtain ⟨q,rfl⟩ := hv
    exact ⟨witnessBalancePackingTensorHAction hk z hd g q,
      (witnessBalancePackingTensorHIntertwiner hk z hd).map_action g q⟩

end
end
end HSTZ
#print axioms HSTZ.witnessBalancePackingTensorAction
#print axioms HSTZ.witnessBalancePackingTensorAction_tprod
#print axioms HSTZ.witnessBalancePackingPairRestriction
#print axioms HSTZ.witnessBalancePackingTensorWords
#print axioms HSTZ.witnessBalancePackingTensorWords_tprod
#print axioms HSTZ.witnessBalancePackingPairRestriction_action
#print axioms HSTZ.witnessBalancePackingTensorIntertwiner

#print axioms HSTZ.witnessBalancePackingPairEquiv
#print axioms HSTZ.witnessBalancePackingTensorWords_injective
#print axioms HSTZ.witnessBalancePackingTensorWords_range

#print axioms HSTZ.witnessBalancePackingPairWords_iff
#print axioms HSTZ.witnessBalancePackingPositionTensor
#print axioms HSTZ.witnessBalancePackingPositionTensor_tprod
#print axioms HSTZ.witnessBalancePackingPositionTensor_projection
#print axioms HSTZ.witnessBalancePackingTensorHAction
#print axioms HSTZ.witnessBalancePackingTensorHIntertwiner
#print axioms HSTZ.witnessBalancePackingTensorImage
