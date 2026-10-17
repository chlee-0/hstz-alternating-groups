import HSTZ.IntertwiningCompat
import HSTZ.YoungDiagramCompat
import HSTZ.WitnessContainedSupport
import HSTZ.SpechtSignTransport
import OAI.RepresentationTheory.Saxl.StaircaseSign

/-! Guarded witness capacity criterion, with the target transposed. Uses interfaces
from OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
This file does not cover all targets, does not use the paper's kappa, and draws no
conclusion about A_n. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped TensorProduct

private def nativeSpechtPair {n : ℕ} {mu : YoungDiagram} (z : Tableau n mu) :=
  (encodedPairModelIntertwiner n (mu.transpose.colLen 0) (mu.colLen 0)).comp
    (pairedSpechtTensorMap (transposeTableau z) z)

private theorem nativeSpechtPair_generator {n : ℕ} {mu : YoungDiagram}
    (z : Tableau n mu) :
    nativeSpechtPair z (spechtTensorGenerator (transposeTableau z) z) =
      wordTensor n _ _ (polytabloid (transposeTableau z) ⊗ₜ[ℂ] polytabloid z) := by
  change encodedPairModelEquiv n _ _ (pairedSpechtTensorMap (transposeTableau z) z
    (spechtTensorGenerator (transposeTableau z) z)) = _
  unfold spechtTensorGenerator
  rw [pairedSpechtTensorMap_generator,encodedPair_tensor_tmul]
  simp only [wordPolytabloid,LinearEquiv.apply_symm_apply]

/-- Concrete pair-word cyclic consumer into the diagonal Specht tensor. -/
private theorem nativePair_target_embedding {n : ℕ} {mu nu : YoungDiagram}
    (z : Tableau n mu) (target : Tableau n nu)
    (J : Representation.IntertwiningMap (spechtRep target)
      (cyclic (wordRep n (mu.transpose.colLen 0 * mu.colLen 0))
        (wordTensor n _ _ (polytabloid (transposeTableau z) ⊗ₜ[ℂ] polytabloid z))).toRepresentation)
    (hJ : Function.Injective J) :
    ∃ F : Representation.IntertwiningMap (spechtRep target)
      ((spechtRep (transposeTableau z)).tprod (spechtRep z)), Function.Injective F := by
  letI : AddCommGroup (Specht (transposeTableau z) ⊗[ℂ] Specht z) := TensorProduct.addCommGroup
  letI : Module ℂ (Specht (transposeTableau z) ⊗[ℂ] Specht z) := TensorProduct.leftModule
  letI : NeZero (Nat.card (Equiv.Perm (Fin n)) : ℂ) :=
    ⟨by exact_mod_cast (Nat.card_pos : 0 < Nat.card (Equiv.Perm (Fin n))).ne'⟩
  have hJ' : ∃ J' : Representation.IntertwiningMap (spechtRep target)
      (cyclicSubrepresentation (wordRep n _)
        (nativeSpechtPair z (spechtTensorGenerator (transposeTableau z) z))).toRepresentation,
      Function.Injective J' := by
    rw [nativeSpechtPair_generator]
    exact ⟨J,hJ⟩
  obtain ⟨J',hJ'⟩ := hJ'
  obtain ⟨F,hF,_⟩ := cyclicImage_embedding_lift (nativeSpechtPair z)
    (spechtTensorGenerator (transposeTableau z) z) J' hJ'
  let inc : Representation.IntertwiningMap
      (cyclicSubrepresentation ((spechtRep (transposeTableau z)).tprod (spechtRep z))
        (spechtTensorGenerator (transposeTableau z) z)).toRepresentation
      ((spechtRep (transposeTableau z)).tprod (spechtRep z)) :=
    { toLinearMap := Submodule.subtype _
      isIntertwining' _ := LinearMap.ext (fun _ => rfl) }
  have hi : Function.Injective inc := fun _ _ he => Subtype.ext he
  exact ⟨inc.comp F,hi.comp hF⟩

/-- The sign inverse on the first factor cancels the sign of the whole diagonal tensor. -/
private def originalSquareSignMap {n : ℕ} {mu : YoungDiagram} (z : Tableau n mu) :
    Representation.IntertwiningMap
      (@signTwist n (Specht (transposeTableau z) ⊗[ℂ] Specht z)
        TensorProduct.addCommGroup TensorProduct.leftModule
        ((spechtRep (transposeTableau z)).tprod (spechtRep z)))
      ((spechtRep z).tprod (spechtRep z)) where
  toLinearMap := TensorProduct.map (spechtSignInverseMap z).toLinearMap LinearMap.id
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    have heq : (TensorProduct.map (spechtSignInverseMap z).toLinearMap LinearMap.id).comp
        (@signTwist n (Specht (transposeTableau z) ⊗[ℂ] Specht z)
          TensorProduct.addCommGroup TensorProduct.leftModule
          ((spechtRep (transposeTableau z)).tprod (spechtRep z)) g) =
      ((spechtRep z).tprod (spechtRep z) g).comp
        (TensorProduct.map (spechtSignInverseMap z).toLinearMap LinearMap.id) := by
      apply TensorProduct.ext
      apply LinearMap.ext
      intro x
      apply LinearMap.ext
      intro y
      change TensorProduct.map (spechtSignInverseMap z).toLinearMap LinearMap.id
        (signC g • (spechtRep (transposeTableau z) g x ⊗ₜ[ℂ] spechtRep z g y)) = _
      rw [map_smul,TensorProduct.map_tmul]
      have hf := (spechtSignInverseMap z).map_action g x
      change (spechtSignInverseMap z).toLinearMap
        (signC g • spechtRep (transposeTableau z) g x) =
        spechtRep z g ((spechtSignInverseMap z).toLinearMap x) at hf
      rw [map_smul] at hf
      change signC g • ((spechtSignInverseMap z).toLinearMap
        (spechtRep (transposeTableau z) g x) ⊗ₜ[ℂ] spechtRep z g y) =
        spechtRep z g ((spechtSignInverseMap z).toLinearMap x) ⊗ₜ[ℂ] spechtRep z g y
      rw [TensorProduct.smul_tmul']
      exact congrArg (fun a : Specht z => a ⊗ₜ[ℂ] spechtRep z g y) hf
    exact DFunLike.congr_fun heq v

private theorem originalSquareSignMap_injective {n : ℕ} {mu : YoungDiagram}
    (z : Tableau n mu) : Function.Injective (originalSquareSignMap z) :=
  (TensorProduct.congr (spechtSignEquiv z).symm (LinearEquiv.refl ℂ (Specht z))).injective

/-- The sign map from the Specht module of the transposed original target into the sign
twist of the target's Specht module. -/
private def targetTransposeSign {n : ℕ} {nu : YoungDiagram} (target : Tableau n nu) :
    Representation.IntertwiningMap (spechtRep (transposeTableau target))
      (signTwist (spechtRep target)) where
  toLinearMap := (spechtSignInverseMap target).toLinearMap
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    have he := (signTwistMap (spechtSignInverseMap target)).map_action g x
    change (spechtSignInverseMap target).toLinearMap
      (signC g • (signC g • spechtRep (transposeTableau target) g x)) = _ at he
    rw [smul_smul,signC_mul_self,one_smul] at he
    exact he

private theorem targetTransposeSign_injective {n : ℕ} {nu : YoungDiagram}
    (target : Tableau n nu) : Function.Injective (targetTransposeSign target) :=
  (spechtSignEquiv target).symm.injective

/-- Capacity support in the original diagonal square with target nu^t.
All geometric guards remain as hypotheses. -/
theorem containedWitness_square_target_embedding
    {e : ℕ → ℕ} (he : Antitone e) {d m t : ℕ}
    (k b delta : ℕ) (hp : PaperWitnessGuard k b delta) {n : ℕ} {nu : YoungDiagram}
    (target : Tableau n nu) (htm : t ≤ m)
    (hroom : ∀ c < t, d+e c ≤ nu.colLen c)
    (hclear : t*d+4 ≤ witnessPathSize k)
    (hcapacity : witnessPathSize k ≤ prefixSum (capacity nu.colLen d) m)
    (hsize : prefixSum e m = 2*b+delta) (hzero : ∀ c, t ≤ c → e c = 0)
    (hpi : (containedPath nu.colLen nu.colLen_antitone d (witnessPathSize k) m).colLen 0 ≤ 4)
    (hc : ColumnParity (containedAttachment e he m).colLen delta)
    (hE : (containedAttachment e he m).rowLen 0 ≤ 4)
    (z : Tableau n (witnessDiagram k b delta hp.staircase_bound)) :
    ∃ F : Representation.IntertwiningMap (spechtRep (transposeTableau target))
      ((spechtRep z).tprod (spechtRep z)), Function.Injective F := by
  obtain ⟨J,hJ⟩ := containedWitness_target_capacity_canonical_embedding he k b delta hp
    target htm hroom hclear hcapacity hsize hzero hpi hc hE z
  obtain ⟨N,hN⟩ := nativePair_target_embedding z target J hJ
  let F := (originalSquareSignMap z).comp ((@signTwistMap n (Specht target) (Specht (transposeTableau z) ⊗[ℂ] Specht z)
      inferInstance inferInstance TensorProduct.addCommGroup TensorProduct.leftModule
      (spechtRep target) ((spechtRep (transposeTableau z)).tprod (spechtRep z)) N).comp
      (targetTransposeSign target))
  exact ⟨F,(originalSquareSignMap_injective z).comp
    (hN.comp (targetTransposeSign_injective target))⟩

/-- Guarded capacity conclusion; the target orientation is nu^t. -/
theorem containedWitness_capacity_kronecker_pos
    {e : ℕ → ℕ} (he : Antitone e) {d m t : ℕ}
    (k b delta : ℕ) (hp : PaperWitnessGuard k b delta) {n : ℕ} {nu : YoungDiagram}
    (target : Tableau n nu) (htm : t ≤ m)
    (hroom : ∀ c < t, d+e c ≤ nu.colLen c)
    (hclear : t*d+4 ≤ witnessPathSize k)
    (hcapacity : witnessPathSize k ≤ prefixSum (capacity nu.colLen d) m)
    (hsize : prefixSum e m = 2*b+delta) (hzero : ∀ c, t ≤ c → e c = 0)
    (hpi : (containedPath nu.colLen nu.colLen_antitone d (witnessPathSize k) m).colLen 0 ≤ 4)
    (hc : ColumnParity (containedAttachment e he m).colLen delta)
    (hE : (containedAttachment e he m).rowLen 0 ≤ 4)
    (z : Tableau n (witnessDiagram k b delta hp.staircase_bound)) :
    0 < kronecker z z (transposeTableau target) := by
  obtain ⟨F,hF⟩ := containedWitness_square_target_embedding he k b delta hp target htm
    hroom hclear hcapacity hsize hzero hpi hc hE z
  apply (kronecker_pos_iff z z (transposeTableau target)).mpr
  refine ⟨F,?_⟩
  intro hz
  have hx : (⟨polytabloid (transposeTableau target),mem_cyclic _ _⟩ :
      Specht (transposeTableau target)) = 0 := by
    apply hF
    rw [hz]
    rfl
  exact polytabloid_ne_zero (transposeTableau target) (congrArg Subtype.val hx)
/-- Concrete witness consumer for a transposed mixed-word target.
It uses the original target sign map rather than a double-tableau identity. -/
theorem witnessMixed_transposed_target_pos (k b delta : ℕ) (hp : PaperWitnessGuard k b delta)
    {n : ℕ} {nu : YoungDiagram} (target : Tableau n nu)
    (z : Tableau n (witnessDiagram k b delta hp.staircase_bound))
    (J : Representation.IntertwiningMap (spechtRep (transposeTableau target))
      (cyclic (wordRep n ((witnessDiagram k b delta hp.staircase_bound).transpose.colLen 0 *
        (witnessDiagram k b delta hp.staircase_bound).colLen 0))
        (witnessMixedWord k b delta hp.staircase_bound z)).toRepresentation)
    (hJ : Function.Injective J) : 0 < kronecker z z target := by
  obtain ⟨N,hN⟩ := nativePair_target_embedding z (transposeTableau target) J hJ
  let F := (originalSquareSignMap z).comp ((@signTwistMap n
    (Specht (transposeTableau target)) (Specht (transposeTableau z) ⊗[ℂ] Specht z)
    inferInstance inferInstance TensorProduct.addCommGroup TensorProduct.leftModule
    (spechtRep (transposeTableau target))
    ((spechtRep (transposeTableau z)).tprod (spechtRep z)) N).comp
    (spechtSignMap target))
  have hF : Function.Injective F := (originalSquareSignMap_injective z).comp
    (hN.comp (spechtSignMap_bijective target).1)
  apply (kronecker_pos_iff z z target).mpr
  refine ⟨F,?_⟩
  intro hz
  have hx : (⟨polytabloid target,mem_cyclic _ _⟩ : Specht target) = 0 := by
    apply hF
    rw [hz]
    rfl
  exact polytabloid_ne_zero target (congrArg Subtype.val hx)

end
end HSTZ
#print axioms HSTZ.containedWitness_square_target_embedding
#print axioms HSTZ.containedWitness_capacity_kronecker_pos

#print axioms HSTZ.witnessMixed_transposed_target_pos
