import HSTZ.FinsuppAction
import HSTZ.WitnessPairStabilizer
import HSTZ.InducedEmbedding

/-! Induction for the asymmetric witness and the common-mask Maschke lift.
Reuses interfaces from OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
The source is an induced factor tensor, not a chosen Young target. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped Classical TensorProduct

def witnessPairFilter (k b delta : ℕ) (hk : 5 ≤ k) (n : ℕ) :
    Representation.IntertwiningMap (witnessPairRep k b delta hk (n := n))
      (witnessPairRep k b delta hk (n := n)) :=
  coordinateFilterIntertwiner (witnessSameMarkedWords n
    ((witnessDiagram k b delta hk).transpose.colLen 0)
    ((witnessDiagram k b delta hk).colLen 0) k b)
    (witnessSameMarkedWords_invariant _ _ _ k b)

/-- Concrete tensor instances keep the two Specht carriers explicit. -/
abbrev witnessPairTensorInduced (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (z : Tableau n (witnessDiagram k b delta hk)) {mu theta : YoungDiagram}
    (u : Tableau (staircase (k-2)).card mu)
    (s : Tableau (witnessComplementSize k b delta) theta) := by
  letI : AddCommGroup (Specht u ⊗[ℂ] Specht s) := TensorProduct.addCommGroup
  letI : Module ℂ (Specht u ⊗[ℂ] Specht s) := TensorProduct.leftModule
  exact Representation.ind (witnessPairLabelStabilizer k b delta hk z).subtype
    ((independentTensor (spechtRep u) (spechtRep s)).comp
      (witnessPairLabelBlockEquiv k b delta hk z).symm.toMonoidHom)

private abbrev finitePairRep (n D E : ℕ) : Representation ℂ (Equiv.Perm (Fin n))
    (PositionWord (Fin n) (Fin D × Fin E) →₀ ℂ) := finsuppAction ℂ _ _

/-- Private specialization reusing the existing injection proof. -/
private def finiteInducedInjection {H U V : Type*} [Group H] [Finite H]
    [NeZero (Nat.card H : ℂ)] [AddCommGroup U] [Module ℂ U]
    [AddCommGroup V] [Module ℂ V] (n : ℕ) (f : H →* Equiv.Perm (Fin n))
    (tau : Representation ℂ H U) (sigma : Representation ℂ H V)
    (j : Representation.IntertwiningMap tau sigma) (hj : Function.Injective j) :=
  inducedMap_injective f j hj

/-- Private finite-word application of the existing induction and Maschke maps. -/
private theorem finitePair_induced_lift {n D E : ℕ}
    (label : PositionWord (Fin n) Bool)
    (v w : PositionWord (Fin n) (Fin D × Fin E) →₀ ℂ)
    (phi : Representation.IntertwiningMap (finitePairRep n D E) (finitePairRep n D E))
    (hv : phi w = v)
    (hb : Function.Bijective (sectorInductionMap (finitePairRep n D E)
      (labelOrbitBase (Equiv.Perm (Fin n)) label) v))
    {U : Type*} [AddCommGroup U] [Module ℂ U]
    (tau : Representation ℂ (MulAction.stabilizer (Equiv.Perm (Fin n))
      (labelOrbitBase (Equiv.Perm (Fin n)) label)) U)
    (j : Representation.IntertwiningMap tau (stabilizerRepresentation (finitePairRep n D E)
      (labelOrbitBase (Equiv.Perm (Fin n)) label) v)) (hj : Function.Injective j) :
    ∃ F : Representation.IntertwiningMap
      (Representation.ind (MulAction.stabilizer (Equiv.Perm (Fin n))
        (labelOrbitBase (Equiv.Perm (Fin n)) label)).subtype tau)
      (cyclicSubrepresentation (finitePairRep n D E) w).toRepresentation,
      Function.Injective F := by
  letI : NeZero (Nat.card (MulAction.stabilizer (Equiv.Perm (Fin n))
      (labelOrbitBase (Equiv.Perm (Fin n)) label)) : ℂ) :=
    ⟨by exact_mod_cast (Nat.card_pos : 0 < Nat.card (MulAction.stabilizer
      (Equiv.Perm (Fin n)) (labelOrbitBase (Equiv.Perm (Fin n)) label))).ne'⟩
  letI : NeZero (Nat.card (Equiv.Perm (Fin n)) : ℂ) :=
    ⟨by exact_mod_cast (Nat.card_pos : 0 < Nat.card (Equiv.Perm (Fin n))).ne'⟩
  let J := (sectorInductionMap (finitePairRep n D E)
    (labelOrbitBase (Equiv.Perm (Fin n)) label) v).comp
    (inducedMap (MulAction.stabilizer (Equiv.Perm (Fin n))
      (labelOrbitBase (Equiv.Perm (Fin n)) label)).subtype j)
  have hT := @finiteInducedInjection
    (MulAction.stabilizer (Equiv.Perm (Fin n))
      (labelOrbitBase (Equiv.Perm (Fin n)) label)) U
    (stabilizerCyclic (finitePairRep n D E)
      (labelOrbitBase (Equiv.Perm (Fin n)) label) v)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance n
    (MulAction.stabilizer (Equiv.Perm (Fin n))
      (labelOrbitBase (Equiv.Perm (Fin n)) label)).subtype tau
    (stabilizerRepresentation (finitePairRep n D E)
      (labelOrbitBase (Equiv.Perm (Fin n)) label) v) j hj
  have hJ : Function.Injective J := by
    intro x y hxy
    apply hT
    exact hb.1 hxy
  have hJ' : ∃ J' : Representation.IntertwiningMap
      (Representation.ind (MulAction.stabilizer (Equiv.Perm (Fin n))
        (labelOrbitBase (Equiv.Perm (Fin n)) label)).subtype tau)
      (cyclicSubrepresentation (finitePairRep n D E) (phi w)).toRepresentation,
      Function.Injective J' := by
    rw [hv]
    exact ⟨J,hJ⟩
  obtain ⟨J',hJ'⟩ := hJ'
  obtain ⟨F,hF,_⟩ := cyclicImage_embedding_lift phi w J' hJ'
  exact ⟨F,hF⟩

private theorem witnessPair_induced_lift (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
    (z : Tableau n (witnessDiagram k b delta hk)) {U : Type*}
    [AddCommGroup U] [Module ℂ U]
    (tau : Representation ℂ (witnessPairLabelStabilizer k b delta hk z) U)
    (j : Representation.IntertwiningMap tau (witnessPairStabilizerRepresentation k b delta hk z))
    (hj : Function.Injective j) :
    ∃ F : Representation.IntertwiningMap
      (Representation.ind (witnessPairLabelStabilizer k b delta hk z).subtype tau)
      (cyclic (wordRep n ((witnessDiagram k b delta hk).transpose.colLen 0 *
        (witnessDiagram k b delta hk).colLen 0))
        (witnessMixedWord k b delta hk z)).toRepresentation, Function.Injective F := by
  obtain ⟨i,hi⟩ := finitePair_induced_lift
    (witnessCorePairLabel k b delta hk z) (witnessPairCut k b delta hk z)
    (witnessPairGenerator k b delta hk z) (witnessPairFilter k b delta hk n) rfl
    (witnessPairCut_induction_bijective k b delta hk z) tau j hj
  let enc := encodedPairModelIntertwiner n
    ((witnessDiagram k b delta hk).transpose.colLen 0)
    ((witnessDiagram k b delta hk).colLen 0)
  let M := cyclicImageMap enc (witnessPairGenerator k b delta hk z)
  have hM : Function.Injective M := by
    intro x y heq
    apply Subtype.ext
    exact (encodedPairModelIntertwiner_bijective _ _ _).1 (congrArg Subtype.val heq)
  have hgen : enc (witnessPairGenerator k b delta hk z) =
    witnessMixedWord k b delta hk z :=
    encodedPair_witnessGenerator k b delta hk z
  have hF : ∃ F : Representation.IntertwiningMap
      (Representation.ind (witnessPairLabelStabilizer k b delta hk z).subtype tau)
      (cyclicSubrepresentation (wordRep n _)
        (enc (witnessPairGenerator k b delta hk z))).toRepresentation,
      Function.Injective F := ⟨M.comp i,hM.comp hi⟩
  rw [hgen] at hF
  exact hF

/-- Ordinary induction of both factor Specht modules embeds in the full cyclic module
of the original mixed word. All sector and filter inputs are proved. -/
theorem containedWitness_induced_embedding
    {h e : ℕ → ℕ} (hh : Antitone h) (he : Antitone e)
    {d m t : ℕ} (k b delta : ℕ) (hp : PaperWitnessGuard k b delta)
    (htm : t ≤ m) (hroom : ∀ c < t, d+e c≤h c) (hclear : t*d+4≤witnessPathSize k)
    (hcapacity : witnessPathSize k≤prefixSum (capacity h d) m)
    (hsize : prefixSum e m=2*b+delta) (hzero : ∀ c, t ≤ c → e c = 0)
    (mu : YoungDiagram) (u : Tableau (staircase (k-2)).card mu)
    (s : Tableau (witnessComplementSize k b delta)
      (containedWhole h e hh he d (witnessPathSize k) m))
    (hpi : (containedPath h hh d (witnessPathSize k) m).colLen 0≤4)
    (hc : ColumnParity (containedAttachment e he m).colLen delta)
    (hE : (containedAttachment e he m).rowLen 0≤4) {n : ℕ}
    (z : Tableau n (witnessDiagram k b delta hp.staircase_bound)) :
    ∃ F : Representation.IntertwiningMap
      (witnessPairTensorInduced k b delta hp.staircase_bound z u s)
      (cyclic (wordRep n ((witnessDiagram k b delta hp.staircase_bound).transpose.colLen 0 *
        (witnessDiagram k b delta hp.staircase_bound).colLen 0))
        (witnessMixedWord k b delta hp.staircase_bound z)).toRepresentation,
      Function.Injective F := by
  letI : AddCommGroup (Specht u ⊗[ℂ] Specht s) := TensorProduct.addCommGroup
  letI : Module ℂ (Specht u ⊗[ℂ] Specht s) := TensorProduct.leftModule
  obtain ⟨j,hj⟩ := containedWitness_pair_stabilizer_embedding hh he k b delta hp
    htm hroom hclear hcapacity hsize hzero mu u s hpi hc hE z
  exact witnessPair_induced_lift k b delta hp.staircase_bound z _ j hj

end
end HSTZ
#print axioms HSTZ.witnessPairFilter
#print axioms HSTZ.containedWitness_induced_embedding
