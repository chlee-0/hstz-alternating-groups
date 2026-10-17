import HSTZ.WitnessPairInducedSupport
import HSTZ.InducedReparam

/-! Core-first block induction at the original witness positions.
Reuses interfaces from OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
The ambient quotient generators and the unequal source alphabets are kept. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped TensorProduct
section Transport
variable (k b delta : ℕ) (hk : 5 ≤ k) {n : ℕ}
  (z : Tableau n (witnessDiagram k b delta hk)) {mu theta : YoungDiagram}
  (u : Tableau (staircase (k-2)).card mu)
  (s : Tableau (witnessComplementSize k b delta) theta)

abbrev witnessTensorConstituent : Representation ℂ
    (witnessPairLabelStabilizer k b delta hk z) (Specht u ⊗[ℂ] Specht s) :=
  (independentTensor (spechtRep u) (spechtRep s)).comp
    (witnessPairLabelBlockEquiv k b delta hk z).symm.toMonoidHom

abbrev witnessBlockTensorInduced := by
  letI : AddCommGroup (Specht u ⊗[ℂ] Specht s) := TensorProduct.addCommGroup
  letI : Module ℂ (Specht u ⊗[ℂ] Specht s) := TensorProduct.leftModule
  exact Representation.ind (sumPermHom (witnessBinaryCut k b delta hk z))
    (independentTensor (spechtRep u) (spechtRep s))

def witnessTensorReparam :=
  @inducedReparam ℂ
    (Equiv.Perm (Fin (staircase (k-2)).card) ×
      Equiv.Perm (Fin (witnessComplementSize k b delta)))
    (witnessPairLabelStabilizer k b delta hk z) (Equiv.Perm (Fin n))
    (Specht u ⊗[ℂ] Specht s)
    inferInstance inferInstance inferInstance inferInstance
    TensorProduct.addCommGroup TensorProduct.leftModule
    (witnessPairLabelBlockEquiv k b delta hk z)
    (witnessPairLabelStabilizer k b delta hk z).subtype
    (witnessTensorConstituent k b delta hk z u s)

/-- The ambient quotient generator is kept without a tensor swap. -/
def witnessTensorReparam_mk (g : Equiv.Perm (Fin n)) (v : Specht u ⊗[ℂ] Specht s) :=
  @inducedReparam_mk ℂ
    (Equiv.Perm (Fin (staircase (k-2)).card) ×
      Equiv.Perm (Fin (witnessComplementSize k b delta)))
    (witnessPairLabelStabilizer k b delta hk z) (Equiv.Perm (Fin n))
    (Specht u ⊗[ℂ] Specht s)
    inferInstance inferInstance inferInstance inferInstance
    TensorProduct.addCommGroup TensorProduct.leftModule
    (witnessPairLabelBlockEquiv k b delta hk z)
    (witnessPairLabelStabilizer k b delta hk z).subtype
    (witnessTensorConstituent k b delta hk z u s) g v

theorem witnessTensorReparam_bijective :
    Function.Bijective (witnessTensorReparam k b delta hk z u s).toLinearMap :=
  @inducedReparam_bijective ℂ
    (Equiv.Perm (Fin (staircase (k-2)).card) ×
      Equiv.Perm (Fin (witnessComplementSize k b delta)))
    (witnessPairLabelStabilizer k b delta hk z) (Equiv.Perm (Fin n))
    (Specht u ⊗[ℂ] Specht s)
    inferInstance inferInstance inferInstance inferInstance
    TensorProduct.addCommGroup TensorProduct.leftModule
    (witnessPairLabelBlockEquiv k b delta hk z)
    (witnessPairLabelStabilizer k b delta hk z).subtype
    (witnessTensorConstituent k b delta hk z u s)

theorem witnessTensorReparam_hom :
    (witnessPairLabelStabilizer k b delta hk z).subtype.comp
      (witnessPairLabelBlockEquiv k b delta hk z).toMonoidHom =
      sumPermHom (witnessBinaryCut k b delta hk z) := by
  apply MonoidHom.ext
  intro gh
  exact witnessPairLabelBlockEquiv_val k b delta hk z gh

theorem witnessTensorReparam_action :
    (witnessTensorConstituent k b delta hk z u s).comp
      (witnessPairLabelBlockEquiv k b delta hk z).toMonoidHom =
      independentTensor (spechtRep u) (spechtRep s) := by
  apply MonoidHom.ext
  intro gh
  apply LinearMap.ext
  intro x
  change independentTensor (spechtRep u) (spechtRep s)
    ((witnessPairLabelBlockEquiv k b delta hk z).symm
      (witnessPairLabelBlockEquiv k b delta hk z gh)) x = _
  rw [MulEquiv.symm_apply_apply]

/-- The bijection specializes to the original core-first block action. -/
theorem witnessTensorReparam_embedding :
    ∃ M : Representation.IntertwiningMap (witnessBlockTensorInduced k b delta hk z u s)
      (witnessPairTensorInduced k b delta hk z u s), Function.Injective M := by
  letI : AddCommGroup (Specht u ⊗[ℂ] Specht s) := TensorProduct.addCommGroup
  letI : Module ℂ (Specht u ⊗[ℂ] Specht s) := TensorProduct.leftModule
  change ∃ M : Representation.IntertwiningMap
    (Representation.ind (sumPermHom (witnessBinaryCut k b delta hk z))
      (independentTensor (spechtRep u) (spechtRep s)))
    (Representation.ind (witnessPairLabelStabilizer k b delta hk z).subtype
      (witnessTensorConstituent k b delta hk z u s)), Function.Injective M
  rw [← witnessTensorReparam_hom k b delta hk z,
    ← witnessTensorReparam_action k b delta hk z u s]
  exact ⟨witnessTensorReparam k b delta hk z u s,
    (witnessTensorReparam_bijective k b delta hk z u s).1⟩
end Transport

/-- Block-induced factor Specht modules embed in the full cyclic module of the
original mixed word. -/
theorem containedWitness_block_induced_embedding
    {h e : ℕ → ℕ} (hh : Antitone h) (he : Antitone e)
    {d m t : ℕ} (k b delta : ℕ) (hp : PaperWitnessGuard k b delta)
    (htm : t ≤ m) (hroom : ∀ c < t, d+e c ≤ h c)
    (hclear : t*d+4 ≤ witnessPathSize k)
    (hcapacity : witnessPathSize k ≤ prefixSum (capacity h d) m)
    (hsize : prefixSum e m = 2*b+delta) (hzero : ∀ c, t ≤ c → e c = 0)
    (mu : YoungDiagram) (u : Tableau (staircase (k-2)).card mu)
    (s : Tableau (witnessComplementSize k b delta)
      (containedWhole h e hh he d (witnessPathSize k) m))
    (hpi : (containedPath h hh d (witnessPathSize k) m).colLen 0 ≤ 4)
    (hc : ColumnParity (containedAttachment e he m).colLen delta)
    (hE : (containedAttachment e he m).rowLen 0 ≤ 4) {n : ℕ}
    (z : Tableau n (witnessDiagram k b delta hp.staircase_bound)) :
    ∃ F : Representation.IntertwiningMap
      (witnessBlockTensorInduced k b delta hp.staircase_bound z u s)
      (cyclic (wordRep n ((witnessDiagram k b delta hp.staircase_bound).transpose.colLen 0 *
        (witnessDiagram k b delta hp.staircase_bound).colLen 0))
        (witnessMixedWord k b delta hp.staircase_bound z)).toRepresentation,
      Function.Injective F := by
  obtain ⟨M,hM⟩ := witnessTensorReparam_embedding k b delta hp.staircase_bound z u s
  obtain ⟨N,hN⟩ := containedWitness_induced_embedding hh he k b delta hp
    htm hroom hclear hcapacity hsize hzero mu u s hpi hc hE z
  exact ⟨N.comp M,hN.comp hM⟩
end
end HSTZ
#check HSTZ.witnessTensorReparam_mk
#print axioms HSTZ.witnessTensorReparam_mk
#print axioms HSTZ.witnessTensorReparam_bijective
#print axioms HSTZ.witnessTensorReparam_hom
#print axioms HSTZ.witnessTensorReparam_action
#print axioms HSTZ.witnessTensorReparam_embedding
#print axioms HSTZ.containedWitness_block_induced_embedding
