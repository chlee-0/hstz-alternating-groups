import HSTZ.BalanceEvenPrecursor
import HSTZ.BalanceSingletonSupport
import HSTZ.PieriBlock
import HSTZ.OneRowInduction
import HSTZ.ContainedProductSupport

/-! Local two-row Pieri support in the ordinary induction of the two filtered
square factors. Uses declarations from OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
This file does not identify the induced module with the full balance component or
packing. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped TensorProduct

def balanceEvenSingletonInduced (m x : ℕ)
    (z : Tableau (witnessAttachment m 0).card (witnessAttachment m 0))
    (u : Tableau x (oneRowDiagram x).transpose)
    (e : Fin ((witnessAttachment m 0).card+x) ≃
      Fin (witnessAttachment m 0).card ⊕ Fin x) := by
  let W := balanceProjectedSquare z (balanceInOutputs ({2} : Set ℕ))
    (balanceInOutputs_invariant ({2} : Set ℕ))
  let V := balanceProjectedSquare u (balanceInOutputs ({x} : Set ℕ))
    (balanceInOutputs_invariant ({x} : Set ℕ))
  letI : AddCommGroup (W.toSubmodule ⊗[ℂ] V.toSubmodule) := TensorProduct.addCommGroup
  letI : Module ℂ (W.toSubmodule ⊗[ℂ] V.toSubmodule) := TensorProduct.leftModule
  exact Representation.ind (A := W.toSubmodule ⊗[ℂ] V.toSubmodule) (sumPermHom e)
    (independentTensor W.toRepresentation V.toRepresentation)

/-- Every target Specht module with at most two rows embeds in the ordinary
induction of the two local factors along the core-first block homomorphism. The
placement and the even precursor are constructed in the proof. -/
theorem balanceEvenSingleton_induced_support (m x : ℕ) (hm : 1 ≤ m)
    (hx : x=1 ∨ x=3) (hlegal : x≤2*m+1)
    (z : Tableau (witnessAttachment m 0).card (witnessAttachment m 0))
    (u : Tableau x (oneRowDiagram x).transpose)
    (e : Fin ((witnessAttachment m 0).card+x) ≃
      Fin (witnessAttachment m 0).card ⊕ Fin x)
    {nu : YoungDiagram} (t : Tableau ((witnessAttachment m 0).card+x) nu)
    (ht : nu.colLen 0≤2) :
    ∃ J : Representation.IntertwiningMap (spechtRep t)
      (balanceEvenSingletonInduced m x z u e), Function.Injective J := by
  classical
  obtain ⟨xi,s,he,hh,hstrip,_,_⟩ := balanceEvenPrecursor_pieri m x hx hlegal t ht
  let aligned := containedBlockTableau s t hstrip.1 e
  have hi := containedBlockTableau_matching s t hstrip.1 e
  obtain ⟨E,hE⟩ := pieri_block_embedding s aligned hstrip e hi
  let Q := tableauSpechtMap t aligned
  have hQ : Function.Injective Q := (tableauSpechtMap_bijective t aligned).1
  let P := oneRowInducedMap (spechtRep s) (oneRowTableau x)
    (oneRowDiagram_rows x) (sumPermHom e)
  have hP : Function.Injective P := oneRowInducedMap_injective
    (spechtRep s) (oneRowTableau x) (oneRowDiagram_rows x) (sumPermHom e)
  obtain ⟨B,hB⟩ := balanceOutputTwo_projected_support m hm z s he hh
  obtain ⟨C,hC⟩ := balanceSingleton_projected_support x u
  let W := balanceProjectedSquare z (balanceInOutputs ({2} : Set ℕ))
    (balanceInOutputs_invariant ({2} : Set ℕ))
  let V := balanceProjectedSquare u (balanceInOutputs ({x} : Set ℕ))
    (balanceInOutputs_invariant ({x} : Set ℕ))
  let H := Equiv.Perm (Fin (witnessAttachment m 0).card) × Equiv.Perm (Fin x)
  let G := Equiv.Perm (Fin ((witnessAttachment m 0).card+x))
  let S := Specht s ⊗[ℂ] Specht (oneRowTableau x)
  let T := W.toSubmodule ⊗[ℂ] V.toSubmodule
  letI : NeZero (Nat.card H : ℂ) :=
    ⟨by exact_mod_cast (Nat.card_pos : 0<Nat.card H).ne'⟩
  let D := independentTensorMap B C
  have hD : Function.Injective D := independentTensorMap_injective B C hB hC
  let I := @inducedMap ℂ H G S T
    inferInstance inferInstance inferInstance
    TensorProduct.addCommGroup TensorProduct.leftModule
    TensorProduct.addCommGroup TensorProduct.leftModule
    _ _ (sumPermHom e) D
  have hI : Function.Injective I :=
    @inducedMap_injective ℂ H G S T
      inferInstance inferInstance inferInstance inferInstance inferInstance
      TensorProduct.addCommGroup TensorProduct.leftModule
      TensorProduct.addCommGroup TensorProduct.leftModule
      _ _ (sumPermHom e) D hD
  exact ⟨I.comp (P.comp (E.comp Q)),hI.comp (hP.comp (hE.comp hQ))⟩

end
end HSTZ
#print axioms HSTZ.balanceEvenSingletonInduced
#print axioms HSTZ.balanceEvenSingleton_induced_support
