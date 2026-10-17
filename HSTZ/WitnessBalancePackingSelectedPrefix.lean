import HSTZ.WitnessBalancePackingProduct
import OAI.RepresentationTheory.Saxl.SpechtClassification

import Mathlib.Algebra.Category.Grp.FiniteGrp

/-! Ordered prefixes of the selected source. Each prefix stores its group, its
module and its homomorphism to the ambient permutation group together. The prefix
source involves no induction, and these cuts are not yet aligned with the physical
groups K and H. Uses declarations from OpenAI's `math` repository (commit adc7f1241, Apache-2.0). -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped TensorProduct Classical

private structure PrefixData (m : ℕ) where
  group : FiniteGrp
  module : Rep ℂ group
  hom : group →* Equiv.Perm (Fin m)

private def prefixZero (nu : YoungDiagram) : PrefixData nu.card where
  group := FiniteGrp.of (Equiv.Perm (Fin nu.card))
  module := Rep.of (spechtRep (shapeTableau nu))
  hom := MonoidHom.id _

private def prefixStep {m r : ℕ} (d : ℕ) (hc : r=m+d)
    (p : Nat.Partition d) (A : PrefixData m) : PrefixData r := by
  letI : AddCommGroup ((A.module : Type) ⊗[ℂ] Specht (partitionTableau p)) :=
    TensorProduct.addCommGroup
  letI : Module ℂ ((A.module : Type) ⊗[ℂ] Specht (partitionTableau p)) :=
    TensorProduct.leftModule
  exact {
    group := FiniteGrp.of (A.group × Equiv.Perm (Fin d))
    module := Rep.of (independentTensor (Rep.ρ A.module) (spechtRep (partitionTableau p)))
    hom := (sumPermHom ((finCongr hc).trans finSumFinEquiv.symm)).comp
      (A.hom.prodMap (MonoidHom.id _)) }

section Actual
variable {k b delta n : ℕ} (hk : 5 ≤ k) (z : Tableau n (witnessDiagram k b delta hk))

/-- The physical degree (number of positions) of the `i`-th block, in block
order. -/
abbrev witnessBalancePackingSelectedDegree
    (i : Fin (witnessBalancePackingBlocks k delta).length) : ℕ :=
  Fintype.card {v : Fin n // witnessBalancePackingPositionKind hk z v=
    (witnessBalancePackingBlocks k delta)[i.val]}

/-- The cut at the boundary between consecutive diagrams, with the local physical
degree. -/
def witnessBalancePackingSelectedCut
    (i : Fin (witnessBalancePackingBlocks k delta).length)
    (nu tau : YoungDiagram)
    (hc : tau.card=nu.card+witnessBalancePackingSelectedDegree hk z i) :=
  (finCongr hc).trans finSumFinEquiv.symm

private def actualPrefix
    (D : Fin ((witnessBalancePackingBlocks k delta).length+1) → YoungDiagram)
    (hc : ∀ i : Fin (witnessBalancePackingBlocks k delta).length,
      (D i.succ).card=(D i.castSucc).card+witnessBalancePackingSelectedDegree hk z i)
    (p : ∀ i, Nat.Partition (witnessBalancePackingSelectedDegree hk z i)) :
    ∀ j : Fin ((witnessBalancePackingBlocks k delta).length+1), PrefixData (D j).card :=
  Fin.induction (prefixZero (D 0))
    (fun i A => prefixStep (witnessBalancePackingSelectedDegree hk z i) (hc i) (p i) A)

/-- The group of the `j`-th prefix: an ordered finite product starting from the
initial boundary group. -/
abbrev witnessBalancePackingSelectedPrefixGroup D hc p j :=
  (actualPrefix hk z D hc p j).group

/-- The module of the `j`-th prefix: the selected local Specht modules tensored in
order, without induction. -/
def witnessBalancePackingSelectedPrefixModule D hc p j :=
  (actualPrefix hk z D hc p j).module

/-- The homomorphism of the `j`-th prefix, built from the boundary cuts at every
step. -/
def witnessBalancePackingSelectedPrefixHom D hc p j :=
  (actualPrefix hk z D hc p j).hom

/-- The next prefix: the previous prefix tensored with the selected local Specht
module for `p i`. -/
def witnessBalancePackingSelectedPrefixExtension D hc p
    (i : Fin (witnessBalancePackingBlocks k delta).length) :=
  prefixStep (witnessBalancePackingSelectedDegree hk z i) (hc i) (p i)
    (actualPrefix hk z D hc p i.castSucc)

/-- The successor prefix equals the extension as data: group, module and
homomorphism. -/
theorem witnessBalancePackingSelectedPrefix_succ D hc p
    (i : Fin (witnessBalancePackingBlocks k delta).length) :
    actualPrefix hk z D hc p i.succ=
      witnessBalancePackingSelectedPrefixExtension hk z D hc p i := by
  simp only [actualPrefix,witnessBalancePackingSelectedPrefixExtension,Fin.induction_succ]

/-- The initial prefix: the full symmetric group, the Specht module of `D 0` and the
identity homomorphism. -/
theorem witnessBalancePackingSelectedPrefix_zero D hc p :
    actualPrefix hk z D hc p 0=prefixZero (D 0) := by
  simp only [actualPrefix,Fin.induction_zero]

/-- The product homomorphism before the next boundary cut is applied. -/
def witnessBalancePackingSelectedPrefixProductHom D hc p
    (i : Fin (witnessBalancePackingBlocks k delta).length) :=
  (witnessBalancePackingSelectedPrefixHom hk z D hc p i.castSucc).prodMap
    (MonoidHom.id (Equiv.Perm (Fin (witnessBalancePackingSelectedDegree hk z i))))

/-- The local tensor source used by both the factorization and the transitivity
steps. -/
def witnessBalancePackingSelectedPrefixTensorAction D hc p
    (i : Fin (witnessBalancePackingBlocks k delta).length) :=
  independentTensor (Rep.ρ (witnessBalancePackingSelectedPrefixModule hk z D hc p i.castSucc))
    (spechtRep (partitionTableau (p i)))

/-- The product homomorphism followed by the next boundary cut. -/
def witnessBalancePackingSelectedPrefixNextHom D hc p
    (i : Fin (witnessBalancePackingBlocks k delta).length) :=
  (sumPermHom (witnessBalancePackingSelectedCut hk z i
    (D i.castSucc) (D i.succ) (hc i))).comp
      (witnessBalancePackingSelectedPrefixProductHom hk z D hc p i)

end Actual
end
end HSTZ
#print axioms HSTZ.witnessBalancePackingSelectedPrefixModule
#print axioms HSTZ.witnessBalancePackingSelectedPrefixHom
#print axioms HSTZ.witnessBalancePackingSelectedPrefix_succ

#print axioms HSTZ.witnessBalancePackingSelectedPrefix_zero
