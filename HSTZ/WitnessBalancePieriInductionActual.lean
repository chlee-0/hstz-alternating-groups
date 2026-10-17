import HSTZ.WitnessBalancePieriActual
import HSTZ.InducedReparam

/-! Ordinary inductions for both original joint blocks, at the original positions
and actions. Reuses induction interfaces from OpenAI's `math` repository (commit adc7f1241, Apache-2.0)
and Mathlib's induced representations. This is a private conjugation step, not an
identification with the global H or a Young support theorem for all compatible targets. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped Classical TensorProduct

section Transport
variable {H J G A V : Type*} [Group H] [Group J] [Group G] [Group A]
  [AddCommGroup V] [Module ℂ V]
  (e : H ≃* J) (a : G ≃* A) (psi : H →* G) (phi : J →* A)
  (sigma : Representation ℂ J V)
  (hc : ∀ h, a (psi h)=phi (e h))

private def jointBase : Representation.IntertwiningMap (sigma.comp e.toMonoidHom)
    (((Representation.ind phi sigma).comp a.toMonoidHom).comp psi) where
  toLinearMap := Representation.IndV.mk phi sigma 1
  isIntertwining' h := by
    apply LinearMap.ext
    intro v
    change Representation.IndV.mk phi sigma 1 (sigma (e h) v)=
      Representation.ind phi sigma (a (psi h)) (Representation.IndV.mk phi sigma 1 v)
    rw [hc,Representation.ind_mk]
    simpa using (ind_mk_inv_mul phi sigma (e h) 1 v).symm

private def jointForward : Representation.IntertwiningMap
    (Representation.ind psi (sigma.comp e.toMonoidHom))
    ((Representation.ind phi sigma).comp a.toMonoidHom) :=
  inducedIntertwiner psi (sigma.comp e.toMonoidHom)
    ((Representation.ind phi sigma).comp a.toMonoidHom) (jointBase e a psi phi sigma hc)

private theorem jointForward_mk (g : G) (v : V) :
    jointForward e a psi phi sigma hc (Representation.IndV.mk psi (sigma.comp e.toMonoidHom) g v)=
      Representation.IndV.mk phi sigma (a g) v := by
  change inducedLinearMap _ _ _ _ _=_
  rw [inducedLinearMap_mk]
  change Representation.ind phi sigma (a g⁻¹) (Representation.IndV.mk phi sigma 1 v)=_
  rw [Representation.ind_mk]
  simp

private def jointBackBase : Representation.IntertwiningMap sigma
    (((Representation.ind psi (sigma.comp e.toMonoidHom)).comp a.symm.toMonoidHom).comp phi) where
  toLinearMap := Representation.IndV.mk psi (sigma.comp e.toMonoidHom) 1
  isIntertwining' j := by
    apply LinearMap.ext
    intro v
    have hrel : a.symm (phi j)=psi (e.symm j) := by
      have he := hc (e.symm j)
      simpa using (congrArg a.symm he).symm
    change Representation.IndV.mk psi (sigma.comp e.toMonoidHom) 1 (sigma j v)=
      Representation.ind psi (sigma.comp e.toMonoidHom) (a.symm (phi j))
        (Representation.IndV.mk psi (sigma.comp e.toMonoidHom) 1 v)
    rw [hrel,Representation.ind_mk]
    simpa using (ind_mk_inv_mul psi (sigma.comp e.toMonoidHom) (e.symm j) 1 v).symm

private def jointBack : Representation.IntertwiningMap
    (Representation.ind phi sigma)
    ((Representation.ind psi (sigma.comp e.toMonoidHom)).comp a.symm.toMonoidHom) :=
  inducedIntertwiner phi sigma
    ((Representation.ind psi (sigma.comp e.toMonoidHom)).comp a.symm.toMonoidHom)
    (jointBackBase e a psi phi sigma hc)

private theorem jointBack_mk (g : A) (v : V) :
    jointBack e a psi phi sigma hc (Representation.IndV.mk phi sigma g v)=
      Representation.IndV.mk psi (sigma.comp e.toMonoidHom) (a.symm g) v := by
  change inducedLinearMap _ _ _ _ _=_
  rw [inducedLinearMap_mk]
  change Representation.ind psi (sigma.comp e.toMonoidHom) (a.symm g⁻¹)
    (Representation.IndV.mk psi (sigma.comp e.toMonoidHom) 1 v)=_
  rw [Representation.ind_mk]
  simp

private theorem jointForward_bijective : Function.Bijective (jointForward e a psi phi sigma hc) := by
  have hleft : (jointBack e a psi phi sigma hc).toLinearMap.comp
      (jointForward e a psi phi sigma hc).toLinearMap=LinearMap.id := by
    apply Representation.IndV.hom_ext
    intro g
    ext v
    change jointBack e a psi phi sigma hc (jointForward e a psi phi sigma hc
      (Representation.IndV.mk psi (sigma.comp e.toMonoidHom) g v))=
        Representation.IndV.mk psi (sigma.comp e.toMonoidHom) g v
    rw [jointForward_mk,jointBack_mk]
    simp
  have hright : (jointForward e a psi phi sigma hc).toLinearMap.comp
      (jointBack e a psi phi sigma hc).toLinearMap=LinearMap.id := by
    apply Representation.IndV.hom_ext
    intro g
    ext v
    change jointForward e a psi phi sigma hc (jointBack e a psi phi sigma hc
      (Representation.IndV.mk phi sigma g v))=Representation.IndV.mk phi sigma g v
    rw [jointBack_mk,jointForward_mk]
    simp
  have hl : Function.LeftInverse (jointBack e a psi phi sigma hc)
      (jointForward e a psi phi sigma hc) := fun x => DFunLike.congr_fun hleft x
  have hr : Function.RightInverse (jointBack e a psi phi sigma hc)
      (jointForward e a psi phi sigma hc) := fun x => DFunLike.congr_fun hright x
  exact ⟨hl.injective,hr.surjective⟩
end Transport

section Tail
variable {k b n : ℕ} (hk : 5 ≤ k) (z : Tableau n (witnessDiagram k b 0 hk))

private abbrev tailSpace := (witnessBalanceLocalProjectedFactor hk z 0).toSubmodule ⊗[ℂ]
  (witnessBalanceLocalProjectedFactor hk z 1).toSubmodule
local instance : AddCommGroup (tailSpace hk z) := TensorProduct.addCommGroup
local instance : Module ℂ (tailSpace hk z) := TensorProduct.leftModule

/-- Induction target for the larger joint block; the original labels keep independent actions. -/
def witnessBalanceTwosTailActualInduced :
    Representation ℂ (Equiv.Perm (Fin (witnessBalanceComponentSize hk z 0+
      witnessBalanceComponentSize hk z 1)))
      (Representation.IndV (sumPermHom (finSumFinEquiv.symm :
        Fin (witnessBalanceComponentSize hk z 0+witnessBalanceComponentSize hk z 1) ≃
          Fin (witnessBalanceComponentSize hk z 0) ⊕ Fin (witnessBalanceComponentSize hk z 1)))
        (witnessBalanceTwosTailActualProduct hk z)) :=
  Representation.ind _ (witnessBalanceTwosTailActualProduct hk z)

private def tailProductEquiv := MulEquiv.prodCongr
  (witnessBalanceTwosPositions hk z).permCongrHom (witnessBalanceTailPositions hk z).permCongrHom
private def tailJointEquiv := (witnessBalanceTwosTailPositions hk z).permCongrHom

/-- Return map for the induced carrier, using the inverse/right `mk` convention and both factors. -/
def witnessBalanceTwosTailInductionReturn : Representation.IntertwiningMap
    (witnessBalanceTwosTailInduced hk z)
    ((witnessBalanceTwosTailActualInduced hk z).comp
      (positionPermHom (witnessBalanceTwosTailPositions hk z))) :=
  jointForward (tailProductEquiv hk z) (tailJointEquiv hk z) _ _
    (witnessBalanceTwosTailActualProduct hk z)
    (fun gh => witnessBalance_twos_tail_group hk z gh.1 gh.2)

theorem witnessBalanceTwosTailInductionReturn_mk
    (g : Equiv.Perm (Fin ((witnessAttachment (b+1) 0).card+1))) (v : tailSpace hk z) :
    witnessBalanceTwosTailInductionReturn hk z
      (Representation.IndV.mk _ _ g v)=
        Representation.IndV.mk _ _ (positionPermHom (witnessBalanceTwosTailPositions hk z) g) v :=
  jointForward_mk (tailProductEquiv hk z) (tailJointEquiv hk z) _ _ _ _ g v

theorem witnessBalanceTwosTailInductionReturn_bijective :
    Function.Bijective (witnessBalanceTwosTailInductionReturn hk z) :=
  jointForward_bijective (tailProductEquiv hk z) (tailJointEquiv hk z) _ _ _ _

/-- The Pieri injection transported to induction from independent factors. -/
theorem witnessBalanceTwosTail_actual_induced_native_support {nu : YoungDiagram}
    (t : Tableau ((witnessAttachment (b+1) 0).card+1) nu) (ht : nu.colLen 0≤2) :
    ∃ J : Representation.IntertwiningMap (spechtRep t)
      ((witnessBalanceTwosTailActualInduced hk z).comp
        (positionPermHom (witnessBalanceTwosTailPositions hk z))), Function.Injective J := by
  obtain ⟨J,hJ⟩ := witnessBalanceTwosTail_induced_support hk z t ht
  exact ⟨(witnessBalanceTwosTailInductionReturn hk z).comp J,
    (witnessBalanceTwosTailInductionReturn_bijective hk z).1.comp hJ⟩
end Tail

section Three
variable {k b n : ℕ} (hk : 5 ≤ k) (z : Tableau n (witnessDiagram k b 1 hk))

private abbrev threeSpace := (witnessBalanceLocalProjectedFactor hk z 0).toSubmodule ⊗[ℂ]
  (witnessBalanceLocalProjectedFactor hk z 2).toSubmodule
local instance : AddCommGroup (threeSpace hk z) := TensorProduct.addCommGroup
local instance : Module ℂ (threeSpace hk z) := TensorProduct.leftModule

def witnessBalanceTwosThreeActualInduced :
    Representation ℂ (Equiv.Perm (Fin (witnessBalanceComponentSize hk z 0+
      witnessBalanceComponentSize hk z 2)))
      (Representation.IndV (sumPermHom (finSumFinEquiv.symm :
        Fin (witnessBalanceComponentSize hk z 0+witnessBalanceComponentSize hk z 2) ≃
          Fin (witnessBalanceComponentSize hk z 0) ⊕ Fin (witnessBalanceComponentSize hk z 2)))
        (witnessBalanceTwosThreeActualProduct hk z)) :=
  Representation.ind _ (witnessBalanceTwosThreeActualProduct hk z)

private def threeProductEquiv := MulEquiv.prodCongr
  (witnessBalanceTwosPositions hk z).permCongrHom (witnessBalanceThreePositions hk z).permCongrHom
private def threeJointEquiv := (witnessBalanceTwosThreePositions hk z).permCongrHom

def witnessBalanceTwosThreeInductionReturn : Representation.IntertwiningMap
    (witnessBalanceTwosThreeInduced hk z)
    ((witnessBalanceTwosThreeActualInduced hk z).comp
      (positionPermHom (witnessBalanceTwosThreePositions hk z))) :=
  jointForward (threeProductEquiv hk z) (threeJointEquiv hk z) _ _
    (witnessBalanceTwosThreeActualProduct hk z)
    (fun gh => witnessBalance_twos_three_group hk z gh.1 gh.2)

theorem witnessBalanceTwosThreeInductionReturn_mk
    (g : Equiv.Perm (Fin ((witnessAttachment (b+1) 0).card+3))) (v : threeSpace hk z) :
    witnessBalanceTwosThreeInductionReturn hk z
      (Representation.IndV.mk _ _ g v)=
        Representation.IndV.mk _ _ (positionPermHom (witnessBalanceTwosThreePositions hk z) g) v :=
  jointForward_mk (threeProductEquiv hk z) (threeJointEquiv hk z) _ _ _ _ g v

theorem witnessBalanceTwosThreeInductionReturn_bijective :
    Function.Bijective (witnessBalanceTwosThreeInductionReturn hk z) :=
  jointForward_bijective (threeProductEquiv hk z) (threeJointEquiv hk z) _ _ _ _

theorem witnessBalanceTwosThree_actual_induced_native_support {nu : YoungDiagram}
    (t : Tableau ((witnessAttachment (b+1) 0).card+3) nu) (ht : nu.colLen 0≤2) :
    ∃ J : Representation.IntertwiningMap (spechtRep t)
      ((witnessBalanceTwosThreeActualInduced hk z).comp
        (positionPermHom (witnessBalanceTwosThreePositions hk z))), Function.Injective J := by
  obtain ⟨J,hJ⟩ := witnessBalanceTwosThree_induced_support hk z t ht
  exact ⟨(witnessBalanceTwosThreeInductionReturn hk z).comp J,
    (witnessBalanceTwosThreeInductionReturn_bijective hk z).1.comp hJ⟩
end Three
end
end HSTZ
#print axioms HSTZ.witnessBalanceTwosTailActualInduced
#print axioms HSTZ.witnessBalanceTwosTailInductionReturn
#print axioms HSTZ.witnessBalanceTwosTailInductionReturn_mk
#print axioms HSTZ.witnessBalanceTwosTailInductionReturn_bijective
#print axioms HSTZ.witnessBalanceTwosTail_actual_induced_native_support
#print axioms HSTZ.witnessBalanceTwosThreeActualInduced
#print axioms HSTZ.witnessBalanceTwosThreeInductionReturn
#print axioms HSTZ.witnessBalanceTwosThreeInductionReturn_mk
#print axioms HSTZ.witnessBalanceTwosThreeInductionReturn_bijective
#print axioms HSTZ.witnessBalanceTwosThree_actual_induced_native_support
