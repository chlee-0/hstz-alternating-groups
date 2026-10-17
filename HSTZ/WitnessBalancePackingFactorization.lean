import HSTZ.WitnessBalancePackingTransitivity

/-! The joint induced pair module tensored with the entire rest, via product induction.
Reuses declarations from OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
The larger group `K` is not `H`, and this module bijection does not supply Young target
support. -/
namespace HSTZ
noncomputable section
open OAI.Saxl
open scoped TensorProduct

section Adapter
variable {K H G R V W : Type*} [CommRing K] [Group H] [Group G] [Group R]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  (phi : H →* G) (rho : Representation K H V) (sigma : Representation K R W)

private abbrev productHom := phi.prodMap (MonoidHom.id R)
private abbrev sourceRep := independentTensor rho sigma
private abbrev assemblyRep := independentTensor (Representation.ind (k:=K) phi rho) sigma
private def factorBase : Representation.IntertwiningMap (sourceRep rho sigma)
    ((assemblyRep phi rho sigma).comp (productHom phi)) where
  toLinearMap := TensorProduct.map (Representation.IndV.mk (k:=K) phi rho 1) LinearMap.id
  isIntertwining' hr := by
    apply LinearMap.ext
    intro q
    have he : (TensorProduct.map (Representation.IndV.mk (k:=K) phi rho 1) LinearMap.id).comp
        (sourceRep rho sigma hr)=
      ((assemblyRep phi rho sigma).comp (productHom phi) hr).comp
        (TensorProduct.map (Representation.IndV.mk (k:=K) phi rho 1) LinearMap.id) := by
      ext v w
      change Representation.IndV.mk (k:=K) phi rho 1 (rho hr.1 v) ⊗ₜ[K] sigma hr.2 w=
        Representation.ind (k:=K) phi rho (phi hr.1)
          (Representation.IndV.mk (k:=K) phi rho 1 v) ⊗ₜ[K] sigma hr.2 w
      rw [Representation.ind_mk]
      have hi := ind_mk_inv_mul phi rho hr.1 1 v
      simpa using congrArg (fun x => x ⊗ₜ[K] sigma hr.2 w) hi.symm
    exact DFunLike.congr_fun he q

private def factorForward : Representation.IntertwiningMap
    (Representation.ind (k:=K) (productHom phi) (sourceRep rho sigma))
    (assemblyRep phi rho sigma) :=
  inducedIntertwiner (R:=K) (H:=H × R) (G:=G × R)
    (U:=V ⊗[K] W) (V:=Representation.IndV (k:=K) phi rho ⊗[K] W)
    (productHom phi) (sourceRep rho sigma) (assemblyRep phi rho sigma) (factorBase phi rho sigma)

private theorem factorForward_mk (g : G) (r : R) (v : V) (w : W) :
    factorForward phi rho sigma
      (Representation.IndV.mk (k:=K) (productHom phi) (sourceRep rho sigma) (g,r) (v ⊗ₜ[K] w))=
    Representation.IndV.mk (k:=K) phi rho g v ⊗ₜ[K] sigma r⁻¹ w := by
  change inducedLinearMap _ _ _ _ _=_
  rw [inducedLinearMap_mk]
  change Representation.ind (k:=K) phi rho g⁻¹ (Representation.IndV.mk (k:=K) phi rho 1 v) ⊗ₜ[K]
    sigma r⁻¹ w=_
  rw [Representation.ind_mk]
  simp

private def firstHom : G →* G × R where
  toFun g := (g,1)
  map_one' := rfl
  map_mul' _ _ := by simp
private abbrev backHomRep := (Representation.trivial K G W).linHom
  ((Representation.ind (k:=K) (productHom phi) (sourceRep rho sigma)).comp (firstHom (R:=R)))

private def productMk : (V ⊗[K] W) →ₗ[K]
    Representation.IndV (k:=K) (phi.prodMap (MonoidHom.id R)) (independentTensor rho sigma) :=
  Representation.IndV.mk (k:=K) (phi.prodMap (MonoidHom.id R)) (independentTensor rho sigma) 1

private def backLinear : V →ₗ[K] W →ₗ[K]
    Representation.IndV (k:=K) (phi.prodMap (MonoidHom.id R)) (independentTensor rho sigma) :=
  LinearMap.compr₂ (R:=K) (A:=K) (TensorProduct.mk K V W) (productMk phi rho sigma)

private def backBase : Representation.IntertwiningMap rho
    ((backHomRep phi rho sigma).comp phi) where
  toLinearMap := backLinear phi rho sigma
  isIntertwining' h := by
    apply LinearMap.ext
    intro v
    ext w
    change Representation.IndV.mk (k:=K) (productHom phi) (sourceRep rho sigma) 1
        (rho h v ⊗ₜ[K] w)=
      Representation.ind (k:=K) (productHom phi) (sourceRep rho sigma) (phi h,1)
        (Representation.IndV.mk (k:=K) (productHom phi) (sourceRep rho sigma) 1 (v ⊗ₜ[K] w))
    rw [Representation.ind_mk]
    have he := ind_mk_inv_mul (productHom phi) (sourceRep rho sigma) (h,1) 1 (v ⊗ₜ[K] w)
    simpa [productHom,sourceRep,independentTensor_tmul] using he.symm

private def backLift : Representation.IntertwiningMap (Representation.ind (k:=K) phi rho)
    (backHomRep phi rho sigma) :=
  inducedIntertwiner (R:=K) phi rho (backHomRep phi rho sigma) (backBase phi rho sigma)
private def factorBack : (Representation.IndV (k:=K) phi rho ⊗[K] W) →ₗ[K]
    Representation.IndV (k:=K) (productHom phi) (sourceRep rho sigma) :=
  TensorProduct.lift (backLift phi rho sigma).toLinearMap

private theorem factorBack_mk (g : G) (v : V) (w : W) :
    factorBack phi rho sigma (Representation.IndV.mk (k:=K) phi rho g v ⊗ₜ[K] w)=
    Representation.IndV.mk (k:=K) (productHom phi) (sourceRep rho sigma) (g,1) (v ⊗ₜ[K] w) := by
  change (inducedLinearMap phi rho (backHomRep phi rho sigma) (backBase phi rho sigma)
    (Representation.IndV.mk (k:=K) phi rho g v)) w=_
  rw [inducedLinearMap_mk]
  change Representation.ind (k:=K) (productHom phi) (sourceRep rho sigma) (g⁻¹,1)
    (Representation.IndV.mk (k:=K) (productHom phi) (sourceRep rho sigma) 1 (v ⊗ₜ[K] w))=_
  rw [Representation.ind_mk]
  simp

private theorem factorForward_leftInverse : Function.LeftInverse
    (factorBack phi rho sigma) (factorForward phi rho sigma) := by
  have he : (factorBack phi rho sigma).comp (factorForward phi rho sigma).toLinearMap=LinearMap.id := by
    apply Representation.IndV.hom_ext
    intro gr
    ext v w
    change factorBack phi rho sigma (factorForward phi rho sigma
      (Representation.IndV.mk (k:=K) (productHom phi) (sourceRep rho sigma) gr (v ⊗ₜ[K] w)))=
        Representation.IndV.mk (k:=K) (productHom phi) (sourceRep rho sigma) gr (v ⊗ₜ[K] w)
    rw [factorForward_mk,factorBack_mk]
    have hi := ind_mk_inv_mul (productHom phi) (sourceRep rho sigma)
      (1,gr.2⁻¹) (gr.1,1) (v ⊗ₜ[K] w)
    simpa [productHom,sourceRep,independentTensor_tmul] using hi.symm
  exact fun x => DFunLike.congr_fun he x

private theorem factorForward_rightInverse : Function.RightInverse
    (factorBack phi rho sigma) (factorForward phi rho sigma) := by
  have he : (factorForward phi rho sigma).toLinearMap.comp (factorBack phi rho sigma)=LinearMap.id := by
    apply TensorProduct.ext'
    intro u w
    have hh : ((factorForward phi rho sigma).toLinearMap.comp
        (factorBack phi rho sigma)).comp ((TensorProduct.mk K _ W).flip w)=
      ((TensorProduct.mk K _ W).flip w) := by
      apply Representation.IndV.hom_ext
      intro g
      ext v
      change factorForward phi rho sigma (factorBack phi rho sigma
        (Representation.IndV.mk (k:=K) phi rho g v ⊗ₜ[K] w))=
          Representation.IndV.mk (k:=K) phi rho g v ⊗ₜ[K] w
      rw [factorBack_mk,factorForward_mk]
      simp
    exact DFunLike.congr_fun hh u
  exact fun x => DFunLike.congr_fun he x

private theorem factorForward_bijective : Function.Bijective (factorForward phi rho sigma) :=
  ⟨(factorForward_leftInverse phi rho sigma).injective,
    (factorForward_rightInverse phi rho sigma).surjective⟩
end Adapter

section Actual
variable {k b delta n : ℕ} (hk : 5 ≤ k) (z : Tableau n (witnessDiagram k b delta hk))
local instance : AddCommGroup (witnessBalancePackingRestTensorSpace hk z) :=
  Module.addCommMonoidToAddCommGroup ℂ
local instance : Module ℂ (witnessBalancePackingJointPairRestSpace hk z) := TensorProduct.leftModule
local instance : AddCommGroup (witnessBalancePackingJointPairSpace hk z) :=
  TensorProduct.addCommGroup (R:=ℂ)
    (M:=(witnessBalanceLocalProjectedFactor hk z 0).toSubmodule)
    (N:=(witnessBalanceLocalProjectedFactor hk z (witnessBalancePackingJointLabel delta)).toSubmodule)
local instance : Module ℂ (witnessBalancePackingJointPairSpace hk z) := TensorProduct.leftModule
local instance : AddCommGroup (witnessBalancePackingJointPairRestSpace hk z) :=
  TensorProduct.addCommGroup (R:=ℂ) (M:=witnessBalancePackingJointPairSpace hk z)
    (N:=witnessBalancePackingRestTensorSpace hk z)
private abbrev actualPairRep : Representation ℂ (witnessBalancePackingPairGroup hk z)
    (witnessBalancePackingJointPairSpace hk z) := independentTensor
  (witnessBalanceLocalProjectedFactor hk z 0).toRepresentation
  (witnessBalanceLocalProjectedFactor hk z (witnessBalancePackingJointLabel delta)).toRepresentation
private abbrev actualPairHom : witnessBalancePackingPairGroup hk z →*
    Equiv.Perm (Fin (witnessBalancePackingJointDegree hk z)) :=
  sumPermHom finSumFinEquiv.symm

abbrev witnessBalancePackingAssemblySpace :=
  Representation.IndV (k:=ℂ) (actualPairHom hk z) (actualPairRep hk z) ⊗[ℂ]
    witnessBalancePackingRestTensorSpace hk z

/-- The larger group `K` acts on the joint induced pair module tensored with the entire
rest, not on an extended pair module. -/
def witnessBalancePackingAssemblyAction : Representation ℂ
    (witnessBalancePackingCoarserGroup hk z) (witnessBalancePackingAssemblySpace hk z) :=
  independentTensor (Representation.ind (k:=ℂ) (actualPairHom hk z) (actualPairRep hk z))
    (witnessBalancePackingRestProductAction hk z)

def witnessBalancePackingFactorization : Representation.IntertwiningMap
    (Representation.ind (k:=ℂ) (witnessBalancePackingProductToCoarser hk z)
      (witnessBalancePackingProductAction hk z)) (witnessBalancePackingAssemblyAction hk z) :=
  factorForward (actualPairHom hk z) (actualPairRep hk z) (witnessBalancePackingRestProductAction hk z)

theorem witnessBalancePackingFactorization_mk
    (g : Equiv.Perm (Fin (witnessBalancePackingJointDegree hk z)))
    (r : witnessBalancePackingRestGroup hk z) (v : witnessBalancePackingJointPairSpace hk z)
    (w : witnessBalancePackingRestTensorSpace hk z) :
    witnessBalancePackingFactorization hk z
      (Representation.IndV.mk (k:=ℂ) (witnessBalancePackingProductToCoarser hk z)
        (witnessBalancePackingProductAction hk z) (g,r) (v ⊗ₜ[ℂ] w))=
    Representation.IndV.mk (k:=ℂ) (actualPairHom hk z) (actualPairRep hk z) g v ⊗ₜ[ℂ]
      witnessBalancePackingRestProductAction hk z r⁻¹ w :=
  factorForward_mk _ _ _ g r v w

theorem witnessBalancePackingFactorization_bijective :
    Function.Bijective (witnessBalancePackingFactorization hk z) := factorForward_bijective _ _ _

def witnessBalancePackingFactorizationEquiv :
    Representation.IndV (k:=ℂ) (witnessBalancePackingProductToCoarser hk z)
      (witnessBalancePackingProductAction hk z) ≃ₗ[ℂ] witnessBalancePackingAssemblySpace hk z :=
  LinearEquiv.ofBijective (witnessBalancePackingFactorization hk z).toLinearMap
    (witnessBalancePackingFactorization_bijective hk z)

end Actual

section SelectedPrefix
variable {k b delta n : ℕ} (hk : 5 ≤ k) (z : Tableau n (witnessDiagram k b delta hk))

/-- Ordinary tensor factorization for the prefix source and the same next selected local
Specht module. The source is the ordered selected product. -/
def witnessBalancePackingSelectedPrefixFactorization D hc p
    (i : Fin (witnessBalancePackingBlocks k delta).length) :=
  factorForward (witnessBalancePackingSelectedPrefixHom hk z D hc p i.castSucc)
    (Rep.ρ (witnessBalancePackingSelectedPrefixModule hk z D hc p i.castSucc))
    (spechtRep (partitionTableau (p i)))

theorem witnessBalancePackingSelectedPrefixFactorization_bijective D hc p
    (i : Fin (witnessBalancePackingBlocks k delta).length) :
    Function.Bijective (witnessBalancePackingSelectedPrefixFactorization hk z D hc p i) :=
  factorForward_bijective _ _ _

end SelectedPrefix
end
end HSTZ
#print axioms HSTZ.witnessBalancePackingAssemblyAction
#print axioms HSTZ.witnessBalancePackingFactorization
#print axioms HSTZ.witnessBalancePackingFactorization_mk
#print axioms HSTZ.witnessBalancePackingFactorization_bijective
#print axioms HSTZ.witnessBalancePackingFactorizationEquiv
#print axioms HSTZ.witnessBalancePackingSelectedPrefixFactorization
#print axioms HSTZ.witnessBalancePackingSelectedPrefixFactorization_bijective
