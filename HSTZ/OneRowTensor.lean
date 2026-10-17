import HSTZ.IndependentTensor
import OAI.RepresentationTheory.Saxl.SpechtSubmodule

/-! One-row Specht vectors and tensor maps. Coordinate evaluation, rather than a
dimension comparison, proves that tensoring with the one-row polytabloid is injective. -/
namespace HSTZ
open scoped TensorProduct

/-- On at most one letter every word is fixed by position permutations. -/
theorem oneLetter_word_fixed {n d : ℕ} (hd : d ≤ 1)
    (g : Equiv.Perm (Fin n)) (x : OAI.Saxl.WordSpace n d) :
    OAI.Saxl.wordRep n d g x = x := by
  letI : Subsingleton (Fin d) := Fin.subsingleton_iff_le_one.mpr hd
  funext w
  change x (w ∘ g) = x w
  exact congrArg x (Subsingleton.elim _ _)

/-- A one-row tableau's Specht representation acts trivially. -/
theorem oneRow_specht_fixed {b : ℕ} {mu : YoungDiagram}
    (u : OAI.Saxl.Tableau b mu) (hmu : mu.colLen 0 ≤ 1)
    (g : Equiv.Perm (Fin b)) (x : OAI.Saxl.Specht u) :
    OAI.Saxl.spechtRep u g x = x := by
  apply Subtype.ext
  exact oneLetter_word_fixed hmu g x.val

/-- Tensoring with the one-row polytabloid, equivariantly. -/
noncomputable def oneRowTensorMap {G U : Type*} [Group G]
    [AddCommGroup U] [Module ℂ U] (rho : Representation ℂ G U)
    {b : ℕ} {mu : YoungDiagram} (u : OAI.Saxl.Tableau b mu) (hmu : mu.colLen 0 ≤ 1) :
    Representation.IntertwiningMap (rho.comp (MonoidHom.fst G (Equiv.Perm (Fin b))))
      (independentTensor rho (OAI.Saxl.spechtRep u)) where
  toLinearMap := (TensorProduct.mk ℂ U (OAI.Saxl.Specht u)).flip
    ⟨OAI.Saxl.polytabloid u, OAI.Saxl.mem_cyclic _ _⟩
  isIntertwining' gh := by
    apply LinearMap.ext
    intro x
    change (rho gh.1 x) ⊗ₜ[ℂ] (⟨OAI.Saxl.polytabloid u, OAI.Saxl.mem_cyclic _ _⟩ : OAI.Saxl.Specht u) =
      TensorProduct.map (rho gh.1) (OAI.Saxl.spechtRep u gh.2)
        (x ⊗ₜ[ℂ] (⟨OAI.Saxl.polytabloid u, OAI.Saxl.mem_cyclic _ _⟩ : OAI.Saxl.Specht u))
    rw [TensorProduct.map_tmul, oneRow_specht_fixed u hmu]

/-- The row-word coordinate, evaluated on the Specht carrier. -/
noncomputable def oneRowEvaluation {b : ℕ} {mu : YoungDiagram}
    (u : OAI.Saxl.Tableau b mu) : OAI.Saxl.Specht u →ₗ[ℂ] ℂ where
  toFun y := y.val (OAI.Saxl.rowWord u)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Coordinate evaluation on the one-row factor is an equivariant retraction; the
independent complement action fixes every vector. -/
noncomputable def oneRowTensorRetraction {G U : Type*} [Group G]
    [AddCommGroup U] [Module ℂ U] (rho : Representation ℂ G U)
    {b : ℕ} {mu : YoungDiagram} (u : OAI.Saxl.Tableau b mu) (hmu : mu.colLen 0 ≤ 1) :
    Representation.IntertwiningMap (independentTensor rho (OAI.Saxl.spechtRep u))
      (rho.comp (MonoidHom.fst G (Equiv.Perm (Fin b)))) where
  toLinearMap := (TensorProduct.rid ℂ U).toLinearMap.comp
    (TensorProduct.map (LinearMap.id : U →ₗ[ℂ] U) (oneRowEvaluation u))
  isIntertwining' gh := by
    apply LinearMap.ext
    intro z
    let L := (TensorProduct.rid ℂ U).toLinearMap.comp
      (TensorProduct.map (LinearMap.id : U →ₗ[ℂ] U) (oneRowEvaluation u))
    have he : L.comp (independentTensor rho (OAI.Saxl.spechtRep u) gh) =
        (rho gh.1).comp L := by
      apply TensorProduct.ext'
      intro x y
      change L (rho gh.1 x ⊗ₜ[ℂ] OAI.Saxl.spechtRep u gh.2 y) =
        rho gh.1 (L (x ⊗ₜ[ℂ] y))
      rw [oneRow_specht_fixed u hmu]
      simp [L, map_smul]
    exact DFunLike.congr_fun he z

/-- Coordinate coefficient one supplies an equivariant left inverse. -/
theorem oneRowTensor_leftInverse {G U : Type*} [Group G]
    [AddCommGroup U] [Module ℂ U] (rho : Representation ℂ G U)
    {b : ℕ} {mu : YoungDiagram} (u : OAI.Saxl.Tableau b mu) (hmu : mu.colLen 0 ≤ 1) :
    Function.LeftInverse (oneRowTensorRetraction rho u hmu).toLinearMap
      (oneRowTensorMap rho u hmu).toLinearMap := by
  intro x
  change (TensorProduct.rid ℂ U) (TensorProduct.map (LinearMap.id : U →ₗ[ℂ] U)
    (oneRowEvaluation u)
      (x ⊗ₜ[ℂ] (⟨OAI.Saxl.polytabloid u, OAI.Saxl.mem_cyclic _ _⟩ : OAI.Saxl.Specht u))) = x
  simp [oneRowEvaluation, OAI.Saxl.polytabloid_rowWord]

/-- Coordinate evaluation proves injectivity, without a `finrank` argument. -/
theorem oneRowTensorMap_injective {G U : Type*} [Group G]
    [AddCommGroup U] [Module ℂ U] (rho : Representation ℂ G U)
    {b : ℕ} {mu : YoungDiagram} (u : OAI.Saxl.Tableau b mu) (hmu : mu.colLen 0 ≤ 1) :
    Function.Injective (oneRowTensorMap rho u hmu) :=
  (oneRowTensor_leftInverse rho u hmu).injective

end HSTZ
#print axioms HSTZ.oneRow_specht_fixed
#print axioms HSTZ.oneRowTensor_leftInverse
#print axioms HSTZ.oneRowTensorMap_injective
