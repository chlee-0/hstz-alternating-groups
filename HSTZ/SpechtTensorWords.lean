import HSTZ.FinsuppAction
import HSTZ.IntertwiningCompat
import HSTZ.TensorInterfaces
import HSTZ.WordModelEquiv
import OAI.RepresentationTheory.Saxl.StaircaseTensor

/-! Tensor coordinates joining the HSTZ pair-word basis with the finite
encoded alphabet of OpenAI's `math` repository. The Specht tensor embeddings are
proved here; no constituent universality or filtered-vector coefficient
statement is assumed. The diagonal action is kept separate from independent
generation. -/
namespace HSTZ
open TensorProduct
open scoped Classical

/-- Encoding changes the names of pair letters bijectively; none are collapsed. -/
def encodedPairWordsEquiv (n d e : ℕ) :
    PositionWord (Fin n) (Fin d × Fin e) ≃ PositionWord (Fin n) (Fin (d*e)) where
  toFun := PositionWord.mapLetters finProdFinEquiv
  invFun := PositionWord.mapLetters finProdFinEquiv.symm
  left_inv w := by
    apply PositionWord.ext
    intro j
    exact finProdFinEquiv.symm_apply_apply (w.letters j)
  right_inv w := by
    apply PositionWord.ext
    intro j
    exact finProdFinEquiv.apply_symm_apply (w.letters j)

noncomputable def pairAlphabetLinearEquiv (n d e : ℕ) :
    (PositionWord (Fin n) (Fin d × Fin e) →₀ ℂ) ≃ₗ[ℂ]
      (PositionWord (Fin n) (Fin (d*e)) →₀ ℂ) :=
  Finsupp.domLCongr (encodedPairWordsEquiv n d e)

noncomputable def pairAlphabetIntertwiner (n d e : ℕ) : Representation.IntertwiningMap
    (finsuppAction ℂ (Equiv.Perm (Fin n)) (PositionWord (Fin n) (Fin d × Fin e)))
    (finsuppAction ℂ (Equiv.Perm (Fin n)) (PositionWord (Fin n) (Fin (d*e)))) where
  toLinearMap := (pairAlphabetLinearEquiv n d e).toLinearMap
  isIntertwining' g := by
    apply LinearMap.ext
    intro f
    have heq : (pairAlphabetLinearEquiv n d e).toLinearMap.comp
        (finsuppAction ℂ (Equiv.Perm (Fin n)) _ g) =
        (finsuppAction ℂ (Equiv.Perm (Fin n)) _ g).comp
          (pairAlphabetLinearEquiv n d e).toLinearMap := by
      apply Finsupp.lhom_ext
      intro w c
      change pairAlphabetLinearEquiv n d e
        (finsuppAction ℂ (Equiv.Perm (Fin n)) _ g (Finsupp.single w c)) =
          finsuppAction ℂ (Equiv.Perm (Fin n)) _ g
            (pairAlphabetLinearEquiv n d e (Finsupp.single w c))
      simp [pairAlphabetLinearEquiv,encodedPairWordsEquiv]
    exact DFunLike.congr_fun heq f

noncomputable def encodedPairModelEquiv (n d e : ℕ) :
    (PositionWord (Fin n) (Fin d × Fin e) →₀ ℂ) ≃ₗ[ℂ] OAI.Saxl.WordSpace n (d*e) :=
  pairAlphabetLinearEquiv n d e ≪≫ₗ wordModelEquiv n (d*e)

@[simp] theorem encodedPairModelEquiv_apply (n d e : ℕ)
    (f : PositionWord (Fin n) (Fin d × Fin e) →₀ ℂ) (a : Fin n → Fin (d*e)) :
    encodedPairModelEquiv n d e f a =
      f ⟨fun j => finProdFinEquiv.symm (a j)⟩ := by
  simp [encodedPairModelEquiv,pairAlphabetLinearEquiv,wordModelEquiv_apply,Finsupp.domLCongr_apply,
    Finsupp.domCongr_apply,encodedPairWordsEquiv,PositionWord.mapLetters]

noncomputable def encodedPairModelIntertwiner (n d e : ℕ) : Representation.IntertwiningMap
    (finsuppAction ℂ (Equiv.Perm (Fin n)) (PositionWord (Fin n) (Fin d × Fin e)))
    (OAI.Saxl.wordRep n (d*e)) :=
  (wordModelIntertwiner n (d*e)).comp (pairAlphabetIntertwiner n d e)

theorem encodedPairModelIntertwiner_bijective (n d e : ℕ) :
    Function.Bijective (encodedPairModelIntertwiner n d e) :=
  (encodedPairModelEquiv n d e).bijective

noncomputable def encodedPairModelInverse (n d e : ℕ) : Representation.IntertwiningMap
    (OAI.Saxl.wordRep n (d*e))
    (finsuppAction ℂ (Equiv.Perm (Fin n)) (PositionWord (Fin n) (Fin d × Fin e))) where
  toLinearMap := (encodedPairModelEquiv n d e).symm.toLinearMap
  isIntertwining' g := by
    apply LinearMap.ext
    intro f
    apply (encodedPairModelEquiv n d e).injective
    change encodedPairModelEquiv n d e ((encodedPairModelEquiv n d e).symm (_)) = _
    rw [LinearEquiv.apply_symm_apply]
    have h := (encodedPairModelIntertwiner n d e).map_action g
      ((encodedPairModelEquiv n d e).symm f)
    change encodedPairModelEquiv n d e
      (finsuppAction ℂ (Equiv.Perm (Fin n))
        (PositionWord (Fin n) (Fin d × Fin e)) g ((encodedPairModelEquiv n d e).symm f)) =
        OAI.Saxl.wordRep n (d*e) g
          (encodedPairModelEquiv n d e ((encodedPairModelEquiv n d e).symm f)) at h
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm

/-- The two tensor coordinate constructions agree at every original pair word. -/
theorem encodedPair_tensor_tmul (n d e : ℕ)
    (f : PositionWord (Fin n) (Fin d) →₀ ℂ)
    (h : PositionWord (Fin n) (Fin e) →₀ ℂ) :
    encodedPairModelEquiv n d e (pairWordTensorEquiv (f ⊗ₜ[ℂ] h)) =
      OAI.Saxl.wordTensor n d e
        (wordModelEquiv n d f ⊗ₜ[ℂ] wordModelEquiv n e h) := by
  funext a
  rw [encodedPairModelEquiv_apply,pairWordTensorEquiv_coefficient,
    OAI.Saxl.wordTensor_tmul,wordModelEquiv_apply,wordModelEquiv_apply]
  rfl

theorem encodedPair_tensor_commutes (n d e : ℕ)
    (z : (PositionWord (Fin n) (Fin d) →₀ ℂ) ⊗[ℂ]
      (PositionWord (Fin n) (Fin e) →₀ ℂ)) :
    encodedPairModelEquiv n d e (pairWordTensorEquiv z) =
      OAI.Saxl.wordTensor n d e
        (TensorProduct.map (wordModelEquiv n d).toLinearMap (wordModelEquiv n e).toLinearMap z) := by
  have hEq : (encodedPairModelEquiv n d e).toLinearMap.comp
      (pairWordTensorEquiv (R := ℂ) (J := Fin n) (A := Fin d) (B := Fin e)).toLinearMap =
      (OAI.Saxl.wordTensor n d e).toLinearMap.comp
        (TensorProduct.map (wordModelEquiv n d).toLinearMap (wordModelEquiv n e).toLinearMap) := by
    apply TensorProduct.ext
    apply LinearMap.ext
    intro f
    apply LinearMap.ext
    intro h
    exact encodedPair_tensor_tmul n d e f h
  exact DFunLike.congr_fun hEq z

/-- The Specht tensor sits inside the pair-word module. -/
noncomputable def pairedSpechtTensorMap {n : ℕ} {mu nu : YoungDiagram}
    (s : OAI.Saxl.Tableau n mu) (t : OAI.Saxl.Tableau n nu) : Representation.IntertwiningMap
    ((OAI.Saxl.spechtRep s).tprod (OAI.Saxl.spechtRep t))
    (finsuppAction ℂ (Equiv.Perm (Fin n))
      (PositionWord (Fin n) (Fin (mu.colLen 0) × Fin (nu.colLen 0)))) :=
  (encodedPairModelInverse n (mu.colLen 0) (nu.colLen 0)).comp
    ((OAI.Saxl.wordTensorIntertwiner n (mu.colLen 0) (nu.colLen 0)).comp
      (OAI.Saxl.spechtTensorInclusion s t))

theorem pairedSpechtTensorMap_injective {n : ℕ} {mu nu : YoungDiagram}
    (s : OAI.Saxl.Tableau n mu) (t : OAI.Saxl.Tableau n nu) :
    Function.Injective (pairedSpechtTensorMap s t) :=
  (encodedPairModelEquiv n (mu.colLen 0) (nu.colLen 0)).symm.injective.comp
    ((OAI.Saxl.wordTensor n (mu.colLen 0) (nu.colLen 0)).injective.comp
      (OAI.Saxl.spechtTensorInclusion_injective s t))

theorem pairedSpechtTensorMap_generator {n : ℕ} {mu nu : YoungDiagram}
    (s : OAI.Saxl.Tableau n mu) (t : OAI.Saxl.Tableau n nu) :
    pairedSpechtTensorMap s t
      ((⟨OAI.Saxl.polytabloid s,OAI.Saxl.mem_cyclic _ _⟩ : OAI.Saxl.Specht s) ⊗ₜ[ℂ]
        (⟨OAI.Saxl.polytabloid t,OAI.Saxl.mem_cyclic _ _⟩ : OAI.Saxl.Specht t)) =
      pairWordTensorEquiv (wordPolytabloid s ⊗ₜ[ℂ] wordPolytabloid t) := by
  apply (encodedPairModelEquiv n (mu.colLen 0) (nu.colLen 0)).injective
  change encodedPairModelEquiv n _ _ ((encodedPairModelEquiv n _ _).symm
      (OAI.Saxl.wordTensor n _ _ (OAI.Saxl.polytabloid s ⊗ₜ[ℂ] OAI.Saxl.polytabloid t))) = _
  rw [LinearEquiv.apply_symm_apply,encodedPair_tensor_tmul]
  simp only [wordPolytabloid,LinearEquiv.apply_symm_apply]

/-- The generating tensor in the two Specht factors. -/
noncomputable def spechtTensorGenerator {n : ℕ} {mu nu : YoungDiagram}
    (s : OAI.Saxl.Tableau n mu) (t : OAI.Saxl.Tableau n nu) :
    OAI.Saxl.Specht s ⊗[ℂ] OAI.Saxl.Specht t :=
  (⟨OAI.Saxl.polytabloid s,OAI.Saxl.mem_cyclic _ _⟩ : OAI.Saxl.Specht s) ⊗ₜ[ℂ]
    (⟨OAI.Saxl.polytabloid t,OAI.Saxl.mem_cyclic _ _⟩ : OAI.Saxl.Specht t)

/-- Restriction to prescribed-vector cyclic spaces, not a full-square claim. -/
noncomputable def pairedSpechtCyclicMap {n : ℕ} {mu nu : YoungDiagram}
    (s : OAI.Saxl.Tableau n mu) (t : OAI.Saxl.Tableau n nu) :=
  cyclicImageMap (pairedSpechtTensorMap s t) (spechtTensorGenerator s t)

theorem pairedSpechtCyclicMap_bijective {n : ℕ} {mu nu : YoungDiagram}
    (s : OAI.Saxl.Tableau n mu) (t : OAI.Saxl.Tableau n nu) :
    Function.Bijective (pairedSpechtCyclicMap s t) := by
  constructor
  · intro x y h
    apply Subtype.ext
    exact pairedSpechtTensorMap_injective s t (congrArg Subtype.val h)
  · exact cyclicImageMap_surjective _ _

/-- The cyclic image is exactly the paired polytabloid orbit span. -/
theorem pairedSpecht_cyclic_image {n : ℕ} {mu nu : YoungDiagram}
    (s : OAI.Saxl.Tableau n mu) (t : OAI.Saxl.Tableau n nu) :
    (cyclicSpan ((OAI.Saxl.spechtRep s).tprod (OAI.Saxl.spechtRep t))
      (spechtTensorGenerator s t)).map (pairedSpechtTensorMap s t).toLinearMap =
    cyclicSpan (finsuppAction ℂ (Equiv.Perm (Fin n)) _)
      (pairWordTensorEquiv (wordPolytabloid s ⊗ₜ[ℂ] wordPolytabloid t)) := by
  rw [cyclicSpan_image]
  exact congrArg (cyclicSpan _) (pairedSpechtTensorMap_generator s t)

/-- Realness is proved for this generator; nonvanishing of contractions is not. -/
theorem encodedPair_polytabloid_real {n : ℕ} {mu nu : YoungDiagram}
    (s : OAI.Saxl.Tableau n mu) (t : OAI.Saxl.Tableau n nu) :
    star (encodedPairModelEquiv n (mu.colLen 0) (nu.colLen 0)
      (pairWordTensorEquiv (wordPolytabloid s ⊗ₜ[ℂ] wordPolytabloid t))) =
    encodedPairModelEquiv n (mu.colLen 0) (nu.colLen 0)
      (pairWordTensorEquiv (wordPolytabloid s ⊗ₜ[ℂ] wordPolytabloid t)) := by
  rw [encodedPair_tensor_tmul]
  simp only [wordPolytabloid,LinearEquiv.apply_symm_apply]
  funext a
  change star (OAI.Saxl.wordTensor n _ _ (_ ⊗ₜ[ℂ] _) a) = _
  rw [OAI.Saxl.wordTensor_tmul,star_mul]
  rw [show star (OAI.Saxl.polytabloid s (OAI.Saxl.splitLeft a)) = _ from
    congrFun (OAI.Saxl.polytabloid_real s) (OAI.Saxl.splitLeft a),
    show star (OAI.Saxl.polytabloid t (OAI.Saxl.splitRight a)) = _ from
    congrFun (OAI.Saxl.polytabloid_real t) (OAI.Saxl.splitRight a)]
  exact mul_comm _ _

end HSTZ

#print axioms OAI.Saxl.spechtSub_tableau_independent
#print axioms OAI.Saxl.wordTensorIntertwiner
#print axioms OAI.Saxl.spechtTensorInclusion_injective
#print axioms OAI.Saxl.staircaseTensorMap_injective
#print axioms OAI.Saxl.staircaseCyclic_le_tensorRange
#print axioms HSTZ.encodedPairModelIntertwiner_bijective
#print axioms HSTZ.encodedPair_tensor_commutes
#print axioms HSTZ.pairedSpechtTensorMap_injective
#print axioms HSTZ.pairedSpechtTensorMap_generator

#print axioms HSTZ.pairedSpechtCyclicMap_bijective
#print axioms HSTZ.pairedSpecht_cyclic_image
#print axioms HSTZ.encodedPair_polytabloid_real
