import HSTZ.IntertwiningCompat
import HSTZ.FixedComplement
import HSTZ.ProjectionLift
import OAI.RepresentationTheory.Saxl.PieriRestriction

/-! Restriction to a contained diagram by fixing complement coordinates.
The pairing/projection proof adapts `PieriRestriction` from OpenAI's `math` repository
(commit adc7f1241b42e322a6451854ab7e4b4c146bf78a, Apache-2.0; see
`OpenAITensorSquares/LICENSE`) and the local PieriSupport range argument. The
fixed-complement contraction is new. Column alternation and the Specht projection
reuse existing proofs. No horizontal-strip assumption is made, and equivariance is
claimed only for permutations that fix the complement. -/
namespace HSTZ
open OAI.Saxl
noncomputable section

theorem contained_contraction_coefficient {a n : ℕ} {nu mu : YoungDiagram}
    (s : Tableau a nu) (t : Tableau n mu) (h : nu ≤ mu) :
    wordRestrictAt (tableauInclusion s t h) (rowLetterInclusion h) (rowWord t)
      (polytabloid t) (rowWord s) = 1 := by
  have hc : rowWord t ∘ tableauInclusion s t h = rowLetterInclusion h ∘ rowWord s := by
    funext k
    apply Fin.ext
    exact congrArg Prod.fst (tableauInclusion_cell s t h k)
  rw [wordRestrictAt_coefficient _ _ _ _ hc]
  exact polytabloid_rowWord t

theorem contained_contraction_pair {a n : ℕ} {nu mu : YoungDiagram}
    (s : Tableau a nu) (t : Tableau n mu) (h : nu ≤ mu) :
    dotProduct (wordRestrictAt (tableauInclusion s t h) (rowLetterInclusion h) (rowWord t)
      (polytabloid t)) (polytabloid s) ≠ 0 := by
  classical
  let i := tableauInclusion s t h
  let j := rowLetterInclusion h
  let x := wordRestrictAt i j (rowWord t) (polytabloid t)
  have hx (g : columnGroup s) : wordRep a (nu.colLen 0) (g : Equiv.Perm (Fin a)) x =
      signC (g : Equiv.Perm (Fin a)) • x := by
    rw [← wordRestrictAt_equivariant i j (rowWord t)
      ((g : Equiv.Perm (Fin a)).viaEmbedding i) (g : Equiv.Perm (Fin a))
      (Equiv.Perm.viaEmbedding_apply _ _)
      (fun k hk => Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hk) (polytabloid t)]
    rw [polytabloid_alternating t ⟨_, column_viaEmbedding s t h g⟩]
    rw [map_smul, signC_viaEmbedding]
  rw [← columnAlt_coefficient]
  let := Fintype.ofFinite (columnGroup s)
  have he : columnAlt s x = (Fintype.card (columnGroup s) : ℂ) • x := by
    change (∑ g : columnGroup s, signC (g : Equiv.Perm (Fin a)) •
      wordRep a (nu.colLen 0) (g : Equiv.Perm (Fin a))) x = _
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, hx, smul_smul,
      signC_mul_self, one_smul, Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
  change columnAlt s x (rowWord s) ≠ 0
  rw [he]
  change (Fintype.card (columnGroup s) : ℂ) *
    wordRestrictAt (tableauInclusion s t h) (rowLetterInclusion h) (rowWord t)
      (polytabloid t) (rowWord s) ≠ 0
  rw [contained_contraction_coefficient s t h, mul_one]
  exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero

/-- A nonzero restriction map, equivariant for compatible permutations
that fix every complement position. Complement permutations are not assumed trivial. -/
theorem contained_specht_restriction {a n : ℕ} {nu mu : YoungDiagram}
    (s : Tableau a nu) (t : Tableau n mu) (h : nu ≤ mu) :
    ∃ F : Specht t →ₗ[ℂ] Specht s, F ≠ 0 ∧
      ∀ (g : Equiv.Perm (Fin n)) (q : Equiv.Perm (Fin a)),
        (∀ k, g (tableauInclusion s t h k) = tableauInclusion s t h (q k)) →
        (∀ k, k ∉ Set.range (tableauInclusion s t h) → g k = k) →
        ∀ x, F (spechtRep t g x) = spechtRep s q (F x) := by
  let pr := subrepProject (spechtSub s) (fun _ hx => cyclic_star _ (polytabloid_real s) hx)
  let T := wordRestrictAt (tableauInclusion s t h) (rowLetterInclusion h) (rowWord t)
  let F := pr.toLinearMap.comp (T.comp (spechtSub t).toSubmodule.subtype)
  refine ⟨F, ?_, ?_⟩
  · intro hF
    have hp := subrepProject_pair (spechtSub s)
      (fun _ hx => cyclic_star _ (polytabloid_real s) hx)
      (T (polytabloid t)) ⟨polytabloid s, mem_cyclic _ _⟩
    have he : pr (T (polytabloid t)) = 0 := by
      exact congrArg (fun L : Specht t →ₗ[ℂ] Specht s => L ⟨polytabloid t, mem_cyclic _ _⟩) hF
    rw [he] at hp
    exact contained_contraction_pair s t h (hp.symm.trans (zero_dotProduct _))
  · intro g q hi hg x
    change pr (T (wordRep n (mu.colLen 0) g x.val)) = spechtRep s q (pr (T x.val))
    rw [wordRestrictAt_equivariant _ _ _ g q hi hg x.val]
    exact pr.map_action q (T x.val)

/-- Surjective restriction to the contained diagram. The range is invariant under all
embedded core permutations, so irreducibility of complex Specht modules applies. -/
theorem contained_restriction_surjective {a n : ℕ} {nu mu : YoungDiagram}
    (s : Tableau a nu) (t : Tableau n mu) (h : nu ≤ mu) :
    ∃ F : Specht t →ₗ[ℂ] Specht s, Function.Surjective F ∧
      ∀ (g : Equiv.Perm (Fin n)) (q : Equiv.Perm (Fin a)),
        (∀ k, g (tableauInclusion s t h k) = tableauInclusion s t h (q k)) →
        (∀ k, k ∉ Set.range (tableauInclusion s t h) → g k = k) →
        ∀ x, F (spechtRep t g x) = spechtRep s q (F x) := by
  classical
  obtain ⟨F, hF, hcomm⟩ := contained_specht_restriction s t h
  let i := tableauInclusion s t h
  let S : Subrepresentation (spechtRep s) :=
    { toSubmodule := F.range
      apply_mem_toSubmodule := by
        intro q y hy
        obtain ⟨x, rfl⟩ := hy
        exact ⟨spechtRep t (q.viaEmbedding i) x,
          hcomm _ q (Equiv.Perm.viaEmbedding_apply _ _)
            (fun k hk => Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hk) x⟩ }
  letI := specht_irreducible s
  have hn : S ≠ ⊥ := by
    intro he
    apply hF
    apply LinearMap.ext
    intro x
    have hx : F x ∈ S.toSubmodule := ⟨x, rfl⟩
    rw [he] at hx
    exact (Submodule.mem_bot ℂ).mp hx
  have ht : S = ⊤ := (eq_bot_or_eq_top S).resolve_left hn
  refine ⟨F, ?_, hcomm⟩
  intro y
  have hy : y ∈ S.toSubmodule := by rw [ht]; trivial
  exact hy

/-- Contained Specht branching under the embedded subgroup fixing complement
positions, without a horizontal-strip hypothesis. -/
theorem contained_restricted_embedding {a n : ℕ} {nu mu : YoungDiagram}
    (s : Tableau a nu) (t : Tableau n mu) (h : nu ≤ mu) :
    ∃ J : Representation.IntertwiningMap (spechtRep s)
      ((spechtRep t).comp (Equiv.Perm.viaEmbeddingHom (tableauInclusion s t h))),
      Function.Injective J := by
  let i := tableauInclusion s t h
  letI : NeZero (Nat.card (Equiv.Perm (Fin a)) : ℂ) :=
    ⟨by exact_mod_cast (Nat.card_pos : 0 < Nat.card (Equiv.Perm (Fin a))).ne'⟩
  obtain ⟨F, hF, hcomm⟩ := contained_restriction_surjective s t h
  let P : Representation.IntertwiningMap
      ((spechtRep t).comp (Equiv.Perm.viaEmbeddingHom i)) (spechtRep s) :=
    { toLinearMap := F
      isIntertwining' := fun q => LinearMap.ext <| fun x => hcomm (q.viaEmbedding i) q
        (Equiv.Perm.viaEmbedding_apply _ _)
        (fun k hk => Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hk) x }
  let I := Representation.IntertwiningMap.id (spechtRep s)
  obtain ⟨J, hJ, _⟩ := equivariant_injective_lift P hF I (fun _ _ he => he)
  exact ⟨J, hJ⟩

end
end HSTZ
#print axioms HSTZ.contained_contraction_coefficient
#print axioms HSTZ.contained_contraction_pair
#print axioms HSTZ.contained_specht_restriction

#print axioms HSTZ.contained_restriction_surjective
#print axioms HSTZ.contained_restricted_embedding
