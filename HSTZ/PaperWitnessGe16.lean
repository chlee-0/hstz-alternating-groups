import HSTZ.PaperWitnessUnique
import HSTZ.AlternatingSquare

/-! Headline statements for every n ≥ 16. With the witness guard `5 ≤ k`, the
support chain and the alternating-group step hold for every guarded witness; the cases
k = 5, 6 are covered through `balancePacking_numeric_coverage_ge5`. Guarded parameters
are unique (`paperWitness_parameters_unique`), so these are statements about the
canonical witness λ_n. -/
namespace HSTZ
open OAI.Saxl

private theorem tri_succ_ge16 (k : ℕ) : (k+1)*(k+1+1)/2=k*(k+1)/2+(k+1) := by
  have h : (k+1)*(k+1+1)=k*(k+1)+(k+1)*2 := by ring
  rw [h,Nat.add_mul_div_right _ _ (by norm_num)]

/-- Every n ≥ 16 is |λ| for a witness satisfying the (k ≥ 5) guard. -/
theorem paperWitness_parameters_ge16 (n : ℕ) (hn : 16 ≤ n) :
    ∃ k b delta : ℕ, ∃ hp : PaperWitnessGuard k b delta,
      (witnessDiagram k b delta hp.staircase_bound).card=n := by
  have hex : ∃ k, n ≤ (k+1)*(k+1+1)/2 := by
    refine ⟨n,?_⟩
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    nlinarith
  classical
  let k := Nat.find hex
  have hup : n ≤ (k+1)*(k+1+1)/2 := Nat.find_spec hex
  have hlow : k*(k+1)/2 < n := by
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · rw [h0]
      omega
    · have hmin := Nat.find_min hex (show k-1 < k by omega)
      have hk : k-1+1=k := by omega
      rw [hk] at hmin
      omega
  have hstep := tri_succ_ge16 k
  have hk5 : 5 ≤ k := by
    by_contra hlt
    push_neg at hlt
    interval_cases hk : k <;> omega
  set r := n-k*(k+1)/2 with hr
  refine ⟨k,r/2,r%2,⟨hk5,by omega,by omega,by omega⟩,?_⟩
  rw [witnessDiagram_card]
  omega

/-- Statement (A) for every n ≥ 16: g(λ,λ,ν)+g(λ,λ,νᵗ) > 0 for every ν ⊢ n. -/
theorem paperWitness_statementA_ge16 (n : ℕ) (hn : 16 ≤ n) :
    ∃ k b delta : ℕ, ∃ hp : PaperWitnessGuard k b delta,
      (witnessDiagram k b delta hp.staircase_bound).card=n ∧
      ∀ (z : Tableau n (witnessDiagram k b delta hp.staircase_bound))
        {nu : YoungDiagram} (target : Tableau n nu),
        0 < kronecker z z target+kronecker z z (transposeTableau target) := by
  obtain ⟨k,b,delta,hp,hcard⟩ := paperWitness_parameters_ge16 n hn
  exact ⟨k,b,delta,hp,hcard,fun z _ target => paperWitness_oriented_pos k b delta hp z target⟩

/-- The alternating-group conclusion for every n ≥ 16: `ψ = S^λ|A_n` is irreducible
and its tensor square contains every irreducible representation of `A_n`. -/
theorem paperWitness_alternating_ge16 (n : ℕ) (hn : 16 ≤ n) :
    ∃ k b delta : ℕ, ∃ hp : PaperWitnessGuard k b delta,
      (witnessDiagram k b delta hp.staircase_bound).card = n ∧
      ∀ z : Tableau n (witnessDiagram k b delta hp.staircase_bound),
        Representation.IsIrreducible ((spechtRep z).comp (alternatingGroup (Fin n)).subtype) ∧
        ∀ (W : Type) [AddCommGroup W] [Module ℂ W]
          (σ : Representation ℂ (alternatingGroup (Fin n)) W) [Representation.IsIrreducible σ],
          ∃ f : Representation.IntertwiningMap σ
            (Representation.tprod ((spechtRep z).comp (alternatingGroup (Fin n)).subtype)
              ((spechtRep z).comp (alternatingGroup (Fin n)).subtype)), f ≠ 0 := by
  obtain ⟨k, b, delta, hp, hcard⟩ := paperWitness_parameters_ge16 n hn
  exact ⟨k, b, delta, hp, hcard, fun z => ⟨paperWitness_alternating_irreducible k b delta hp z,
    fun W _ _ σ _ => paperWitness_alternating_square k b delta hp z σ⟩⟩

end HSTZ
#print axioms HSTZ.paperWitness_parameters_ge16
#print axioms HSTZ.paperWitness_statementA_ge16
#print axioms HSTZ.paperWitness_alternating_ge16
