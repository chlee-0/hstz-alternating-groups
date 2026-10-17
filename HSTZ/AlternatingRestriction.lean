import HSTZ.IntertwiningCompat
import HSTZ.SpechtSignTransport
import HSTZ.FDRepBridge
import HSTZ.WitnessBalancePackingSupport
import OAI.RepresentationTheory.Saxl.ShapeRigidity

import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.LinearAlgebra.Projection

/-! Irreducibility of the witness Specht representation restricted to the alternating
group (part (i) of the alternating step).
Elementary Clifford-type argument: if the restriction of an irreducible `S_n`-representation
to `A_n` is reducible, a proper `A_n`-subspace `U` and its translate by a transposition are
complementary, and `2·proj_U − id` is an isomorphism `ρ ≅ ρ ⊗ sgn`. For Specht modules this
forces a self-conjugate shape (sign-transpose isomorphism and shape rigidity, adapted from
OpenAI's `math` repository). -/
namespace HSTZ
noncomputable section
open OAI.Saxl

section Clifford
variable {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ (Equiv.Perm (Fin n)) V)

/-- The sign twist is invisible on the alternating group. -/
theorem signTwist_comp_alternating :
    (signTwist ρ).comp (alternatingGroup (Fin n)).subtype = ρ.comp (alternatingGroup (Fin n)).subtype := by
  apply MonoidHom.ext
  intro g
  have hg : Equiv.Perm.sign (g : Equiv.Perm (Fin n)) = 1 := Equiv.Perm.mem_alternatingGroup.mp g.2
  change signC (g : Equiv.Perm (Fin n)) • ρ g = ρ g
  rw [signC_def, hg]
  simp

/-- Clifford-type criterion: an irreducible `S_n`-representation not isomorphic to its
sign twist stays irreducible on `A_n`. -/
theorem alternating_restriction_irreducible (hn : 2 ≤ n) [Representation.IsIrreducible ρ]
    (hns : ∀ T : Representation.IntertwiningMap ρ (signTwist ρ), ¬ Function.Bijective T) :
    Representation.IsIrreducible (ρ.comp (alternatingGroup (Fin n)).subtype) := by
  classical
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  have h01 : i0 ≠ i1 := by
    intro h
    have := congrArg Fin.val h
    simp [i0, i1] at this
  let τ : Equiv.Perm (Fin n) := Equiv.swap i0 i1
  have hτs : Equiv.Perm.sign τ = -1 := Equiv.Perm.sign_swap h01
  have hττ : τ * τ = 1 := Equiv.swap_mul_self i0 i1
  have hmul : ∀ x y : Equiv.Perm (Fin n), ∀ v : V, ρ x (ρ y v) = ρ (x * y) v := by
    intro x y v
    rw [map_mul]
    rfl
  have hpar : ∀ g : Equiv.Perm (Fin n), Equiv.Perm.sign g = 1 ∨ Equiv.Perm.sign g = -1 :=
    fun g => Int.units_eq_one_or _
  have hbt : (⊥ : Subrepresentation ρ) ≠ ⊤ := bot_ne_top
  refine { exists_pair_ne := ⟨⊥, ⊤, fun h => by
      have h' := congrArg Subrepresentation.toSubmodule h
      exact hbt (Subrepresentation.toSubmodule_injective h')⟩, eq_bot_or_eq_top := ?_ }
  intro U
  by_contra hU
  push_neg at hU
  obtain ⟨hUb, hUt⟩ := hU
  let A := U.toSubmodule
  have hA : ∀ g : Equiv.Perm (Fin n), Equiv.Perm.sign g = 1 → ∀ v ∈ A, ρ g v ∈ A :=
    fun g hg v hv => U.apply_mem_toSubmodule ⟨g, Equiv.Perm.mem_alternatingGroup.mpr hg⟩ hv
  let B := A.map (ρ τ)
  have hBe : ∀ g : Equiv.Perm (Fin n), Equiv.Perm.sign g = 1 → ∀ v ∈ B, ρ g v ∈ B := by
    rintro g hg v ⟨a, ha, rfl⟩
    refine ⟨ρ (τ * g * τ) a, hA _ (by simp [Equiv.Perm.sign_mul, hτs, hg]) a ha, ?_⟩
    change ρ τ (ρ (τ * g * τ) a) = ρ g (ρ τ a)
    rw [hmul, hmul, show τ * (τ * g * τ) = g * τ by rw [← mul_assoc, ← mul_assoc, hττ, one_mul]]
  have hAo : ∀ g : Equiv.Perm (Fin n), Equiv.Perm.sign g = -1 → ∀ v ∈ A, ρ g v ∈ B := by
    intro g hg v hv
    refine ⟨ρ (τ * g) v, hA _ (by simp [Equiv.Perm.sign_mul, hτs, hg]) v hv, ?_⟩
    change ρ τ (ρ (τ * g) v) = ρ g v
    rw [hmul, ← mul_assoc, hττ, one_mul]
  have hBo : ∀ g : Equiv.Perm (Fin n), Equiv.Perm.sign g = -1 → ∀ v ∈ B, ρ g v ∈ A := by
    rintro g hg v ⟨a, ha, rfl⟩
    change ρ g (ρ τ a) ∈ A
    rw [hmul]
    exact hA _ (by simp [Equiv.Perm.sign_mul, hτs, hg]) a ha
  have hS : ∀ (g : Equiv.Perm (Fin n)) (v : V), v ∈ A ⊔ B → ρ g v ∈ A ⊔ B := by
    intro g v hv
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
    rw [map_add]
    rcases hpar g with hg | hg
    · exact Submodule.add_mem_sup (hA g hg a ha) (hBe g hg b hb)
    · exact Submodule.mem_sup.mpr ⟨ρ g b, hBo g hg b hb, ρ g a, hAo g hg a ha, add_comm _ _⟩
  have hI : ∀ (g : Equiv.Perm (Fin n)) (v : V), v ∈ A ⊓ B → ρ g v ∈ A ⊓ B := by
    intro g v hv
    obtain ⟨hva, hvb⟩ := Submodule.mem_inf.mp hv
    rcases hpar g with hg | hg
    · exact Submodule.mem_inf.mpr ⟨hA g hg v hva, hBe g hg v hvb⟩
    · exact Submodule.mem_inf.mpr ⟨hBo g hg v hvb, hAo g hg v hva⟩
  let SR : Subrepresentation ρ := ⟨A ⊔ B, fun g v hv => hS g v hv⟩
  let IR : Subrepresentation ρ := ⟨A ⊓ B, fun g v hv => hI g v hv⟩
  have hsup : A ⊔ B = ⊤ := by
    rcases IsSimpleOrder.eq_bot_or_eq_top SR with h | h
    · exfalso
      apply hUb
      apply Subrepresentation.toSubmodule_injective
      have hle : A ≤ A ⊔ B := le_sup_left
      have h' : A ⊔ B = ⊥ := congrArg Subrepresentation.toSubmodule h
      exact le_bot_iff.mp (h' ▸ hle)
    · exact congrArg Subrepresentation.toSubmodule h
  have hinf : A ⊓ B = ⊥ := by
    rcases IsSimpleOrder.eq_bot_or_eq_top IR with h | h
    · exact congrArg Subrepresentation.toSubmodule h
    · exfalso
      apply hUt
      apply Subrepresentation.toSubmodule_injective
      have h' : A ⊓ B = ⊤ := congrArg Subrepresentation.toSubmodule h
      exact (inf_eq_top_iff.mp h').1
  have hc : IsCompl A B := IsCompl.of_eq hinf hsup
  let π := Submodule.linearProjOfIsCompl A B hc
  let Tl : V →ₗ[ℂ] V := (2 : ℂ) • (A.subtype ∘ₗ π) - LinearMap.id
  have hT : ∀ a ∈ A, ∀ b ∈ B, Tl (a + b) = a - b := by
    intro a ha b hb
    have h1 : π a = ⟨a, ha⟩ := Submodule.linearProjOfIsCompl_apply_left hc ⟨a, ha⟩
    have h2 : π b = 0 := Submodule.linearProjOfIsCompl_apply_right hc ⟨b, hb⟩
    change (2 : ℂ) • ((π (a + b) : A) : V) - (a + b) = a - b
    rw [map_add, h1, h2, add_zero]
    change (2 : ℂ) • a - (a + b) = a - b
    rw [two_smul]
    abel
  have hdec : ∀ v : V, ∃ a ∈ A, ∃ b ∈ B, a + b = v := by
    intro v
    have hv : v ∈ A ⊔ B := hsup ▸ Submodule.mem_top
    exact Submodule.mem_sup.mp hv
  let T : Representation.IntertwiningMap ρ (signTwist ρ) :=
    { toLinearMap := Tl
      isIntertwining' := by
        intro g
        apply LinearMap.ext
        intro v
        obtain ⟨a, ha, b, hb, rfl⟩ := hdec v
        show Tl (ρ g (a + b)) = signC g • ρ g (Tl (a + b))
        rw [hT a ha b hb, map_add]
        rcases hpar g with hg | hg
        · rw [hT _ (hA g hg a ha) _ (hBe g hg b hb), signC_def, hg]
          simp [map_sub]
        · rw [show ρ g a + ρ g b = ρ g b + ρ g a from add_comm _ _,
            hT _ (hBo g hg b hb) _ (hAo g hg a ha), signC_def, hg]
          simp [map_sub] }
  have hinv : Function.Involutive Tl := by
    intro v
    obtain ⟨a, ha, b, hb, rfl⟩ := hdec v
    rw [hT a ha b hb, sub_eq_add_neg, hT a ha (-b) (B.neg_mem hb), sub_neg_eq_add]
  exact hns T hinv.bijective
end Clifford

/-- A Specht module of a non-self-conjugate shape is not isomorphic to its sign twist. -/
theorem specht_no_sign_iso {n : ℕ} {mu : YoungDiagram} (t : Tableau n mu)
    (hmu : mu.transpose ≠ mu)
    (T : Representation.IntertwiningMap (spechtRep t) (signTwist (spechtRep t))) :
    ¬ Function.Bijective T := by
  intro hT
  let e := spechtSignEquiv t
  let F : Representation.IntertwiningMap (spechtRep t) (spechtRep (transposeTableau t)) :=
    { toLinearMap := e.toLinearMap ∘ₗ T.toLinearMap
      isIntertwining' := by
        intro g
        apply LinearMap.ext
        intro x
        have hs : signC g * signC g = 1 := by
          rw [signC_def]
          rcases Int.units_eq_one_or (Equiv.Perm.sign g) with h | h <;> simp [h]
        change e (T (spechtRep t g x)) = spechtRep (transposeTableau t) g (e (T x))
        rw [T.map_action]
        change e (signC g • spechtRep t g (T x)) = _
        rw [map_smul, spechtSignEquiv_equivariant, smul_smul, hs, one_smul] }
  have hF : Function.Bijective F := e.bijective.comp hT
  exact hmu (specht_shape_rigidity t (transposeTableau t) (F.ofBijective hF)).symm

/-- Part (i) of the alternating step: for the paper witness, ψ = S^λ|A_n is irreducible. -/
theorem paperWitness_alternating_irreducible (k b delta : ℕ) (hp : PaperWitnessGuard k b delta)
    {n : ℕ} (z : Tableau n (witnessDiagram k b delta hp.staircase_bound)) :
    Representation.IsIrreducible ((spechtRep z).comp (alternatingGroup (Fin n)).subtype) := by
  haveI := specht_irreducible z
  have hz : (witnessDiagram k b delta hp.staircase_bound).card = n := by
    simpa using (Fintype.card_congr z).symm
  rw [witnessDiagram_card] at hz
  have h56 : 5 * 6 ≤ k * (k + 1) := Nat.mul_le_mul hp.staircase_bound (by have := hp.staircase_bound; omega)
  have hn : 2 ≤ n := by
    have h2 : 2 ≤ k * (k + 1) / 2 := (Nat.le_div_iff_mul_le (by norm_num)).mpr (by omega)
    omega
  exact alternating_restriction_irreducible (spechtRep z) hn (fun T => specht_no_sign_iso z
    (witnessDiagram_not_self_conjugate k b delta hp.staircase_bound hp.positive_remainder) T)

end
end HSTZ
#print axioms HSTZ.signTwist_comp_alternating
#print axioms HSTZ.alternating_restriction_irreducible
#print axioms HSTZ.specht_no_sign_iso
#print axioms HSTZ.paperWitness_alternating_irreducible
