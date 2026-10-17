import HSTZ.IntertwiningCompat
import OAI.RepresentationTheory.Saxl.PieriRestriction

import HSTZ.InducedEmbedding
import HSTZ.SectorInduction

/-! Horizontal-strip restriction and split support on the full group of
compatible position permutations. This does not identify arbitrary branching
or the core/band induced constituents. -/
namespace HSTZ

/-- All ambient/core permutation pairs respecting the position embedding.
The ambient permutation is unrestricted on the complement. -/
def positionPairGroup {a n : ℕ} (i : Fin a ↪ Fin n) :
    Subgroup (Equiv.Perm (Fin n) × Equiv.Perm (Fin a)) where
  carrier := {g | ∀ k, g.1 (i k) = i (g.2 k)}
  one_mem' := fun _ => rfl
  mul_mem' := by
    intro g h hg hh k
    change g.1 (h.1 (i k)) = i (g.2 (h.2 k))
    rw [hh, hg]
  inv_mem' := by
    intro g hg k
    change g.1⁻¹ (i k) = i (g.2⁻¹ k)
    apply g.1.injective
    simpa using (hg (g.2⁻¹ k)).symm

def positionPairAmbient {a n : ℕ} (i : Fin a ↪ Fin n) :
    positionPairGroup i →* Equiv.Perm (Fin n) :=
  (MonoidHom.fst _ _).comp (positionPairGroup i).subtype

def positionPairCore {a n : ℕ} (i : Fin a ↪ Fin n) :
    positionPairGroup i →* Equiv.Perm (Fin a) :=
  (MonoidHom.snd _ _).comp (positionPairGroup i).subtype


/-- Compatible pairs identify a subgroup of ambient permutations. -/
theorem positionPairAmbient_injective {a n : ℕ} (i : Fin a ↪ Fin n) :
    Function.Injective (positionPairAmbient i) := by
  intro g h he
  apply Subtype.ext
  apply Prod.ext
  · exact he
  · apply Equiv.ext
    intro k
    apply i.injective
    rw [← g.property k, ← h.property k]
    exact congrArg (fun p : Equiv.Perm (Fin n) => p (i k)) he

/-- The native positive map is onto the core Specht space. -/
theorem pieri_restriction_surjective {a n : ℕ} {nu mu : YoungDiagram}
    (s : OAI.Saxl.Tableau a nu) (t : OAI.Saxl.Tableau n mu)
    (hs : OAI.Saxl.HorizontalStrip nu mu) :
    ∃ F : OAI.Saxl.Specht t →ₗ[ℂ] OAI.Saxl.Specht s,
      Function.Surjective F ∧ ∀ (g : Equiv.Perm (Fin n)) (h : Equiv.Perm (Fin a)),
        (∀ k, g (OAI.Saxl.tableauInclusion s t hs.1 k) =
          OAI.Saxl.tableauInclusion s t hs.1 (h k)) →
        ∀ x, F (OAI.Saxl.spechtRep t g x) = OAI.Saxl.spechtRep s h (F x) := by
  classical
  obtain ⟨F, hF, hcomm⟩ := OAI.Saxl.pieri_strip_restriction s t hs
  let i := OAI.Saxl.tableauInclusion s t hs.1
  let S : Subrepresentation (OAI.Saxl.spechtRep s) :=
    { toSubmodule := F.range
      apply_mem_toSubmodule := by
        intro h y hy
        obtain ⟨x, rfl⟩ := hy
        exact ⟨OAI.Saxl.spechtRep t (h.viaEmbedding i) x,
          hcomm _ h (Equiv.Perm.viaEmbedding_apply _ _) x⟩ }
  letI := OAI.Saxl.specht_irreducible s
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

/-- A core Specht embedding in the ambient Specht module restricted to all
compatible permutations, including arbitrary complement permutations. -/
theorem pieri_restricted_embedding {a n : ℕ} {nu mu : YoungDiagram}
    (s : OAI.Saxl.Tableau a nu) (t : OAI.Saxl.Tableau n mu)
    (hs : OAI.Saxl.HorizontalStrip nu mu) :
    ∃ j : Representation.IntertwiningMap
      ((OAI.Saxl.spechtRep s).comp (positionPairCore (OAI.Saxl.tableauInclusion s t hs.1)))
      ((OAI.Saxl.spechtRep t).comp (positionPairAmbient (OAI.Saxl.tableauInclusion s t hs.1))),
      Function.Injective j := by
  let i := OAI.Saxl.tableauInclusion s t hs.1
  letI : NeZero (Nat.card (positionPairGroup i) : ℂ) :=
    ⟨by exact_mod_cast (Nat.card_pos : 0 < Nat.card (positionPairGroup i)).ne'⟩
  obtain ⟨F, hF, hcomm⟩ := pieri_restriction_surjective s t hs
  let P : Representation.IntertwiningMap
      ((OAI.Saxl.spechtRep t).comp (positionPairAmbient i))
      ((OAI.Saxl.spechtRep s).comp (positionPairCore i)) :=
    { toLinearMap := F
      isIntertwining' := fun g => LinearMap.ext <| fun x => hcomm g.val.1 g.val.2 g.property x }
  let J := Representation.IntertwiningMap.id ((OAI.Saxl.spechtRep s).comp (positionPairCore i))
  obtain ⟨j, hj, _⟩ := equivariant_injective_lift P hF J (fun _ _ he => he)
  exact ⟨j, hj⟩

/-- A nonzero map onto an irreducible representation is surjective. -/
theorem intertwiner_surjective_of_irreducible
    {K G U V : Type*} [Field K] [Group G]
    [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
    {tau : Representation K G U} {rho : Representation K G V}
    [Representation.IsIrreducible rho]
    (F : Representation.IntertwiningMap tau rho) (hF : F ≠ 0) :
    Function.Surjective F := by
  let S : Subrepresentation rho :=
    { toSubmodule := F.toLinearMap.range
      apply_mem_toSubmodule := by
        intro g y hy
        obtain ⟨x, rfl⟩ := hy
        exact ⟨tau g x, F.map_action g x⟩ }
  have hn : S ≠ ⊥ := by
    intro he
    apply hF
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    have hx : F x ∈ S.toSubmodule := ⟨x, rfl⟩
    rw [he] at hx
    exact (Submodule.mem_bot K).mp hx
  have ht : S = ⊤ := (eq_bot_or_eq_top S).resolve_left hn
  intro y
  have hy : y ∈ S.toSubmodule := by rw [ht]; trivial
  exact hy

/-- Horizontal-strip Specht support in ordinary induction. The source action
factors through the core permutation; complement permutations act trivially. -/
theorem pieri_induced_embedding {a n : ℕ} {nu mu : YoungDiagram}
    (s : OAI.Saxl.Tableau a nu) (t : OAI.Saxl.Tableau n mu)
    (hs : OAI.Saxl.HorizontalStrip nu mu) :
    ∃ E : Representation.IntertwiningMap (OAI.Saxl.spechtRep t)
      (Representation.ind (A := OAI.Saxl.Specht s)
        (positionPairAmbient (OAI.Saxl.tableauInclusion s t hs.1))
        ((OAI.Saxl.spechtRep s).comp (positionPairCore (OAI.Saxl.tableauInclusion s t hs.1)))),
      Function.Injective E := by
  let i := OAI.Saxl.tableauInclusion s t hs.1
  let phi := positionPairAmbient i
  let tau := (OAI.Saxl.spechtRep s).comp (positionPairCore i)
  let rho := OAI.Saxl.spechtRep t
  letI : NeZero (Nat.card (Equiv.Perm (Fin n)) : ℂ) :=
    ⟨by exact_mod_cast (Nat.card_pos : 0 < Nat.card (Equiv.Perm (Fin n))).ne'⟩
  letI : Representation.IsIrreducible rho := OAI.Saxl.specht_irreducible t
  obtain ⟨j, hj⟩ := pieri_restricted_embedding s t hs
  let J := inducedIntertwiner phi tau rho j
  let p : OAI.Saxl.Specht s := ⟨OAI.Saxl.polytabloid s, OAI.Saxl.mem_cyclic _ _⟩
  have hJ : J ≠ 0 := by
    intro he
    have hz : J (Representation.IndV.mk phi tau 1 p) = 0 := by rw [he]; rfl
    change inducedLinearMap phi tau rho j (Representation.IndV.mk phi tau 1 p) = 0 at hz
    rw [inducedLinearMap_mk] at hz
    have hzj : j p = 0 := by simpa using hz
    have hp : p = 0 := hj (hzj.trans (map_zero j.toLinearMap).symm)
    exact OAI.Saxl.polytabloid_ne_zero s (congrArg Subtype.val hp)
  have hsur := intertwiner_surjective_of_irreducible J hJ
  let Id := Representation.IntertwiningMap.id rho
  obtain ⟨E, hE, _⟩ := equivariant_injective_lift J hsur Id (fun _ _ he => he)
  exact ⟨E, hE⟩

end HSTZ
#print axioms HSTZ.pieri_restriction_surjective
#print axioms HSTZ.pieri_restricted_embedding

#print axioms HSTZ.intertwiner_surjective_of_irreducible
#print axioms HSTZ.pieri_induced_embedding

#print axioms HSTZ.positionPairAmbient_injective
