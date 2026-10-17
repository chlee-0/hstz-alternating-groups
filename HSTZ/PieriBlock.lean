import HSTZ.PositionPairBlock
import HSTZ.InducedReparam

/-! Horizontal-strip induction on independent position blocks, and the
staircase label stabilizer. Position alignment is an explicit equality hypothesis. -/
namespace HSTZ

/-- Horizontal-strip support under the independent block inclusion. -/
theorem pieri_block_embedding {n a b : ℕ} {nu mu : YoungDiagram}
    (s : OAI.Saxl.Tableau a nu) (t : OAI.Saxl.Tableau n mu)
    (hs : OAI.Saxl.HorizontalStrip nu mu) (e : Fin n ≃ Fin a ⊕ Fin b)
    (hi : OAI.Saxl.tableauInclusion s t hs.1 = blockInclusion e) :
    ∃ E : Representation.IntertwiningMap (OAI.Saxl.spechtRep t)
      (Representation.ind (A := OAI.Saxl.Specht s) (sumPermHom e)
        ((OAI.Saxl.spechtRep s).comp (MonoidHom.fst _ _))), Function.Injective E := by
  have hExist := pieri_induced_embedding s t hs
  rw [hi] at hExist
  obtain ⟨E, hE⟩ := hExist
  let M := inducedReparamInverse (positionBlockPairEquiv e)
    (positionPairAmbient (blockInclusion e))
    ((OAI.Saxl.spechtRep s).comp (positionPairCore (blockInclusion e)))
  exact ⟨M.comp E, (inducedReparam_rightInverse _ _ _).injective.comp hE⟩

/-- Core Specht action on the staircase label stabilizer; its complement
is trivial. No identification with a one-row tensor carrier is assumed. -/
noncomputable abbrev staircasePieriCore (h q : ℕ) {nu : YoungDiagram}
    (s : OAI.Saxl.Tableau (OAI.Saxl.staircase h).card nu) :=
  (OAI.Saxl.spechtRep s).comp ((positionPairCore
    (blockInclusion (OAI.Saxl.cutPositions h q))).comp
      (staircasePairLabelEquiv h q).symm.toMonoidHom)

/-- The target Specht module lies inside ordinary induction from the label
stabilizer, with the tableau/core-position matching as an explicit hypothesis. -/
theorem staircase_pieri_label_embedding (h q : ℕ) {nu mu : YoungDiagram}
    (s : OAI.Saxl.Tableau (OAI.Saxl.staircase h).card nu)
    (t : OAI.Saxl.Tableau (OAI.Saxl.staircase (h+q)).card mu)
    (hs : OAI.Saxl.HorizontalStrip nu mu)
    (hi : OAI.Saxl.tableauInclusion s t hs.1 =
      blockInclusion (OAI.Saxl.cutPositions h q)) :
    ∃ E : Representation.IntertwiningMap (OAI.Saxl.spechtRep t)
      (Representation.ind (A := OAI.Saxl.Specht s) (staircaseLabelStabilizer h q).subtype
        (staircasePieriCore h q s)), Function.Injective E := by
  let e := staircasePairLabelEquiv h q
  let phi := (staircaseLabelStabilizer h q).subtype
  let rho := staircasePieriCore h q s
  have hphi : phi.comp e.toMonoidHom =
      positionPairAmbient (blockInclusion (OAI.Saxl.cutPositions h q)) := by
    apply MonoidHom.ext
    intro g
    exact staircasePairLabelEquiv_val h q g
  have hrho : rho.comp e.toMonoidHom =
      (OAI.Saxl.spechtRep s).comp
        (positionPairCore (blockInclusion (OAI.Saxl.cutPositions h q))) := by
    ext g x
    simp [rho, staircasePieriCore, e, MonoidHom.comp_apply]
  have hExist := pieri_induced_embedding s t hs
  rw [hi] at hExist
  obtain ⟨E, hE⟩ := hExist
  let M := inducedReparam e phi rho
  have hM : Function.Injective M := (inducedReparam_bijective e phi rho).1
  have hm : ∃ M' : Representation.IntertwiningMap
      (Representation.ind (A := OAI.Saxl.Specht s)
        (positionPairAmbient (blockInclusion (OAI.Saxl.cutPositions h q)))
        ((OAI.Saxl.spechtRep s).comp
          (positionPairCore (blockInclusion (OAI.Saxl.cutPositions h q)))))
      (Representation.ind (A := OAI.Saxl.Specht s) phi rho), Function.Injective M' := by
    rw [← hphi, ← hrho]
    exact ⟨M, hM⟩
  obtain ⟨M', hM'⟩ := hm
  exact ⟨M'.comp E, hM'.comp hE⟩

end HSTZ
#print axioms HSTZ.pieri_block_embedding
#print axioms HSTZ.staircase_pieri_label_embedding
