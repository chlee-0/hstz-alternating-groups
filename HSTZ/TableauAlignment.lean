import HSTZ.PieriBlock
import HSTZ.SpechtTableauTransport
import OAI.RepresentationTheory.Saxl.TableauTransport

/-! Align a contained tableau with arbitrary position blocks.
Coefficient-preserving Specht transport removes the need for a caller-supplied
position matching. -/
namespace HSTZ

/-- A finite permutation places the contained tableau on the prescribed block.
Only containment is needed for this coordinate construction. -/
theorem exists_block_tableau {n a b : ℕ} {nu mu : YoungDiagram}
    (s : OAI.Saxl.Tableau a nu) (t : OAI.Saxl.Tableau n mu) (h : nu ≤ mu)
    (e : Fin n ≃ Fin a ⊕ Fin b) :
    ∃ t' : OAI.Saxl.Tableau n mu,
      OAI.Saxl.tableauInclusion s t' h = blockInclusion e := by
  classical
  let i := OAI.Saxl.tableauInclusion s t h
  let j := blockInclusion e
  let er : Set.range (fun k => j k) ≃ Set.range (fun k => i k) :=
    (Equiv.ofInjective (fun k => j k) j.injective).symm.trans
      (Equiv.ofInjective (fun k => i k) i.injective)
  let p := er.extendSubtype
  have hp (k : Fin a) : p (j k) = i k := by
    rw [Equiv.extendSubtype_apply_of_mem er (j k) ⟨k, rfl⟩]
    change i ((Equiv.ofInjective (fun k => j k) j.injective).symm
      ⟨j k, ⟨k, rfl⟩⟩) = i k
    rw [Equiv.ofInjective_symm_apply]
  let t' := p.trans t
  refine ⟨t', ?_⟩
  apply Function.Embedding.ext
  intro k
  apply t'.injective
  apply Subtype.ext
  rw [OAI.Saxl.tableauInclusion_cell]
  change (s k).val = (t (p (j k))).val
  rw [hp k]
  exact (OAI.Saxl.tableauInclusion_cell s t h k).symm

/-- Ordinary block induction contains the original target Specht, without a
caller-tableau position matching hypothesis. -/
theorem pieri_block_embedding_of_strip {n a b : ℕ} {nu mu : YoungDiagram}
    (s : OAI.Saxl.Tableau a nu) (t : OAI.Saxl.Tableau n mu)
    (hs : OAI.Saxl.HorizontalStrip nu mu) (e : Fin n ≃ Fin a ⊕ Fin b) :
    ∃ E : Representation.IntertwiningMap (OAI.Saxl.spechtRep t)
      (Representation.ind (A := OAI.Saxl.Specht s) (sumPermHom e)
        ((OAI.Saxl.spechtRep s).comp (MonoidHom.fst _ _))), Function.Injective E := by
  obtain ⟨t', hi⟩ := exists_block_tableau s t hs.1 e
  obtain ⟨E, hE⟩ := pieri_block_embedding s t' hs e hi
  exact ⟨E.comp (tableauSpechtMap t t'),
    hE.comp (tableauSpechtMap_bijective t t').1⟩

end HSTZ
#print axioms HSTZ.exists_block_tableau

#print axioms HSTZ.pieri_block_embedding_of_strip
