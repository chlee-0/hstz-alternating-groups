import HSTZ.WitnessAttachmentBinaryRepeated

/-! Column fibers of the attachment and its alternant, written in column order.
Here `finProdFinEquiv` sends the pair `(c, r)` to `2*c+r`. Uses the fiber
reindexing and `letterLift` declarations from OpenAI's `math` repository
(commit adc7f1241, Apache-2.0). -/
namespace HSTZ
noncomputable section
open OAI.Saxl

def witnessAttachmentColumnOrderFin (b delta : ℕ) :
    WitnessAttachmentColumnOrder b delta ≃ Fin (witnessAttachment b delta).card :=
  ((Equiv.sumCongr (finProdFinEquiv : Fin b × Fin 2 ≃ Fin (b*2))
    (Equiv.refl (Fin delta))).trans finSumFinEquiv).trans
      (finCongr (by rw [witnessAttachment_card]; omega))

theorem witnessAttachmentColumnOrderFin_pair (b delta : ℕ) (c : Fin b) (r : Fin 2) :
    (witnessAttachmentColumnOrderFin b delta (.inl (c,r))).val=2*c.val+r.val := by
  simp only [witnessAttachmentColumnOrderFin,Equiv.trans_apply,Equiv.sumCongr_apply,
    Sum.map_inl,finProdFinEquiv,finSumFinEquiv_apply_left,finCongr_apply,Fin.val_cast,
    Fin.val_castAdd]
  change r.val+2*c.val=2*c.val+r.val
  omega

theorem witnessAttachmentColumnOrderFin_single (b delta : ℕ) (j : Fin delta) :
    (witnessAttachmentColumnOrderFin b delta (.inr j)).val=2*b+j.val := by
  simp only [witnessAttachmentColumnOrderFin,Equiv.trans_apply,Equiv.sumCongr_apply,
    Sum.map_inr,Equiv.refl_apply,finSumFinEquiv_apply_right,finCongr_apply,Fin.val_cast,
    Fin.val_natAdd]
  omega

/-- Change of enumeration from the explicit column order to the canonical
tableau. -/
def witnessAttachmentColumnEnumeration (b delta : ℕ) :
    Fin (witnessAttachment b delta).card ≃ Fin (witnessAttachment b delta).card :=
  (witnessAttachmentColumnOrderFin b delta).symm.trans
    (witnessAttachmentColumnPositions b delta)

def witnessAttachmentOrderedColumnLabel (b delta : ℕ) :
    Fin (witnessAttachment b delta).card → ℕ :=
  witnessAttachmentOrderedColumn b delta ∘ (witnessAttachmentColumnOrderFin b delta).symm

def witnessAttachmentOrderedBinaryBase (b delta : ℕ) :
    Fin (witnessAttachment b delta).card → Fin 2 :=
  witnessAttachmentOrderedRow b delta ∘ (witnessAttachmentColumnOrderFin b delta).symm

theorem witnessAttachmentOrderedColumnFiber (b delta : ℕ) :
    fiberGroup (fun i => (witnessCanonicalAttachment b delta
      (witnessAttachmentColumnEnumeration b delta i)).val.2)=
      fiberGroup (witnessAttachmentOrderedColumnLabel b delta) := by
  congr 1
  funext i
  exact witnessAttachmentColumnPositions_column b delta _

theorem witnessAttachmentOrderedBinaryBase_exact (b delta : ℕ) :
    (witnessAttachmentBinaryLetter b delta ∘ rowWord (witnessCanonicalAttachment b delta)) ∘
      witnessAttachmentColumnEnumeration b delta = witnessAttachmentOrderedBinaryBase b delta := by
  funext i
  exact witnessAttachmentBinaryRowWord_ordered b delta _

/-- Every coordinate of the lifted polytabloid, as an alternant over the full
column group. -/
theorem witnessAttachmentOrderedAlternant (b delta : ℕ)
    (w : Fin (witnessAttachment b delta).card → Fin 2) :
    letterLift (witnessAttachmentBinaryLetter b delta)
      (polytabloid (witnessCanonicalAttachment b delta))
      (w ∘ (witnessAttachmentColumnEnumeration b delta).symm)=
    altWord (fiberGroup (witnessAttachmentOrderedColumnLabel b delta))
      (witnessAttachmentOrderedBinaryBase b delta) w := by
  rw [polytabloid_eq_altWord,letterLift_altWord]
  change altWord (fiberGroup (fun i => (witnessCanonicalAttachment b delta i).val.2))
    (witnessAttachmentBinaryLetter b delta ∘ rowWord (witnessCanonicalAttachment b delta))
    (w ∘ (witnessAttachmentColumnEnumeration b delta).symm)=_
  rw [altWord_fiber_relabel]
  change altWord (fiberGroup (fun i => (witnessCanonicalAttachment b delta
    (witnessAttachmentColumnEnumeration b delta i)).val.2))
    ((witnessAttachmentBinaryLetter b delta ∘ rowWord (witnessCanonicalAttachment b delta)) ∘
      witnessAttachmentColumnEnumeration b delta) w=_
  rw [witnessAttachmentOrderedColumnFiber,witnessAttachmentOrderedBinaryBase_exact]

/-- The coordinates of the repeated pair in column order. -/
theorem witnessAttachmentOrderedRepeated_coordinates (b delta : ℕ)
    (u v : Fin (witnessAttachment b delta).card → Fin 2) :
    witnessAttachmentBinaryRepeatedWord b delta
      (mergeWords (u ∘ (witnessAttachmentColumnEnumeration b delta).symm)
        (v ∘ (witnessAttachmentColumnEnumeration b delta).symm)) =
      altWord (fiberGroup (witnessAttachmentOrderedColumnLabel b delta))
        (witnessAttachmentOrderedBinaryBase b delta) u *
      altWord (fiberGroup (witnessAttachmentOrderedColumnLabel b delta))
        (witnessAttachmentOrderedBinaryBase b delta) v := by
  rw [witnessAttachmentBinaryRepeatedWord_tensor,wordTensor_tmul,splitLeft_merge,
    splitRight_merge,witnessAttachmentOrderedAlternant,witnessAttachmentOrderedAlternant]


end
end HSTZ
#print axioms HSTZ.witnessAttachmentColumnOrderFin_pair
#print axioms HSTZ.witnessAttachmentColumnOrderFin_single
#print axioms HSTZ.witnessAttachmentOrderedColumnFiber
#print axioms HSTZ.witnessAttachmentOrderedBinaryBase_exact
#print axioms HSTZ.witnessAttachmentOrderedAlternant

#print axioms HSTZ.witnessAttachmentOrderedRepeated_coordinates
