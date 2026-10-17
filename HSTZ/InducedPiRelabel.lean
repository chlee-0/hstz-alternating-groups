import HSTZ.InducedPiTower

/-! Generic block relabelling for ordered Young-subgroup induction.
A position equivalence and a blockwise relabelling of an ordered block product
into a "joint ⊕ rest" block product make the two block homs conjugate; induction
along them is then bijective by `inducedConj`. Also: Pi tensor maps of injective
maps are injective over ℂ. -/
namespace HSTZ
noncomputable section

section PiInj
/-- Pi tensor of injective linear maps over ℂ is injective. -/
theorem piTensorMap_injective {ι : Type*} {s t : ι → Type*}
    [∀ i, AddCommGroup (s i)] [∀ i, Module ℂ (s i)]
    [∀ i, AddCommGroup (t i)] [∀ i, Module ℂ (t i)]
    (f : ∀ i, s i →ₗ[ℂ] t i) (hf : ∀ i, Function.Injective (f i)) :
    Function.Injective (PiTensorProduct.map f) := by
  choose g hg using fun i =>
    (f i).exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr (hf i))
  have h2 : (PiTensorProduct.map g).comp (PiTensorProduct.map f) = LinearMap.id := by
    rw [← PiTensorProduct.map_comp]
    simp only [hg]
    exact PiTensorProduct.map_id
  have hl : Function.LeftInverse (PiTensorProduct.map g) (PiTensorProduct.map f) := fun x => by
    simpa using LinearMap.congr_fun h2 x
  exact hl.injective
end PiInj

section PosConj
variable {a : ℕ} {X Z H K : Type*} [Group H] [Group K]

/-- Two block homs described through position equivalences and a relabelling
of the blocks are conjugate by the explicit permutation built from the positions. -/
theorem hom_conj_of_positions (P : Fin a ≃ X) (Q : Fin a ≃ Z) (B : X ≃ Z)
    (Y : H →* Equiv.Perm (Fin a)) (phi : K →* Equiv.Perm (Fin a)) (mu : H → K)
    (AX : H → X → X) (AZ : K → Z → Z)
    (hY : ∀ h x, Y h (P.symm x) = P.symm (AX h x))
    (hphi : ∀ k z, phi k (Q.symm z) = Q.symm (AZ k z))
    (hB : ∀ h x, B (AX h x) = AZ (mu h) (B x)) (h : H) :
    Y h = ((Q.trans B.symm).trans P.symm : Equiv.Perm (Fin a)) * phi (mu h) *
      ((Q.trans B.symm).trans P.symm : Equiv.Perm (Fin a))⁻¹ := by
  apply Equiv.ext
  intro y
  obtain ⟨x, rfl⟩ := P.symm.surjective y
  rw [hY]
  have h1 : ((Q.trans B.symm).trans P.symm : Equiv.Perm (Fin a))⁻¹ (P.symm x) = Q.symm (B x) := by
    rw [Equiv.Perm.inv_def]
    simp
  change P.symm (AX h x) = ((Q.trans B.symm).trans P.symm)
    (phi (mu h) (((Q.trans B.symm).trans P.symm : Equiv.Perm (Fin a))⁻¹ (P.symm x)))
  rw [h1, hphi, ← hB]
  simp
end PosConj

section Relabel
variable {I R : Type*} (J : ℕ) (sz : R → ℕ) (d : I → ℕ) (beta : I ≃ Unit ⊕ R)
  (f : ∀ v, Fin (d v) ≃ Fin (Sum.elim (fun _ : Unit => J) sz (beta v)))

/-- Blockwise relabelling of the ordered block product. -/
def piRelabel : (∀ v, Equiv.Perm (Fin (d v))) ≃*
    ∀ x : Unit ⊕ R, Equiv.Perm (Fin (Sum.elim (fun _ : Unit => J) sz x)) where
  toEquiv := (Equiv.piCongrRight fun v => (f v).permCongr).trans
    (Equiv.piCongrLeft (fun x => Equiv.Perm (Fin (Sum.elim (fun _ : Unit => J) sz x))) beta)
  map_mul' g h := by
    funext x
    obtain ⟨v, rfl⟩ := beta.surjective x
    simp only [Equiv.toFun_as_coe, Equiv.trans_apply, Equiv.piCongrLeft_apply_apply,
      Equiv.piCongrRight_apply, Pi.mul_apply]
    exact (f v).permCongrHom.map_mul (g v) (h v)

theorem piRelabel_apply (g : ∀ v, Equiv.Perm (Fin (d v))) (v : I) :
    piRelabel J sz d beta f g (beta v) = (f v).permCongr (g v) := by
  change (Equiv.piCongrLeft (fun x => Equiv.Perm (Fin (Sum.elim (fun _ : Unit => J) sz x))) beta)
    ((Equiv.piCongrRight fun v => (f v).permCongr) g) (beta v) = _
  rw [Equiv.piCongrLeft_apply_apply]
  rfl

/-- Blockwise relabelling of the ordered block positions. -/
def sigmaRelabel : (Σ v, Fin (d v)) ≃ Σ x : Unit ⊕ R, Fin (Sum.elim (fun _ : Unit => J) sz x) :=
  (Equiv.sigmaCongrRight f).trans
    (Equiv.sigmaCongrLeft (β := fun x => Fin (Sum.elim (fun _ : Unit => J) sz x)) beta)

/-- Joint ⊕ rest positions. -/
def sumSplitPos : (Σ x : Unit ⊕ R, Fin (Sum.elim (fun _ : Unit => J) sz x)) ≃
    Fin J ⊕ Σ r : R, Fin (sz r) :=
  (Equiv.sumSigmaDistrib (fun x => Fin (Sum.elim (fun _ : Unit => J) sz x))).trans
    (Equiv.sumCongr (Equiv.uniqueSigma fun _ : Unit => Fin J) (Equiv.refl _))

/-- Joint × rest groups. -/
def sumSplitGroup : (∀ x : Unit ⊕ R, Equiv.Perm (Fin (Sum.elim (fun _ : Unit => J) sz x))) ≃*
    Equiv.Perm (Fin J) × ∀ r : R, Equiv.Perm (Fin (sz r)) where
  toEquiv := (Equiv.sumPiEquivProdPi
      (fun x => Equiv.Perm (Fin (Sum.elim (fun _ : Unit => J) sz x)))).trans
    (Equiv.prodCongr (Equiv.piUnique fun _ : Unit => Equiv.Perm (Fin J)) (Equiv.refl _))
  map_mul' _ _ := rfl

theorem sumSplit_conj (g : ∀ x : Unit ⊕ R, Equiv.Perm (Fin (Sum.elim (fun _ : Unit => J) sz x)))
    (w : Σ x : Unit ⊕ R, Fin (Sum.elim (fun _ : Unit => J) sz x)) :
    sumSplitPos J sz (Equiv.sigmaCongrRight g w) =
      Sum.map (sumSplitGroup J sz g).1 (fun z => ⟨z.1, (sumSplitGroup J sz g).2 z.1 z.2⟩)
        (sumSplitPos J sz w) := by
  rcases w with ⟨⟨⟩ | r, y⟩ <;> rfl

/-- The combined block relabelling group equivalence. -/
def blockRelabel : (∀ v, Equiv.Perm (Fin (d v))) ≃* Equiv.Perm (Fin J) × ∀ r : R, Equiv.Perm (Fin (sz r)) :=
  (piRelabel J sz d beta f).trans (sumSplitGroup J sz)

theorem blockRelabel_conj (g : ∀ v, Equiv.Perm (Fin (d v))) (x : Σ v, Fin (d v)) :
    ((sigmaRelabel J sz d beta f).trans (sumSplitPos J sz)) (Equiv.sigmaCongrRight g x) =
      Sum.map (blockRelabel J sz d beta f g).1
        (fun z => ⟨z.1, (blockRelabel J sz d beta f g).2 z.1 z.2⟩)
        (((sigmaRelabel J sz d beta f).trans (sumSplitPos J sz)) x) := by
  rcases x with ⟨v, y⟩
  have he : sigmaRelabel J sz d beta f (Equiv.sigmaCongrRight g ⟨v, y⟩) =
      Equiv.sigmaCongrRight (piRelabel J sz d beta f g) (sigmaRelabel J sz d beta f ⟨v, y⟩) := by
    change (⟨beta v, f v (g v y)⟩ : Σ x : Unit ⊕ R, Fin (Sum.elim (fun _ : Unit => J) sz x)) =
      ⟨beta v, piRelabel J sz d beta f g (beta v) (f v y)⟩
    rw [piRelabel_apply]
    simp [Equiv.permCongr_apply]
  rw [Equiv.trans_apply, he, sumSplit_conj]
  rfl

variable {a : ℕ}

/-- An ordered block hom and a joint ⊕ rest block hom with position descriptions
are conjugate through the block relabelling. -/
theorem blockHom_conj (P : Fin a ≃ Σ v, Fin (d v)) (Q : Fin a ≃ Fin J ⊕ Σ r : R, Fin (sz r))
    (Y : (∀ v, Equiv.Perm (Fin (d v))) →* Equiv.Perm (Fin a))
    (phi : (Equiv.Perm (Fin J) × ∀ r : R, Equiv.Perm (Fin (sz r))) →* Equiv.Perm (Fin a))
    (hY : ∀ h x, Y h (P.symm x) = P.symm (Equiv.sigmaCongrRight h x))
    (hphi : ∀ k z, phi k (Q.symm z) = Q.symm (Sum.map k.1 (fun w => ⟨w.1, k.2 w.1 w.2⟩) z))
    (h : ∀ v, Equiv.Perm (Fin (d v))) :
    Y h = ((Q.trans ((sigmaRelabel J sz d beta f).trans (sumSplitPos J sz)).symm).trans P.symm :
        Equiv.Perm (Fin a)) * phi (blockRelabel J sz d beta f h) *
      ((Q.trans ((sigmaRelabel J sz d beta f).trans (sumSplitPos J sz)).symm).trans P.symm :
        Equiv.Perm (Fin a))⁻¹ :=
  hom_conj_of_positions P Q ((sigmaRelabel J sz d beta f).trans (sumSplitPos J sz)) Y phi
    (blockRelabel J sz d beta f) (fun h x => Equiv.sigmaCongrRight h x)
    (fun k z => Sum.map k.1 (fun w => ⟨w.1, k.2 w.1 w.2⟩) z) hY hphi
    (fun h x => blockRelabel_conj J sz d beta f h x) h
end Relabel

section InducedRelabel
variable {H K G V : Type*} [Group H] [Group K] [Group G] [AddCommGroup V] [Module ℂ V]

/-- Induction along conjugate block homs, with the source pulled back along the
relabelling, is bijective. -/
def inducedRelabel (Y : H →* G) (phi : K →* G) (mu : H ≃* K) (s : G)
    (rho : Representation ℂ H V) (hphi : ∀ h, Y h = s * phi (mu h) * s⁻¹) :
    Representation.IntertwiningMap (Representation.ind Y rho)
      (Representation.ind phi (rho.comp mu.symm.toMonoidHom)) :=
  inducedConj phi Y mu s (rho.comp mu.symm.toMonoidHom) rho (LinearEquiv.refl ℂ V) hphi
    (fun h v => by
      change rho h v = rho (mu.symm (mu h)) v
      rw [MulEquiv.symm_apply_apply])

theorem inducedRelabel_bijective (Y : H →* G) (phi : K →* G) (mu : H ≃* K) (s : G)
    (rho : Representation ℂ H V) (hphi : ∀ h, Y h = s * phi (mu h) * s⁻¹) :
    Function.Bijective (inducedRelabel Y phi mu s rho hphi) :=
  inducedConj_bijective _ _ _ _ _ _ _ _ _
end InducedRelabel

end
end HSTZ

#print axioms HSTZ.piTensorMap_injective
#print axioms HSTZ.hom_conj_of_positions
#print axioms HSTZ.piRelabel_apply
#print axioms HSTZ.sumSplit_conj
#print axioms HSTZ.blockRelabel_conj
#print axioms HSTZ.blockHom_conj
#print axioms HSTZ.inducedRelabel_bijective
