import HSTZ.WitnessBalancePackingAssemblyH
import HSTZ.WitnessBalanceFrontier
import OAI.RepresentationTheory.Saxl.DominatedSupport

import OAI.RepresentationTheory.Saxl.YoungRule

import OAI.RepresentationTheory.Saxl.SignEquivalence

/-! Ordered strip chains for the original, unsorted packing; no representation
support is assumed. Reuses OpenAI's `math` repository (commit adc7f1241, Apache-2.0).
Private list arithmetic uses the existing corner/`stripRemove` interfaces. A global
compatible constituent is a separate matter, not proved here. -/
namespace HSTZ
noncomputable section
open OAI.Saxl

private theorem selected_excess {xs bs : List ℕ} (hs : xs.Sublist bs) (t : ℕ) :
    xs.sum ≤ xs.length*t + (bs.map (fun a => a-t)).sum := by
  induction hs with
  | slnil => simp
  | cons a hs ih =>
    simp only [List.map_cons,List.sum_cons]
    omega
  | cons_cons a hs ih =>
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    have ha : a ≤ t+(a-t) := by omega
    nlinarith

private theorem excess_identity (bs : List ℕ) (t : ℕ) :
    youngPrefix bs t + (bs.map (fun a => a-t)).sum = bs.sum := by
  induction bs with
  | nil => simp [youngPrefix]
  | cons a bs ih =>
    simp only [youngPrefix,List.map_cons,List.sum_cons] at ih ⊢
    have ha : min t a+(a-t)=a := by omega
    omega

private theorem prefix_sublist (mu : YoungDiagram) (bs : List ℕ)
    (hc : bs.sum=mu.card) (hp : ∀ j, prefixSum mu.colLen j≤youngPrefix bs j) :
    ∀ xs : List ℕ, xs.Sublist bs → xs.sum≤rowPrefix mu xs.length := by
  intro xs hs
  let t := mu.rowLen xs.length
  have he : prefixSum mu.colLen t + rowPrefix mu xs.length = mu.card+t*xs.length := by
    simpa only [rowPrefix,prefixSum,YoungDiagram.rowLen_transpose,
      YoungDiagram.colLen_transpose,YoungDiagram.transpose_transpose,transpose_card,t,Nat.add_comm]
      using corner_equality mu.transpose xs.length
  have hi := excess_identity bs t
  have hb := selected_excess hs t
  have hh := hp t
  rw [hc] at hi
  nlinarith

private theorem ordered_chain (bs : List ℕ) (mu : YoungDiagram)
    (hc : bs.sum=mu.card)
    (hd : ∀ xs : List ℕ, xs.Sublist bs → xs.sum≤rowPrefix mu xs.length) :
    SizedStripChain bs ⊥ mu := by
  induction bs using List.reverseRecOn generalizing mu with
  | nil =>
    have hz : mu.card=0 := by simpa using hc.symm
    have hm := (card_zero_iff_bot mu).mp hz
    subst mu
    exact SizedStripChain.nil ⊥
  | append_singleton bs a ih =>
    have hw : a≤ mu.rowLen 0 := by
      have hh := hd [a] ((List.nil_sublist bs).append (List.Sublist.refl [a]))
      simpa [rowPrefix] using hh
    have hrem := stripRemove_card mu a
    rw [min_eq_left hw] at hrem
    have hsum : bs.sum+a=mu.card := by simpa using hc
    have hc' : bs.sum=(stripRemove mu a).card := by omega
    have hd' : ∀ xs : List ℕ, xs.Sublist bs →
        xs.sum≤rowPrefix (stripRemove mu a) xs.length := by
      intro xs hs
      have hh := hd xs (by simpa using hs.append (List.nil_sublist [a]))
      have ha := hd (xs++[a]) (hs.append (List.Sublist.refl [a]))
      simp only [List.sum_append,List.sum_cons,List.sum_nil,Nat.add_zero,
        List.length_append,List.length_singleton] at ha
      have he := stripRemove_prefix mu a xs.length
      rw [min_eq_left hw] at he
      have hn := rowPrefix_succ mu xs.length
      by_cases hrow : a≤ mu.rowLen xs.length
      · rw [min_eq_left hrow] at he
        omega
      · rw [min_eq_right (by omega : mu.rowLen xs.length≤a)] at he
        omega
    exact SizedStripChain.snoc (ih _ hc' hd') (stripRemove_horizontal mu a) hrem

/-- The unsorted `balancePacking` admits the required ordered strip chain. -/
theorem paperWitness_balance_ordered_stripChain (k b delta : ℕ)
    (hp : PaperWitnessGuard k b delta) {n : ℕ} {mu : YoungDiagram}
    (z : Tableau n (witnessDiagram k b delta hp.staircase_bound)) (s : Tableau n mu)
    (hprefix : ∀ j, prefixSum mu.colLen j≤youngPrefix (balancePacking k b delta) j) :
    SizedStripChain (balancePacking k b delta) ⊥ mu := by
  have hz : (witnessDiagram k b delta hp.staircase_bound).card=n := by
    simpa using (Fintype.card_congr z).symm
  rw [witnessDiagram_card] at hz
  have hs : mu.card=n := by simpa using (Fintype.card_congr s).symm
  have hdiv := Nat.div_mul_cancel (Nat.two_dvd_mul_add_one k)
  have hn : 2*mu.card=k*(k+1)+2*(2*b+delta) := by omega
  have hc := (balancePacking_properties (k:=k) (b:=b) (delta:=delta)
    (r:=2*b+delta) (n:=mu.card) (by have hh:=hp.staircase_bound; omega)
    hp.parity rfl hp.remainder_bound hn).1
  exact ordered_chain _ _ hc (prefix_sublist _ _ hc hprefix)

/-- Target restriction with the original ordered part counts and full color covariance.
This is an onto/nonzero map to the empty Specht module, not the projected H-source support. -/
theorem paperWitness_balance_ordered_restriction (k b delta : ℕ)
    (hp : PaperWitnessGuard k b delta) {n : ℕ} {mu : YoungDiagram}
    (z : Tableau n (witnessDiagram k b delta hp.staircase_bound)) (s : Tableau n mu)
    (hprefix : ∀ j, prefixSum mu.colLen j≤youngPrefix (balancePacking k b delta) j) :
    ∃ (c : Fin n → ℕ) (F : Specht s →ₗ[ℂ] Specht (shapeTableau ⊥)),
      Function.Surjective F ∧ F≠0 ∧
      (∀ i, 1≤c i ∧ c i≤(balancePacking k b delta).length) ∧
      (∀ j (hj : j<(balancePacking k b delta).length),
        (Finset.univ.filter (fun i => c i=j+1)).card=(balancePacking k b delta)[j]) ∧
      (∀ g : Equiv.Perm (Fin n), (∀ i, c (g i)=c i) →
        ∀ x, F (spechtRep s g x)=F x) := by
  classical
  let hs := paperWitness_balance_ordered_stripChain k b delta hp z s hprefix
  obtain ⟨c,F,hF,hc,hzero,hcount,he⟩ :=
    stripChain_restriction_any hs (shapeTableau ⊥) s
  have hpos (i) : 1≤c i := by
    have hn : c i≠0 := by
      intro hh
      obtain ⟨j,hj⟩ := (hzero i).mp hh
      exact Fin.elim0 j
    omega
  let v : Specht (shapeTableau ⊥) := ⟨polytabloid (shapeTableau ⊥),mem_cyclic _ _⟩
  have hv : v≠0 := by
    intro hh
    exact polytabloid_ne_zero _ (congrArg Subtype.val hh)
  have hne : F≠0 := by
    intro hh
    obtain ⟨x,hx⟩ := hF v
    apply hv
    exact hx.symm.trans (by simpa using LinearMap.congr_fun hh x)
  refine ⟨c,F,hF,hne,fun i => ⟨hpos i,hc i⟩,hcount,?_⟩
  intro g hg x
  simpa using he g 1 hg (fun j => Fin.elim0 j) x

/-- The target occurs on a word whose content is the unsorted packing.
This is word-orbit support, not support in the physical projected H-source. -/
theorem paperWitness_balance_ordered_word_map (k b delta : ℕ)
    (hp : PaperWitnessGuard k b delta) {n : ℕ} {mu : YoungDiagram}
    (z : Tableau n (witnessDiagram k b delta hp.staircase_bound)) (s : Tableau n mu)
    (hprefix : ∀ j, prefixSum mu.colLen j≤youngPrefix (balancePacking k b delta) j) :
    ∃ (a : Fin n → Fin (balancePacking k b delta).length)
      (J : (wordRep n (balancePacking k b delta).length).IntertwiningMap (spechtRep s)),
      (∀ j : Fin (balancePacking k b delta).length,
        (Finset.univ.filter (fun i => a i=j)).card=(balancePacking k b delta)[j.val]) ∧
      J (Pi.single (M:=fun _ => ℂ) a 1)≠0 := by
  classical
  obtain ⟨c,F,hF,hne,hc,hcount,he⟩ := paperWitness_balance_ordered_restriction k b delta hp z s hprefix
  let a : Fin n → Fin (balancePacking k b delta).length :=
    fun i => ⟨c i-1,by have hh:=hc i; omega⟩
  let L : Specht (shapeTableau ⊥) →ₗ[ℂ] ℂ :=
    { toFun := fun x => x.val (rowWord (shapeTableau ⊥))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hL : L≠0 := by
    intro hh
    have hv := LinearMap.congr_fun hh
      (⟨polytabloid (shapeTableau ⊥),mem_cyclic _ _⟩ : Specht (shapeTableau ⊥))
    change polytabloid (shapeTableau ⊥) (rowWord (shapeTableau ⊥))=0 at hv
    rw [polytabloid_rowWord] at hv
    norm_num at hv
  let l : Module.Dual ℂ (Specht s) := L.comp F
  have hl : l≠0 := by
    intro hh
    apply hL
    apply LinearMap.ext
    intro x
    obtain ⟨y,rfl⟩ := hF x
    exact LinearMap.congr_fun hh y
  have hinv : ∀ g : Equiv.Perm (Fin n), a ∘ g=a →
      ∀ x, l (spechtRep s g x)=l x := by
    intro g hg x
    have hcol (i) : c (g i)=c i := by
      have hv := congrArg Fin.val (congrFun hg i)
      change c (g i)-1=c i-1 at hv
      have h1 := (hc (g i)).1
      have h2 := (hc i).1
      omega
    change L (F (spechtRep s g x))=L (F x)
    rw [he g hcol x]
  obtain ⟨y,hy,hyinv⟩ := vector_of_invariant_functional s a l hl hinv
  let J := orbitAverage (spechtRep s) a y
  refine ⟨a,J,?_,?_⟩
  · intro j
    rw [← hcount j.val j.isLt]
    congr 1
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Fin.ext_iff]
    change c i-1=j.val ↔ c i=j.val+1
    have hp := (hc i).1
    omega
  · rw [show J (Pi.single (M:=fun _ => ℂ) a 1)=_ from orbitAverage_base (spechtRep s) a y hyinv]
    apply smul_ne_zero _ hy
    apply Nat.cast_ne_zero.mpr
    exact Finset.card_ne_zero.mpr ⟨1,by simp⟩

end
end HSTZ
#print axioms HSTZ.paperWitness_balance_ordered_stripChain

#print axioms HSTZ.paperWitness_balance_ordered_restriction

#print axioms HSTZ.paperWitness_balance_ordered_word_map
