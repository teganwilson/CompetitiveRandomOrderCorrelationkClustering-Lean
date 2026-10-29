module

public import RequestProject.LB3Core
public import RequestProject.LBProb

/-!
# Four indistinguishable vertices (proof of Theorem 3, second step)

In the proof of Theorem 3 the paper argues: "consider a time step at which exactly two large
cliques have not yet arrived.  For the remainder of the arrival pattern, the probability that
we receive exactly one vertex from each remaining large clique before we receive a second
vertex from either is at least `1/2`."  We formalize this with the exchangeability lemma: let
`t₁` be the first arrival of the second-to-last component, and `J` the positions after `t₁` of
the vertices of the last two components (except the one at `t₁`); re-shuffling the vertices at
`J`, the first of them belongs to the last component with probability `m/(2m-1) ≥ 1/2`, and then
at time `tstar` there are at least four isolated vertices (event `E''`).
-/

@[expose] public section

open Finset
open scoped Classical

namespace CCK

variable {c m : ℕ}

/-! ### Generalities on leaders -/

/-- Auxiliary result for the proof of Theorem 3. -/
lemma exists_leaders_L (hm : 1 ≤ m) {L : ℕ} (hL : L ≤ c + 2) (σ : Equiv.Perm (Fin (c * m + 2))) :
    ∃ t, L ≤ (leaders (view (lbGraph c m) σ t) t).card :=
  ⟨_, hL.trans (card_leaders_full hm σ)⟩

/-- Auxiliary result for the proof of Theorem 3. -/
lemma tstar_le_L (hm : 1 ≤ m) {L : ℕ} (hL : L ≤ c + 2) (σ : Equiv.Perm (Fin (c * m + 2))) :
    tstar (lbGraph c m) L σ ≤ c * m + 1 :=
  Nat.sInf_le (hL.trans (card_leaders_full hm σ))

/-- If all labels of `S` are hit by time `t`, there are at least `|S|` leaders by time `t`. -/
lemma card_le_card_leaders_of_hit (σ : Equiv.Perm (Fin (c * m + 2))) (t : ℕ) (S : Finset ℕ)
    (hS : ∀ x ∈ S, ∃ q : Fin (c * m + 2), (q : ℕ) ≤ t ∧ lbComp c m (σ q) = x) :
    S.card ≤ (leaders (view (lbGraph c m) σ t) t).card := by
  rw [leaders_lb]
  set F : ℕ → Finset (Fin (c * m + 2)) :=
    fun x => univ.filter (fun p => (p : ℕ) ≤ t ∧ lbComp c m (σ p) = x)
  have hne : ∀ x ∈ S, (F x).Nonempty := by
    intro x hx
    obtain ⟨q, hq, hqx⟩ := hS x hx
    exact ⟨q, by simp [F, hq, hqx]⟩
  set g : ℕ → Fin (c * m + 2) := fun x => if h : (F x).Nonempty then (F x).min' h else 0
  have hg : ∀ x ∈ S, (g x : ℕ) ≤ t ∧ lbComp c m (σ (g x)) = x ∧ IsFirst c m σ (g x) := by
    intro x hx
    simp only [g, dif_pos (hne x hx)]
    have hmem := min'_mem (F x) (hne x hx)
    simp only [F, mem_filter, mem_univ, true_and] at hmem
    refine ⟨hmem.1, hmem.2, fun q hq he => ?_⟩
    have : q ∈ F x := by
      simp only [F, mem_filter, mem_univ, true_and]
      exact ⟨le_trans (le_of_lt (Fin.lt_def.1 hq)) hmem.1, he.trans hmem.2⟩
    exact absurd (min'_le _ _ this) (not_le.2 hq)
  exact card_le_card_of_injOn g
    (fun x hx => by
      simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq]
      exact ⟨(hg x hx).1, (hg x hx).2.2⟩)
    (fun x hx y hy h => by rw [← (hg x hx).2.1, ← (hg y hy).2.1, h])

/-- If the labels of `M` are not hit by time `t`, there are at most `c + 2 - |M|` leaders. -/
lemma card_leaders_le_of_missing (hm : 1 ≤ m) (σ : Equiv.Perm (Fin (c * m + 2))) (t : ℕ)
    (M : Finset ℕ) (hM : M ⊆ range (c + 2))
    (hmiss : ∀ p : Fin (c * m + 2), (p : ℕ) ≤ t → lbComp c m (σ p) ∉ M) :
    (leaders (view (lbGraph c m) σ t) t).card ≤ c + 2 - M.card := by
  rw [leaders_lb]
  have := card_le_card_of_injOn (fun p => lbComp c m (σ p))
    (s := univ.filter (fun p : Fin (c * m + 2) => (p : ℕ) ≤ t ∧ IsFirst c m σ p))
    (t := range (c + 2) \ M)
    (by
      intro p hp
      simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hp
      simp only [coe_sdiff, coe_range, Set.mem_diff, Set.mem_Iio, mem_coe]
      exact ⟨lbComp_lt hm _, hmiss p hp.1⟩)
    (by
      intro p hp q hq hpq
      simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hp hq
      by_contra h
      exact isFirst_comp_ne hp.2 hq.2 h hpq)
  rw [card_sdiff_of_subset hM, card_range] at this
  exact this

/-- The position `tstar L` is the first arrival of its component. -/
lemma isFirst_tstar (hm : 1 ≤ m) {L : ℕ} (hL : L ≤ c + 2)
    (σ : Equiv.Perm (Fin (c * m + 2))) :
    IsFirst c m σ ⟨tstar (lbGraph c m) L σ, by have := tstar_le_L hm hL σ; omega⟩ := by
  set ts := tstar (lbGraph c m) L σ with hts
  intro q hq
  have hq' : (q : ℕ) < ts := hq
  by_contra hc
  have hspec := tstar_spec (lbGraph c m) L σ (exists_leaders_L hm hL σ)
  rw [← hts] at hspec
  have hlt := lt_of_lt_tstar (lbGraph c m) L σ (t := ts - 1) (by omega)
  rw [leaders_lb] at hspec hlt
  have hsub : univ.filter (fun p : Fin (c * m + 2) => (p : ℕ) ≤ ts ∧ IsFirst c m σ p) ⊆
      univ.filter (fun p : Fin (c * m + 2) => (p : ℕ) ≤ ts - 1 ∧ IsFirst c m σ p) := by
    intro p hp
    simp only [mem_filter, mem_univ, true_and] at hp ⊢
    refine ⟨?_, hp.2⟩
    by_contra h
    have hpts : (p : ℕ) = ts := by omega
    exact hp.2 q (Fin.lt_def.2 (by omega)) (by
      have : p = ⟨ts, by have := tstar_le_L hm hL σ; omega⟩ := Fin.ext hpts
      rw [this]; exact hc)
  have := card_le_card hsub
  omega

/-- At most `L` leaders at time `tstar L`. -/
lemma card_leaders_tstar_le (hm : 1 ≤ m) {L : ℕ} (hL1 : 1 ≤ L) (hL : L ≤ c + 2)
    (σ : Equiv.Perm (Fin (c * m + 2))) :
    (leaders (view (lbGraph c m) σ (tstar (lbGraph c m) L σ)) (tstar (lbGraph c m) L σ)).card
      ≤ L := by
  set ts := tstar (lbGraph c m) L σ with hts
  rw [leaders_lb]
  have hle := tstar_le_L hm hL σ
  rw [← hts] at hle
  set pt : Fin (c * m + 2) := ⟨ts, by omega⟩
  have hsub : univ.filter (fun p : Fin (c * m + 2) => (p : ℕ) ≤ ts ∧ IsFirst c m σ p) ⊆
      insert pt (univ.filter (fun p : Fin (c * m + 2) => (p : ℕ) ≤ ts - 1 ∧
        IsFirst c m σ p)) := by
    intro p hp
    simp only [mem_filter, mem_univ, true_and, mem_insert] at hp ⊢
    by_cases h : (p : ℕ) = ts
    · left; exact Fin.ext h
    · right; exact ⟨by omega, hp.2⟩
  have h1 := (card_le_card hsub).trans (card_insert_le _ _)
  by_cases h0 : ts = 0
  · have : univ.filter (fun p : Fin (c * m + 2) => (p : ℕ) ≤ ts - 1 ∧ IsFirst c m σ p) ⊆
        {pt} := by
      intro p hp
      simp only [mem_filter, mem_univ, true_and] at hp
      simp only [mem_singleton]
      exact Fin.ext (by simp [pt]; omega)
    have := card_le_card this
    rw [card_singleton] at this
    have hsub' : univ.filter (fun p : Fin (c * m + 2) => (p : ℕ) ≤ ts ∧ IsFirst c m σ p) ⊆
        {pt} := by
      intro p hp
      simp only [mem_filter, mem_univ, true_and] at hp
      simp only [mem_singleton]
      exact Fin.ext (by simp [pt]; omega)
    have := card_le_card hsub'
    rw [card_singleton] at this
    omega
  · have hlt := lt_of_lt_tstar (lbGraph c m) L σ (t := ts - 1) (by omega)
    rw [leaders_lb] at hlt
    omega

/-! ### The second-to-last component -/

/-- `t₁`: the first arrival time of the second-to-last component. -/
noncomputable def lbT1 (c m : ℕ) (σ : Equiv.Perm (Fin (c * m + 2))) : ℕ :=
  tstar (lbGraph c m) (c + 1) σ

/-- The position `t₁` as an element of `Fin n`. -/
noncomputable def lbT1pos (c m : ℕ) (σ : Equiv.Perm (Fin (c * m + 2))) : Fin (c * m + 2) :=
  ⟨min (lbT1 c m σ) (c * m + 1), by omega⟩

/-- Auxiliary result for the proof of Theorem 3. -/
lemma lbT1pos_val (hm : 1 ≤ m) (σ : Equiv.Perm (Fin (c * m + 2))) :
    (lbT1pos c m σ : ℕ) = lbT1 c m σ := by
  have := tstar_le_L hm (L := c + 1) (by omega) σ
  simp [lbT1pos, lbT1] at this ⊢
  omega

/-- The label `x` has no vertex arrived by time `t₁`. -/
def Unhit (c m : ℕ) (σ : Equiv.Perm (Fin (c * m + 2))) (x : ℕ) : Prop :=
  ∀ q : Fin (c * m + 2), (q : ℕ) ≤ lbT1 c m σ → lbComp c m (σ q) ≠ x

/-- The positions after `t₁` of the vertices of the last two components. -/
noncomputable def lbJ (c m : ℕ) (σ : Equiv.Perm (Fin (c * m + 2))) : Finset (Fin (c * m + 2)) :=
  univ.filter (fun p => lbT1 c m σ < p ∧
    (lbComp c m (σ p) = lbComp c m (σ (lbT1pos c m σ)) ∨ Unhit c m σ (lbComp c m (σ p))))

/-- The event `W`: the first vertex arriving after `t₁` from the last two components belongs to
the last component. -/
def lbW (c m : ℕ) (σ : Equiv.Perm (Fin (c * m + 2))) : Prop :=
  ∃ p ∈ lbJ c m σ, (∀ p' ∈ lbJ c m σ, p ≤ p') ∧ Unhit c m σ (lbComp c m (σ p))

/-- The event of Theorem 3 at time `T`: both singletons arrive by `T` and at least two cliques
have no vertex arrived by `T`. -/
def lbEvent3 (c m T : ℕ) (σ : Equiv.Perm (Fin (c * m + 2))) : Prop :=
  lbS1 c m ∈ firstSet σ T ∧ lbS2 c m ∈ firstSet σ T ∧
    ∃ j₁ < c, ∃ j₂ < c, j₁ ≠ j₂ ∧ Disjoint (firstSet σ T) (lbClique c m j₁) ∧
      Disjoint (firstSet σ T) (lbClique c m j₂)

/-- Auxiliary result for the proof of Theorem 3. -/
lemma mem_firstSet_iff {n : ℕ} {σ : Equiv.Perm (Fin n)} {T : ℕ} {v : Fin n} :
    v ∈ firstSet σ T ↔ (σ.symm v : ℕ) < T := by
  simp [firstSet, arrTime]

/-- On the event of Theorem 3, `T ≤ t₁`. -/
lemma le_lbT1 (hm : 1 ≤ m) {T : ℕ} {σ : Equiv.Perm (Fin (c * m + 2))}
    (hE : lbEvent3 c m T σ) : T ≤ lbT1 c m σ := by
  obtain ⟨-, -, j₁, hj₁, j₂, hj₂, hne, hd1, hd2⟩ := hE
  by_contra hlt
  push_neg at hlt
  have h := tstar_spec (lbGraph c m) (c + 1) σ (exists_leaders_L hm (by omega) σ)
  have := card_leaders_le_of_missing hm σ (lbT1 c m σ) {j₁, j₂}
    (by intro x hx; simp only [mem_insert, mem_singleton] at hx; rcases hx with rfl | rfl <;>
          simp <;> omega)
    (by
      intro p hp hmem
      have hpT : σ p ∈ firstSet σ T := by
        rw [mem_firstSet_iff, Equiv.symm_apply_apply]; omega
      simp only [mem_insert, mem_singleton] at hmem
      rcases hmem with h | h
      · exact disjoint_left.1 hd1 hpT (by simp [lbClique, h])
      · exact disjoint_left.1 hd2 hpT (by simp [lbClique, h]))
  rw [card_pair hne] at this
  unfold lbT1 at this
  omega

end CCK
