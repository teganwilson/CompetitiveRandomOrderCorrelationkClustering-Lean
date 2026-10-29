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


/-!
# Four indistinguishable vertices, continued (proof of Theorem 3)

Invariance of `t₁`, `J` and the event of Theorem 3 under re-shuffling the vertices at `J`, and
the per-order counting bound `P(W) ≥ 1/2`.
-/

@[expose] public section

open Finset
open scoped Classical

namespace CCK

variable {c m : ℕ}

/-- Auxiliary result for the proof of Theorem 3. -/
lemma card_leaders_lbT1 (hm : 1 ≤ m) (σ : Equiv.Perm (Fin (c * m + 2))) :
    (leaders (view (lbGraph c m) σ (lbT1 c m σ)) (lbT1 c m σ)).card = c + 1 :=
  le_antisymm (card_leaders_tstar_le hm (by omega) (by omega) σ)
    (tstar_spec (lbGraph c m) (c + 1) σ (exists_leaders_L hm (by omega) σ))

/-- Exactly one label is not hit by time `t₁` (the last component). -/
lemma exists_unique_unhit (hm : 1 ≤ m) (σ : Equiv.Perm (Fin (c * m + 2))) :
    ∃ x < c + 2, Unhit c m σ x ∧ ∀ y < c + 2, Unhit c m σ y → y = x := by
  have hcard := card_leaders_lbT1 hm σ
  have hex : ∃ x < c + 2, Unhit c m σ x := by
    by_contra h
    push_neg at h
    have := card_le_card_leaders_of_hit σ (lbT1 c m σ) (range (c + 2)) (by
      intro x hx
      have := h x (mem_range.1 hx)
      simp only [Unhit, not_forall, not_not] at this
      obtain ⟨q, hq, hqx⟩ := this
      exact ⟨q, hq, hqx⟩)
    rw [card_range] at this
    omega
  obtain ⟨x, hx, hux⟩ := hex
  refine ⟨x, hx, hux, fun y hy huy => ?_⟩
  by_contra hne
  have := card_leaders_le_of_missing hm σ (lbT1 c m σ) {y, x}
    (by intro z hz; simp only [mem_insert, mem_singleton] at hz
        rcases hz with rfl | rfl <;> simpa)
    (by
      intro p hp hmem
      simp only [mem_insert, mem_singleton] at hmem
      rcases hmem with h | h
      · exact huy p hp h
      · exact hux p hp h)
  rw [card_pair hne] at this
  omega

section invariance

variable (hm : 1 ≤ m) (σ ρ : Equiv.Perm (Fin (c * m + 2))) (hρ : ρ ∈ fixOutside (lbJ c m σ))
include hρ

/-- Auxiliary result for the proof of Theorem 3. -/
lemma mul_apply_of_le_lbT1 {p : Fin (c * m + 2)} (hp : (p : ℕ) ≤ lbT1 c m σ) :
    (σ * ρ) p = σ p := by
  have : p ∉ lbJ c m σ := by
    simp only [lbJ, mem_filter, mem_univ, true_and, not_and]
    intro h; exact absurd hp (not_le.2 h)
  rw [Equiv.Perm.mul_apply, (fixOutside_mem_iff.1 hρ) p this]

/-- Auxiliary result for the proof of Theorem 3. -/
lemma leaders_mul_of_le_lbT1 {t : ℕ} (ht : t ≤ lbT1 c m σ) :
    leaders (view (lbGraph c m) (σ * ρ) t) t = leaders (view (lbGraph c m) σ t) t := by
  rw [leaders_lb, leaders_lb]
  apply filter_congr
  intro p _
  apply and_congr_right
  intro hp
  have hagree : ∀ q : Fin (c * m + 2), q ≤ p → (σ * ρ) q = σ q :=
    fun q hq => mul_apply_of_le_lbT1 σ ρ hρ (le_trans (Fin.le_def.1 hq) (hp.trans ht))
  unfold IsFirst
  constructor
  · intro h q hq
    rw [← hagree q hq.le, ← hagree p le_rfl]; exact h q hq
  · intro h q hq
    rw [hagree q hq.le, hagree p le_rfl]; exact h q hq

include hm in
/-- Auxiliary result for the proof of Theorem 3. -/
lemma lbT1_mul : lbT1 c m (σ * ρ) = lbT1 c m σ := by
  have hex := exists_leaders_L hm (L := c + 1) (by omega) σ
  apply le_antisymm
  · apply Nat.sInf_le
    show c + 1 ≤ (leaders (view (lbGraph c m) (σ * ρ) (lbT1 c m σ)) (lbT1 c m σ)).card
    rw [leaders_mul_of_le_lbT1 σ ρ hρ le_rfl]
    exact tstar_spec (lbGraph c m) (c + 1) σ hex
  · apply le_csInf (exists_leaders_L hm (L := c + 1) (by omega) (σ * ρ))
    intro t ht
    by_contra hlt
    push_neg at hlt
    have := lt_of_lt_tstar (lbGraph c m) (c + 1) σ hlt
    change c + 1 ≤ (leaders (view (lbGraph c m) (σ * ρ) t) t).card at ht
    rw [leaders_mul_of_le_lbT1 σ ρ hρ (le_of_lt hlt)] at ht
    omega

include hm in
/-- Auxiliary result for the proof of Theorem 3. -/
lemma lbT1pos_mul : lbT1pos c m (σ * ρ) = lbT1pos c m σ := by
  simp only [lbT1pos, lbT1_mul hm σ ρ hρ]

include hm in
/-- Auxiliary result for the proof of Theorem 3. -/
lemma unhit_mul (x : ℕ) : Unhit c m (σ * ρ) x ↔ Unhit c m σ x := by
  simp only [Unhit, lbT1_mul hm σ ρ hρ]
  constructor
  · intro h q hq; rw [← mul_apply_of_le_lbT1 σ ρ hρ hq]; exact h q hq
  · intro h q hq; rw [mul_apply_of_le_lbT1 σ ρ hρ hq]; exact h q hq

include hm in
/-- Auxiliary result for the proof of Theorem 3. -/
lemma lbJ_mul : lbJ c m (σ * ρ) = lbJ c m σ := by
  have hpos : (σ * ρ) (lbT1pos c m σ) = σ (lbT1pos c m σ) :=
    mul_apply_of_le_lbT1 σ ρ hρ (by rw [lbT1pos_val hm])
  ext p
  simp only [lbJ, mem_filter, mem_univ, true_and, lbT1_mul hm σ ρ hρ, lbT1pos_mul hm σ ρ hρ,
    hpos, unhit_mul hm σ ρ hρ]
  rw [Equiv.Perm.mul_apply]
  by_cases hpJ : p ∈ lbJ c m σ
  · have hρp := fixOutside_apply_mem hρ hpJ
    simp only [lbJ, mem_filter, mem_univ, true_and] at hpJ hρp
    exact ⟨fun _ => hpJ, fun _ => ⟨hpJ.1, hρp.2⟩⟩
  · rw [(fixOutside_mem_iff.1 hρ) p hpJ]

/-- Auxiliary result for the proof of Theorem 3. -/
lemma firstSet_mul {T : ℕ} (hT : T ≤ lbT1 c m σ) : firstSet (σ * ρ) T = firstSet σ T := by
  ext v
  rw [mem_firstSet_iff, mem_firstSet_iff]
  constructor
  · intro h
    have := mul_apply_of_le_lbT1 σ ρ hρ (p := (σ * ρ).symm v) (by omega)
    rw [Equiv.apply_symm_apply] at this
    rw [this, Equiv.symm_apply_apply]; exact h
  · intro h
    have := mul_apply_of_le_lbT1 σ ρ hρ (p := σ.symm v) (by omega)
    rw [Equiv.apply_symm_apply] at this
    rw [← this, Equiv.symm_apply_apply]; exact h

end invariance

/-- On the event of Theorem 3, the unique label not hit by `t₁` is a clique. -/
lemma unhit_lt (hm : 1 ≤ m) {T : ℕ} {σ : Equiv.Perm (Fin (c * m + 2))}
    (hE : lbEvent3 c m T σ) {x : ℕ} (hx : x < c + 2) (hux : Unhit c m σ x) : x < c := by
  have hT := le_lbT1 hm hE
  by_contra hc
  push_neg at hc
  have hs : ∀ s, s ∈ firstSet σ T → lbComp c m s ≠ x := by
    intro s hs
    rw [mem_firstSet_iff] at hs
    have := hux (σ.symm s) (by omega)
    rwa [Equiv.apply_symm_apply] at this
  rcases (show x = c ∨ x = c + 1 by omega) with rfl | rfl
  · exact hs _ hE.1 lbComp_s1
  · exact hs _ hE.2.1 lbComp_s2

/-- On the event of Theorem 3, the vertex arriving at `t₁` belongs to a clique. -/
lemma lbComp_lbT1pos_lt (hm : 1 ≤ m) {T : ℕ} {σ : Equiv.Perm (Fin (c * m + 2))}
    (hE : lbEvent3 c m T σ) : lbComp c m (σ (lbT1pos c m σ)) < c := by
  have hT := le_lbT1 hm hE
  by_contra hc
  push_neg at hc
  have hv : (lbT1pos c m σ : ℕ) = lbT1 c m σ := lbT1pos_val hm σ
  rcases eq_s1_or_s2 hm hc with h | h
  · have := mem_firstSet_iff.1 hE.1
    rw [← h, Equiv.symm_apply_apply] at this; omega
  · have := mem_firstSet_iff.1 hE.2.1
    rw [← h, Equiv.symm_apply_apply] at this; omega

/-- Per-order bound: for each order in the event of Theorem 3, at least half of the
re-shufflings of `J` satisfy `W`. -/
lemma half_W (hm : 1 ≤ m) {T : ℕ} (σ : Equiv.Perm (Fin (c * m + 2))) (hE : lbEvent3 c m T σ) :
    (1 / 2 : ℝ) * (fixOutside (lbJ c m σ)).card ≤
      ((fixOutside (lbJ c m σ)).filter (fun ρ => lbW c m (σ * ρ))).card := by
  set J := lbJ c m σ
  set H := fixOutside J
  obtain ⟨x, hx, hux, -⟩ := exists_unique_unhit hm σ
  have hxc := unhit_lt hm hE hx hux
  set Q := J.filter (fun p => Unhit c m σ (lbComp c m (σ p)))
  -- the positions of the last clique lie in `Q`
  have hQm : m ≤ Q.card := by
    have h1 := card_lbClique hm hxc
    have h2 : ((lbClique c m x).map σ.symm.toEmbedding).card ≤ Q.card := by
      apply card_le_card
      intro p hp
      obtain ⟨v, hv, rfl⟩ := mem_map.1 hp
      simp only [lbClique, mem_filter, mem_univ, true_and] at hv
      simp only [Equiv.coe_toEmbedding, Q, J, lbJ, mem_filter, mem_univ, true_and,
        Equiv.apply_symm_apply, hv]
      refine ⟨⟨?_, Or.inr hux⟩, hux⟩
      by_contra hle
      push_neg at hle
      exact hux _ hle (by rw [Equiv.apply_symm_apply, hv])
    rw [card_map] at h2
    omega
  have hJQ : (J \ Q).card + 1 ≤ m := by
    set C := lbComp c m (σ (lbT1pos c m σ))
    have hC := lbComp_lbT1pos_lt hm hE
    have h1 : (lbClique c m C).card = m := card_lbClique hm hC
    have hsub : (J \ Q).map σ.toEmbedding ⊆ (lbClique c m C).erase (σ (lbT1pos c m σ)) := by
      intro v hv
      obtain ⟨p, hp, rfl⟩ := mem_map.1 hv
      simp only [Q, J, lbJ, mem_sdiff, mem_filter, mem_univ, true_and, not_and] at hp
      simp only [Equiv.coe_toEmbedding, mem_erase, lbClique, mem_filter, mem_univ, true_and]
      have hpC : lbComp c m (σ p) = C := by
        rcases hp.1.2 with h | h
        · exact h
        · exact absurd h (hp.2 hp.1)
      refine ⟨fun h => ?_, hpC⟩
      have := σ.injective h
      have h1 := hp.1.1
      rw [this, lbT1pos_val hm] at h1
      exact lt_irrefl _ h1
    have := card_le_card hsub
    rw [card_map, card_erase_of_mem (by simp [lbClique, C])] at this
    omega
  have hQJ : Q ⊆ J := filter_subset _ _
  have hJne : J.Nonempty := by
    obtain ⟨p, hp⟩ : Q.Nonempty := card_pos.1 (by omega)
    exact ⟨p, hQJ hp⟩
  set p₀ := J.min' hJne
  have hp₀ : p₀ ∈ J := min'_mem J hJne
  have hpt := card_fixOutside_point J hp₀ Q hQJ
  -- `W (σ ρ)` iff `ρ p₀ ∈ Q`
  have hsub : H.filter (fun ρ => ρ p₀ ∈ Q) ⊆ H.filter (fun ρ => lbW c m (σ * ρ)) := by
    intro ρ hρ
    simp only [mem_filter] at hρ ⊢
    refine ⟨hρ.1, ?_⟩
    unfold lbW
    rw [lbJ_mul hm σ ρ hρ.1]
    refine ⟨p₀, hp₀, fun p' hp' => min'_le _ _ hp', ?_⟩
    rw [unhit_mul hm σ ρ hρ.1, Equiv.Perm.mul_apply]
    exact (mem_filter.1 hρ.2).2
  have hFc := card_le_card hsub
  have hJcard : J.card = Q.card + (J \ Q).card := by
    rw [card_sdiff_of_subset hQJ]; have := card_le_card hQJ; omega
  have hJpos : (0 : ℝ) < J.card := by exact_mod_cast card_pos.2 hJne
  have hpt' : ((H.filter (fun ρ => ρ p₀ ∈ Q)).card : ℝ) * J.card = Q.card * H.card := by
    exact_mod_cast hpt
  have hJQ' : (J.card : ℝ) ≤ 2 * Q.card := by
    have : J.card ≤ 2 * Q.card := by omega
    exact_mod_cast this
  have hF' : ((H.filter (fun ρ => ρ p₀ ∈ Q)).card : ℝ) ≤
      (H.filter (fun ρ => lbW c m (σ * ρ))).card := by exact_mod_cast hFc
  have hH0 : (0 : ℝ) ≤ H.card := Nat.cast_nonneg _
  have key : (1 / 2 : ℝ) * H.card * J.card ≤
      ((H.filter (fun ρ => ρ p₀ ∈ Q)).card : ℝ) * J.card := by
    rw [hpt']; nlinarith
  have := le_of_mul_le_mul_right key hJpos
  linarith

end CCK
