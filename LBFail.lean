module

public import RequestProject.LBInstance

/-!
# Indistinguishability on the lower-bound instance (Section 5)

Combinatorial core of the proofs of Theorem 2 and Theorem 3.  On the instance of Section 5, let
`tstar` be the time at which the last of the `c + 2` components receives its first vertex.  At
that time the `c + 2` components occupy at most `k = c + 1` clusters, so two of them share a
cluster.  The algorithm cannot distinguish the vertices without arrived neighbours (the two
singletons and the first vertex of a clique which has a single arrived vertex), and an
exchangeability argument shows that it fails with constant probability.
-/

@[expose] public section

open Finset
open scoped Classical

namespace CCK

variable {c m : ℕ}

/-- `p` is the first arrival of its component. -/
def IsFirst (c m : ℕ) (σ : Equiv.Perm (Fin (c * m + 2))) (p : Fin (c * m + 2)) : Prop :=
  ∀ q, q < p → lbComp c m (σ q) ≠ lbComp c m (σ p)

/-- Auxiliary result for the lower-bound construction of Section 5 (proof of Theorem 2). -/
lemma leaders_lb (σ : Equiv.Perm (Fin (c * m + 2))) (t : ℕ) :
    leaders (view (lbGraph c m) σ t) t =
      univ.filter (fun p : Fin (c * m + 2) => (p : ℕ) ≤ t ∧ IsFirst c m σ p) := by
  ext p
  simp only [leaders, view, lbGraph, cliqueGraph, IsFirst, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨hp, h⟩
    refine ⟨hp, fun q hq hc => h q hq ⟨le_trans (le_of_lt hq) hp, hp, ?_, hc⟩⟩
    intro he; exact (ne_of_lt hq) (σ.injective he)
  · rintro ⟨hp, h⟩
    exact ⟨hp, fun q hq ⟨_, _, _, hc⟩ => h q hq hc⟩

/-- Auxiliary result for the lower-bound construction of Section 5 (proof of Theorem 2). -/
lemma isFirst_comp_ne {σ : Equiv.Perm (Fin (c * m + 2))} {p q : Fin (c * m + 2)}
    (hp : IsFirst c m σ p) (hq : IsFirst c m σ q) (hpq : p ≠ q) :
    lbComp c m (σ p) ≠ lbComp c m (σ q) := by
  rcases lt_or_gt_of_ne hpq with h | h
  · exact fun e => hq p h e
  · exact fun e => hp q h e.symm

/-- Auxiliary result for the lower-bound construction of Section 5 (proof of Theorem 2). -/
lemma card_leaders_lt_of_missing (hm : 1 ≤ m) (σ : Equiv.Perm (Fin (c * m + 2))) {t j : ℕ}
    (hj : j < c + 2) (hmiss : ∀ p : Fin (c * m + 2), (p : ℕ) ≤ t → lbComp c m (σ p) ≠ j) :
    (leaders (view (lbGraph c m) σ t) t).card < c + 2 := by
  rw [leaders_lb]
  have := card_le_card_of_injOn (fun p => lbComp c m (σ p))
    (s := univ.filter (fun p : Fin (c * m + 2) => (p : ℕ) ≤ t ∧ IsFirst c m σ p)) (t := (range (c + 2)).erase j)
    (by
      intro p hp
      simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hp
      simp only [coe_erase, coe_range, Set.mem_diff, Set.mem_Iio, Set.mem_singleton_iff]
      exact ⟨lbComp_lt hm _, hmiss p hp.1⟩)
    (by
      intro p hp q hq hpq
      simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hp hq
      by_contra h
      exact isFirst_comp_ne hp.2 hq.2 h hpq)
  rw [card_erase_of_mem (mem_range.2 hj), card_range] at this
  omega

/-- Auxiliary result for the lower-bound construction of Section 5 (proof of Theorem 2). -/
lemma card_leaders_full (hm : 1 ≤ m) (σ : Equiv.Perm (Fin (c * m + 2))) :
    c + 2 ≤ (leaders (view (lbGraph c m) σ (c * m + 1)) (c * m + 1)).card := by
  rw [leaders_lb]
  set F : ℕ → Finset (Fin (c * m + 2)) := fun j => univ.filter (fun p => lbComp c m (σ p) = j)
  have hne : ∀ j < c + 2, (F j).Nonempty := by
    intro j hj
    exact ⟨σ.symm (lbRep c m j), by simp [F, lbComp_rep hm hj]⟩
  set g : ℕ → Fin (c * m + 2) := fun j => if h : (F j).Nonempty then (F j).min' h else 0
  have hg : ∀ j < c + 2, lbComp c m (σ (g j)) = j ∧ IsFirst c m σ (g j) := by
    intro j hj
    simp only [g, dif_pos (hne j hj)]
    have hmem := min'_mem (F j) (hne j hj)
    simp only [F, mem_filter, mem_univ, true_and] at hmem
    refine ⟨hmem, fun q hq he => ?_⟩
    have : q ∈ F j := by simp [F, he, hmem]
    exact absurd (min'_le _ _ this) (not_le.2 hq)
  have := card_le_card_of_injOn g (s := range (c + 2))
    (t := univ.filter (fun p : Fin (c * m + 2) => (p : ℕ) ≤ c * m + 1 ∧ IsFirst c m σ p))
    (by
      intro j hj
      simp only [coe_range, Set.mem_Iio] at hj
      simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq]
      exact ⟨by have := (g j).2; omega, (hg j hj).2⟩)
    (by
      intro j hj j' hj' h
      simp only [coe_range, Set.mem_Iio] at hj hj'
      rw [← (hg j hj).1, ← (hg j' hj').1, h])
  simpa using this

/-- Auxiliary result for the lower-bound construction of Section 5 (proof of Theorem 2). -/
lemma exists_leaders_lb (hm : 1 ≤ m) (σ : Equiv.Perm (Fin (c * m + 2))) :
    ∃ t, c + 2 ≤ (leaders (view (lbGraph c m) σ t) t).card :=
  ⟨_, card_leaders_full hm σ⟩

/-- Auxiliary result for the lower-bound construction of Section 5 (proof of Theorem 2). -/
lemma tstar_le (hm : 1 ≤ m) (σ : Equiv.Perm (Fin (c * m + 2))) :
    tstar (lbGraph c m) (c + 2) σ ≤ c * m + 1 :=
  Nat.sInf_le (card_leaders_full hm σ)

/-- The pigeonhole step: at time `tstar` two leaders (first arrivals of two different
components) have been put in the same cluster. -/
lemma exists_collision (hm : 1 ≤ m) (A : OnlineAlg (c * m + 2) (c + 1))
    (τ : Equiv.Perm (Fin (c * m + 2))) :
    ∃ p q : Fin (c * m + 2), p ≠ q ∧ (p : ℕ) ≤ tstar (lbGraph c m) (c + 2) τ ∧
      (q : ℕ) ≤ tstar (lbGraph c m) (c + 2) τ ∧
      lbComp c m (τ p) ≠ lbComp c m (τ q) ∧
      A.dec (lbGraph c m) τ p = A.dec (lbGraph c m) τ q := by
  have h := tstar_spec (lbGraph c m) (c + 2) τ (exists_leaders_lb hm τ)
  rw [leaders_lb] at h
  obtain ⟨p, hp, q, hq, hpq, he⟩ := exists_ne_map_eq_of_card_lt_of_maps_to
    (s := univ.filter (fun p : Fin (c * m + 2) =>
      (p : ℕ) ≤ tstar (lbGraph c m) (c + 2) τ ∧ IsFirst c m τ p))
    (t := (univ : Finset (Fin (c + 1)))) (f := fun p => A.dec (lbGraph c m) τ p)
    (by rw [card_univ, Fintype.card_fin]; omega) (fun _ _ => by simp)
  simp only [mem_filter, mem_univ, true_and] at hp hq
  exact ⟨p, q, hpq, hp.1, hq.1, isFirst_comp_ne hp.2 hq.2 hpq, he⟩

/-- The event `E` of Section 5 at time `T`: both singletons arrive by time `T`, and some clique
has no vertex arrived by time `T`. -/
def lbEvent (c m T : ℕ) (σ : Equiv.Perm (Fin (c * m + 2))) : Prop :=
  lbS1 c m ∈ firstSet σ T ∧ lbS2 c m ∈ firstSet σ T ∧
    ∃ j < c, ∀ v ∈ firstSet σ T, lbComp c m v ≠ j

/-- On the event `E`, `tstar ≥ T`. -/
lemma le_tstar_of_lbEvent (hm : 1 ≤ m) {T : ℕ} {σ : Equiv.Perm (Fin (c * m + 2))}
    (hE : lbEvent c m T σ) : T ≤ tstar (lbGraph c m) (c + 2) σ := by
  obtain ⟨-, -, j, hj, hmiss⟩ := hE
  by_contra hlt
  push_neg at hlt
  have h := tstar_spec (lbGraph c m) (c + 2) σ (exists_leaders_lb hm σ)
  have := card_leaders_lt_of_missing hm σ (t := tstar (lbGraph c m) (c + 2) σ) (j := j)
    (by omega) (by
      intro p hp
      apply hmiss
      simp only [firstSet, arrTime, mem_filter, mem_univ, true_and, Equiv.symm_apply_apply]
      omega)
  omega

/-- The isolated positions are the positions `≤ tstar` without arrived neighbours. -/
lemma mem_isoSet_iff {σ : Equiv.Perm (Fin (c * m + 2))} {p : Fin (c * m + 2)} :
    p ∈ isoSet (lbGraph c m) (c + 2) σ ↔ (p : ℕ) ≤ tstar (lbGraph c m) (c + 2) σ ∧
      ∀ q : Fin (c * m + 2), (q : ℕ) ≤ tstar (lbGraph c m) (c + 2) σ → q ≠ p →
        lbComp c m (σ q) ≠ lbComp c m (σ p) := by
  simp only [isoSet, view, lbGraph, cliqueGraph, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨hp, h⟩
    refine ⟨hp, fun q hq hqp hc => h q ⟨hp, hq, fun he => hqp (σ.injective he).symm, hc.symm⟩⟩
  · rintro ⟨hp, h⟩
    exact ⟨hp, fun q ⟨_, hq, hne, hc⟩ => h q hq (fun he => hne (he ▸ rfl)) hc.symm⟩

/-- A singleton which arrived by `tstar` is isolated. -/
lemma singleton_mem_isoSet (hm : 1 ≤ m) {σ : Equiv.Perm (Fin (c * m + 2))}
    {s : Fin (c * m + 2)} (hs : s = lbS1 c m ∨ s = lbS2 c m)
    (harr : (σ.symm s : ℕ) ≤ tstar (lbGraph c m) (c + 2) σ) :
    σ.symm s ∈ isoSet (lbGraph c m) (c + 2) σ := by
  rw [mem_isoSet_iff]
  refine ⟨harr, fun q _ hq hc => hq ?_⟩
  rw [Equiv.apply_symm_apply] at hc
  rcases hs with rfl | rfl
  · rw [lbComp_s1] at hc
    rw [← lbComp_eq_s1 hm hc]; simp
  · rw [lbComp_s2] at hc
    rw [← lbComp_eq_s2 hm hc]; simp

/-- The extended event `E'`: both singletons are isolated at `tstar`, and there are at least
three isolated positions. -/
def lbEvent' (c m : ℕ) (σ : Equiv.Perm (Fin (c * m + 2))) : Prop :=
  σ.symm (lbS1 c m) ∈ isoSet (lbGraph c m) (c + 2) σ ∧
    σ.symm (lbS2 c m) ∈ isoSet (lbGraph c m) (c + 2) σ ∧
    3 ≤ (isoSet (lbGraph c m) (c + 2) σ).card

/-- `E ⊆ E'`: on `E`, the two singletons and the vertex arriving at `tstar` are isolated. -/
lemma lbEvent'_of_lbEvent (hm : 1 ≤ m) {T : ℕ} {σ : Equiv.Perm (Fin (c * m + 2))}
    (hE : lbEvent c m T σ) : lbEvent' c m σ := by
  have hT := le_tstar_of_lbEvent hm hE
  set ts := tstar (lbGraph c m) (c + 2) σ with hts
  have h1 : (σ.symm (lbS1 c m) : ℕ) < T := by
    have := hE.1; simp only [firstSet, arrTime, mem_filter, mem_univ, true_and] at this
    exact this
  have h2 : (σ.symm (lbS2 c m) : ℕ) < T := by
    have := hE.2.1; simp only [firstSet, arrTime, mem_filter, mem_univ, true_and] at this
    exact this
  have hs1 := singleton_mem_isoSet hm (Or.inl rfl) (σ := σ) (by omega)
  have hs2 := singleton_mem_isoSet hm (Or.inr rfl) (σ := σ) (by omega)
  refine ⟨hs1, hs2, ?_⟩
  -- the position `tstar` is isolated
  have htsle := tstar_le hm σ
  set pt : Fin (c * m + 2) := ⟨ts, by omega⟩
  have hT1 : 1 ≤ ts := by
    have := (σ.symm (lbS1 c m)).2; omega
  have hfirst : IsFirst c m σ pt := by
    by_contra hnf
    have hspec := tstar_spec (lbGraph c m) (c + 2) σ (exists_leaders_lb hm σ)
    rw [← hts] at hspec
    have hlt := lt_of_lt_tstar (lbGraph c m) (c + 2) σ (t := ts - 1) (by omega)
    rw [leaders_lb] at hspec hlt
    have : univ.filter (fun p : Fin (c * m + 2) => (p : ℕ) ≤ ts ∧ IsFirst c m σ p) ⊆
        univ.filter (fun p : Fin (c * m + 2) => (p : ℕ) ≤ ts - 1 ∧ IsFirst c m σ p) := by
      intro p hp
      simp only [mem_filter, mem_univ, true_and] at hp ⊢
      refine ⟨?_, hp.2⟩
      by_contra h
      have : p = pt := Fin.ext (by simp [pt]; omega)
      exact hnf (this ▸ hp.2)
    have := card_le_card this
    omega
  have hpt : pt ∈ isoSet (lbGraph c m) (c + 2) σ := by
    rw [mem_isoSet_iff]
    refine ⟨le_rfl, fun q hq hqp => ?_⟩
    have : q < pt := by
      rcases lt_or_gt_of_ne hqp with h | h
      · exact h
      · exact absurd hq (not_le.2 (by simpa [pt] using h))
    exact hfirst q this
  have hne1 : pt ≠ σ.symm (lbS1 c m) := by
    intro h; have := congrArg Fin.val h; simp [pt] at this; omega
  have hne2 : pt ≠ σ.symm (lbS2 c m) := by
    intro h; have := congrArg Fin.val h; simp [pt] at this; omega
  have hne12 : σ.symm (lbS1 c m) ≠ σ.symm (lbS2 c m) := by
    intro h; exact lbS1_ne_lbS2 (σ.symm.injective h)
  have : ({pt, σ.symm (lbS1 c m), σ.symm (lbS2 c m)} : Finset _) ⊆
      isoSet (lbGraph c m) (c + 2) σ := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have := card_le_card this
  rw [card_insert_of_notMem (by simp [hne1, hne2]), card_pair hne12] at this
  exact this

end CCK


/-!
# Every online algorithm fails with constant probability (proof of Theorem 2, combinatorial part)

On the instance of Section 5, conditioned on the event `E'` (both singletons are among at least
three indistinguishable isolated vertices at time `tstar`), any deterministic online algorithm
incurs cost at least `m` with probability at least `1/2` (in the paper: "the algorithm succeeds
with probability at most `1/3`").
-/

@[expose] public section

open Finset
open scoped Classical

namespace CCK

variable {c m : ℕ}

/-- Auxiliary result for the proof of Theorem 2 (Section 5). -/
lemma symm_mul_apply (σ ρ : Equiv.Perm (Fin (c * m + 2))) (v : Fin (c * m + 2)) :
    (σ * ρ).symm v = ρ.symm (σ.symm v) := by
  rw [Equiv.Perm.mul_def, Equiv.symm_trans_apply]

/-- If the algorithm succeeds (cost `< m`) on a re-shuffled order `σ ρ`, then the new positions
`(x, y)` of the two singletons form a "good" pair: among the isolated positions, exactly `x` and
`y` were put in the cluster of `x`. -/
lemma good_of_succ (hm : 1 ≤ m) (A : OnlineAlg (c * m + 2) (c + 1))
    (σ ρ : Equiv.Perm (Fin (c * m + 2)))
    (hρ : ρ ∈ fixOutside (isoSet (lbGraph c m) (c + 2) σ)) (hE : lbEvent' c m σ)
    (hs : cost (lbGraph c m) (A.run (lbGraph c m) (σ * ρ)) < m) :
    ∀ r ∈ isoSet (lbGraph c m) (c + 2) σ,
      (A.dec (lbGraph c m) σ r = A.dec (lbGraph c m) σ (ρ.symm (σ.symm (lbS1 c m))) ↔
        r = ρ.symm (σ.symm (lbS1 c m)) ∨ r = ρ.symm (σ.symm (lbS2 c m))) := by
  set G := lbGraph c m
  set I := isoSet G (c + 2) σ
  set τ := σ * ρ with hτ
  set x := ρ.symm (σ.symm (lbS1 c m)) with hx
  set y := ρ.symm (σ.symm (lbS2 c m)) with hy
  have hxI : x ∈ I := fixOutside_symm_apply_mem hρ hE.1
  have hyI : y ∈ I := fixOutside_symm_apply_mem hρ hE.2.1
  have hτx : τ.symm (lbS1 c m) = x := symm_mul_apply σ ρ _
  have hτy : τ.symm (lbS2 c m) = y := symm_mul_apply σ ρ _
  have hle : ∀ r ∈ I, (r : ℕ) ≤ tstar G (c + 2) σ := fun r hr => (mem_filter.1 hr).2.1
  have hdec : ∀ r ∈ I, A.dec G τ r = A.dec G σ r :=
    fun r hr => dec_mul_fixOutside A G (c + 2) σ ρ hρ (hle r hr)
  have hts : tstar G (c + 2) τ = tstar G (c + 2) σ :=
    tstar_mul_fixOutside G (c + 2) σ ρ hρ (exists_leaders_lb hm σ)
  have hrun : ∀ v, A.run G τ v = A.dec G τ (τ.symm v) := fun v => rfl
  have hsing : ∀ v, c ≤ lbComp c m v → τ.symm v = x ∨ τ.symm v = y := by
    intro v hv
    rcases eq_s1_or_s2 hm hv with rfl | rfl
    · exact Or.inl hτx
    · exact Or.inr hτy
  -- step 1: the two singletons share a cluster
  have hxy : A.dec G σ x = A.dec G σ y := by
    obtain ⟨p, q, hpq, -, -, hcomp, hdpq⟩ := exists_collision hm A τ
    have h := singletons_of_cost_lt hm (A.run G τ) hs (u := τ p) (v := τ q)
      (by rw [hrun, hrun]; simpa using hdpq) hcomp
    have hp := hsing _ h.1
    have hq := hsing _ h.2
    simp only [Equiv.symm_apply_apply] at hp hq
    rw [← hdec x hxI, ← hdec y hyI]
    rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
    · exact absurd rfl hpq
    · exact hdpq
    · exact hdpq.symm
    · exact absurd rfl hpq
  intro r hr
  constructor
  · intro h
    have h' : A.run G τ (τ r) = A.run G τ (lbS1 c m) := by
      rw [hrun, hrun, Equiv.symm_apply_apply, hτx, hdec r hr, hdec x hxI, h]
    by_cases hc : lbComp c m (τ r) = lbComp c m (lbS1 c m)
    · rw [lbComp_s1] at hc
      have := lbComp_eq_s1 hm hc
      left
      rw [← hτx, ← this, Equiv.symm_apply_apply]
    · have := (singletons_of_cost_lt hm (A.run G τ) hs h' hc).1
      have := hsing _ this
      rwa [Equiv.symm_apply_apply] at this
  · rintro (rfl | rfl)
    · rfl
    · exact hxy.symm

/-- For each order in `E'`, at least half of the re-shufflings of the isolated vertices make the
algorithm pay at least `m`. -/
lemma half_bad (hm : 1 ≤ m) (A : OnlineAlg (c * m + 2) (c + 1))
    (σ : Equiv.Perm (Fin (c * m + 2))) (hE : lbEvent' c m σ) :
    (1 / 2 : ℝ) * (fixOutside (isoSet (lbGraph c m) (c + 2) σ)).card ≤
      ((fixOutside (isoSet (lbGraph c m) (c + 2) σ)).filter
        (fun ρ => m ≤ cost (lbGraph c m) (A.run (lbGraph c m) (σ * ρ)))).card := by
  set G := lbGraph c m
  set I := isoSet G (c + 2) σ
  set H := fixOutside I
  set a := σ.symm (lbS1 c m)
  set b := σ.symm (lbS2 c m)
  have hab : a ≠ b := fun h => lbS1_ne_lbS2 (σ.symm.injective h)
  set Good := I.offDiag.filter (fun xy => ∀ r ∈ I,
    (A.dec G σ r = A.dec G σ xy.1 ↔ r = xy.1 ∨ r = xy.2))
  set B := I.offDiag \ Good
  have hpair := card_fixOutside_pair I hE.1 hE.2.1 hab B sdiff_subset
  have hsub : H.filter (fun ρ => (ρ.symm a, ρ.symm b) ∈ B) ⊆
      H.filter (fun ρ => m ≤ cost G (A.run G (σ * ρ))) := by
    intro ρ hρ
    simp only [mem_filter] at hρ ⊢
    refine ⟨hρ.1, ?_⟩
    by_contra hlt
    push_neg at hlt
    have hgood := good_of_succ hm A σ ρ hρ.1 hE hlt
    have := mem_sdiff.1 hρ.2
    apply this.2
    simp only [Good, mem_filter]
    exact ⟨this.1, hgood⟩
  have hGood : Good.card ≤ I.card := by
    apply card_le_card_of_injOn Prod.fst
    · intro xy hxy
      simp only [Good, coe_filter, Set.mem_setOf_eq, mem_offDiag] at hxy
      exact hxy.1.1
    · rintro ⟨x, y⟩ hxy ⟨x', y'⟩ hxy' (h : x = x')
      subst h
      simp only [coe_filter, Set.mem_setOf_eq, mem_offDiag, Good] at hxy hxy'
      have h1 := (hxy'.2 y' hxy'.1.2.1).2 (Or.inr rfl)
      rcases (hxy.2 y' hxy'.1.2.1).1 h1 with h | h
      · exact absurd h.symm hxy'.1.2.2
      · rw [h]
  have hBcard : B.card + Good.card = I.offDiag.card := by
    have hsubG : Good ⊆ I.offDiag := filter_subset _ _
    rw [card_sdiff_of_subset hsubG]
    have := card_le_card hsubG
    omega
  have hj := hE.2.2
  have hoff : I.offDiag.card = I.card * I.card - I.card := offDiag_card I
  have hFc := card_le_card hsub
  -- arithmetic
  set j := I.card
  have hO : (I.offDiag.card : ℝ) = (j : ℝ) * j - j := by
    rw [hoff, Nat.cast_sub (Nat.le_mul_self j)]; push_cast; ring
  have hpair' : ((H.filter (fun ρ => (ρ.symm a, ρ.symm b) ∈ B)).card : ℝ) *
      I.offDiag.card = B.card * H.card := by exact_mod_cast hpair
  have hB' : (B.card : ℝ) + Good.card = I.offDiag.card := by exact_mod_cast hBcard
  have hG' : (Good.card : ℝ) ≤ j := by exact_mod_cast hGood
  have hj' : (3 : ℝ) ≤ j := by exact_mod_cast hj
  have hF' : ((H.filter (fun ρ => (ρ.symm a, ρ.symm b) ∈ B)).card : ℝ) ≤
      (H.filter (fun ρ => m ≤ cost G (A.run G (σ * ρ)))).card := by exact_mod_cast hFc
  have hHpos : (0 : ℝ) ≤ H.card := Nat.cast_nonneg _
  have hOpos : (0 : ℝ) < I.offDiag.card := by rw [hO]; nlinarith
  have key : (1 / 2 : ℝ) * H.card * I.offDiag.card ≤
      ((H.filter (fun ρ => (ρ.symm a, ρ.symm b) ∈ B)).card : ℝ) * I.offDiag.card := by
    rw [hpair']
    have : (1 / 2 : ℝ) * I.offDiag.card ≤ B.card := by rw [hO] at hB' ⊢; nlinarith
    nlinarith
  have := le_of_mul_le_mul_right key hOpos
  linarith

/-- **Combinatorial core of Theorem 2.**  For every deterministic online algorithm with
`k = c + 1` clusters on the instance of Section 5 and every time `T`, the expected cost is at
least `m · P(E) / 2`, where `E` is the event that both singletons arrive by time `T` while some
clique has no vertex arrived by time `T`. -/
theorem lb_expCost (hm : 1 ≤ m) (A : OnlineAlg (c * m + 2) (c + 1)) (T : ℕ) :
    (m : ℝ) * prob (lbEvent c m T) / 2 ≤ A.expCost (lbGraph c m) := by
  set G := lbGraph c m
  set S := (univ : Finset (Equiv.Perm (Fin (c * m + 2)))).filter (lbEvent' c m)
  have hex := exchange_count S (isoSet G (c + 2))
    (fun τ => m ≤ cost G (A.run G τ)) (1 / 2)
    (by
      intro σ hσ ρ hρ
      have hE := (mem_filter.1 hσ).2
      have hI := isoSet_mul_fixOutside G (c + 2) σ ρ hρ (exists_leaders_lb hm σ)
      refine ⟨?_, hI⟩
      simp only [S, mem_filter, mem_univ, true_and, lbEvent', symm_mul_apply]
      rw [show isoSet (lbGraph c m) (c + 2) (σ * ρ) = isoSet (lbGraph c m) (c + 2) σ from hI]
      exact ⟨fixOutside_symm_apply_mem hρ hE.1, fixOutside_symm_apply_mem hρ hE.2.1, hE.2.2⟩)
    (fun σ hσ => half_bad hm A σ (mem_filter.1 hσ).2)
  have hcardpos := card_perm_pos (n := c * m + 2)
  have h1 : prob (lbEvent c m T) ≤ (S.card : ℝ) / Fintype.card (Equiv.Perm (Fin (c * m + 2))) :=
    prob_mono (fun σ hσ => lbEvent'_of_lbEvent hm hσ)
  have h2 : ((S.filter (fun τ => m ≤ cost G (A.run G τ))).card : ℝ) ≤
      ((univ.filter (fun τ => m ≤ cost G (A.run G τ))).card : ℝ) := by
    exact_mod_cast card_le_card (filter_subset_filter _ (subset_univ _))
  have h3 := expect_ge_of_event (fun σ => (cost G (A.run G σ) : ℝ))
    (fun τ => m ≤ cost G (A.run G τ)) (m : ℝ) (fun σ => Nat.cast_nonneg _)
    (fun σ hσ => by simp only at hσ ⊢; exact_mod_cast hσ)
  unfold OnlineAlg.expCost
  unfold prob at h3
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have : prob (lbEvent c m T) / 2 ≤
      ((univ.filter (fun τ => m ≤ cost G (A.run G τ))).card : ℝ) /
        Fintype.card (Equiv.Perm (Fin (c * m + 2))) := by
    rw [div_le_iff₀ two_pos]
    calc prob (lbEvent c m T) ≤ (S.card : ℝ) / Fintype.card (Equiv.Perm (Fin (c * m + 2))) := h1
      _ ≤ _ := by
        rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hcardpos]
        linarith
  calc (m : ℝ) * prob (lbEvent c m T) / 2 = m * (prob (lbEvent c m T) / 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left this hm0
    _ ≤ _ := h3

end CCK
