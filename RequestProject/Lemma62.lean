module

public import RequestProject.Lemma61
public import RequestProject.CliqueInstance
public import RequestProject.PivotLoad
public import RequestProject.Lemma710

/-!
# Lemma 6.2

Lemma 6.2 of the paper: for a disjoint-cliques instance, at the time `T₀` at which the `k`-th
pivot arrives, with high probability at least `k - r(I)` pivot clusters have load at most
`4 c ln n`.

Our argument follows the paper (time `T' = ⌈c n ln n / a(I)⌉`, a partition of the small cliques
into `k - r` groups of total size at least `a(I)/2`, a hit/miss estimate for every group via
Fact 2.3, and an upper-tail Chernoff bound (Fact 2.2) for every small clique), but organises the
union bounds slightly differently, which yields the stronger bound `n^{1-c/2} + n^{1-2c/3}`;
the bound `n^{1-c} + n^{-c/8} + n^{1-c/4} + n^{1-c/3}` of the paper follows.
-/

@[expose] public section

open Finset
open scoped Classical

namespace CCK

/-! ### Partitioning small cliques into groups -/

section groups

variable (w : ℕ → ℕ)

/-- A subset of total weight between `a/2` and `a` (used in the greedy grouping of the proof of
Lemma 6.2). -/
lemma exists_subset_half_le_sum_le {a : ℝ} (ha : 0 ≤ a) (T : Finset ℕ)
    (hlt : ∀ i ∈ T, (w i : ℝ) < a) (hT : a / 2 ≤ ∑ i ∈ T, (w i : ℝ)) :
    ∃ U ⊆ T, a / 2 ≤ ∑ i ∈ U, (w i : ℝ) ∧ ∑ i ∈ U, (w i : ℝ) ≤ a := by
  by_cases hbig : ∃ i ∈ T, a / 2 ≤ (w i : ℝ)
  · obtain ⟨i, hi, hi2⟩ := hbig
    exact ⟨{i}, by simpa using hi, by simpa using hi2, by simpa using (hlt i hi).le⟩
  push_neg at hbig
  clear hlt
  induction T using Finset.induction_on with
  | empty => simp at hT; exact ⟨∅, by simp, by simpa using hT, by simpa using ha⟩
  | insert x T hx ih =>
    by_cases h : a / 2 ≤ ∑ i ∈ T, (w i : ℝ)
    · obtain ⟨U, hU, h1, h2⟩ := ih h (fun i hi => hbig i (mem_insert_of_mem hi))
      exact ⟨U, hU.trans (subset_insert _ _), h1, h2⟩
    · refine ⟨insert x T, subset_refl _, hT, ?_⟩
      rw [sum_insert hx]
      have := hbig x (mem_insert_self _ _)
      linarith

/-- The grouping step of the proof of Lemma 6.2: if all weights in `T` are below `a` and the
total weight is at least `m a`, then `T` contains `m` pairwise disjoint groups, each of total
weight at least `a / 2`. -/
lemma exists_groups {a : ℝ} (ha : 0 ≤ a) (m : ℕ) (T : Finset ℕ)
    (hlt : ∀ i ∈ T, (w i : ℝ) < a) (hT : m * a ≤ ∑ i ∈ T, (w i : ℝ)) :
    ∃ g : ℕ → Finset ℕ, (∀ j < m, g j ⊆ T) ∧ (∀ j < m, a / 2 ≤ ∑ i ∈ g j, (w i : ℝ)) ∧
      ∀ j < m, ∀ j' < m, j ≠ j' → Disjoint (g j) (g j') := by
  induction m generalizing T with
  | zero => exact ⟨fun _ => ∅, by simp, by simp, by simp⟩
  | succ m ih =>
    have h2 : a / 2 ≤ ∑ i ∈ T, (w i : ℝ) := by
      push_cast at hT; nlinarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]
    obtain ⟨U, hU, hU1, hU2⟩ := exists_subset_half_le_sum_le w ha T hlt h2
    have hrest : (m : ℝ) * a ≤ ∑ i ∈ T \ U, (w i : ℝ) := by
      have := sum_sdiff hU (f := fun i => (w i : ℝ))
      push_cast at hT; linarith
    obtain ⟨g, hg1, hg2, hg3⟩ := ih (T \ U) (fun i hi => hlt i (mem_sdiff.1 hi).1) hrest
    refine ⟨fun j => if j = m then U else g j, ?_, ?_, ?_⟩
    · intro j hj; dsimp only; split_ifs
      · exact hU
      · exact (hg1 j (by omega)).trans sdiff_subset
    · intro j hj; dsimp only; split_ifs
      · exact hU1
      · exact hg2 j (by omega)
    · intro j hj j' hj' hne
      dsimp only
      split_ifs with h1 h2 h2
      · omega
      · exact disjoint_of_subset_right (hg1 j' (by omega)) disjoint_sdiff
      · exact disjoint_of_subset_left (hg1 j (by omega)) sdiff_disjoint
      · exact hg3 j (by omega) j' (by omega) hne

end groups

/-! ### The time of arrival of the `k`-th pivot -/

variable {n : ℕ}

/-- The time `T₀` at which the `k`-th pivot arrives (Section 6), i.e. the number of arrivals up to
and including the `k`-th pivot (`n` if there are fewer than `k` pivots). -/
noncomputable def kthPivotTime (G : SimpleGraph (Fin n)) (σ : Equiv.Perm (Fin n)) (k : ℕ) : ℕ :=
  if h : ∃ t, k ≤ (pivotsUpTo G σ t).card then Nat.find h else n

/-- The set `S` of Lemma 6.2: the pivots arrived by the time `T₀` of the `k`-th pivot whose pivot
clusters have load at most `L` at time `T₀`. -/
noncomputable def lightPivots (G : SimpleGraph (Fin n)) (σ : Equiv.Perm (Fin n)) (k : ℕ) (L : ℝ) :
    Finset (Fin n) :=
  (pivotsUpTo G σ (kthPivotTime G σ k)).filter
    (fun v => (pclAt G σ v (kthPivotTime G σ k) : ℝ) ≤ L)

/-! ### PIVOT on a disjoint-cliques graph -/

section cliques

variable {ι : Type*} (q : Fin n → ι) (σ : Equiv.Perm (Fin n))

/-- Auxiliary result for Lemma 6.2 (Section 6). -/
lemma cidx_pivotOf_clique (u : Fin n) : cidx q (pivotOf (cliqueGraph q) σ u) = cidx q u := by
  rw [cidx_eq_iff]
  by_cases hu : IsPivot (cliqueGraph q) σ u
  · rw [pivotOf_of_isPivot _ σ hu]
  · exact (pivotOf_spec_of_not_isPivot _ σ hu).2.1.2

/-- Auxiliary result for Lemma 6.2 (Section 6). -/
lemma cidx_injOn_pivots (t : ℕ) :
    Set.InjOn (cidx q) (pivotsUpTo (cliqueGraph q) σ t : Set _) := by
  intro u hu v hv huv
  by_contra hne
  have hu' := ((mem_pivotsUpTo_iff _ σ t u).1 hu).1
  have hv' := ((mem_pivotsUpTo_iff _ σ t v).1 hv).1
  exact not_adj_of_isPivot _ σ hu' hv' ⟨hne, (cidx_eq_iff q u v).1 huv⟩

/-- Auxiliary result for Lemma 6.2 (Section 6). -/
lemma card_image_cidx_firstSet_le (t : ℕ) :
    ((firstSet σ t).image (cidx q)).card ≤ (pivotsUpTo (cliqueGraph q) σ t).card := by
  refine le_trans (card_le_card (t := (pivotsUpTo (cliqueGraph q) σ t).image (cidx q)) ?_)
    card_image_le
  intro i hi
  obtain ⟨u, hu, rfl⟩ := mem_image.1 hi
  refine mem_image.2 ⟨pivotOf (cliqueGraph q) σ u, ?_, cidx_pivotOf_clique q σ u⟩
  rw [mem_pivotsUpTo_iff]
  refine ⟨isPivot_pivotOf _ σ u, lt_of_le_of_lt (arrTime_pivotOf_le _ σ u) ?_⟩
  simpa [firstSet] using hu

/-- Auxiliary result for Lemma 6.2 (Section 6). -/
lemma pclAt_le_clique (v : Fin n) (t : ℕ) :
    pclAt (cliqueGraph q) σ v t ≤
      (firstSet σ t ∩ univ.filter (fun u => cidx q u = cidx q v)).card := by
  unfold pclAt
  apply card_le_card
  intro u hu
  simp only [mem_inter, mem_filter, mem_univ, true_and] at hu ⊢
  refine ⟨hu.1, ?_⟩
  rw [← hu.2, cidx_pivotOf_clique]

end cliques

/-! ### The two probabilistic estimates of the proof of Lemma 6.2 -/

/-- The time `T' = ⌈c n ln n / a⌉` of the proof of Lemma 6.2 (capped at `n`). -/
noncomputable def tPrime (n : ℕ) (a c : ℝ) : ℕ := min ⌈c * n * Real.log n / a⌉₊ n

/-- Proof of Lemma 6.2: a group of at least `a/2` vertices is missed by the first `T'` arrivals
with probability at most `n^{-c/2}` (Fact 2.3). -/
lemma prob_miss_group {a c : ℝ} (ha : 0 < a) (M : Finset (Fin n))
    (hM : a / 2 ≤ (M.card : ℝ)) :
    prob (fun σ => Disjoint (firstSet σ (tPrime n a c)) M) ≤ (n : ℝ) ^ (-c / 2) := by
  have hT : tPrime n a c ≤ n := min_le_right _ _
  rw [prob_disjoint_firstSet hT]
  have hMpos : 0 < M.card := by exact_mod_cast (show (0:ℝ) < M.card by linarith)
  have hMn : M.card ≤ n := by simpa using card_le_univ M
  have hn : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  by_cases hb : tPrime n a c ≤ n - M.card
  · obtain ⟨-, h2, h3⟩ := fact_2_3 n M.card (tPrime n a c) hMn hb hn
    refine (h2.trans h3).trans ?_
    have hTeq : tPrime n a c = ⌈c * n * Real.log n / a⌉₊ := by
      unfold tPrime at hb ⊢
      rcases min_cases ⌈c * n * Real.log n / a⌉₊ n with h | h
      · exact h.1
      · exfalso; rw [h.1] at hb; omega
    have hge : c * n * Real.log n / a ≤ tPrime n a c := by rw [hTeq]; exact Nat.le_ceil _
    rw [Real.rpow_def_of_pos hnR]
    apply Real.exp_le_exp.2
    have hT0 : (0:ℝ) ≤ tPrime n a c := Nat.cast_nonneg _
    have h1 : a / 2 * (c * n * Real.log n / a) ≤ (M.card : ℝ) * tPrime n a c := by
      nlinarith
    have h2 : a / 2 * (c * n * Real.log n / a) = Real.log n * (c / 2) * n := by
      field_simp
    have h4 : Real.log n * (c / 2) ≤ (M.card : ℝ) * tPrime n a c / n := by
      rw [le_div_iff₀ hnR]; linarith
    rw [neg_div]; linarith
  · push_neg at hb
    rw [Nat.choose_eq_zero_of_lt hb]
    simp only [Nat.cast_zero, zero_div]
    exact Real.rpow_nonneg hnR.le _

/-- Auxiliary result for Lemma 6.2 (Section 6). -/
lemma prob_false_eq : prob (fun _ : Equiv.Perm (Fin n) => False) = 0 := by
  unfold prob; simp

/-- Proof of Lemma 6.2: a set of fewer than `a` vertices (a clique of `A`) has more than
`4 c ln n` vertices among the first `T'` arrivals with probability at most `n^{-2c/3}`
(Fact 2.2), provided `c ln n ≥ 1`. -/
lemma prob_tail_clique (hCh : ChernoffBound) (hPNA : PermNegAssoc) {a c : ℝ} (ha : 0 < a)
    (hcl : 1 ≤ c * Real.log n) (M : Finset (Fin n)) (hM : (M.card : ℝ) < a) :
    prob (fun σ => 4 * c * Real.log n < ((firstSet σ (tPrime n a c) ∩ M).card : ℝ)) ≤
      (n : ℝ) ^ (-(2 * c) / 3) := by
  have hT : tPrime n a c ≤ n := min_le_right _ _
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp at hcl; linarith
    · exact h
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set T := tPrime n a c with hTdef
  set μ := (M.card : ℝ) * T / n with hμ
  set x := c * n * Real.log n / a with hx
  have hx0 : 0 ≤ x := by
    rw [hx]; apply div_nonneg _ ha.le
    have : 0 ≤ c * Real.log n := by linarith
    nlinarith
  have hTx : (T : ℝ) ≤ x + 1 := by
    have h1 : T ≤ ⌈x⌉₊ := min_le_left _ _
    have h2 : (⌈x⌉₊ : ℝ) < x + 1 := Nat.ceil_lt_add_one hx0
    have : (T : ℝ) ≤ ⌈x⌉₊ := by exact_mod_cast h1
    linarith
  have hMn : (M.card : ℝ) ≤ n := by exact_mod_cast (by simpa using card_le_univ M)
  have hμ0 : 0 ≤ μ := by positivity
  have hμle : 2 * μ ≤ 4 * c * Real.log n := by
    have h1 : (M.card : ℝ) * T ≤ M.card * x + n := by
      have := mul_le_mul_of_nonneg_left hTx (Nat.cast_nonneg M.card)
      nlinarith
    have h2 : (M.card : ℝ) * x ≤ a * x := mul_le_mul_of_nonneg_right hM.le hx0
    have h3 : a * x = c * Real.log n * n := by rw [hx]; field_simp
    have h4 : μ ≤ c * Real.log n + 1 := by
      rw [hμ, div_le_iff₀ hnR]; nlinarith
    linarith
  have hL : 0 < 4 * c * Real.log n := by linarith
  have hexp : Real.exp (-(4 * c * Real.log n) / 6) = (n : ℝ) ^ (-(2 * c) / 3) := by
    rw [Real.rpow_def_of_pos hnR]; congr 1; ring
  obtain ⟨-, h2, -, -⟩ := fact_2_2 hCh hPNA M hT
  rcases chernoff_choice_710 hμ0 hL hμle with ⟨δ, hδ, hδL, hδe⟩ | ⟨h0, -⟩
  · calc prob (fun σ => 4 * c * Real.log n < ((firstSet σ T ∩ M).card : ℝ))
        ≤ prob (fun σ => (1 + δ) * μ ≤ ((firstSet σ T ∩ M).card : ℝ)) :=
          prob_mono (fun σ h => by linarith)
      _ ≤ Real.exp (-(δ ^ 2 * μ) / (2 + δ)) := h2 δ hδ
      _ ≤ _ := hδe.trans hexp.le
  · have hz : ∀ σ : Equiv.Perm (Fin n), (firstSet σ T ∩ M).card = 0 := by
      intro σ
      rw [hμ, div_eq_zero_iff] at h0
      rcases h0 with h0 | h0
      · rcases mul_eq_zero.1 h0 with h | h
        · have : M = ∅ := card_eq_zero.1 (by exact_mod_cast h)
          simp [this]
        · have hT0 : T = 0 := by exact_mod_cast h
          simp [firstSet, hT0]
      · exact absurd h0 hnR.ne'
    calc prob (fun σ => 4 * c * Real.log n < ((firstSet σ T ∩ M).card : ℝ))
        ≤ prob (fun _ : Equiv.Perm (Fin n) => False) :=
          prob_mono (fun σ h => by rw [hz σ] at h; simp at h; linarith)
      _ = 0 := prob_false_eq
      _ ≤ _ := Real.rpow_nonneg hnR.le _

/-! ### The deterministic part of the proof of Lemma 6.2 -/

/-- Auxiliary result for Lemma 6.2 (Section 6). -/
lemma card_filter_cidx_mem {ι : Type*} (q : Fin n → ι) (I : Finset ℕ)
    (hI : I ⊆ range (numCliques q)) :
    (univ.filter (fun v => cidx q v ∈ I)).card = ∑ i ∈ I, cw q i := by
  have := card_eq_sum_card_fiberwise (s := univ.filter (fun v => cidx q v ∈ I)) (t := I)
    (f := cidx q) (by intro v hv; simpa using hv)
  rw [this]
  apply sum_congr rfl
  intro i hi
  rw [← card_cidx_fiber q (mem_range.1 (hI hi))]
  congr 1; ext v; simp only [mem_filter, mem_univ, true_and]
  constructor
  · exact fun h => h.2
  · intro h; exact ⟨h ▸ hi, h⟩

/-- Auxiliary result for Lemma 6.2 (Section 6). -/
lemma numCliques_le {ι : Type*} (q : Fin n → ι) : numCliques q ≤ n := by
  unfold numCliques cliqueSet
  simpa using card_image_le (s := (univ : Finset (Fin n))) (f := q)

/-- The deterministic core of the proof of Lemma 6.2: if each of `k` pairwise disjoint groups of
cliques has a vertex among the first `T` arrivals (so `T₀ ≤ T`), and every clique `K_i` with
`i ≥ r` has at most `L` vertices among the first `T` arrivals, then at least `k - r` pivot
clusters have load at most `L` at time `T₀`. -/
lemma light_of_good {ι : Type*} (q : Fin n → ι) (σ : Equiv.Perm (Fin n)) {k r T : ℕ} {L : ℝ}
    (g : ℕ → Finset ℕ) (hgd : ∀ j < k, ∀ j' < k, j ≠ j' → Disjoint (g j) (g j'))
    (hhit : ∀ j < k, ¬ Disjoint (firstSet σ T) (univ.filter (fun v => cidx q v ∈ g j)))
    (htail : ∀ i, r ≤ i → i < numCliques q →
      ((firstSet σ T ∩ univ.filter (fun v => cidx q v = i)).card : ℝ) ≤ L) :
    k - r ≤ (lightPivots (cliqueGraph q) σ k L).card := by
  set G := cliqueGraph q
  set Im := (firstSet σ T).image (cidx q)
  have hIm : k ≤ Im.card := by
    have hsub : (range k).biUnion (fun j => g j ∩ Im) ⊆ Im := by
      intro i hi; obtain ⟨j, -, hj⟩ := mem_biUnion.1 hi; exact (mem_inter.1 hj).2
    have hcard := card_biUnion (s := range k) (t := fun j => g j ∩ Im) (by
      intro j hj j' hj' hne
      exact disjoint_of_subset_left inter_subset_left (disjoint_of_subset_right inter_subset_left
        (hgd j (mem_range.1 hj) j' (mem_range.1 hj') hne)))
    have hpos : ∀ j ∈ range k, 1 ≤ (g j ∩ Im).card := by
      intro j hj
      obtain ⟨v, hv1, hv2⟩ := not_disjoint_iff.1 (hhit j (mem_range.1 hj))
      apply card_pos.2
      refine ⟨cidx q v, mem_inter.2 ⟨(mem_filter.1 hv2).2, mem_image.2 ⟨v, hv1, rfl⟩⟩⟩
    calc k = ∑ j ∈ range k, 1 := by simp
      _ ≤ ∑ j ∈ range k, (g j ∩ Im).card := sum_le_sum hpos
      _ = _ := hcard.symm
      _ ≤ Im.card := card_le_card hsub
  have hex : ∃ t, k ≤ (pivotsUpTo G σ t).card :=
    ⟨T, hIm.trans (card_image_cidx_firstSet_le q σ T)⟩
  have hT0 : kthPivotTime G σ k = Nat.find hex := by unfold kthPivotTime; rw [dif_pos hex]
  have hT0le : kthPivotTime G σ k ≤ T := by
    rw [hT0]; exact Nat.find_min' hex (hIm.trans (card_image_cidx_firstSet_le q σ T))
  have hk : k ≤ (pivotsUpTo G σ (kthPivotTime G σ k)).card := by
    rw [hT0]; exact Nat.find_spec hex
  set P := pivotsUpTo G σ (kthPivotTime G σ k)
  have hbig : (P.filter (fun v => cidx q v < r)).card ≤ r := by
    have := card_le_card_of_injOn (s := P.filter (fun v => cidx q v < r)) (t := range r) (cidx q)
      (fun v hv => by simpa using (mem_filter.1 hv).2)
      ((cidx_injOn_pivots q σ _).mono (by intro v hv; exact (mem_filter.1 hv).1))
    simpa using this
  have hsplit := card_filter_add_card_filter_not (s := P) (fun v => cidx q v < r)
  have hsmall : (P.filter (fun v => ¬ cidx q v < r)) ⊆ lightPivots G σ k L := by
    intro v hv
    obtain ⟨hvP, hvr⟩ := mem_filter.1 hv
    refine mem_filter.2 ⟨hvP, ?_⟩
    have h1 := pclAt_le_clique q σ v (kthPivotTime G σ k)
    have h2 : (firstSet σ (kthPivotTime G σ k) ∩
        univ.filter (fun u => cidx q u = cidx q v)).card ≤
        (firstSet σ T ∩ univ.filter (fun u => cidx q u = cidx q v)).card := by
      apply card_le_card; apply inter_subset_inter_right
      intro u hu; simp only [firstSet, mem_filter, mem_univ, true_and] at hu ⊢; omega
    have h3 := htail (cidx q v) (by omega) (cidx_lt q v)
    have : (pclAt G σ v (kthPivotTime G σ k) : ℝ) ≤
        (firstSet σ T ∩ univ.filter (fun u => cidx q u = cidx q v)).card := by
      exact_mod_cast h1.trans h2
    linarith
  have := card_le_card hsmall
  omega

/-- **Lemma 6.2, sharpened form.**  Under the hypotheses of Lemma 6.2, the probability that fewer
than `k - r(I)` pivot clusters have load at most `4 c ln n` at time `T₀` is at most
`n^{1-c/2} + n^{1-2c/3}`. -/
theorem lemma_6_2_strong (hCh : ChernoffBound) (hPNA : PermNegAssoc) {ι : Type*}
    (q : Fin n → ι) {k : ℕ} (hk0 : 0 < k) (hkℓ : k < numCliques q) {c : ℝ} (hc : 4 < c) :
    prob (fun σ => (lightPivots (cliqueGraph q) σ k (4 * c * Real.log n)).card < k - rOf q k) ≤
      (n : ℝ) ^ (1 - c / 2) + (n : ℝ) ^ (1 - 2 * c / 3) := by
  set ℓ := numCliques q with hℓ
  set r := rOf q k with hrdef
  set a := aOf q k with hadef
  have hpos : ∀ i < ℓ, 0 < cw q i := fun i hi => cw_pos q hi
  have hr : r < k := rParam_lt hpos hk0 hkℓ
  have hrℓ : r < ℓ := by omega
  have hts : (tailSum (cw q) ℓ r : ℝ) = ((k : ℝ) - r) * a := tailSum_rParam_eq hr
  have hkr : (0 : ℝ) < (k : ℝ) - r := by
    have : (r : ℝ) < k := by exact_mod_cast hr
    linarith
  have ha : 0 < a := by
    have h1 : 0 < tailSum (cw q) ℓ r := by
      rw [tailSum_succ hrℓ]; have := hpos r hrℓ; omega
    have h2 : (0 : ℝ) < tailSum (cw q) ℓ r := by exact_mod_cast h1
    rw [hts] at h2
    exact pos_of_mul_pos_right h2 hkr.le
  have hℓn : ℓ ≤ n := numCliques_le q
  have hn2 : 2 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hcl : 1 ≤ c * Real.log n := by
    have h1 : Real.log 2 ≤ Real.log n :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hn2)
    have h2 := Real.log_two_gt_d9
    nlinarith
  -- the groups
  obtain ⟨g, hg1, hg2, hg3⟩ := exists_groups (cw q) ha.le (k - r) (Ico r ℓ)
    (fun i hi => lt_aParam_of_rParam_le (cw_sorted q) hr (mem_Ico.1 hi).1 (mem_Ico.1 hi).2)
    (by
      have : ∑ i ∈ Ico r ℓ, (cw q i : ℝ) = tailSum (cw q) ℓ r := by
        unfold tailSum; push_cast; rfl
      rw [this, hts, Nat.cast_sub hr.le])
  set G' : ℕ → Finset ℕ := fun j => if j < r then {j} else g (j - r) with hG'
  have hG'sub : ∀ j < k, G' j ⊆ range ℓ := by
    intro j hj
    simp only [hG']
    split_ifs with h
    · intro i hi; rw [mem_singleton] at hi; subst hi; exact mem_range.2 (by omega)
    · intro i hi; have := mem_Ico.1 (hg1 (j - r) (by omega) hi); exact mem_range.2 this.2
  have hG'sum : ∀ j < k, a / 2 ≤ ∑ i ∈ G' j, (cw q i : ℝ) := by
    intro j hj
    simp only [hG']
    split_ifs with h
    · rw [sum_singleton]
      have := aParam_le_of_lt_rParam (w := cw q) (ℓ := ℓ) (k := k) h
      have h' : a ≤ cw q j := this
      linarith
    · exact hg2 (j - r) (by omega)
  have hG'd : ∀ j < k, ∀ j' < k, j ≠ j' → Disjoint (G' j) (G' j') := by
    intro j hj j' hj' hne
    simp only [hG']
    split_ifs with h1 h2 h2
    · simpa using hne
    · rw [disjoint_singleton_left]
      intro hm; have := mem_Ico.1 (hg1 (j' - r) (by omega) hm); omega
    · rw [disjoint_singleton_right]
      intro hm; have := mem_Ico.1 (hg1 (j - r) (by omega) hm); omega
    · exact hg3 (j - r) (by omega) (j' - r) (by omega) (by omega)
  set T := tPrime n a c with hT
  set Vg : ℕ → Finset (Fin n) := fun j => univ.filter (fun v => cidx q v ∈ G' j) with hVg
  set F : ℕ → Finset (Fin n) := fun i => univ.filter (fun v => cidx q v = i) with hF
  have hbad : ∀ σ : Equiv.Perm (Fin n),
      (lightPivots (cliqueGraph q) σ k (4 * c * Real.log n)).card < k - r →
      (∃ j ∈ range k, Disjoint (firstSet σ T) (Vg j)) ∨
        (∃ i ∈ Ico r ℓ, 4 * c * Real.log n < ((firstSet σ T ∩ F i).card : ℝ)) := by
    intro σ hσ
    by_contra hcon
    push_neg at hcon
    have := light_of_good q σ (k := k) (r := r) (T := T) (L := 4 * c * Real.log n) G' hG'd
      (fun j hj => hcon.1 j (mem_range.2 hj))
      (fun i hi1 hi2 => hcon.2 i (mem_Ico.2 ⟨hi1, hi2⟩))
    omega
  have hA : ∀ j ∈ range k, prob (fun σ => Disjoint (firstSet σ T) (Vg j)) ≤
      (n : ℝ) ^ (-c / 2) := by
    intro j hj
    apply prob_miss_group ha
    simp only [hVg]
    rw [card_filter_cidx_mem q _ (hG'sub j (mem_range.1 hj))]
    push_cast
    exact hG'sum j (mem_range.1 hj)
  have hB : ∀ i ∈ Ico r ℓ, prob (fun σ => 4 * c * Real.log n < ((firstSet σ T ∩ F i).card : ℝ)) ≤
      (n : ℝ) ^ (-(2 * c) / 3) := by
    intro i hi
    apply prob_tail_clique hCh hPNA ha hcl
    simp only [hF]
    rw [card_cidx_fiber q (mem_Ico.1 hi).2]
    exact lt_aParam_of_rParam_le (cw_sorted q) hr (mem_Ico.1 hi).1 (mem_Ico.1 hi).2
  have hkn : (k : ℝ) ≤ n := by exact_mod_cast (by omega : k ≤ n)
  have hIn : ((Ico r ℓ).card : ℝ) ≤ n := by
    rw [Nat.card_Ico]; exact_mod_cast (by omega : ℓ - r ≤ n)
  have e1 : (n : ℝ) ^ (1 - c / 2) = n * (n : ℝ) ^ (-c / 2) := by
    rw [sub_eq_add_neg, Real.rpow_add hnR, Real.rpow_one, neg_div]
  have e2 : (n : ℝ) ^ (1 - 2 * c / 3) = n * (n : ℝ) ^ (-(2 * c) / 3) := by
    rw [sub_eq_add_neg, Real.rpow_add hnR, Real.rpow_one, neg_div]
  have key := prob_mono hbad
  have key2 := prob_or_le (fun σ => ∃ j ∈ range k, Disjoint (firstSet σ T) (Vg j))
    (fun σ => ∃ i ∈ Ico r ℓ, 4 * c * Real.log n < ((firstSet σ T ∩ F i).card : ℝ))
  refine le_trans (le_of_eq (prob_congr fun σ => Iff.rfl)) (key.trans
    (le_trans (le_of_eq (prob_congr fun σ => Iff.rfl)) (key2.trans ?_)))
  refine (add_le_add ((prob_congr (fun σ => Iff.rfl)).trans_le ((prob_exists_le _ _).trans
      (sum_le_sum (fun j hj => (prob_congr (fun σ => Iff.rfl)).trans_le (hA j hj)))))
    ((prob_congr (fun σ => Iff.rfl)).trans_le ((prob_exists_le _ _).trans
      (sum_le_sum (fun i hi => (prob_congr (fun σ => Iff.rfl)).trans_le (hB i hi)))))).trans ?_
  rw [sum_const, sum_const, card_range, nsmul_eq_mul, nsmul_eq_mul, e1, e2]
  gcongr

/-- **Lemma 6.2 (sufficiently many clusters have small load at the time of arrival of the `k`-th
pivot).**  Let `c > 4` and let `S` be the set of pivot clusters with load at most `4 c ln n` at
the time `T₀` the `k`-th pivot arrives (`lightPivots`).  Then `|S| ≥ k - r(I)` with probability
at least `1 - n^{1-c} - n^{-c/8} - n^{1-c/4} - n^{1-c/3}`; we bound the failure probability.
Here `0 < k < ℓ` (if `ℓ ≤ k` the algorithm never needs the set `S`).  (Assumes Fact 2.1 and
Lemma 5.3, through Fact 2.2.) -/
theorem lemma_6_2 (hCh : ChernoffBound) (hPNA : PermNegAssoc) {ι : Type*} (q : Fin n → ι)
    {k : ℕ} (hk0 : 0 < k) (hkℓ : k < numCliques q) {c : ℝ} (hc : 4 < c) :
    prob (fun σ => (lightPivots (cliqueGraph q) σ k (4 * c * Real.log n)).card < k - rOf q k) ≤
      (n : ℝ) ^ (1 - c) + (n : ℝ) ^ (-c / 8) + (n : ℝ) ^ (1 - c / 4) + (n : ℝ) ^ (1 - c / 3) := by
  have hn : (1 : ℝ) ≤ n := by
    have := numCliques_le q
    exact_mod_cast (by omega : 1 ≤ n)
  refine (lemma_6_2_strong hCh hPNA q hk0 hkℓ hc).trans ?_
  have h1 : (n : ℝ) ^ (1 - c / 2) ≤ (n : ℝ) ^ (-c / 8) :=
    Real.rpow_le_rpow_of_exponent_le hn (by linarith)
  have h2 : (n : ℝ) ^ (1 - 2 * c / 3) ≤ (n : ℝ) ^ (1 - c / 3) :=
    Real.rpow_le_rpow_of_exponent_le hn (by linarith)
  have h3 : 0 ≤ (n : ℝ) ^ (1 - c) := Real.rpow_nonneg (by linarith) _
  have h4 : 0 ≤ (n : ℝ) ^ (1 - c / 4) := Real.rpow_nonneg (by linarith) _
  linarith

end CCK
