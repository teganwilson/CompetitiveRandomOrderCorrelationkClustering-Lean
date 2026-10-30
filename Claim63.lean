module

public import RequestProject.UniformPivot

/-!
# Claim 6.3 (proof of Theorem 5)

Notation of the proof of Theorem 5 for a disjoint-cliques instance `cliqueGraph q` with `ℓ > k`
cliques, sorted by non-increasing size (`K_1, …, K_ℓ` are the fibres of `cidx q`, `0`-indexed):

* `tailVerts q k = ⋃_{j>k} K_j` (of size `s(I)`), `aVerts q k = A = ⋃_{j>r} K_j`;
* the window event `T_i`: `2^i ≤ T₀ < 2^{i+1}`;
* `Y_i`, `N_i`: the number of vertices of `⋃_{j>k} K_j`, resp. of `A`, among the first
  `min(2^{i+1}, n)` arrivals;
* `B_i = c₁ n ln n / 2^i`;
* the good event `G₁`: for every `i ≤ log₂ n`, every clique of size at least `B_i` has more than
  `c₁ ln n / 2` vertices among the first `2^i` arrivals;
* `m`: the number of cliques among `K_1, …, K_k` contained in the uncovered set `U`.
-/

@[expose] public section

open Finset
open scoped Classical

namespace CCK

variable {n : ℕ} {ι : Type*} (q : Fin n → ι) (k : ℕ)

/-- The clique `K_{j+1}` (vertices whose clique has index `j` in the sorted order). -/
noncomputable def fib (j : ℕ) : Finset (Fin n) := univ.filter (fun v => cidx q v = j)

/-- The vertices of the cliques `K_{k+1}, …, K_ℓ` (`|·| = s(I)`). -/
noncomputable def tailVerts : Finset (Fin n) := univ.filter (fun v => k ≤ cidx q v)

/-- The set `A = ⋃_{j > r(I)} K_j` of the proofs of Lemma 6.2 and Theorem 5. -/
noncomputable def aVerts : Finset (Fin n) := univ.filter (fun v => rOf q k ≤ cidx q v)

/-- The number `min(2^{i+1}, n)` of arrivals counted by `Y_i` and `N_i`. -/
def tWin (n i : ℕ) : ℕ := min (2 ^ (i + 1)) n

/-- `B_i = c₁ n ln n / 2^i`. -/
noncomputable def bPar (c₁ : ℝ) (n i : ℕ) : ℝ := c₁ * n * Real.log n / 2 ^ i

/-- The event `T_i`: `2^i ≤ T₀ < 2^{i+1}`. -/
def InWindow (σ : Equiv.Perm (Fin n)) (i : ℕ) : Prop :=
  2 ^ i ≤ kthPivotTime (cliqueGraph q) σ k ∧ kthPivotTime (cliqueGraph q) σ k < 2 ^ (i + 1)

/-- The good event `G₁` of the proof of Theorem 5. -/
def GoodG1 (c₁ : ℝ) (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ i ≤ Nat.log 2 n, ∀ j < numCliques q, bPar c₁ n i ≤ cw q j →
    c₁ * Real.log n / 2 < ((firstSet σ (2 ^ i) ∩ fib q j).card : ℝ)

/-- `m`: the number of cliques among `K_1, …, K_k` contained in the uncovered set `U`. -/
noncomputable def mTop (σ : Equiv.Perm (Fin n)) : ℕ :=
  ((range k).filter (fun j => fib q j ⊆ lateSet q σ k)).card

section basic

variable (σ : Equiv.Perm (Fin n))

/-- Auxiliary result for Claim 6.3 (proof of Theorem 5). -/
lemma card_fib {j : ℕ} (hj : j < numCliques q) : (fib q j).card = cw q j :=
  card_cidx_fiber q hj

/-- Auxiliary result for Claim 6.3 (proof of Theorem 5). -/
lemma card_tailVerts : (tailVerts q k).card = sOf q k := by
  have : tailVerts q k = univ.filter (fun v => cidx q v ∈ Ico k (numCliques q)) := by
    ext v; simp [tailVerts, cidx_lt q v]
  rw [this, card_filter_cidx_mem q _ (by intro i hi; simp at hi ⊢; omega)]
  rfl

/-- Auxiliary result for Claim 6.3 (proof of Theorem 5). -/
lemma card_aVerts : (aVerts q k).card = tailSum (cw q) (numCliques q) (rOf q k) := by
  have : aVerts q k = univ.filter (fun v => cidx q v ∈ Ico (rOf q k) (numCliques q)) := by
    ext v; simp [aVerts, cidx_lt q v]
  rw [this, card_filter_cidx_mem q _ (by intro i hi; simp at hi ⊢; omega)]
  rfl

/-- Auxiliary result for Claim 6.3 (proof of Theorem 5). -/
lemma exists_kth (hk : k ≤ numCliques q) :
    ∃ t, k ≤ (pivotsUpTo (cliqueGraph q) σ t).card := by
  refine ⟨n, le_trans ?_ (card_image_cidx_firstSet_le q σ n)⟩
  have : (firstSet σ n).image (cidx q) = range (numCliques q) := by
    ext j
    simp only [mem_image, mem_range]
    constructor
    · rintro ⟨v, -, rfl⟩; exact cidx_lt q v
    · intro hj
      obtain ⟨v, hv⟩ := card_pos.1 (by rw [card_fib q hj]; exact cw_pos q hj)
      refine ⟨v, ?_, (mem_filter.1 hv).2⟩
      simp [firstSet, arrTime]
  rw [this, card_range]; exact hk

/-- Auxiliary result for Claim 6.3 (proof of Theorem 5). -/
lemma kthPivotTime_eq (hk : k ≤ numCliques q) :
    kthPivotTime (cliqueGraph q) σ k = Nat.find (exists_kth q k σ hk) := by
  unfold kthPivotTime; rw [dif_pos (exists_kth q k σ hk)]

/-- Auxiliary result for Claim 6.3 (proof of Theorem 5). -/
lemma le_card_pivots_kth (hk : k ≤ numCliques q) :
    k ≤ (pivotsUpTo (cliqueGraph q) σ (kthPivotTime (cliqueGraph q) σ k)).card := by
  rw [kthPivotTime_eq q k σ hk]; exact Nat.find_spec (exists_kth q k σ hk)

/-- Auxiliary result for Claim 6.3 (proof of Theorem 5). -/
lemma kthPivotTime_le (hk : k ≤ numCliques q) : kthPivotTime (cliqueGraph q) σ k ≤ n := by
  rw [kthPivotTime_eq q k σ hk]
  apply Nat.find_min'
  refine le_trans ?_ (card_image_cidx_firstSet_le q σ n)
  have : (firstSet σ n).image (cidx q) = range (numCliques q) := by
    ext j
    simp only [mem_image, mem_range]
    constructor
    · rintro ⟨v, -, rfl⟩; exact cidx_lt q v
    · intro hj
      obtain ⟨v, hv⟩ := card_pos.1 (by rw [card_fib q hj]; exact cw_pos q hj)
      refine ⟨v, ?_, (mem_filter.1 hv).2⟩
      simp [firstSet, arrTime]
  rw [this, card_range]; exact hk

/-- Auxiliary result for Claim 6.3 (proof of Theorem 5). -/
lemma one_le_kthPivotTime (hk0 : 0 < k) (hk : k ≤ numCliques q) :
    1 ≤ kthPivotTime (cliqueGraph q) σ k := by
  have h := le_card_pivots_kth q k σ hk
  by_contra h0
  push_neg at h0
  have : kthPivotTime (cliqueGraph q) σ k = 0 := by omega
  rw [this] at h
  simp [pivotsUpTo] at h
  omega

/-- A vertex is uncovered at time `T₀` iff no vertex of its clique arrives by time `T₀`. -/
lemma mem_lateSet_iff (v : Fin n) :
    v ∈ lateSet q σ k ↔ ∀ u, cidx q u = cidx q v →
      kthPivotTime (cliqueGraph q) σ k ≤ arrTime σ u := by
  simp only [lateSet, mem_filter, mem_univ, true_and]
  constructor
  · intro h u hu
    rw [← pivotOf_eq_of_cidx_eq q σ hu] at h
    exact h.trans (arrTime_pivotOf_le _ σ u)
  · intro h
    exact h _ (cidx_pivotOf_clique q σ v)

/-- For a pivot `p`, the size of its pivot cluster at time `t` is the number of vertices of its
clique among the first `t` arrivals. -/
lemma pclAt_eq_clique {p : Fin n} (hp : IsPivot (cliqueGraph q) σ p) (t : ℕ) :
    pclAt (cliqueGraph q) σ p t = (firstSet σ t ∩ fib q (cidx q p)).card := by
  unfold pclAt fib
  congr 1
  ext u
  simp only [mem_inter, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [← h2, cidx_pivotOf_clique]⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rw [pivotOf_eq_of_cidx_eq q σ h2, pivotOf_of_isPivot _ σ hp]

/-- Auxiliary result for Claim 6.3 (proof of Theorem 5). -/
lemma firstSet_mono {s t : ℕ} (h : s ≤ t) : firstSet σ s ⊆ firstSet σ t := by
  intro u hu; simp only [firstSet, mem_filter, mem_univ, true_and] at hu ⊢; omega

end basic

/-! ### Claim 6.3 -/

section claim

variable {q k} {σ : Equiv.Perm (Fin n)} {c₁ L : ℝ} {i : ℕ}

/-- Auxiliary result for Claim 6.3 (proof of Theorem 5). -/
lemma firstSet_kth_subset_tWin (hk : k ≤ numCliques q) (hT : InWindow q k σ i) :
    firstSet σ (kthPivotTime (cliqueGraph q) σ k) ⊆ firstSet σ (tWin n i) := by
  apply firstSet_mono
  have := kthPivotTime_le q k σ hk
  unfold tWin; exact le_min hT.2.le this

/-- **Claim 6.3 (a).**  On `G₁ ∩ T_i` (and for a threshold `L ≤ c₁ ln n / 2`), every leading
clique of a cluster in `S` has size less than `B_i`. -/
theorem claim_6_3_a (hG1 : GoodG1 q c₁ σ) (hT : InWindow q k σ i)
    (hi : i ≤ Nat.log 2 n) (hL : L ≤ c₁ * Real.log n / 2) :
    ∀ p ∈ lightPivots (cliqueGraph q) σ k L, (cw q (cidx q p) : ℝ) < bPar c₁ n i := by
  intro p hp
  obtain ⟨hp1, hp2⟩ := mem_filter.1 hp
  have hpiv := ((mem_pivotsUpTo_iff _ σ _ p).1 hp1).1
  by_contra hcon
  push_neg at hcon
  have h1 := hG1 i hi (cidx q p) (cidx_lt q p) hcon
  rw [pclAt_eq_clique q σ hpiv] at hp2
  have h2 : (firstSet σ (2 ^ i) ∩ fib q (cidx q p)).card ≤
      (firstSet σ (kthPivotTime (cliqueGraph q) σ k) ∩ fib q (cidx q p)).card :=
    card_le_card (inter_subset_inter_right (firstSet_mono σ hT.1))
  have h3 : ((firstSet σ (2 ^ i) ∩ fib q (cidx q p)).card : ℝ) ≤
      (firstSet σ (kthPivotTime (cliqueGraph q) σ k) ∩ fib q (cidx q p)).card := by
    exact_mod_cast h2
  linarith

/-- **Claim 6.3 (b).**  On `G₁ ∩ T_i`, every clique contained in `U` has size less than `B_i`. -/
theorem claim_6_3_b (hG1 : GoodG1 q c₁ σ) (hT : InWindow q k σ i)
    (hi : i ≤ Nat.log 2 n) (hc : 0 ≤ c₁ * Real.log n / 2) :
    ∀ v ∈ lateSet q σ k, (cw q (cidx q v) : ℝ) < bPar c₁ n i := by
  intro v hv
  by_contra hcon
  push_neg at hcon
  have h1 := hG1 i hi (cidx q v) (cidx_lt q v) hcon
  have h0 : firstSet σ (2 ^ i) ∩ fib q (cidx q v) = ∅ := by
    ext u
    simp only [mem_inter, fib, firstSet, mem_filter, mem_univ, true_and, Finset.notMem_empty,
      iff_false, not_and]
    intro hu hcu
    have := (mem_lateSet_iff q k σ v).1 hv u hcu
    have := hT.1
    omega
  rw [h0, card_empty, Nat.cast_zero] at h1
  linarith

/-- **Claim 6.3 (c), first part.**  On `T_i`, `m ≤ Y_i`. -/
theorem claim_6_3_c_m (hk : k ≤ numCliques q) (hT : InWindow q k σ i) :
    mTop q k σ ≤ (firstSet σ (tWin n i) ∩ tailVerts q k).card := by
  set T0 := kthPivotTime (cliqueGraph q) σ k
  set P0 := pivotsUpTo (cliqueGraph q) σ T0
  set J := (range k).filter (fun j => fib q j ⊆ lateSet q σ k)
  have hP0 : k ≤ P0.card := le_card_pivots_kth q k σ hk
  have hnotJ : ∀ p ∈ P0, cidx q p ∉ J := by
    intro p hp hJ
    have hpl : p ∈ lateSet q σ k := (mem_filter.1 hJ).2 (by simp [fib])
    have h1 := ((mem_pivotsUpTo_iff _ σ _ p).1 hp)
    have h2 := (mem_lateSet_iff q k σ p).1 hpl p rfl
    omega
  have hsmall : (P0.filter (fun p => cidx q p < k)).card ≤ k - J.card := by
    have := card_le_card_of_injOn (s := P0.filter (fun p => cidx q p < k)) (t := range k \ J)
      (cidx q) (fun p hp => by
        obtain ⟨hp1, hp2⟩ := mem_filter.1 hp
        simp only [coe_sdiff, Set.mem_diff, mem_coe, mem_range]
        exact ⟨hp2, hnotJ p hp1⟩)
      ((cidx_injOn_pivots q σ _).mono (by intro v hv; exact (mem_filter.1 hv).1))
    rwa [card_sdiff_of_subset (filter_subset _ _), card_range] at this
  have hsplit := card_filter_add_card_filter_not (s := P0) (fun p => cidx q p < k)
  have hJk : J.card ≤ k := by
    simpa using card_le_card (filter_subset (fun j => fib q j ⊆ lateSet q σ k) (range k))
  have hbig : P0.filter (fun p => ¬ cidx q p < k) ⊆ firstSet σ (tWin n i) ∩ tailVerts q k := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := mem_filter.1 hp
    refine mem_inter.2 ⟨firstSet_kth_subset_tWin hk hT ?_, ?_⟩
    · exact pivotsUpTo_subset_firstSet _ σ _ hp1
    · simp only [tailVerts, mem_filter, mem_univ, true_and]; omega
  have := card_le_card hbig
  show J.card ≤ _
  omega

/-- **Claim 6.3 (c), second part.**  On `G₁ ∩ T_i`, `W ≤ s(I) + B_i m`. -/
theorem claim_6_3_c_W (hk : k ≤ numCliques q) (hG1 : GoodG1 q c₁ σ) (hT : InWindow q k σ i)
    (hi : i ≤ Nat.log 2 n) (hc : 0 ≤ c₁ * Real.log n / 2) :
    ((lateSet q σ k).card : ℝ) ≤ sOf q k + bPar c₁ n i * mTop q k σ := by
  set J := (range k).filter (fun j => fib q j ⊆ lateSet q σ k)
  have hsub : lateSet q σ k ⊆ tailVerts q k ∪ J.biUnion (fib q) := by
    intro v hv
    by_cases hvk : k ≤ cidx q v
    · exact mem_union_left _ (by simp [tailVerts, hvk])
    · apply mem_union_right
      refine mem_biUnion.2 ⟨cidx q v, ?_, by simp [fib]⟩
      simp only [J, mem_filter, mem_range]
      refine ⟨by omega, ?_⟩
      intro u hu
      have hu' : cidx q u = cidx q v := (mem_filter.1 hu).2
      rw [mem_lateSet_iff] at hv ⊢
      intro w hw
      exact hv w (hw.trans hu')
  have h1 := (card_le_card hsub).trans (card_union_le _ _)
  have h2 : (J.biUnion (fib q)).card ≤ ∑ j ∈ J, cw q j := by
    refine card_biUnion_le.trans (le_of_eq (sum_congr rfl fun j hj => card_fib q ?_))
    have := (mem_range.1 (mem_filter.1 hj).1); omega
  have h3 : (∑ j ∈ J, (cw q j : ℝ)) ≤ ∑ j ∈ J, bPar c₁ n i := by
    apply sum_le_sum
    intro j hj
    have hjl : j < numCliques q := by have := (mem_range.1 (mem_filter.1 hj).1); omega
    obtain ⟨v, hv⟩ := card_pos.1 (by rw [card_fib q hjl]; exact cw_pos q hjl)
    have hvl : v ∈ lateSet q σ k := (mem_filter.1 hj).2 hv
    have := claim_6_3_b hG1 hT hi hc v hvl
    rw [(mem_filter.1 hv).2] at this
    exact this.le
  rw [sum_const, nsmul_eq_mul] at h3
  have h4 : ((lateSet q σ k).card : ℝ) ≤ (tailVerts q k).card + ∑ j ∈ J, (cw q j : ℝ) := by
    exact_mod_cast h1.trans (Nat.add_le_add_left h2 _)
  rw [card_tailVerts] at h4
  have : (mTop q k σ : ℝ) = J.card := rfl
  rw [this]
  linarith

/-- **Claim 6.3 (d).**  On `T_i`, `N_i ≥ k - r`. -/
theorem claim_6_3_d (hk : k ≤ numCliques q) (hT : InWindow q k σ i) :
    k - rOf q k ≤ (firstSet σ (tWin n i) ∩ aVerts q k).card := by
  set T0 := kthPivotTime (cliqueGraph q) σ k
  set P0 := pivotsUpTo (cliqueGraph q) σ T0
  set r := rOf q k
  have hP0 : k ≤ P0.card := le_card_pivots_kth q k σ hk
  have hsmall : (P0.filter (fun p => cidx q p < r)).card ≤ r := by
    have := card_le_card_of_injOn (s := P0.filter (fun p => cidx q p < r)) (t := range r)
      (cidx q) (fun v hv => by simpa using (mem_filter.1 hv).2)
      ((cidx_injOn_pivots q σ _).mono (by intro v hv; exact (mem_filter.1 hv).1))
    simpa using this
  have hsplit := card_filter_add_card_filter_not (s := P0) (fun p => cidx q p < r)
  have hbig : P0.filter (fun p => ¬ cidx q p < r) ⊆ firstSet σ (tWin n i) ∩ aVerts q k := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := mem_filter.1 hp
    refine mem_inter.2 ⟨firstSet_kth_subset_tWin hk hT ?_, ?_⟩
    · exact pivotsUpTo_subset_firstSet _ σ _ hp1
    · simp only [aVerts, mem_filter, mem_univ, true_and]; omega
  have := card_le_card hbig
  omega

end claim

end CCK
