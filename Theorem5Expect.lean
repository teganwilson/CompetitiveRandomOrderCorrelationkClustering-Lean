module

public import RequestProject.Claim63

/-!
# Pointwise estimates in the proof of Theorem 5

On the event `G₁ ∩ T_i` we bound the number `2F` of ordered pairs of uncovered vertices in
distinct cliques by `s(I)² + 2 s(I) B_i m + B_i² m (m - 1)`, and, in the case `k - r = 1`, we
bound `W` on the event `E` that each of `K_1, …, K_r` contains one of the first `k` pivots, and
show `N_i ≥ 2` on its complement.
-/

@[expose] public section

open Finset
open scoped Classical

namespace CCK

variable {n : ℕ} {ι : Type*} {q : Fin n → ι} {k : ℕ} {σ : Equiv.Perm (Fin n)} {c₁ : ℝ} {i : ℕ}

/-- The set `J` of indices `j < k` with `K_{j+1} ⊆ U` (so `m = |J|`). -/
noncomputable def topLate (q : Fin n → ι) (k : ℕ) (σ : Equiv.Perm (Fin n)) : Finset ℕ :=
  (range k).filter (fun j => fib q j ⊆ lateSet q σ k)

/-- Auxiliary result for the proof of Theorem 5 (Section 6). -/
lemma mTop_eq : mTop q k σ = (topLate q k σ).card := rfl

/-- Auxiliary result for the proof of Theorem 5 (Section 6). -/
lemma lt_numCliques_of_mem_topLate (hk : k ≤ numCliques q) {j : ℕ} (hj : j ∈ topLate q k σ) :
    j < numCliques q := by
  have := mem_range.1 (mem_filter.1 hj).1; omega

/-- Auxiliary result for the proof of Theorem 5 (Section 6). -/
lemma cw_lt_of_mem_topLate (hk : k ≤ numCliques q) (hG1 : GoodG1 q c₁ σ)
    (hT : InWindow q k σ i) (hi : i ≤ Nat.log 2 n) (hc : 0 ≤ c₁ * Real.log n / 2) {j : ℕ}
    (hj : j ∈ topLate q k σ) : (cw q j : ℝ) < bPar c₁ n i := by
  have hjl := lt_numCliques_of_mem_topLate hk hj
  obtain ⟨v, hv⟩ := card_pos.1 (by rw [card_fib q hjl]; exact cw_pos q hjl)
  have hvl : v ∈ lateSet q σ k := (mem_filter.1 hj).2 hv
  have := claim_6_3_b hG1 hT hi hc v hvl
  rwa [(mem_filter.1 hv).2] at this

/-- Auxiliary result for the proof of Theorem 5 (Section 6). -/
lemma lateSet_subset (q : Fin n → ι) (k : ℕ) (σ : Equiv.Perm (Fin n)) :
    lateSet q σ k ⊆ tailVerts q k ∪ (topLate q k σ).biUnion (fib q) := by
  intro v hv
  by_cases hvk : k ≤ cidx q v
  · exact mem_union_left _ (by simp [tailVerts, hvk])
  · apply mem_union_right
    refine mem_biUnion.2 ⟨cidx q v, ?_, by simp [fib]⟩
    simp only [topLate, mem_filter, mem_range]
    refine ⟨by omega, ?_⟩
    intro u hu
    have hu' : cidx q u = cidx q v := (mem_filter.1 hu).2
    rw [mem_lateSet_iff] at hv ⊢
    intro w hw
    exact hv w (hw.trans hu')

/-- Auxiliary result for the proof of Theorem 5 (Section 6). -/
lemma card_biUnion_fib_le (hk : k ≤ numCliques q) (s : Finset ℕ) (hs : s ⊆ topLate q k σ) :
    ((s.biUnion (fib q)).card : ℝ) ≤ ∑ j ∈ s, (cw q j : ℝ) := by
  have : (s.biUnion (fib q)).card ≤ ∑ j ∈ s, cw q j :=
    card_biUnion_le.trans (le_of_eq (sum_congr rfl fun j hj =>
      card_fib q (lt_numCliques_of_mem_topLate hk (hs hj))))
  exact_mod_cast this

/-- Auxiliary result for the proof of Theorem 5 (Section 6). -/
lemma bPar_nonneg (hc : 0 ≤ c₁ * Real.log n / 2) : 0 ≤ bPar c₁ n i := by
  unfold bPar
  have : 0 ≤ c₁ * Real.log n := by linarith
  have : 0 ≤ c₁ * n * Real.log n := by nlinarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  positivity

/-- The pair bound of the proof of Theorem 5 (estimate of `F`): on `G₁ ∩ T_i`,
`2F ≤ s(I)² + 2 s(I) B_i m + B_i² m (m - 1)`. -/
theorem latePairs_le (hk : k ≤ numCliques q) (hG1 : GoodG1 q c₁ σ) (hT : InWindow q k σ i)
    (hi : i ≤ Nat.log 2 n) (hc : 0 ≤ c₁ * Real.log n / 2) :
    (latePairs q σ k : ℝ) ≤ (sOf q k : ℝ) ^ 2 +
      2 * sOf q k * bPar c₁ n i * mTop q k σ +
        bPar c₁ n i ^ 2 * (mTop q k σ * ((mTop q k σ : ℝ) - 1)) := by
  set J := topLate q k σ with hJ
  set M := J.biUnion (fib q) with hM
  set Tl := tailVerts q k with hTl
  set B := bPar c₁ n i with hB
  set m := mTop q k σ with hm
  have hB0 : 0 ≤ B := bPar_nonneg hc
  have hmJ : m = J.card := rfl
  have hMle : (M.card : ℝ) ≤ m * B := by
    refine (card_biUnion_fib_le hk J subset_rfl).trans ?_
    rw [hmJ, ← nsmul_eq_mul, ← sum_const]
    exact sum_le_sum (fun j hj => (cw_lt_of_mem_topLate hk hG1 hT hi hc hj).le)
  have hTl : (Tl.card : ℝ) = sOf q k := by rw [hTl, card_tailVerts]
  -- pairs inside `M` in distinct cliques
  set X := (M ×ˢ M).filter (fun x => cidx q x.1 ≠ cidx q x.2) with hX
  have hXle : (X.card : ℝ) ≤ M.card * (((m : ℝ) - 1) * B) := by
    have hXsub : X ⊆ M.biUnion (fun u => (M.filter (fun v => cidx q u ≠ cidx q v)).map
        ⟨fun v => (u, v), fun a b h => by simpa using h⟩) := by
      rintro ⟨u, v⟩ hx
      simp only [hX, mem_filter, mem_product] at hx
      simp only [mem_biUnion, mem_map, mem_filter, Function.Embedding.coeFn_mk, Prod.mk.injEq]
      exact ⟨u, hx.1.1, v, ⟨hx.1.2, hx.2⟩, rfl, rfl⟩
    have hinner : ∀ u ∈ M, ((M.filter (fun v => cidx q u ≠ cidx q v)).card : ℝ) ≤
        ((m : ℝ) - 1) * B := by
      intro u hu
      have hcu : cidx q u ∈ J := by
        obtain ⟨j, hj, hju⟩ := mem_biUnion.1 hu
        rwa [(mem_filter.1 hju).2]
      have hsub : M.filter (fun v => cidx q u ≠ cidx q v) ⊆ (J.erase (cidx q u)).biUnion (fib q) := by
        intro v hv
        obtain ⟨hvM, hne⟩ := mem_filter.1 hv
        obtain ⟨j, hj, hjv⟩ := mem_biUnion.1 hvM
        refine mem_biUnion.2 ⟨j, mem_erase.2 ⟨?_, hj⟩, hjv⟩
        rw [← (mem_filter.1 hjv).2]; exact Ne.symm hne
      have h1 : ((M.filter (fun v => cidx q u ≠ cidx q v)).card : ℝ) ≤
          ((J.erase (cidx q u)).biUnion (fib q)).card := by exact_mod_cast card_le_card hsub
      refine h1.trans ((card_biUnion_fib_le hk _ (erase_subset _ _)).trans ?_)
      have h2 : ∑ j ∈ J.erase (cidx q u), (cw q j : ℝ) ≤ ∑ j ∈ J.erase (cidx q u), B :=
        sum_le_sum (fun j hj => (cw_lt_of_mem_topLate hk hG1 hT hi hc (mem_of_mem_erase hj)).le)
      rw [sum_const, nsmul_eq_mul, card_erase_of_mem hcu] at h2
      have hJ1 : 1 ≤ J.card := card_pos.2 ⟨_, hcu⟩
      rw [Nat.cast_sub hJ1, Nat.cast_one] at h2
      rw [hmJ]; linarith
    have h1 : (X.card : ℝ) ≤ ∑ u ∈ M, ((M.filter (fun v => cidx q u ≠ cidx q v)).card : ℝ) := by
      have := (card_le_card hXsub).trans card_biUnion_le
      simp only [card_map] at this
      exact_mod_cast this
    refine h1.trans ?_
    rw [← nsmul_eq_mul, ← sum_const]
    exact sum_le_sum hinner
  -- the decomposition
  have hsub : (lateSet q σ k ×ˢ lateSet q σ k).filter (fun x => cidx q x.1 ≠ cidx q x.2) ⊆
      (Tl ×ˢ Tl) ∪ (Tl ×ˢ M) ∪ (M ×ˢ Tl) ∪ X := by
    rintro ⟨u, v⟩ hx
    simp only [mem_filter, mem_product] at hx
    have hu := lateSet_subset q k σ hx.1.1
    have hv := lateSet_subset q k σ hx.1.2
    rw [mem_union] at hu hv
    simp only [mem_union, mem_product, hX, mem_filter]
    rcases hu with hu | hu <;> rcases hv with hv | hv
    · tauto
    · tauto
    · tauto
    · right; exact ⟨⟨hu, hv⟩, hx.2⟩
  have hcard : (latePairs q σ k : ℝ) ≤ Tl.card * Tl.card + Tl.card * M.card +
      M.card * Tl.card + X.card := by
    have e0 := card_le_card hsub
    have e1 := card_union_le (Tl ×ˢ Tl ∪ Tl ×ˢ M ∪ M ×ˢ Tl) X
    have e2 := card_union_le (Tl ×ˢ Tl ∪ Tl ×ˢ M) (M ×ˢ Tl)
    have e3 := card_union_le (Tl ×ˢ Tl) (Tl ×ˢ M)
    simp only [card_product] at e1 e2 e3
    have : latePairs q σ k ≤ Tl.card * Tl.card + Tl.card * M.card + M.card * Tl.card + X.card := by
      unfold latePairs; omega
    exact_mod_cast this
  rw [hTl] at hcard
  have hs0 : (0 : ℝ) ≤ sOf q k := Nat.cast_nonneg _
  have hM0 : (0 : ℝ) ≤ M.card := Nat.cast_nonneg _
  rcases Nat.eq_zero_or_pos m with hm0 | hm0
  · have hMe : (M.card : ℝ) ≤ 0 := by rw [hm0] at hMle; simpa using hMle
    have hMz : (M.card : ℝ) = 0 := le_antisymm hMe hM0
    have hXz : (X.card : ℝ) ≤ 0 := by rw [hMz] at hXle; simpa using hXle
    rw [hm0]; simp only [Nat.cast_zero]
    nlinarith
  · have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm0
    have h1 : (sOf q k : ℝ) * M.card ≤ sOf q k * (m * B) := mul_le_mul_of_nonneg_left hMle hs0
    have h2 : (M.card : ℝ) * (((m : ℝ) - 1) * B) ≤ (m * B) * (((m : ℝ) - 1) * B) :=
      mul_le_mul_of_nonneg_right hMle (by nlinarith)
    nlinarith

/-- The event `E` of the proof of Theorem 5 (case `k - r = 1`): each of `K_1, …, K_r` contains one
of the `k` pivots that arrive by time `T₀`. -/
def CoverTop (q : Fin n → ι) (k : ℕ) (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ j < rOf q k, ∃ p ∈ pivotsUpTo (cliqueGraph q) σ (kthPivotTime (cliqueGraph q) σ k),
    cidx q p = j

/-- Auxiliary result for the proof of Theorem 5 (Section 6). -/
lemma aOf_nonneg (hk0 : 0 < k) (hk : k < numCliques q) : 0 ≤ aOf q k := by
  unfold aOf aParam
  have hr : rOf q k < k := rParam_lt (fun i hi => cw_pos q hi) hk0 hk
  have : ((rParam (cw q) (numCliques q) k : ℕ) : ℝ) < k := by exact_mod_cast hr
  apply div_nonneg (Nat.cast_nonneg _); linarith

/-- Case `k - r = 1` of the proof of Theorem 5, on the event `E ∩ T_i`:
`W ≤ s(I) 1{N_i ≥ 1} + a(I) 1{Y_i ≥ 1}`. -/
theorem W_le_of_cover (hk0 : 0 < k) (hk : k < numCliques q) (hkr : k = rOf q k + 1)
    (hT : InWindow q k σ i) (hE : CoverTop q k σ) :
    ((lateSet q σ k).card : ℝ) ≤
      sOf q k * (if 1 ≤ (firstSet σ (tWin n i) ∩ aVerts q k).card then 1 else 0) +
        aOf q k * (if 1 ≤ (firstSet σ (tWin n i) ∩ tailVerts q k).card then 1 else 0) := by
  set T0 := kthPivotTime (cliqueGraph q) σ k
  set P0 := pivotsUpTo (cliqueGraph q) σ T0
  set r := rOf q k with hr
  have hP0 : k ≤ P0.card := le_card_pivots_kth q k σ hk.le
  -- a pivot outside `K_1, …, K_r`
  obtain ⟨p0, hp0, hp0r⟩ : ∃ p0 ∈ P0, r ≤ cidx q p0 := by
    by_contra hcon
    push_neg at hcon
    have := card_le_card_of_injOn (s := P0) (t := range r) (cidx q)
      (fun p hp => by simpa using hcon p hp) (cidx_injOn_pivots q σ _)
    simp at this; omega
  have hp0T := ((mem_pivotsUpTo_iff _ σ _ p0).1 hp0).2
  set j0 := cidx q p0 with hj0
  have hj0l : j0 < numCliques q := cidx_lt q p0
  have hsub : lateSet q σ k ⊆ aVerts q k \ fib q j0 := by
    intro v hv
    have hv' := (mem_lateSet_iff q k σ v).1 hv
    refine mem_sdiff.2 ⟨?_, ?_⟩
    · simp only [aVerts, mem_filter, mem_univ, true_and]
      by_contra hlt
      push_neg at hlt
      obtain ⟨p, hp, hpj⟩ := hE _ hlt
      have := hv' p hpj
      have := ((mem_pivotsUpTo_iff _ σ _ p).1 hp).2
      omega
    · intro hvf
      have := hv' p0 (by rw [← hj0]; exact ((mem_filter.1 hvf).2).symm)
      omega
  have hfib : fib q j0 ⊆ aVerts q k := by
    intro v hv; simp only [aVerts, mem_filter, mem_univ, true_and, fib] at hv ⊢; omega
  have hW : (lateSet q σ k).card ≤ tailSum (cw q) (numCliques q) r - cw q j0 := by
    have := card_le_card hsub
    rwa [card_sdiff_of_subset hfib, card_aVerts, card_fib q hj0l] at this
  have hrl : r < numCliques q := by omega
  have hp0win : p0 ∈ firstSet σ (tWin n i) :=
    firstSet_kth_subset_tWin hk.le hT (pivotsUpTo_subset_firstSet _ σ _ hp0)
  have ha : (tailSum (cw q) (numCliques q) r : ℝ) = aOf q k := by
    have := tailSum_rParam_eq (w := cw q) (ℓ := numCliques q) (k := k) (by change rOf q k < k; omega)
    rw [show ((k : ℝ) - rParam (cw q) (numCliques q) k) = 1 by
      rw [show rParam (cw q) (numCliques q) k = r from rfl]
      have : (k : ℝ) = r + 1 := by exact_mod_cast hkr
      linarith, one_mul] at this
    exact this
  have hs0 : (0 : ℝ) ≤ sOf q k := Nat.cast_nonneg _
  have ha0 := aOf_nonneg hk0 hk
  have hi1 : (0 : ℝ) ≤ (if 1 ≤ (firstSet σ (tWin n i) ∩ aVerts q k).card then 1 else 0) := by
    split_ifs <;> norm_num
  have hi2 : (0 : ℝ) ≤ (if 1 ≤ (firstSet σ (tWin n i) ∩ tailVerts q k).card then 1 else 0) := by
    split_ifs <;> norm_num
  rcases eq_or_lt_of_le hp0r with heq | hlt
  · -- the pivot is in `K_k`: `W ≤ s(I)` and `N_i ≥ 1`
    have hN : 1 ≤ (firstSet σ (tWin n i) ∩ aVerts q k).card :=
      card_pos.2 ⟨p0, mem_inter.2 ⟨hp0win, by simp [aVerts]; omega⟩⟩
    rw [if_pos hN, mul_one]
    have hts : tailSum (cw q) (numCliques q) r = cw q r + tailSum (cw q) (numCliques q) k := by
      rw [tailSum_succ hrl, ← hkr]
    have hWs : (lateSet q σ k).card ≤ sOf q k := by
      have : sOf q k = tailSum (cw q) (numCliques q) k := rfl
      rw [← heq] at hW; omega
    have : ((lateSet q σ k).card : ℝ) ≤ sOf q k := by exact_mod_cast hWs
    nlinarith
  · -- the pivot is in `⋃_{j>k} K_j`: `W ≤ a(I)` and `Y_i ≥ 1`
    have hY : 1 ≤ (firstSet σ (tWin n i) ∩ tailVerts q k).card :=
      card_pos.2 ⟨p0, mem_inter.2 ⟨hp0win, by simp [tailVerts]; omega⟩⟩
    rw [if_pos hY, mul_one]
    have : ((lateSet q σ k).card : ℝ) ≤ tailSum (cw q) (numCliques q) r := by
      exact_mod_cast hW.trans (Nat.sub_le _ _)
    nlinarith

/-- Case `k - r = 1` of the proof of Theorem 5, on the complement of `E` (and on `T_i`):
`N_i ≥ 2`. -/
theorem two_le_N_of_not_cover (hk : k ≤ numCliques q) (hkr : k = rOf q k + 1)
    (hT : InWindow q k σ i) (hE : ¬ CoverTop q k σ) :
    2 ≤ (firstSet σ (tWin n i) ∩ aVerts q k).card := by
  set T0 := kthPivotTime (cliqueGraph q) σ k
  set P0 := pivotsUpTo (cliqueGraph q) σ T0
  set r := rOf q k with hr
  have hP0 : k ≤ P0.card := le_card_pivots_kth q k σ hk
  unfold CoverTop at hE
  push_neg at hE
  obtain ⟨j, hjr, hj⟩ := hE
  have hsmall : (P0.filter (fun p => cidx q p < r)).card ≤ r - 1 := by
    have := card_le_card_of_injOn (s := P0.filter (fun p => cidx q p < r))
      (t := (range r).erase j) (cidx q) (fun p hp => by
        obtain ⟨hp1, hp2⟩ := mem_filter.1 hp
        simp only [coe_erase, Set.mem_diff, mem_coe, mem_range, Set.mem_singleton_iff]
        exact ⟨hp2, hj p hp1⟩)
      ((cidx_injOn_pivots q σ _).mono (by intro v hv; exact (mem_filter.1 hv).1))
    rwa [card_erase_of_mem (mem_range.2 hjr), card_range] at this
  have hsplit := card_filter_add_card_filter_not (s := P0) (fun p => cidx q p < r)
  have hbig : P0.filter (fun p => ¬ cidx q p < r) ⊆ firstSet σ (tWin n i) ∩ aVerts q k := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := mem_filter.1 hp
    refine mem_inter.2 ⟨firstSet_kth_subset_tWin hk hT ?_, ?_⟩
    · exact pivotsUpTo_subset_firstSet _ σ _ hp1
    · simp only [aVerts, mem_filter, mem_univ, true_and]; omega
  have := card_le_card hbig
  omega

end CCK


/-!
# Expectation estimates in the proof of Theorem 5

For each window `i` we bound `E[W 1_{G₁} 1_{T_i}]` and `E[2F 1_{G₁} 1_{T_i}]`, using the moment
estimates (4) and (5) of the proof of Theorem 5 for the hypergeometric counts `Y_i` and `N_i`.
Here `ρ_i = min(2^{i+1}, n)/n ≤ p_i`.
-/

@[expose] public section

open Finset
open scoped Classical

namespace CCK

variable {n : ℕ} {ι : Type*} (q : Fin n → ι) (k : ℕ)

/-- `Y_i`: the number of vertices of `⋃_{j>k} K_j` among the first `min(2^{i+1}, n)` arrivals. -/
noncomputable def Ycnt (i : ℕ) (σ : Equiv.Perm (Fin n)) : ℕ :=
  (firstSet σ (tWin n i) ∩ tailVerts q k).card

/-- `N_i`: the number of vertices of `A` among the first `min(2^{i+1}, n)` arrivals. -/
noncomputable def Ncnt (i : ℕ) (σ : Equiv.Perm (Fin n)) : ℕ :=
  (firstSet σ (tWin n i) ∩ aVerts q k).card

/-- `ρ_i = min(2^{i+1}, n) / n`. -/
noncomputable def rhoW (n i : ℕ) : ℝ := (tWin n i : ℝ) / n

/-- Auxiliary result for the proof of Theorem 5 (Section 6). -/
lemma tWin_le (i : ℕ) : tWin n i ≤ n := min_le_right _ _

/-- Auxiliary result for the proof of Theorem 5 (Section 6). -/
lemma rhoW_nonneg (i : ℕ) : 0 ≤ rhoW n i := by unfold rhoW; positivity

variable {q k}

/-- Auxiliary result for the proof of Theorem 5 (Section 6). -/
lemma rOf_lt (hk0 : 0 < k) (hk : k < numCliques q) : rOf q k < k :=
  rParam_lt (fun _ hi => cw_pos q hi) hk0 hk

/-- Auxiliary result for the proof of Theorem 5 (Section 6). -/
lemma tailVerts_subset_aVerts (hk0 : 0 < k) (hk : k < numCliques q) :
    tailVerts q k ⊆ aVerts q k := by
  intro v hv
  have := rOf_lt hk0 hk
  simp only [tailVerts, aVerts, mem_filter, mem_univ, true_and] at hv ⊢; omega

/-- Auxiliary result for the proof of Theorem 5 (Section 6). -/
lemma card_aVerts_real (hk0 : 0 < k) (hk : k < numCliques q) :
    ((aVerts q k).card : ℝ) = ((k : ℝ) - rOf q k) * aOf q k := by
  rw [card_aVerts]; exact tailSum_rParam_eq (rOf_lt hk0 hk)

/-- Auxiliary result for the proof of Theorem 5 (Section 6). -/
lemma Ycnt_le_Ncnt (hk0 : 0 < k) (hk : k < numCliques q) (i : ℕ) (σ : Equiv.Perm (Fin n)) :
    Ycnt q k i σ ≤ Ncnt q k i σ :=
  card_le_card (inter_subset_inter_left (tailVerts_subset_aVerts hk0 hk))

/-- Auxiliary result for the proof of Theorem 5 (Section 6). -/
lemma Y_mul_N_sub_one_nonneg (hk0 : 0 < k) (hk : k < numCliques q) (i : ℕ)
    (σ : Equiv.Perm (Fin n)) : 0 ≤ (Ycnt q k i σ : ℝ) * ((Ncnt q k i σ : ℝ) - 1) := by
  have h := Ycnt_le_Ncnt hk0 hk i σ
  rcases Nat.eq_zero_or_pos (Ycnt q k i σ) with h0 | h0
  · rw [h0]; simp
  · have : (1 : ℝ) ≤ Ncnt q k i σ := by exact_mod_cast (h0.trans_le h)
    have : (0 : ℝ) ≤ Ycnt q k i σ := Nat.cast_nonneg _
    nlinarith

/-- Auxiliary result for the proof of Theorem 5 (Section 6). -/
lemma s_le_ka (hk0 : 0 < k) (hk : k < numCliques q) :
    (sOf q k : ℝ) ≤ ((k : ℝ) - rOf q k) * aOf q k := by
  rw [← card_aVerts_real hk0 hk, ← card_tailVerts]
  exact_mod_cast card_le_card (tailVerts_subset_aVerts hk0 hk)

/-! ### Moment estimates (4) and (5) -/

/-- Auxiliary result for the proof of Theorem 5 (Section 6). -/
lemma expect_Ycnt (i : ℕ) : expect (fun σ => (Ycnt q k i σ : ℝ)) = sOf q k * rhoW n i := by
  unfold Ycnt rhoW
  rw [expect_card_firstSet_inter (tWin_le i), card_tailVerts]; ring

/-- Auxiliary result for the proof of Theorem 5 (Section 6). -/
lemma expect_Ncnt (hk0 : 0 < k) (hk : k < numCliques q) (i : ℕ) :
    expect (fun σ => (Ncnt q k i σ : ℝ)) = ((k : ℝ) - rOf q k) * aOf q k * rhoW n i := by
  unfold Ncnt rhoW
  rw [expect_card_firstSet_inter (tWin_le i), card_aVerts_real hk0 hk]; ring

/-- Auxiliary result for the proof of Theorem 5 (Section 6). -/
lemma pair_ratio_le_rho (i : ℕ) :
    (tWin n i : ℝ) * (tWin n i - 1) / (n * (n - 1)) ≤ rhoW n i ^ 2 := by
  unfold rhoW; rw [div_pow]; exact pair_ratio_le (tWin_le i)

/-- Auxiliary result for the proof of Theorem 5 (Section 6). -/
lemma expect_YN (hk0 : 0 < k) (hk : k < numCliques q) (i : ℕ) :
    expect (fun σ => (Ycnt q k i σ : ℝ) * ((Ncnt q k i σ : ℝ) - 1)) ≤
      sOf q k * (((k : ℝ) - rOf q k) * aOf q k) * rhoW n i ^ 2 := by
  unfold Ycnt Ncnt
  rw [expect_pair_count (tWin_le i) (tailVerts_subset_aVerts hk0 hk), card_tailVerts,
    card_aVerts_real hk0 hk]
  have hA : 0 ≤ ((k : ℝ) - rOf q k) * aOf q k := by
    rw [← card_aVerts_real hk0 hk]; positivity
  have hs : (0 : ℝ) ≤ sOf q k := Nat.cast_nonneg _
  have h1 := pair_ratio_le_rho (n := n) i
  have h0 := pair_ratio_nonneg (tWin n i) n
  calc (sOf q k : ℝ) * (((k : ℝ) - rOf q k) * aOf q k - 1) *
        ((tWin n i : ℝ) * (tWin n i - 1) / (n * (n - 1)))
      ≤ (sOf q k : ℝ) * (((k : ℝ) - rOf q k) * aOf q k) *
        ((tWin n i : ℝ) * (tWin n i - 1) / (n * (n - 1))) := by
        apply mul_le_mul_of_nonneg_right _ h0
        apply mul_le_mul_of_nonneg_left _ hs; linarith
    _ ≤ _ := mul_le_mul_of_nonneg_left h1 (mul_nonneg hs hA)

/-- Auxiliary result for the proof of Theorem 5 (Section 6). -/
lemma expect_YY (i : ℕ) :
    expect (fun σ => (Ycnt q k i σ : ℝ) * ((Ycnt q k i σ : ℝ) - 1)) ≤
      (sOf q k : ℝ) ^ 2 * rhoW n i ^ 2 := by
  unfold Ycnt
  have := expect_pair_count_le (tWin_le (n := n) i) (tailVerts q k)
  rw [card_tailVerts] at this
  unfold rhoW; rw [div_pow]; exact this

/-! ### The window estimates -/

variable {c₁ : ℝ} {i : ℕ}

/-- `E[W 1_{G₁} 1_{T_i}] ≤ 3 s(I) a(I) ρ_i + 2 B_i s(I) a(I) ρ_i²` (both cases `k - r ≥ 2` and
`k - r = 1` of the proof of Theorem 5). -/
theorem expect_W_window (hk0 : 0 < k) (hk : k < numCliques q) (hi : i ≤ Nat.log 2 n)
    (hc : 0 ≤ c₁ * Real.log n / 2) :
    expect (fun σ => if GoodG1 q c₁ σ ∧ InWindow q k σ i then ((lateSet q σ k).card : ℝ)
      else 0) ≤
      3 * sOf q k * aOf q k * rhoW n i +
        2 * bPar c₁ n i * sOf q k * aOf q k * rhoW n i ^ 2 := by
  set s : ℝ := (sOf q k : ℝ)
  set a := aOf q k
  set B := bPar c₁ n i
  set ρ := rhoW n i
  set r := rOf q k
  have hr := rOf_lt hk0 hk
  have hB0 : 0 ≤ B := bPar_nonneg hc
  have hs0 : 0 ≤ s := Nat.cast_nonneg _
  have ha0 : 0 ≤ a := aOf_nonneg hk0 hk
  have hρ0 : 0 ≤ ρ := rhoW_nonneg i
  have hkr : (1 : ℝ) ≤ (k : ℝ) - r := by
    have : ((r : ℕ) : ℝ) + 1 ≤ k := by exact_mod_cast hr
    linarith
  have hYN := expect_YN hk0 hk i
  have hN := expect_Ncnt hk0 hk i
  have hY := expect_Ycnt (q := q) (k := k) i
  rcases Nat.lt_or_ge (r + 1) k with hk2 | hk1
  · -- case `k - r ≥ 2`
    have hkr2 : (2 : ℝ) ≤ (k : ℝ) - r := by
      have : ((r : ℕ) : ℝ) + 2 ≤ k := by exact_mod_cast hk2
      linarith
    set g : Equiv.Perm (Fin n) → ℝ := fun σ =>
      s / ((k : ℝ) - r) * (Ncnt q k i σ : ℝ) +
        B / ((k : ℝ) - r - 1) * ((Ycnt q k i σ : ℝ) * ((Ncnt q k i σ : ℝ) - 1)) with hg
    have hpt : ∀ σ, (if GoodG1 q c₁ σ ∧ InWindow q k σ i then ((lateSet q σ k).card : ℝ)
        else 0) ≤ g σ := by
      intro σ
      have hN0 : (0 : ℝ) ≤ Ncnt q k i σ := Nat.cast_nonneg _
      have hYN0 := Y_mul_N_sub_one_nonneg hk0 hk i σ
      have hg0 : 0 ≤ g σ := by
        simp only [hg]
        have : 0 ≤ s / ((k : ℝ) - r) := div_nonneg hs0 (by linarith)
        have : 0 ≤ B / ((k : ℝ) - r - 1) := div_nonneg hB0 (by linarith)
        positivity
      split_ifs with h
      · obtain ⟨hG1, hT⟩ := h
        have hW := claim_6_3_c_W hk.le hG1 hT hi hc
        have hm := claim_6_3_c_m hk.le hT
        have hNk := claim_6_3_d hk.le hT
        have hmY : (mTop q k σ : ℝ) ≤ Ycnt q k i σ := by exact_mod_cast hm
        have hNk' : (k : ℝ) - r ≤ Ncnt q k i σ := by
          have : ((k - r : ℕ) : ℝ) ≤ Ncnt q k i σ := by exact_mod_cast hNk
          rwa [Nat.cast_sub hr.le] at this
        have h1 : s ≤ s / ((k : ℝ) - r) * (Ncnt q k i σ : ℝ) := by
          rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
          exact mul_le_mul_of_nonneg_left hNk' hs0
        have hY0 : (0 : ℝ) ≤ Ycnt q k i σ := Nat.cast_nonneg _
        have h2 : B * Ycnt q k i σ ≤
            B / ((k : ℝ) - r - 1) * ((Ycnt q k i σ : ℝ) * ((Ncnt q k i σ : ℝ) - 1)) := by
          rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
          have : (k : ℝ) - r - 1 ≤ (Ncnt q k i σ : ℝ) - 1 := by linarith
          have := mul_le_mul_of_nonneg_left this (mul_nonneg hB0 hY0)
          nlinarith
        have h3 : B * mTop q k σ ≤ B * Ycnt q k i σ := mul_le_mul_of_nonneg_left hmY hB0
        simp only [hg]
        linarith
      · exact hg0
    refine (expect_mono hpt).trans ?_
    simp only [hg]
    rw [expect_add, expect_smul, expect_smul, hN]
    have hdiv : s / ((k : ℝ) - r) * (((k : ℝ) - r) * a * ρ) = s * a * ρ := by
      field_simp
    rw [hdiv]
    have h2 : B / ((k : ℝ) - r - 1) *
        expect (fun σ => (Ycnt q k i σ : ℝ) * ((Ncnt q k i σ : ℝ) - 1)) ≤
        B / ((k : ℝ) - r - 1) * (s * (((k : ℝ) - r) * a) * ρ ^ 2) :=
      mul_le_mul_of_nonneg_left hYN (div_nonneg hB0 (by linarith))
    have h3 : B / ((k : ℝ) - r - 1) * (s * (((k : ℝ) - r) * a) * ρ ^ 2) ≤
        2 * B * s * a * ρ ^ 2 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
      have : 0 ≤ B * s * a * ρ ^ 2 := by positivity
      nlinarith
    have : 0 ≤ s * a * ρ := by positivity
    linarith
  · -- case `k - r = 1`
    have hkr1 : k = r + 1 := by omega
    have hkrR : (k : ℝ) - r = 1 := by
      have : (k : ℝ) = r + 1 := by exact_mod_cast hkr1
      linarith
    set g : Equiv.Perm (Fin n) → ℝ := fun σ =>
      s * (Ncnt q k i σ : ℝ) + a * (Ycnt q k i σ : ℝ) +
        B * ((Ycnt q k i σ : ℝ) * ((Ncnt q k i σ : ℝ) - 1)) with hg
    have hpt : ∀ σ, (if GoodG1 q c₁ σ ∧ InWindow q k σ i then ((lateSet q σ k).card : ℝ)
        else 0) ≤ g σ := by
      intro σ
      have hN0 : (0 : ℝ) ≤ Ncnt q k i σ := Nat.cast_nonneg _
      have hY0 : (0 : ℝ) ≤ Ycnt q k i σ := Nat.cast_nonneg _
      have hYN0 := Y_mul_N_sub_one_nonneg hk0 hk i σ
      have hg0 : 0 ≤ g σ := by simp only [hg]; positivity
      split_ifs with h
      · obtain ⟨hG1, hT⟩ := h
        by_cases hE : CoverTop q k σ
        · have hW := W_le_of_cover hk0 hk hkr1 hT hE
          have e1 : s * (if 1 ≤ (firstSet σ (tWin n i) ∩ aVerts q k).card then (1 : ℝ) else 0)
              ≤ s * Ncnt q k i σ := by
            apply mul_le_mul_of_nonneg_left _ hs0
            split_ifs with h1
            · exact_mod_cast h1
            · exact hN0
          have e2 : a * (if 1 ≤ (firstSet σ (tWin n i) ∩ tailVerts q k).card then (1 : ℝ) else 0)
              ≤ a * Ycnt q k i σ := by
            apply mul_le_mul_of_nonneg_left _ ha0
            split_ifs with h1
            · exact_mod_cast h1
            · exact hY0
          have : 0 ≤ B * ((Ycnt q k i σ : ℝ) * ((Ncnt q k i σ : ℝ) - 1)) :=
            mul_nonneg hB0 hYN0
          simp only [hg]
          linarith
        · have hN2 := two_le_N_of_not_cover hk.le hkr1 hT hE
          have hN2' : (2 : ℝ) ≤ Ncnt q k i σ := by exact_mod_cast hN2
          have hW := claim_6_3_c_W hk.le hG1 hT hi hc
          have hm := claim_6_3_c_m hk.le hT
          have hmY : (mTop q k σ : ℝ) ≤ Ycnt q k i σ := by exact_mod_cast hm
          have h3 : B * mTop q k σ ≤ B * Ycnt q k i σ := mul_le_mul_of_nonneg_left hmY hB0
          have h4 : B * Ycnt q k i σ ≤ B * ((Ycnt q k i σ : ℝ) * ((Ncnt q k i σ : ℝ) - 1)) := by
            apply mul_le_mul_of_nonneg_left _ hB0; nlinarith
          have h5 : s ≤ s * Ncnt q k i σ := by nlinarith
          have : 0 ≤ a * (Ycnt q k i σ : ℝ) := mul_nonneg ha0 hY0
          simp only [hg]
          linarith
      · exact hg0
    refine (expect_mono hpt).trans ?_
    simp only [hg]
    rw [expect_add, expect_add, expect_smul, expect_smul, expect_smul, hN, hY]
    rw [hkrR] at hYN ⊢
    have h2 : B * expect (fun σ => (Ycnt q k i σ : ℝ) * ((Ncnt q k i σ : ℝ) - 1)) ≤
        B * (s * (1 * a) * ρ ^ 2) := mul_le_mul_of_nonneg_left hYN hB0
    have : 0 ≤ s * a * ρ := by positivity
    have : 0 ≤ B * s * a * ρ ^ 2 := by positivity
    nlinarith

/-- `E[2F 1_{G₁} 1_{T_i}] ≤ s(I)² P[T_i] + 2 s(I)² B_i ρ_i + B_i² s(I)² ρ_i²`. -/
theorem expect_LP_window (hk : k < numCliques q) (hi : i ≤ Nat.log 2 n)
    (hc : 0 ≤ c₁ * Real.log n / 2) :
    expect (fun σ => if GoodG1 q c₁ σ ∧ InWindow q k σ i then (latePairs q σ k : ℝ) else 0) ≤
      (sOf q k : ℝ) ^ 2 * expect (fun σ => if InWindow q k σ i then (1 : ℝ) else 0) +
        2 * (sOf q k : ℝ) ^ 2 * bPar c₁ n i * rhoW n i +
          bPar c₁ n i ^ 2 * (sOf q k : ℝ) ^ 2 * rhoW n i ^ 2 := by
  set s : ℝ := (sOf q k : ℝ)
  set B := bPar c₁ n i
  set ρ := rhoW n i
  have hB0 : 0 ≤ B := bPar_nonneg hc
  have hs0 : 0 ≤ s := Nat.cast_nonneg _
  set g : Equiv.Perm (Fin n) → ℝ := fun σ =>
    s ^ 2 * (if InWindow q k σ i then (1 : ℝ) else 0) + 2 * s * B * (Ycnt q k i σ : ℝ) +
      B ^ 2 * ((Ycnt q k i σ : ℝ) * ((Ycnt q k i σ : ℝ) - 1)) with hg
  have hpt : ∀ σ, (if GoodG1 q c₁ σ ∧ InWindow q k σ i then (latePairs q σ k : ℝ) else 0) ≤
      g σ := by
    intro σ
    have hY0 : (0 : ℝ) ≤ Ycnt q k i σ := Nat.cast_nonneg _
    have hYY := card_mul_card_sub_one_nonneg (Ycnt q k i σ)
    have hind : (0 : ℝ) ≤ (if InWindow q k σ i then (1 : ℝ) else 0) := by
      split_ifs <;> norm_num
    split_ifs with h
    · obtain ⟨hG1, hT⟩ := h
      have hLP := latePairs_le hk.le hG1 hT hi hc
      have hm := claim_6_3_c_m hk.le hT
      have hmY : (mTop q k σ : ℝ) ≤ Ycnt q k i σ := by exact_mod_cast hm
      have hm0 : (0 : ℝ) ≤ mTop q k σ := Nat.cast_nonneg _
      have hmm : (mTop q k σ : ℝ) * ((mTop q k σ : ℝ) - 1) ≤
          (Ycnt q k i σ : ℝ) * ((Ycnt q k i σ : ℝ) - 1) := by
        rcases Nat.eq_zero_or_pos (mTop q k σ) with h0 | h0
        · rw [h0]; simpa using hYY
        · have : (1 : ℝ) ≤ mTop q k σ := by exact_mod_cast h0
          nlinarith
      simp only [hg, if_pos hT]
      have e1 : 2 * s * B * mTop q k σ ≤ 2 * s * B * Ycnt q k i σ :=
        mul_le_mul_of_nonneg_left hmY (by positivity)
      have e2 : B ^ 2 * ((mTop q k σ : ℝ) * ((mTop q k σ : ℝ) - 1)) ≤
          B ^ 2 * ((Ycnt q k i σ : ℝ) * ((Ycnt q k i σ : ℝ) - 1)) :=
        mul_le_mul_of_nonneg_left hmm (by positivity)
      linarith
    · simp only [hg]
      have : 0 ≤ 2 * s * B * (Ycnt q k i σ : ℝ) := by positivity
      have : 0 ≤ B ^ 2 * ((Ycnt q k i σ : ℝ) * ((Ycnt q k i σ : ℝ) - 1)) := by positivity
      have : 0 ≤ s ^ 2 * (if InWindow q k σ i then (1 : ℝ) else 0) := by positivity
      linarith
  refine (expect_mono hpt).trans ?_
  simp only [hg]
  rw [expect_add, expect_add, expect_smul, expect_smul, expect_smul, expect_Ycnt]
  have h2 : B ^ 2 * expect (fun σ => (Ycnt q k i σ : ℝ) * ((Ycnt q k i σ : ℝ) - 1)) ≤
      B ^ 2 * (s ^ 2 * ρ ^ 2) := mul_le_mul_of_nonneg_left (expect_YY i) (by positivity)
  nlinarith

end CCK
