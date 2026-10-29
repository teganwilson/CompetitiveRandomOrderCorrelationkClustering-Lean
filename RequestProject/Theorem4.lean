module

public import RequestProject.Theorem4Bad
public import RequestProject.Theorem5

/-!
# Theorem 4: BALANCED PIVOT is `O(log⁴ n)`-competitive

We assemble the proof of Theorem 4: the cost of BALANCED PIVOT is at most the cost of PIVOT plus
the merging cost (cost of type (iii)); the merging cost is bounded pointwise using the Large-`U`
case (comparison with Lemma 7.5), the Small-`U` case (comparison with the clique instance of an
optimal correlation clustering, window by window), and the trivial bound `n²` on the bad events.
-/

@[expose] public section

open Finset
open scoped Classical

namespace CCK

variable {n : ℕ} (G : SimpleGraph (Fin n)) {ι : Type*} (Q : Fin n → ι) (k : ℕ)

/-- Auxiliary result for the proof of Theorem 4 (Section 7.3.4). -/
lemma sOf_mul_aOf_nonneg {ι' : Type*} (q : Fin n → ι') (hk : 0 < k) : 0 ≤ (sOf q k : ℝ) * aOf q k := by
  by_cases h : k < numCliques q
  · exact mul_nonneg (Nat.cast_nonneg _) (aOf_nonneg hk h)
  · push_neg at h
    have : sOf q k = 0 := tailSum_eq_zero h
    simp [this]

/-- The window sum of the Small-`U` case. -/
noncomputable def winSum (σ : Equiv.Perm (Fin n)) : ℝ :=
  ∑ i ∈ range (Nat.log 2 n + 1),
    90000 * Real.log n * ((n : ℝ) * Real.log n / 2 ^ i) * fWin G Q k i σ

/-- Auxiliary result for the proof of Theorem 4 (Section 7.3.4). -/
lemma winSum_nonneg (hn : 2 ≤ n) (σ : Equiv.Perm (Fin n)) : 0 ≤ winSum G Q k σ := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hl : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  exact sum_nonneg (fun i _ => mul_nonneg (by positivity) (fWin_nonneg G Q k σ i))

/-- **Pointwise bound on the merging cost (proof of Theorem 4).**  For every arrival order,
`Cost_merge ≤ n² 1_{bad} + 2400 ln n · s(J_σ) a(J_σ) + ∑_i 90000 ln n · (n ln n / 2^i) ·
|U| 1_{L_i ≤ T < H_i} 1_{G^groups}`. -/
theorem mergeCost_pointwise (hk : 0 < k) (hn : 2 ≤ n) (σ : Equiv.Perm (Fin n)) :
    (mergeCost G k σ : ℝ) ≤ (n : ℝ) ^ 2 * (if ¬ GoodAll G Q σ then 1 else 0) +
      2400 * Real.log n * ((sOf (pivotOf G σ) k : ℝ) * aOf (pivotOf G σ) k) +
      winSum G Q k σ := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hl : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  have hsa := sOf_mul_aOf_nonneg k (pivotOf G σ) hk
  have hW := winSum_nonneg G Q k hn σ
  have hind : 0 ≤ (n : ℝ) ^ 2 * (if ¬ GoodAll G Q σ then 1 else 0) := by
    split_ifs <;> positivity
  have hsa' : 0 ≤ 2400 * Real.log n * ((sOf (pivotOf G σ) k : ℝ) * aOf (pivotOf G σ) k) := by
    positivity
  by_cases hex : ∃ t, k < (pivotsUpTo G σ (t + 1)).card
  swap
  · rw [mergeCost_eq_zero_of_not G k σ hk hex]; push_cast; linarith
  by_cases hg : GoodAll G Q σ
  swap
  · have := mergeCost_le_sq G k σ
    rw [if_pos hg]; linarith
  obtain ⟨hGL, hLate, hHeavy, hGG⟩ := hg
  obtain ⟨hTn, -, -⟩ := Tk_spec G k σ hex
  by_cases hc : 24 * (S1set G k σ 60).card * thetaT G k σ < (uncovered G σ (Tk G k σ)).card
  · have := mergeCost_case1 G k σ hk hn hex hGL hLate hHeavy hc
    have e : 2400 * Real.log n * sOf (pivotOf G σ) k * aOf (pivotOf G σ) k =
        2400 * Real.log n * ((sOf (pivotOf G σ) k : ℝ) * aOf (pivotOf G σ) k) := by ring
    linarith
  · push_neg at hc
    have h2 := mergeCost_case2 G k σ hk hn hex hGL hc
    have hT1 := one_le_Tk G k σ hk hex
    set T := Tk G k σ with hTdef
    set i := Nat.log 2 T
    have hi1 : 2 ^ i ≤ T := Nat.pow_log_le_self 2 (by omega)
    have hi2 : T < 2 ^ (i + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
    have hin : i ≤ Nat.log 2 n := Nat.log_mono_right hTn.le
    have hWin : InWin G k i σ := ⟨hi1, lt_min hi2 hTn, hTn⟩
    have hf : fWin G Q k i σ = ((uncovered G σ T).card : ℝ) := by
      unfold fWin; rw [if_pos ⟨hWin, hGG⟩]
    have hθ : thetaT G k σ ≤ (n : ℝ) * Real.log n / 2 ^ i := by
      unfold thetaT
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact_mod_cast hi1
    have hterm : (mergeCost G k σ : ℝ) ≤
        90000 * Real.log n * ((n : ℝ) * Real.log n / 2 ^ i) * fWin G Q k i σ := by
      rw [hf]
      refine h2.trans ?_
      have hU : (0 : ℝ) ≤ (uncovered G σ T).card := Nat.cast_nonneg _
      have := mul_le_mul_of_nonneg_left hθ (by positivity : (0 : ℝ) ≤ 90000 * Real.log n)
      exact mul_le_mul_of_nonneg_right this hU
    have hsingle : 90000 * Real.log n * ((n : ℝ) * Real.log n / 2 ^ i) * fWin G Q k i σ ≤
        winSum G Q k σ := by
      unfold winSum
      apply single_le_sum (f := fun i => 90000 * Real.log n * ((n : ℝ) * Real.log n / 2 ^ i) *
        fWin G Q k i σ) (fun j _ => mul_nonneg (by positivity) (fWin_nonneg G Q k σ j))
        (mem_range.2 (by omega))
    linarith

/-! ### Taking expectations -/

/-- Auxiliary result for the proof of Theorem 4 (Section 7.3.4). -/
lemma card_missPairs_le : ((missPairs G Q).card : ℝ) ≤ 2 * cost G Q := by
  have h : (missPairs G Q).card ≤ disagreeCount G Q := by
    apply card_le_card
    intro x hx
    obtain ⟨h1, h2, h3⟩ := (mem_filter.1 hx).2
    exact mem_filter.2 ⟨mem_univ _, h1, Or.inr ⟨h3, h2⟩⟩
  rw [← two_mul_cost] at h
  exact_mod_cast h

/-- **(30)**: `K₀ = s₀ a₀ + 2 e_m ≤ 10 Cost(OPT_k)` for an optimal correlation clustering `Q`. -/
lemma K0_le (Q : Fin n → Fin n) (hQ : cost G Q = optCC G) (hk : 0 < k) :
    (sOf Q k : ℝ) * aOf Q k + (missPairs G Q).card ≤ 10 * optK G k := by
  haveI : Nonempty (Fin n → Fin k) := ⟨fun _ => ⟨0, hk⟩⟩
  have h1 := (lemma_3_4 Q hk).1
  have h2 : (optK (cliqueGraph Q) k : ℝ) ≤ optK G k + cost G Q := by
    exact_mod_cast optK_cliqueGraph_le G Q k
  have h3 : (optCC G : ℝ) ≤ optK G k := by exact_mod_cast optCC_le_optK G k
  have h4 := card_missPairs_le G Q
  have hQR : (cost G Q : ℝ) = optCC G := by exact_mod_cast hQ
  rw [hQR] at h2 h4
  linarith

/-- **Expected merging cost (proof of Theorem 4).** -/
theorem expect_mergeCost_le (hH : HypergeomChernoff) (hPiv : PivotThreeApprox) (hk : 0 < k)
    (hn : 2 ≤ n) (Q : Fin n → Fin n) (hQ : cost G Q = optCC G) :
    expect (fun σ => (mergeCost G k σ : ℝ)) ≤ 5 + 38400 * Real.log n * optK G k +
      ((Nat.log 2 n : ℝ) + 1) * (180000 * Real.log n ^ 2 * (4 + 48 * Real.log n) *
        (10 * optK G k)) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hl : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  have hE := expect_mono (mergeCost_pointwise G Q k hk hn)
  rw [expect_add, expect_add, expect_smul, expect_smul, expect_indicator] at hE
  have hbad := bad_prob_le G Q hH hn
  have h75 := lemma_7_5 hPiv G hk
  have hK := K0_le G k Q hQ hk
  have hK0 : 0 ≤ (sOf Q k : ℝ) * aOf Q k + (missPairs G Q).card :=
    add_nonneg (sOf_mul_aOf_nonneg k Q hk) (Nat.cast_nonneg _)
  have hwin : expect (winSum G Q k) ≤ ((Nat.log 2 n : ℝ) + 1) *
      (180000 * Real.log n ^ 2 * (4 + 48 * Real.log n) *
        ((sOf Q k : ℝ) * aOf Q k + (missPairs G Q).card)) := by
    unfold winSum
    rw [expect_sum]
    have hper : ∀ i ∈ range (Nat.log 2 n + 1), expect (fun σ => 90000 * Real.log n *
        ((n : ℝ) * Real.log n / 2 ^ i) * fWin G Q k i σ) ≤
        180000 * Real.log n ^ 2 * (4 + 48 * Real.log n) *
          ((sOf Q k : ℝ) * aOf Q k + (missPairs G Q).card) := by
      intro i _
      rw [expect_smul]
      have h1 := expect_fWin_le (G := G) (Q := Q) hk hn i
      have h2 := kappa_mul_rho hn i
      have hc : 0 ≤ 90000 * Real.log n * ((n : ℝ) * Real.log n / 2 ^ i) := by positivity
      refine (mul_le_mul_of_nonneg_left h1 hc).trans ?_
      have e : 90000 * Real.log n * ((n : ℝ) * Real.log n / 2 ^ i) *
          (rhoW n i * (4 + 48 * Real.log n) * ((sOf Q k : ℝ) * aOf Q k + (missPairs G Q).card)) =
          15000 * Real.log n * (6 * n * Real.log n / 2 ^ i * rhoW n i) *
          ((4 + 48 * Real.log n) * ((sOf Q k : ℝ) * aOf Q k + (missPairs G Q).card)) := by ring
      rw [e]
      have hA : 0 ≤ (4 + 48 * Real.log n) * ((sOf Q k : ℝ) * aOf Q k + (missPairs G Q).card) := by
        positivity
      have := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 15000 * Real.log n)
      have := mul_le_mul_of_nonneg_right this hA
      nlinarith
    refine (sum_le_sum hper).trans (le_of_eq ?_)
    rw [sum_const, card_range, nsmul_eq_mul]; push_cast; ring
  have hwin' : ((Nat.log 2 n : ℝ) + 1) * (180000 * Real.log n ^ 2 * (4 + 48 * Real.log n) *
        ((sOf Q k : ℝ) * aOf Q k + (missPairs G Q).card)) ≤
      ((Nat.log 2 n : ℝ) + 1) * (180000 * Real.log n ^ 2 * (4 + 48 * Real.log n) *
        (10 * optK G k)) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact mul_le_mul_of_nonneg_left hK (by positivity)
  have h75' : 2400 * Real.log n * expect (fun σ =>
      (sOf (pivotOf G σ) k : ℝ) * aOf (pivotOf G σ) k) ≤ 2400 * Real.log n * (16 * optK G k) :=
    mul_le_mul_of_nonneg_left h75 (by positivity)
  linarith

/-! ### The final bound -/

/-- If `Cost(OPT_k) = 0`, the input is a union of at most `k` disjoint cliques and PIVOT creates at
most `k` pivots (end of the proof of Theorem 4). -/
lemma not_many_pivots_of_optK_zero (hk : 0 < k) (h0 : optK G k = 0) (σ : Equiv.Perm (Fin n)) :
    ¬ ∃ t, k < (pivotsUpTo G σ (t + 1)).card := by
  haveI : Nonempty (Fin n → Fin k) := ⟨fun _ => ⟨0, hk⟩⟩
  obtain ⟨C, hC⟩ := exists_optK G k
  rw [h0] at hC
  have hD : disagreeCount G C = 0 := by rw [← two_mul_cost, hC]
  have hno : ∀ u v, ¬ Disagree G C u v := by
    intro u v huv
    have : (u, v) ∈ univ.filter (fun p : Fin n × Fin n => Disagree G C p.1 p.2) :=
      mem_filter.2 ⟨mem_univ _, huv⟩
    unfold disagreeCount at hD
    rw [card_eq_zero] at hD
    rw [hD] at this
    exact absurd this (notMem_empty _)
  have hcard : (pivotsUpTo G σ n).card ≤ k := by
    have := card_le_card_of_injOn C (s := pivotsUpTo G σ n) (t := (univ : Finset (Fin k)))
      (fun _ _ => mem_coe.2 (mem_univ _)) (by
        intro u hu v hv he
        by_contra hne
        exact hno u v ⟨hne, Or.inr ⟨not_adj_of_isPivot G σ hu hv, he⟩⟩)
    simpa using this
  rintro ⟨t, ht⟩
  have : (pivotsUpTo G σ (t + 1)).card ≤ (pivotsUpTo G σ n).card := by
    rcases le_or_gt (t + 1) n with h | h
    · exact card_le_card (pivotsUpTo_mono G σ h)
    · rw [pivotsUpTo_eq_of_ge G σ h.le]
  omega

/-- Auxiliary result for the proof of Theorem 4 (Section 7.3.4). -/
lemma theorem4_numeric {L N O c E : ℝ} (hL : 0.69 ≤ L) (hN : N ≤ 3 * L) (_hN0 : 0 ≤ N)
    (hO : 1 ≤ O) (hc : 0 ≤ c) (hcO : c ≤ O)
    (hE : E ≤ 5 + 38400 * L * O + N * (180000 * L ^ 2 * (4 + 48 * L) * (10 * O))) :
    3 * c + E ≤ 3 * 10 ^ 8 * L ^ 4 * O := by
  have hL0 : 0 ≤ L := by linarith
  have hO0 : 0 ≤ O := by linarith
  have hL2 : 0.4761 ≤ L ^ 2 := by nlinarith
  have hL3 : 0.3285 ≤ L ^ 3 := by nlinarith
  have hL4 : 0.2266 ≤ L ^ 4 := by nlinarith
  have t1 : N * (180000 * L ^ 2 * (4 + 48 * L) * (10 * O)) ≤ 291600000 * L ^ 4 * O := by
    have h1 : 4 + 48 * L ≤ 54 * L := by linarith
    have h2 : 0 ≤ 180000 * L ^ 2 * (10 * O) := by positivity
    have h3 : N * (180000 * L ^ 2 * (4 + 48 * L) * (10 * O)) ≤
        (3 * L) * (180000 * L ^ 2 * (54 * L) * (10 * O)) := by
      apply mul_le_mul hN _ (by positivity) (by positivity)
      have := mul_le_mul_of_nonneg_left h1 h2
      nlinarith
    have e : (3 * L) * (180000 * L ^ 2 * (54 * L) * (10 * O)) = 291600000 * L ^ 4 * O := by ring
    linarith
  have t2 : 38400 * L * O ≤ 117000 * L ^ 4 * O := by
    have : 0.3285 * L ≤ L ^ 4 := by
      have e : L ^ 4 = L * L ^ 3 := by ring
      rw [e]; nlinarith
    have : 38400 * L ≤ 117000 * L ^ 4 := by nlinarith
    exact mul_le_mul_of_nonneg_right this hO0
  have t3 : 3 * c + 5 ≤ 36 * L ^ 4 * O := by
    have : 8 * O ≤ 36 * L ^ 4 * O := by nlinarith
    linarith
  nlinarith

/-- **Theorem 4.**  BALANCED PIVOT has a competitive ratio of `O(log⁴ n)` for online correlation
k-clustering under random-order vertex arrivals: for every graph on `n ≥ 2` vertices and every
`k ≥ 1`, the expected cost of BALANCED PIVOT is at most `3·10⁸ (ln n)⁴ Cost(OPT_k)`.

(Assumes Fact 2.2, as the hypothesis `HypergeomChernoff`, and the 3-approximation guarantee of
PIVOT [ACN05], as the hypothesis `PivotThreeApprox`.) -/
theorem theorem_4 (hH : HypergeomChernoff) (hPiv : PivotThreeApprox) (hn : 2 ≤ n)
    (G : SimpleGraph (Fin n)) {k : ℕ} (hk : 0 < k) :
    balancedPivotExpCost G k ≤ 3 * 10 ^ 8 * Real.log n ^ 4 * optK G k := by
  haveI : Nonempty (Fin n → Fin k) := ⟨fun _ => ⟨0, hk⟩⟩
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hcost : balancedPivotExpCost G k ≤ expect (fun σ => (cost G (pivotOf G σ) : ℝ)) +
      expect (fun σ => (mergeCost G k σ : ℝ)) := by
    unfold balancedPivotExpCost
    rw [← expect_add]
    apply expect_mono
    intro σ
    exact_mod_cast cost_bp_le G k σ
  have hP := hPiv n G
  have hCC : (optCC G : ℝ) ≤ optK G k := by exact_mod_cast optCC_le_optK G k
  have hCC0 : (0 : ℝ) ≤ optCC G := Nat.cast_nonneg _
  rcases Nat.eq_zero_or_pos (optK G k) with h0 | hpos
  · -- `Cost(OPT_k) = 0`: no merging cost
    have hm : expect (fun σ => (mergeCost G k σ : ℝ)) ≤ 0 := by
      have : expect (fun σ => (mergeCost G k σ : ℝ)) ≤
          expect (fun _ : Equiv.Perm (Fin n) => (0 : ℝ)) := by
        apply expect_mono
        intro σ
        rw [mergeCost_eq_zero_of_not G k σ hk (not_many_pivots_of_optK_zero G k hk h0 σ)]
        simp
      rwa [expect_const] at this
    rw [h0] at hCC ⊢
    push_cast at hCC ⊢
    linarith
  · obtain ⟨Q, hQ⟩ := exists_optCC G
    have hM := expect_mergeCost_le G k hH hPiv hk hn Q hQ
    have hl2 := Real.log_two_gt_d9
    have hlog : (0.69 : ℝ) ≤ Real.log n := by
      have := Real.log_le_log (by norm_num) hnR; linarith
    have hO : (1 : ℝ) ≤ optK G k := by exact_mod_cast hpos
    have := theorem4_numeric hlog (natLog_le_three_log hn) (by positivity) hO hCC0 hCC hM
    linarith

end CCK
