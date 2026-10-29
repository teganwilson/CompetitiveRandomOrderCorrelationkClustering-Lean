module

public import RequestProject.Lemma710

/-!
# Lemma 7.6 (projected pivot cluster size is predictable)
-/

@[expose] public section

open Finset
open scoped Classical

namespace CCK

variable {n : ℕ} (G : SimpleGraph (Fin n))

/-- The event of Lemma 7.6 for a fixed vertex `v` and time `t`: `v` arrives before time `t`
(`t_v < t` in the paper's `1`-indexed convention), is a pivot, and
`p_n(v) ≥ 4 n p_t(v) / t + 2 c n ln n / t + 1`. -/
def BadPred76 (σ : Equiv.Perm (Fin n)) (v : Fin n) (t : ℕ) (c : ℝ) : Prop :=
  arrTime σ v + 1 < t ∧ IsPivot G σ v ∧
    4 * n * (pclAt G σ v t : ℝ) / t + 2 * c * n * Real.log n / t + 1 ≤ pclSize G σ v

/-- Auxiliary result for Lemma 7.6 (Section 7.3.2). -/
lemma pclSize_le_n (σ : Equiv.Perm (Fin n)) (v : Fin n) : pclSize G σ v ≤ n := by
  unfold pclSize
  exact (card_le_univ _).trans (by simp)

/-- Auxiliary result for Lemma 7.6 (Section 7.3.2). -/
lemma one_le_pclAt (σ : Equiv.Perm (Fin n)) {v : Fin n} (hv : IsPivot G σ v) {t : ℕ}
    (ht : arrTime σ v < t) : 1 ≤ pclAt G σ v t := by
  rw [pclAt_eq G σ hv ht]; omega

/-- Case `t ≤ 2 t_v` of the proof of Lemma 7.6 (via Lemma 7.7). -/
lemma lemma_7_6_case1 (v : Fin n) {j t : ℕ} (hjt : t ≤ 2 * (j + 1)) {c : ℝ} (hc : 0 < c) :
    prob (fun σ => arrTime σ v = j ∧ BadPred76 G σ v t c) ≤
      (n : ℝ) ^ (-c / 8) * prob (fun σ => arrTime σ v = j) := by
  rcases Nat.eq_zero_or_pos n with hn0 | hn0
  · subst hn0; exact absurd (Fin.isLt v) (by omega)
  have hn : (0 : ℝ) < n := by exact_mod_cast hn0
  have hL0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn0)
  set L := c * Real.log n with hLdef
  have hL : 0 ≤ L := mul_nonneg hc.le hL0
  set m : ℝ := (2 + L) * n / (j + 1) with hm
  have hmono : prob (fun σ => arrTime σ v = j ∧ BadPred76 G σ v t c) ≤
      prob (fun σ => arrTime σ v + 1 = j + 1 ∧ IsPivot G σ v ∧ m + 1 ≤ (pclSize G σ v : ℝ)) := by
    apply prob_mono
    rintro σ ⟨ha, hlt, hp, hbad⟩
    refine ⟨by omega, hp, ?_⟩
    have h1 : (1 : ℝ) ≤ pclAt G σ v t := by exact_mod_cast one_le_pclAt G σ hp (by omega)
    have ht0 : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
    have htj : (t : ℝ) ≤ 2 * (j + 1) := by exact_mod_cast hjt
    have hj1 : (0 : ℝ) < j + 1 := by positivity
    have : m ≤ 4 * n * (pclAt G σ v t : ℝ) / t + 2 * c * n * Real.log n / t := by
      rw [hm, ← add_div, div_le_div_iff₀ hj1 ht0]
      have : (2 + L) * n * t ≤ (2 + L) * n * (2 * (j + 1)) := by
        apply mul_le_mul_of_nonneg_left htj; positivity
      have h2 : (4 * n + 2 * c * n * Real.log n) * (j + 1) ≤
          (4 * n * (pclAt G σ v t : ℝ) + 2 * c * n * Real.log n) * (j + 1) := by
        apply mul_le_mul_of_nonneg_right _ hj1.le
        nlinarith
      rw [hLdef] at this
      nlinarith
    linarith
  refine hmono.trans ?_
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · -- `t_v = 1`: the event is impossible
    have : prob (fun σ => arrTime σ v + 1 = 0 + 1 ∧ IsPivot G σ v ∧
        m + 1 ≤ (pclSize G σ v : ℝ)) = 0 := by
      unfold prob
      rw [div_eq_zero_iff]; left
      simp only [Nat.cast_eq_zero, card_eq_zero, filter_eq_empty_iff, mem_univ, true_implies]
      rintro σ ⟨-, -, h⟩
      have h1 : (pclSize G σ v : ℝ) ≤ n := by exact_mod_cast pclSize_le_n G σ v
      have h2 : m = (2 + L) * n := by rw [hm]; simp
      rw [h2] at h
      nlinarith
    rw [this]; exact mul_nonneg (by positivity) (prob_nonneg _)
  have h77 := lemma_7_7 G v m (j + 1)
  refine le_trans (le_of_eq (prob_congr (fun σ => Iff.rfl))) (h77.trans ?_)
  have hprob : prob (fun σ => arrTime σ v + 1 = j + 1) = prob (fun σ => arrTime σ v = j) :=
    prob_congr (fun σ => by omega)
  rw [show ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 by push_cast; ring, hprob]
  apply mul_le_mul_of_nonneg_right _ (prob_nonneg _)
  rw [Real.rpow_def_of_pos hn]
  apply Real.exp_le_exp.2
  rcases eq_or_lt_of_le (show 1 ≤ n from hn0) with hn1 | hn1
  · subst hn1; simp
  have hn1' : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn1
    linarith
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have key : L / 8 ≤ m * (j + 1 - 1) / (n - 1) := by
    rw [hm, le_div_iff₀ hn1']
    have e : (2 + L) * n / (j + 1) * (j + 1 - 1) = (2 + L) * n * j / (j + 1) := by ring
    rw [e, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    have h1 : L / 8 * ((n : ℝ) - 1) * (j + 1) ≤ L / 8 * n * (2 * j) := by
      apply mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) (by linarith)
        (by positivity) (by positivity)
    have h2 : L / 8 * n * (2 * j) ≤ (2 + L) * n * j := by
      have : 0 ≤ (n : ℝ) * j := by positivity
      nlinarith
    linarith
  rw [hLdef] at key
  nlinarith

/-- `(t - j - 1) / (n - j - 1) ≥ t / (2n)` when `2 (j + 1) < t ≤ n`. -/
lemma ratio_shift_ge {j t : ℕ} (hjt : 2 * (j + 1) < t) (ht : t ≤ n) :
    (t : ℝ) / (2 * n) ≤ ((t : ℝ) - (j + 1 : ℕ)) / ((n : ℝ) - (j + 1 : ℕ)) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h' : (0 : ℝ) < (n : ℝ) - (j + 1 : ℕ) := by
    have : ((j + 1 : ℕ) : ℝ) < n := by exact_mod_cast (show j + 1 < n by omega)
    linarith
  have h2 : 2 * ((j + 1 : ℕ) : ℝ) < t := by exact_mod_cast hjt
  rw [div_le_div_iff₀ (by positivity) h']
  have hj0 : (0 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg _
  nlinarith

/-- Case `t > 2 t_v` of the proof of Lemma 7.6 (via the lower-tail Chernoff bound for the
hypergeometric number of early arrivals of the pivot cluster). -/
lemma lemma_7_6_case2 (hH : HypergeomChernoff) (v : Fin n) {j t : ℕ} (hjt : 2 * (j + 1) < t)
    (ht : t ≤ n) {c : ℝ} (hc : 0 < c) :
    prob (fun σ => arrTime σ v = j ∧ BadPred76 G σ v t c) ≤
      (n : ℝ) ^ (-c / 8) * prob (fun σ => arrTime σ v = j) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have ht0 : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  set A : Equiv.Perm (Fin n) → Prop := fun σ => (arrTime σ v = j ∧ IsPivot G σ v) ∧
    2 * c * n * Real.log n / t ≤ (pclSize G σ v : ℝ) - 1 with hA
  set θ : Equiv.Perm (Fin n) → ℝ := fun σ => ((pclSize G σ v : ℝ) - 1) * t / (4 * n) with hθ
  have hmono : prob (fun σ => arrTime σ v = j ∧ BadPred76 G σ v t c) ≤
      prob (fun σ => A σ ∧ ((firstSet σ t ∩ uncNbrs G σ v).card : ℝ) ≤ θ σ) := by
    apply prob_mono
    rintro σ ⟨ha, hlt, hp, hbad⟩
    rw [pclAt_eq G σ hp (by omega)] at hbad
    push_cast at hbad
    set X := ((firstSet σ t ∩ uncNbrs G σ v).card : ℝ)
    have hX : 0 ≤ X := Nat.cast_nonneg _
    have e1 : 4 * n * (1 + X) / t = 4 * n * (1 + X) * (1 / t) := by ring
    have h4 : 0 ≤ 4 * n * (1 + X) / t := by positivity
    refine ⟨⟨⟨ha, hp⟩, by linarith⟩, ?_⟩
    simp only [hθ]
    rw [le_div_iff₀ (by positivity)]
    have : 4 * n * (1 + X) ≤ ((pclSize G σ v : ℝ) - 1) * t := by
      have h5 : 4 * n * (1 + X) / t ≤ (pclSize G σ v : ℝ) - 1 := by
        have : 0 ≤ 2 * c * n * Real.log n / t := by
          have := Real.log_nonneg (show (1 : ℝ) ≤ n by exact_mod_cast (show 1 ≤ n by omega))
          positivity
        linarith
      rwa [div_le_iff₀ ht0] at h5
    nlinarith
  refine hmono.trans ?_
  have hexp : Real.exp (-(c * Real.log n) / 8) = (n : ℝ) ^ (-c / 8) := by
    rw [Real.rpow_def_of_pos hn]; congr 1; ring
  rw [← hexp]
  have hA' : prob A ≤ prob (fun σ => arrTime σ v = j) := prob_mono (fun σ h => h.1.1)
  refine le_trans ?_ (mul_le_mul_of_nonneg_left hA' (Real.exp_pos _).le)
  convert prob_cond_lower hH (j := j + 1) (by omega) ht A
    (fun σ ρ hρ h => ⟨pivotEvent_mul hρ h.1, by rw [pclSize_mul hρ h.1]; exact h.2⟩)
    (fun σ => uncNbrs G σ v)
    (fun σ ρ hρ h => uncNbrs_mul hρ h.1.1)
    (fun σ h u hu => by
      have := lt_arrTime_of_mem_uncNbrs G σ hu
      rw [h.1.1] at this; omega)
    θ
    (fun σ ρ hρ h => by simp only [hθ, pclSize_mul hρ h.1])
    (Real.exp (-(c * Real.log n) / 8)) ?_ using 2
  · convert rfl
  intro σ hσ
  simp only
  have hp := pclSize_eq G σ hσ.1.2
  set r := (uncNbrs G σ v).card
  have hr : (pclSize G σ v : ℝ) - 1 = r := by rw [hp]; push_cast; ring
  have hratio := ratio_shift_ge (n := n) hjt ht
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hμ : (r : ℝ) * t / (2 * n) ≤ (r : ℝ) * ((t : ℝ) - (j + 1 : ℕ)) / ((n : ℝ) - (j + 1 : ℕ)) := by
    rw [mul_div_assoc, mul_div_assoc]; gcongr
  refine ⟨1 / 2, by norm_num, by norm_num, ?_, ?_⟩
  · simp only [hθ, hr]
    have : (r : ℝ) * t / (4 * n) = (1 - 1 / 2) * ((r : ℝ) * t / (2 * n)) := by
      field_simp; ring
    rw [this]; gcongr
  · apply Real.exp_le_exp.2
    have h2 := hσ.2
    rw [hr] at h2
    have hcL : c * Real.log n ≤ (r : ℝ) * t / (2 * n) := by
      rw [le_div_iff₀ (by positivity)]
      rw [div_le_iff₀ ht0] at h2
      nlinarith
    rw [neg_div, neg_div, neg_le_neg_iff]
    nlinarith

/-- The per-vertex estimate of Lemma 7.6: `Pr[E_{v,t}] ≤ n^{-c/8}`. -/
lemma prob_badPred76_le (hH : HypergeomChernoff) (v : Fin n) {t : ℕ} (ht : t ≤ n) {c : ℝ}
    (hc : 0 < c) : prob (fun σ => BadPred76 G σ v t c) ≤ (n : ℝ) ^ (-c / 8) := by
  have hn0 : 0 < n := lt_of_le_of_lt (Nat.zero_le _) (Fin.isLt v)
  have hn : (0 : ℝ) < n := by exact_mod_cast hn0
  have hε : (0 : ℝ) ≤ (n : ℝ) ^ (-c / 8) := by positivity
  rw [← sum_prob_arrTime v]
  calc ∑ j ∈ range n, prob (fun σ => arrTime σ v = j ∧ BadPred76 G σ v t c)
      ≤ ∑ j ∈ range n, (n : ℝ) ^ (-c / 8) * prob (fun σ => arrTime σ v = j ∧ True) := by
        refine sum_le_sum (fun j _ => ?_)
        rw [prob_congr (P := fun σ => arrTime σ v = j ∧ True) (Q := fun σ => arrTime σ v = j)
          (fun σ => by simp)]
        by_cases hjt : j + 1 < t
        · rcases le_or_gt t (2 * (j + 1)) with h | h
          · exact lemma_7_6_case1 G v h hc
          · exact lemma_7_6_case2 G hH v h ht hc
        · have : prob (fun σ => arrTime σ v = j ∧ BadPred76 G σ v t c) = 0 := by
            unfold prob
            rw [div_eq_zero_iff]; left
            simp only [Nat.cast_eq_zero, card_eq_zero, filter_eq_empty_iff, mem_univ,
              true_implies]
            rintro σ ⟨ha, hlt, -⟩
            omega
          rw [this]; exact mul_nonneg hε (prob_nonneg _)
    _ = (n : ℝ) ^ (-c / 8) * prob (fun _ => True) := by rw [← mul_sum, sum_prob_arrTime]
    _ ≤ (n : ℝ) ^ (-c / 8) * 1 := by gcongr; exact prob_le_one _
    _ = (n : ℝ) ^ (-c / 8) := mul_one _

/-- **Lemma 7.6 (projected pivot cluster size is predictable).**  For any time `t ≤ n` and any
constant `c > 0`, the probability that some vertex `v` arrives at a time `t_v < t`, is chosen as
a pivot, and has final pivot cluster size `p_n(v) ≥ 4 n p_t(v) / t + 2 c n ln n / t + 1` is at
most `n^{2 - c/8}`.  (Times are `1`-indexed as in the paper: `t_v = arrTime σ v + 1`.)
(Assumes Fact 2.2, as the hypothesis `HypergeomChernoff`.) -/
theorem lemma_7_6 (hH : HypergeomChernoff) {t : ℕ} (ht : t ≤ n) {c : ℝ} (hc : 0 < c) :
    prob (fun σ => ∃ v, arrTime σ v + 1 < t ∧ IsPivot G σ v ∧
      4 * n * (pclAt G σ v t : ℝ) / t + 2 * c * n * Real.log n / t + 1 ≤ pclSize G σ v) ≤
      (n : ℝ) ^ (2 - c / 8) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · have : prob (fun σ : Equiv.Perm (Fin 0) => ∃ v : Fin 0, arrTime σ v + 1 < t ∧
        IsPivot G σ v ∧ 4 * (0 : ℕ) * (pclAt G σ v t : ℝ) / t +
        2 * c * (0 : ℕ) * Real.log (0 : ℕ) / t + 1 ≤ pclSize G σ v) = 0 := by
      unfold prob; simp
    rw [this]; exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hn : (0 : ℝ) < n := by exact_mod_cast hn0
  have hU := prob_exists_le (univ : Finset (Fin n)) (fun v σ => BadPred76 G σ v t c)
  refine ((prob_congr (fun σ => ?_)).trans_le hU).trans ?_
  · simp [BadPred76]
  calc ∑ v ∈ (univ : Finset (Fin n)), prob (fun σ => BadPred76 G σ v t c)
      ≤ ∑ v ∈ (univ : Finset (Fin n)), (n : ℝ) ^ (-c / 8) :=
        sum_le_sum (fun v _ => prob_badPred76_le G hH v ht hc)
    _ = (n : ℝ) ^ (1 - c / 8) := by
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, sub_eq_add_neg,
          Real.rpow_add hn, Real.rpow_one, neg_div]
    _ ≤ (n : ℝ) ^ (2 - c / 8) := by
        apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn0) (by linarith)

end CCK
