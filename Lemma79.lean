module

public import RequestProject.Lemma77

/-!
# Lemma 7.9 (pivot clusters with many early arrivals remain large)
-/

@[expose] public section

open Finset
open scoped Classical

namespace CCK

variable {n : ℕ} (G : SimpleGraph (Fin n))

/-- Decomposing an event according to the arrival time of a vertex `v`. -/
lemma sum_prob_arrTime (v : Fin n) (B : Equiv.Perm (Fin n) → Prop) [DecidablePred B] :
    ∑ j ∈ range n, prob (fun σ => arrTime σ v = j ∧ B σ) = prob B := by
  unfold prob
  rw [← sum_div]
  congr 1
  rw [card_eq_sum_card_fiberwise (f := fun σ => arrTime σ v) (t := range n)
    (fun σ _ => by simp [arrTime])]
  push_cast
  refine sum_congr rfl (fun j _ => ?_)
  congr 2
  ext σ; simp [and_comm]

/-- If `P[A_j ∧ E] ≤ ε P[A_j]` for the events `A_j = {t_v = j} ∧ B`, then `P[E ∧ B] ≤ ε`. -/
lemma prob_le_of_arrTime_cond (v : Fin n) (B E : Equiv.Perm (Fin n) → Prop) [DecidablePred B]
    [DecidablePred E] {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ j < n, prob (fun σ => (arrTime σ v = j ∧ B σ) ∧ E σ) ≤
      ε * prob (fun σ => arrTime σ v = j ∧ B σ)) :
    prob (fun σ => B σ ∧ E σ) ≤ ε := by
  calc prob (fun σ => B σ ∧ E σ)
      = ∑ j ∈ range n, prob (fun σ => arrTime σ v = j ∧ B σ ∧ E σ) := by
        rw [← sum_prob_arrTime v (fun σ => B σ ∧ E σ)]
    _ ≤ ∑ j ∈ range n, ε * prob (fun σ => arrTime σ v = j ∧ B σ) := by
        refine sum_le_sum (fun j hj => ?_)
        refine le_trans (le_of_eq ?_) (h j (mem_range.1 hj))
        exact prob_congr (fun σ => by simp [and_assoc])
    _ = ε * prob B := by rw [← mul_sum, sum_prob_arrTime]
    _ ≤ ε * 1 := by gcongr; exact prob_le_one _
    _ = ε := mul_one ε

/-- The Chernoff estimate used in the proof of Lemma 7.9: if `0 ≤ μ ≤ L / 2` and `L > 0`, then
`P[Y ≥ L] ≤ exp(-L/6)` follows from `prob_cond_upper` (with `δ = L/μ - 1 ≥ 1`). -/
lemma chernoff_choice_710 {μ L : ℝ} (hμ : 0 ≤ μ) (hL : 0 < L) (hμL : 2 * μ ≤ L) :
    (∃ δ : ℝ, 0 < δ ∧ (1 + δ) * μ ≤ L ∧ Real.exp (-(δ ^ 2 * μ) / (2 + δ)) ≤ Real.exp (-L / 6)) ∨
      (μ = 0 ∧ 0 < L) := by
  rcases eq_or_lt_of_le hμ with h0 | hpos
  · exact Or.inr ⟨h0.symm, hL⟩
  left
  have hδ1 : 1 ≤ L / μ - 1 := by rw [le_sub_iff_add_le, le_div_iff₀ hpos]; linarith
  refine ⟨L / μ - 1, by linarith, ?_, ?_⟩
  · have : (1 + (L / μ - 1)) * μ = L := by field_simp; ring
    rw [this]
  · apply Real.exp_le_exp.2
    set δ := L / μ - 1 with hδ
    have hδμ : δ * μ = L - μ := by rw [hδ]; field_simp
    have h1 : δ * μ / 3 ≤ δ ^ 2 * μ / (2 + δ) := by
      rw [div_le_div_iff₀ (by norm_num) (by linarith)]
      have : 0 ≤ δ * μ * (δ - 1) := by
        apply mul_nonneg (mul_nonneg (by linarith) hpos.le) (by linarith)
      nlinarith
    rw [neg_div, neg_div, neg_le_neg_iff]
    linarith

/-- The conditional estimate behind Lemma 7.9: conditioned on `v` arriving at time `j < t` and
being a pivot with final cluster size `p_n(v) < c n ln n / (2t)`, the probability that
`p_t(v) ≥ c ln n + 1` is at most `n^{-c/6}`. -/
lemma lemma_7_10_cond (hH : HypergeomChernoff) (v : Fin n) {j t : ℕ} (hjt : j < t) (ht : t ≤ n)
    {c : ℝ} (hc : 0 < c) :
    prob (fun σ => (arrTime σ v = j ∧ IsPivot G σ v ∧
        (pclSize G σ v : ℝ) < c * n * Real.log n / (2 * t)) ∧
      c * Real.log n + 1 ≤ pclAt G σ v t) ≤
      (n : ℝ) ^ (-c / 6) * prob (fun σ => arrTime σ v = j ∧ IsPivot G σ v ∧
        (pclSize G σ v : ℝ) < c * n * Real.log n / (2 * t)) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have htR : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  set A : Equiv.Perm (Fin n) → Prop := fun σ => arrTime σ v = j ∧ IsPivot G σ v ∧
    (pclSize G σ v : ℝ) < c * n * Real.log n / (2 * t) with hA
  have hmono : prob (fun σ => A σ ∧ c * Real.log n + 1 ≤ pclAt G σ v t) ≤
      prob (fun σ => A σ ∧ (fun _ => c * Real.log n) σ ≤
        ((firstSet σ t ∩ uncNbrs G σ v).card : ℝ)) := by
    apply prob_mono
    rintro σ ⟨hAσ, hle⟩
    refine ⟨hAσ, ?_⟩
    rw [pclAt_eq G σ hAσ.2.1 (by rw [hAσ.1]; exact hjt)] at hle
    push_cast at hle
    show c * Real.log n ≤ _
    linarith
  refine hmono.trans ?_
  have hexp : Real.exp (-(c * Real.log n) / 6) = (n : ℝ) ^ (-c / 6) := by
    rw [Real.rpow_def_of_pos hn]; congr 1; ring
  rw [← hexp]
  convert prob_cond_upper hH (j := j + 1) (by omega) ht A
    (fun σ ρ hρ h => ⟨(pivotEvent_mul hρ ⟨h.1, h.2.1⟩).1, (pivotEvent_mul hρ ⟨h.1, h.2.1⟩).2,
      by rw [pclSize_mul hρ ⟨h.1, h.2.1⟩]; exact h.2.2⟩)
    (fun σ => uncNbrs G σ v)
    (fun σ ρ hρ h => uncNbrs_mul hρ h.1)
    (fun σ h u hu => by
      have := lt_arrTime_of_mem_uncNbrs G σ hu
      rw [h.1] at this; omega)
    (fun _ => c * Real.log n)
    (fun σ ρ hρ h => rfl)
    (Real.exp (-(c * Real.log n) / 6)) (Real.exp_pos _).le ?_ using 2
  · convert rfl
  intro σ hσ
  simp only
  have hp := pclSize_eq G σ hσ.2.1
  set r := (uncNbrs G σ v).card
  have hr : (r : ℝ) < c * n * Real.log n / (2 * t) := by
    have := hσ.2.2; rw [hp] at this; push_cast at this; linarith
  have hL : 0 < c * Real.log n := by
    have h1 : (1 : ℝ) ≤ pclSize G σ v := by
      rw [hp]; push_cast; linarith [(Nat.cast_nonneg r : (0:ℝ) ≤ r)]
    have h2 := hσ.2.2
    have h3 : 0 < c * n * Real.log n / (2 * t) := by linarith
    have h4 : 0 < c * n * Real.log n := by
      have := (div_pos_iff.1 h3)
      rcases this with ⟨h, _⟩ | ⟨_, h⟩
      · exact h
      · linarith
    have : c * n * Real.log n = (c * Real.log n) * n := by ring
    rw [this] at h4
    exact pos_of_mul_pos_left h4 hn.le
  have hμ0 : 0 ≤ (r : ℝ) * ((t : ℝ) - (j + 1 : ℕ)) / ((n : ℝ) - (j + 1 : ℕ)) := by
    have h1 : ((j + 1 : ℕ) : ℝ) ≤ t := by exact_mod_cast (show j + 1 ≤ t by omega)
    have h2 : ((j + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast (show j + 1 ≤ n by omega)
    apply div_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith)) (by linarith)
  have hμle : 2 * ((r : ℝ) * ((t : ℝ) - (j + 1 : ℕ)) / ((n : ℝ) - (j + 1 : ℕ))) ≤
      c * Real.log n := by
    have hratio := ratio_shift_le (n := n) hjt ht
    have hrat0 : 0 ≤ ((t : ℝ) - (j + 1 : ℕ)) / ((n : ℝ) - (j + 1 : ℕ)) := by
      have h1 : ((j + 1 : ℕ) : ℝ) ≤ t := by exact_mod_cast (show j + 1 ≤ t by omega)
      have h2 : ((j + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast (show j + 1 ≤ n by omega)
      apply div_nonneg <;> linarith
    rw [mul_div_assoc]
    calc 2 * ((r : ℝ) * (((t : ℝ) - (j + 1 : ℕ)) / ((n : ℝ) - (j + 1 : ℕ))))
        ≤ 2 * ((c * n * Real.log n / (2 * t)) * (t / n)) := by gcongr
      _ = c * Real.log n := by field_simp
  exact chernoff_choice_710 hμ0 hL hμle

/-- **Lemma 7.9 (pivot clusters with many early arrivals remain large).**  For any `c > 0`,
the probability that some pivot cluster has at least `c ln n + 1` vertices at time `2^i`, yet
has final size less than `c n ln n / 2^{i+1}`, for some `i` with `2^i ≤ n` (there are
`⌊log₂ n⌋ + 1` such `i`), is at most `n (⌊log₂ n⌋ + 1) / n^{c/6}`.  (The paper assumes `c > 6`,
which is only needed for the bound to be meaningful, and writes `n log n / n^{c/6}`.)
(Assumes Fact 2.2, as the hypothesis `HypergeomChernoff`.) -/
theorem lemma_7_10 (hH : HypergeomChernoff) {c : ℝ} (hc : 0 < c) :
    prob (fun σ => ∃ v, ∃ i ∈ range (Nat.log 2 n + 1), IsPivot G σ v ∧
      c * Real.log n + 1 ≤ pclAt G σ v (2 ^ i) ∧
      (pclSize G σ v : ℝ) < c * n * Real.log n / 2 ^ (i + 1)) ≤
      n * (Nat.log 2 n + 1) / (n : ℝ) ^ (c / 6) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · have : prob (fun σ : Equiv.Perm (Fin 0) => ∃ v : Fin 0, ∃ i ∈ range (Nat.log 2 0 + 1),
        IsPivot G σ v ∧ c * Real.log (0 : ℕ) + 1 ≤ pclAt G σ v (2 ^ i) ∧
        (pclSize G σ v : ℝ) < c * (0 : ℕ) * Real.log (0 : ℕ) / 2 ^ (i + 1)) = 0 := by
      unfold prob; simp
    rw [this]; simp
  have hn : (0 : ℝ) < n := by exact_mod_cast hn0
  have hL0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn0)
  have hε : (0 : ℝ) ≤ (n : ℝ) ^ (-c / 6) := by positivity
  have hper : ∀ v : Fin n, ∀ i ∈ range (Nat.log 2 n + 1),
      prob (fun σ => IsPivot G σ v ∧ c * Real.log n + 1 ≤ pclAt G σ v (2 ^ i) ∧
        (pclSize G σ v : ℝ) < c * n * Real.log n / 2 ^ (i + 1)) ≤ (n : ℝ) ^ (-c / 6) := by
    intro v i hi
    set t := 2 ^ i with ht
    have htn : t ≤ n := by
      have := Nat.pow_log_le_self 2 (show n ≠ 0 by omega)
      exact le_trans (Nat.pow_le_pow_right (by norm_num) (by simpa [Nat.lt_succ_iff] using hi)) this
    have h2t : (2 : ℝ) ^ (i + 1) = 2 * (t : ℝ) := by rw [ht]; push_cast; ring
    have key := prob_le_of_arrTime_cond v
      (fun σ => IsPivot G σ v ∧ (pclSize G σ v : ℝ) < c * n * Real.log n / (2 * t))
      (fun σ => c * Real.log n + 1 ≤ pclAt G σ v t) hε (by
        intro j hj
        rcases lt_or_ge j t with hjt | hjt
        · refine le_trans (le_of_eq (prob_congr (fun σ => by tauto))) ((lemma_7_10_cond G hH v hjt
            htn hc).trans (le_of_eq ?_))
          congr 1
        · have : prob (fun σ => (arrTime σ v = j ∧ IsPivot G σ v ∧
              (pclSize G σ v : ℝ) < c * n * Real.log n / (2 * t)) ∧
              c * Real.log n + 1 ≤ pclAt G σ v t) = 0 := by
            unfold prob
            rw [div_eq_zero_iff]; left
            simp only [Nat.cast_eq_zero, card_eq_zero, filter_eq_empty_iff, mem_univ, true_implies]
            rintro σ ⟨⟨ha, -, -⟩, hle⟩
            have h0 : pclAt G σ v t = 0 := by
              unfold pclAt
              rw [card_eq_zero, eq_empty_iff_forall_notMem]
              intro u hu
              simp only [mem_inter, firstSet, mem_filter, mem_univ, true_and] at hu
              have := arrTime_pivotOf_le G σ u
              rw [hu.2] at this
              omega
            rw [h0] at hle; push_cast at hle
            have : 0 ≤ c * Real.log n := mul_nonneg hc.le hL0
            linarith
          rw [this]; exact mul_nonneg hε (prob_nonneg _))
    refine le_trans (le_of_eq (prob_congr (fun σ => ?_))) key
    rw [h2t]; tauto
  set F : Fin n × ℕ → Equiv.Perm (Fin n) → Prop := fun p σ => IsPivot G σ p.1 ∧
    c * Real.log n + 1 ≤ pclAt G σ p.1 (2 ^ p.2) ∧
    (pclSize G σ p.1 : ℝ) < c * n * Real.log n / 2 ^ (p.2 + 1) with hF
  have hU := prob_exists_le ((univ : Finset (Fin n)) ×ˢ range (Nat.log 2 n + 1)) F
  have hval : ∑ p ∈ (univ : Finset (Fin n)) ×ˢ range (Nat.log 2 n + 1), (n : ℝ) ^ (-c / 6) =
      n * (Nat.log 2 n + 1) / (n : ℝ) ^ (c / 6) := by
    rw [sum_const, card_product, card_univ, Fintype.card_fin, card_range, nsmul_eq_mul,
      neg_div, Real.rpow_neg hn.le]
    push_cast
    field_simp
  refine ((prob_congr (fun σ => ?_)).trans_le hU).trans
    (le_trans (sum_le_sum (fun p hp => ?_)) (le_of_eq hval))
  · simp only [hF, mem_product, mem_univ, true_and, Prod.exists]
  · rw [mem_product] at hp
    exact (prob_congr (fun σ => Iff.rfl)).trans_le (hper p.1 p.2 hp.2)

end CCK
