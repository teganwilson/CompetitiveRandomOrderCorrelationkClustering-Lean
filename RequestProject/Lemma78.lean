module

public import RequestProject.PivotLoad

/-!
# Lemma 7.8 (pivot cluster size at an arbitrary instant)
-/

@[expose] public section

open Finset
open scoped Classical

namespace CCK

variable {n : ℕ} (G : SimpleGraph (Fin n))

/-- `(t - j - 1) / (n - j - 1) ≤ t / n` for `j < t ≤ n`. -/
lemma ratio_shift_le {j t : ℕ} (hjt : j < t) (ht : t ≤ n) :
    ((t : ℝ) - (j + 1 : ℕ)) / ((n : ℝ) - (j + 1 : ℕ)) ≤ (t : ℝ) / n := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rcases eq_or_lt_of_le (show j + 1 ≤ n by omega) with h | h
  · rw [h, sub_self, div_zero]; positivity
  · have h' : (0 : ℝ) < (n : ℝ) - (j + 1 : ℕ) := by
      have : ((j + 1 : ℕ) : ℝ) < n := by exact_mod_cast h
      linarith
    rw [div_le_div_iff₀ h' hn]
    have htn : (t : ℝ) ≤ n := by exact_mod_cast ht
    push_cast
    nlinarith

/-- The Chernoff estimate used in the proof of Lemma 7.8: for `μ ≥ 0`, `L ≥ 0` (with `L = c ln n`)
and a threshold `θ ≥ 2μ + L` with `θ > 0`, one of the two alternatives of `prob_cond_upper` holds
with bound `exp(-L/3)`. -/
lemma chernoff_choice_upper {μ L θ : ℝ} (hμ : 0 ≤ μ) (hL : 0 ≤ L) (hθ : 2 * μ + L ≤ θ)
    (hθ0 : 0 < θ) :
    (∃ δ : ℝ, 0 < δ ∧ (1 + δ) * μ ≤ θ ∧ Real.exp (-(δ ^ 2 * μ) / (2 + δ)) ≤ Real.exp (-L / 3)) ∨
      (μ = 0 ∧ 0 < θ) := by
  rcases eq_or_lt_of_le hμ with h0 | hpos
  · exact Or.inr ⟨h0.symm, hθ0⟩
  left
  rcases le_or_gt L μ with hLμ | hLμ
  · refine ⟨1, one_pos, by linarith, ?_⟩
    apply Real.exp_le_exp.2
    rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
    nlinarith
  · have hL0 : 0 < L := by linarith
    refine ⟨L / μ, by positivity, ?_, ?_⟩
    · have : (1 + L / μ) * μ = μ + L := by field_simp
      rw [this]; linarith
    · apply Real.exp_le_exp.2
      have e : (L / μ) ^ 2 * μ / (2 + L / μ) = L ^ 2 / (2 * μ + L) := by
        field_simp
      rw [neg_div, e, neg_div, neg_le_neg_iff, div_le_div_iff₀ (by norm_num) (by positivity)]
      nlinarith

/-- **Lemma 7.8 (pivot cluster size at an arbitrary instant), corrected.**  Let `v` be a vertex,
`j` a (`0`-indexed) arrival time and `t > j` (i.e. `t ≥ t_v` in the paper's `1`-indexed
convention).  Conditioned on `v` arriving at time `j` and being a pivot, the probability that
`p_t(v) > 1 + 2 p_n(v) t / n + c ln n` is at most `n^{-c/3}`, for any constant `c > 0`.
The conditional probability is written as `Pr[A ∧ E] ≤ n^{-c/3} Pr[A]`.
(The paper states the bound `1 + p_n(v) t / n + c ln n`, which is false in general; see the module
docstring.)  (Assumes Fact 2.2, as the hypothesis `HypergeomChernoff`.) -/
theorem lemma_7_8 (hH : HypergeomChernoff) (v : Fin n) {j t : ℕ} (hjt : j < t) (ht : t ≤ n)
    {c : ℝ} (hc : 0 < c) :
    prob (fun σ => (arrTime σ v = j ∧ IsPivot G σ v) ∧
      1 + 2 * (pclSize G σ v : ℝ) * t / n + c * Real.log n < pclAt G σ v t) ≤
      (n : ℝ) ^ (-c / 3) * prob (fun σ => arrTime σ v = j ∧ IsPivot G σ v) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hL : 0 ≤ c * Real.log n :=
    mul_nonneg hc.le (Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega)))
  set A : Equiv.Perm (Fin n) → Prop := fun σ => arrTime σ v = j ∧ IsPivot G σ v with hA
  set θ : Equiv.Perm (Fin n) → ℝ := fun σ => 2 * (pclSize G σ v : ℝ) * t / n + c * Real.log n
    with hθ
  have hmono : prob (fun σ => A σ ∧
      1 + 2 * (pclSize G σ v : ℝ) * t / n + c * Real.log n < pclAt G σ v t) ≤
      prob (fun σ => A σ ∧ θ σ ≤ ((firstSet σ t ∩ uncNbrs G σ v).card : ℝ)) := by
    apply prob_mono
    rintro σ ⟨hAσ, hlt⟩
    refine ⟨hAσ, ?_⟩
    rw [pclAt_eq G σ hAσ.2 (by rw [hAσ.1]; exact hjt)] at hlt
    push_cast at hlt
    simp only [hθ]; linarith
  refine hmono.trans ?_
  have hexp : Real.exp (-(c * Real.log n) / 3) = (n : ℝ) ^ (-c / 3) := by
    rw [Real.rpow_def_of_pos hn]; congr 1; ring
  rw [← hexp]
  convert prob_cond_upper hH (j := j + 1) (by omega) ht A
    (fun σ ρ hρ h => pivotEvent_mul hρ h) (fun σ => uncNbrs G σ v)
    (fun σ ρ hρ h => uncNbrs_mul hρ h.1)
    (fun σ h u hu => by
      have := lt_arrTime_of_mem_uncNbrs G σ hu
      rw [h.1] at this; omega)
    θ
    (fun σ ρ hρ h => by simp only [hθ, pclSize_mul hρ h])
    (Real.exp (-(c * Real.log n) / 3)) (Real.exp_pos _).le ?_ using 2
  · convert rfl
  intro σ hσ
  simp only
  have hp := pclSize_eq G σ hσ.2
  set r := (uncNbrs G σ v).card
  have hμ0 : 0 ≤ (r : ℝ) * ((t : ℝ) - (j + 1 : ℕ)) / ((n : ℝ) - (j + 1 : ℕ)) := by
    have h1 : ((j + 1 : ℕ) : ℝ) ≤ t := by exact_mod_cast (show j + 1 ≤ t by omega)
    have h2 : ((j + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast (show j + 1 ≤ n by omega)
    apply div_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith)) (by linarith)
  have hμle : (r : ℝ) * ((t : ℝ) - (j + 1 : ℕ)) / ((n : ℝ) - (j + 1 : ℕ)) ≤
      (pclSize G σ v : ℝ) * t / n := by
    rw [mul_div_assoc, mul_div_assoc]
    have hr : (r : ℝ) ≤ pclSize G σ v := by rw [hp]; push_cast; linarith
    have hratio := ratio_shift_le (n := n) hjt ht
    have hrat0 : 0 ≤ ((t : ℝ) - (j + 1 : ℕ)) / ((n : ℝ) - (j + 1 : ℕ)) := by
      have h1 : ((j + 1 : ℕ) : ℝ) ≤ t := by exact_mod_cast (show j + 1 ≤ t by omega)
      have h2 : ((j + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast (show j + 1 ≤ n by omega)
      apply div_nonneg <;> linarith
    calc (r : ℝ) * (((t : ℝ) - (j + 1 : ℕ)) / ((n : ℝ) - (j + 1 : ℕ)))
        ≤ (pclSize G σ v : ℝ) * (((t : ℝ) - (j + 1 : ℕ)) / ((n : ℝ) - (j + 1 : ℕ))) := by
          gcongr
      _ ≤ (pclSize G σ v : ℝ) * (t / n) := by gcongr
  have hθ0 : 0 < θ σ := by
    simp only [hθ]
    have : (1 : ℝ) ≤ pclSize G σ v := by rw [hp]; push_cast; linarith [(Nat.cast_nonneg r : (0:ℝ) ≤ r)]
    have ht0 : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
    positivity
  have e2 : 2 * (pclSize G σ v : ℝ) * t / n = 2 * ((pclSize G σ v : ℝ) * t / n) := by ring
  exact chernoff_choice_upper hμ0 hL (by simp only [hθ]; linarith) hθ0

end CCK
