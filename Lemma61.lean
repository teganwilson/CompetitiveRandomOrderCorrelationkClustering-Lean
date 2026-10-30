module

public import RequestProject.ProbTools

/-!
# Lemma 6.1

Lemma 6.1 of the paper: large cliques have many early arrivals, with high probability.  This
uses the hypergeometric Chernoff bound (Fact 2.2), which is derived from the assumed Fact 2.1 and
Lemma 5.3 (see `RequestProject/Hyp.lean`).
-/

@[expose] public section

open Finset
open scoped Classical

namespace CCK

variable {n : ℕ}

/-- **Lemma 6.1 (lower bound on the number of vertices arriving from large cliques).**  For any
time `t` and constant `c₁ > 0`, and any clique (indeed any set of vertices) `K` of size at least
`c₁ n log n / t`, the number of vertices of `K` arriving by time `t` is more than `c₁ log n / 2`
with probability at least `1 - n^{-c₁/8}`.  (The hypothesis `c₁ > 0` of the paper turns out
to be unnecessary.)  (Assumes Fact 2.1 and Lemma 5.3, through Fact 2.2.) -/
theorem lemma_6_1 (hCh : ChernoffBound) (hPNA : PermNegAssoc) {t : ℕ} (ht0 : 0 < t)
    (ht : t ≤ n) (c₁ : ℝ) (K : Finset (Fin n))
    (hK : c₁ * n * Real.log n / t ≤ K.card) :
    prob (fun σ => ((firstSet σ t ∩ K).card : ℝ) ≤ c₁ * Real.log n / 2) ≤
      (n : ℝ) ^ (-c₁ / 8) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast lt_of_lt_of_le ht0 ht
  have htR : (0 : ℝ) < t := by exact_mod_cast ht0
  obtain ⟨-, -, h3, -⟩ := fact_2_2 hCh hPNA K ht
  set μ := (K.card : ℝ) * t / n with hμ
  have hμge : c₁ * Real.log n ≤ μ := by
    rw [hμ, le_div_iff₀ hn]
    rw [div_le_iff₀ htR] at hK
    linarith
  have hb := h3 (1 / 2) (by norm_num) (by norm_num)
  calc prob (fun σ => ((firstSet σ t ∩ K).card : ℝ) ≤ c₁ * Real.log n / 2)
      ≤ prob (fun σ => ((firstSet σ t ∩ K).card : ℝ) ≤ (1 - 1 / 2) * μ) :=
        prob_mono (fun σ h => by linarith)
    _ ≤ Real.exp (-((1 / 2) ^ 2 * μ) / 2) := hb
    _ ≤ Real.exp (Real.log n * (-c₁ / 8)) := by
        apply Real.exp_le_exp.2; nlinarith
    _ = (n : ℝ) ^ (-c₁ / 8) := by rw [Real.rpow_def_of_pos hn]

end CCK
