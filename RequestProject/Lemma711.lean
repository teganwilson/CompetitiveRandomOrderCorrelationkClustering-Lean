module

public import RequestProject.ProbTools

/-!
# Lemma 7.11

Lemma 7.11 of the paper (small sets have few early arrivals).
-/

@[expose] public section

open Finset
open scoped Classical

namespace CCK

variable {n : ℕ}

/-- **Lemma 7.11 (small sets have few early arrivals).**  For any `i ≥ 0` and any set `Y` of
`c m log n` vertices, the probability that at least two vertices of `Y` arrive by time `2^{i+1}`
is at most `2 c² m² log² n · 4^i / n²`.  (The paper's side conditions `c > 0` and `m ≤ n / 2^i`
turn out to be unnecessary; "by time `2^{i+1}`" means among the first `min(2^{i+1}, n)`
arrivals.) -/
theorem lemma_7_11 (i : ℕ) (Y : Finset (Fin n)) {c m : ℝ}
    (hY : (Y.card : ℝ) = c * m * Real.log n) :
    prob (fun σ => 2 ≤ (firstSet σ (min (2 ^ (i + 1)) n) ∩ Y).card) ≤
      2 * c ^ 2 * m ^ 2 * Real.log n ^ 2 * 4 ^ i / n ^ 2 := by
  set t := min (2 ^ (i + 1)) n with ht
  have htn : t ≤ n := min_le_right _ _
  have ht2 : (t : ℝ) ≤ 2 ^ (i + 1) := by exact_mod_cast min_le_left _ _
  set f := fun σ : Equiv.Perm (Fin n) =>
    ((firstSet σ t ∩ Y).card : ℝ) * ((firstSet σ t ∩ Y).card - 1)
  have hf0 : ∀ σ, 0 ≤ f σ := fun σ => card_mul_card_sub_one_nonneg _
  have hev : ∀ σ, 2 ≤ (firstSet σ t ∩ Y).card → 2 ≤ f σ := by
    intro σ h
    have : (2 : ℝ) ≤ (firstSet σ t ∩ Y).card := by exact_mod_cast h
    simp only [f]; nlinarith
  calc prob (fun σ => 2 ≤ (firstSet σ t ∩ Y).card) ≤ prob (fun σ => 2 ≤ f σ) := prob_mono hev
    _ ≤ expect f / 2 := prob_ge_le_expect_div f hf0 (by norm_num)
    _ ≤ (Y.card : ℝ) ^ 2 * ((t : ℝ) ^ 2 / n ^ 2) / 2 := by
        gcongr; exact expect_pair_count_le htn Y
    _ ≤ (Y.card : ℝ) ^ 2 * ((2 ^ (i + 1)) ^ 2 / n ^ 2) / 2 := by
        gcongr
    _ = 2 * c ^ 2 * m ^ 2 * Real.log n ^ 2 * 4 ^ i / n ^ 2 := by
        rw [hY]
        have : ((2 : ℝ) ^ (i + 1)) ^ 2 = 4 * 4 ^ i := by
          rw [← pow_mul, mul_comm (i + 1), pow_mul, pow_succ]; norm_num; ring
        rw [this]; ring

end CCK
