module

public import RequestProject.Thm4Expect

/-!
# Theorem 4: bad events and trivial bounds

The good events used in the proof of Theorem 4 fail with probability `O(n^{-2})`, so that their
contribution `n² · P[bad]` to the expected merging cost is bounded by a constant.  We also record
the trivial bound `Cost_merge ≤ n²`, and that the merging cost vanishes when there are at most `k`
pivots.
-/

@[expose] public section

open Finset
open scoped Classical

namespace CCK

variable {n : ℕ} (G : SimpleGraph (Fin n)) {ι : Type*} (Q : Fin n → ι) (k : ℕ)

/-- All good events of the proof of Theorem 4. -/
def GoodAll (σ : Equiv.Perm (Fin n)) : Prop :=
  GoodLoad G σ 48 ∧ GoodLate G σ 6 ∧ GoodHeavy G σ 60 ∧ GoodGroups G Q σ

/-- Auxiliary result for the proof of Theorem 4 (Section 7.3.4: bad events). -/
lemma rpow_neg_nat (x : ℝ) (hx : 0 ≤ x) (m : ℕ) : x ^ (-(m : ℝ)) = 1 / x ^ m := by
  rw [Real.rpow_neg hx, Real.rpow_natCast, one_div]

/-- **Bad events (proof of Theorem 4).**  `n² P[some good event fails] ≤ 5`. -/
lemma bad_prob_le (hH : HypergeomChernoff) (hn : 2 ≤ n) :
    (n : ℝ) ^ 2 * prob (fun σ => ¬ GoodAll G Q σ) ≤ 5 := by
  have hx : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) ≤ n := by linarith
  have hL : ((Nat.log 2 n + 1 : ℕ) : ℝ) ≤ n := by
    have : Nat.log 2 n < n := Nat.log_lt_self 2 (by omega)
    exact_mod_cast (by omega : Nat.log 2 n + 1 ≤ n)
  have hL0 : (0 : ℝ) ≤ ((Nat.log 2 n + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hsub : ∀ σ, ¬ GoodAll G Q σ →
      (¬ GoodLoad G σ 48 ∨ ¬ GoodLate G σ 6) ∨ (¬ GoodHeavy G σ 60 ∨ ¬ GoodGroups G Q σ) := by
    intro σ h
    unfold GoodAll at h
    by_cases h1 : GoodLoad G σ 48
    · by_cases h2 : GoodLate G σ 6
      · by_cases h3 : GoodHeavy G σ 60
        · exact Or.inr (Or.inr (fun h4 => h ⟨h1, h2, h3, h4⟩))
        · exact Or.inr (Or.inl h3)
      · exact Or.inl (Or.inr h2)
    · exact Or.inl (Or.inl h1)
  have hP : prob (fun σ => ¬ GoodAll G Q σ) ≤
      (prob (fun σ => ¬ GoodLoad G σ 48) + prob (fun σ => ¬ GoodLate G σ 6)) +
      (prob (fun σ => ¬ GoodHeavy G σ 60) + prob (fun σ => ¬ GoodGroups G Q σ)) := by
    refine (prob_mono hsub).trans ((le_of_eq (prob_congr fun σ => Iff.rfl)).trans
      ((prob_or_le _ _).trans (add_le_add ?_ ?_)))
    · exact (le_of_eq (prob_congr fun σ => Iff.rfl)).trans ((prob_or_le _ _).trans (le_of_eq
        (congrArg₂ (· + ·) (prob_congr fun σ => Iff.rfl) (prob_congr fun σ => Iff.rfl))))
    · exact (le_of_eq (prob_congr fun σ => Iff.rfl)).trans ((prob_or_le _ _).trans (le_of_eq
        (congrArg₂ (· + ·) (prob_congr fun σ => Iff.rfl) (prob_congr fun σ => Iff.rfl))))
  -- the four bounds
  have h1 := prob_not_goodLoad G hH (by norm_num : (0 : ℝ) < 48) hn
  have h2 := prob_not_goodLate G 6
  have h3 := prob_not_goodHeavy G hH (by norm_num : (0 : ℝ) < 60)
  have h4 := prob_not_goodGroups G Q
  rw [show -(48 : ℝ) / 3 = -((16 : ℕ) : ℝ) by norm_num, rpow_neg_nat _ hx0,
    show (2 : ℝ) - 48 / 8 = -((4 : ℕ) : ℝ) by norm_num, rpow_neg_nat _ hx0] at h1
  rw [show -(6 : ℝ) = -((6 : ℕ) : ℝ) by norm_num, rpow_neg_nat _ hx0] at h2 h4
  rw [show (60 : ℝ) / 6 = ((10 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h3
  push_cast at h1 h2 h3 h4
  have hpos : ∀ m : ℕ, (0 : ℝ) < (n : ℝ) ^ m := fun m => by positivity
  have p16 : (n : ℝ) ^ 16 = (n : ℝ) ^ 2 * (n : ℝ) ^ 14 := by ring
  have hx1 : (1 : ℝ) ≤ n := by linarith
  -- bound for the load event
  have e1 : (n : ℝ) ^ 2 * prob (fun σ => ¬ GoodLoad G σ 48) ≤ 2 := by
    refine (mul_le_mul_of_nonneg_left h1 (by positivity)).trans ?_
    have n3 : (n : ℝ) ^ 3 ≤ (n : ℝ) ^ 4 := pow_le_pow_right₀ hx1 (by norm_num)
    have n2 : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 4 := pow_le_pow_right₀ hx1 (by norm_num)
    have n8 : (n : ℝ) ^ 8 ≤ (n : ℝ) ^ 16 := pow_le_pow_right₀ hx1 (by norm_num)
    have n40 : (0 : ℝ) ≤ (n : ℝ) ^ 4 := by positivity
    have n4 : 16 * (n : ℝ) ^ 4 ≤ (n : ℝ) ^ 8 := by
      have h4 : (16 : ℝ) ≤ (n : ℝ) ^ 4 := by
        have : (2 : ℝ) ^ 4 ≤ (n : ℝ) ^ 4 := pow_le_pow_left₀ (by norm_num) hx 4
        norm_num at this; linarith
      have : (n : ℝ) ^ 8 = (n : ℝ) ^ 4 * (n : ℝ) ^ 4 := by ring
      rw [this]; nlinarith
    have a1 : (n : ℝ) ^ 2 * ((n : ℝ) * (n + 1) * (1 / (n : ℝ) ^ 16)) ≤ 1 / 8 := by
      rw [mul_one_div, ← mul_div_assoc, div_le_iff₀ (hpos 16)]
      have e : (n : ℝ) ^ 2 * ((n : ℝ) * (n + 1)) = (n : ℝ) ^ 4 + (n : ℝ) ^ 3 := by ring
      rw [e]; linarith
    have a2 : (n : ℝ) ^ 2 * (((n : ℝ) + 1) * (1 / (n : ℝ) ^ 4)) ≤ 3 / 2 := by
      rw [mul_one_div, ← mul_div_assoc, div_le_iff₀ (hpos 4)]
      have e : (n : ℝ) ^ 2 * ((n : ℝ) + 1) = (n : ℝ) ^ 3 + (n : ℝ) ^ 2 := by ring
      have e4 : (n : ℝ) ^ 4 = (n : ℝ) * (n : ℝ) ^ 3 := by ring
      have n23 : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 3 := pow_le_pow_right₀ hx1 (by norm_num)
      have : 2 * (n : ℝ) ^ 3 ≤ (n : ℝ) ^ 4 := by
        rw [e4]; exact mul_le_mul_of_nonneg_right hx (by positivity)
      rw [e]; linarith
    have a3 : (n : ℝ) ^ 2 * (((n : ℝ) + 1) * (n + 1) * (1 / (n : ℝ) ^ 16)) ≤ 1 / 4 := by
      rw [mul_one_div, ← mul_div_assoc, div_le_iff₀ (hpos 16)]
      have e : (n : ℝ) ^ 2 * (((n : ℝ) + 1) * (n + 1)) = (n : ℝ) ^ 4 + 2 * (n : ℝ) ^ 3 +
          (n : ℝ) ^ 2 := by ring
      rw [e]; linarith
    linarith
  have hLate : ∀ q : ℝ, q ≤ ((Nat.log 2 n : ℝ) + 1) * n * (1 / (n : ℝ) ^ 6) →
      (n : ℝ) ^ 2 * q ≤ 1 := by
    intro q hq
    refine (mul_le_mul_of_nonneg_left hq (by positivity)).trans ?_
    rw [mul_one_div, ← mul_div_assoc, div_le_iff₀ (hpos 6)]
    have hL' : (Nat.log 2 n : ℝ) + 1 ≤ n := by exact_mod_cast hL
    have : (n : ℝ) ^ 2 * (((Nat.log 2 n : ℝ) + 1) * n) ≤ (n : ℝ) ^ 4 := by
      have : ((Nat.log 2 n : ℝ) + 1) * n ≤ (n : ℝ) * n := mul_le_mul_of_nonneg_right hL' hx0
      nlinarith
    have : (n : ℝ) ^ 4 ≤ (n : ℝ) ^ 6 := pow_le_pow_right₀ hx1 (by norm_num)
    linarith
  have e2 := hLate _ h2
  have e4 := hLate _ h4
  have e3 : (n : ℝ) ^ 2 * prob (fun σ => ¬ GoodHeavy G σ 60) ≤ 1 := by
    refine (mul_le_mul_of_nonneg_left h3 (by positivity)).trans ?_
    rw [← mul_div_assoc, div_le_iff₀ (hpos 10)]
    have hL' : (Nat.log 2 n : ℝ) + 1 ≤ n := by exact_mod_cast hL
    have : (n : ℝ) ^ 2 * ((n : ℝ) * ((Nat.log 2 n : ℝ) + 1)) ≤ (n : ℝ) ^ 4 := by
      have : (n : ℝ) * ((Nat.log 2 n : ℝ) + 1) ≤ (n : ℝ) * n := mul_le_mul_of_nonneg_left hL' hx0
      nlinarith
    have : (n : ℝ) ^ 4 ≤ (n : ℝ) ^ 10 := pow_le_pow_right₀ hx1 (by norm_num)
    linarith
  have := mul_le_mul_of_nonneg_left hP (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 2)
  nlinarith

variable (σ : Equiv.Perm (Fin n))

/-- Auxiliary result for the proof of Theorem 4 (Section 7.3.4: bad events). -/
lemma sum_pclSize_le (S : Finset (Fin n)) : ∑ p ∈ S, pclSize G σ p ≤ n := by
  unfold pclSize
  rw [← card_biUnion]
  · exact (card_le_univ _).trans (by simp)
  · intro p _ q _ hne
    simp only [Function.onFun]
    rw [disjoint_left]
    intro u hu hu'
    simp only [mem_filter, mem_univ, true_and] at hu hu'
    exact hne (hu.symm.trans hu')

/-- The trivial bound `Cost_merge ≤ n²`. -/
lemma mergeCost_le_sq : (mergeCost G k σ : ℝ) ≤ (n : ℝ) ^ 2 := by
  have h : mergeCost G k σ ≤ n * n := by
    unfold mergeCost
    calc ∑ p ∈ pivotsUpTo G σ n, pclSize G σ p * projLoad G k σ (arrTime σ p) (bpLabel G k σ p)
        ≤ ∑ p ∈ pivotsUpTo G σ n, pclSize G σ p * n := by
          apply sum_le_sum; intro p _
          apply Nat.mul_le_mul_left
          unfold projLoad; exact sum_pclSize_le G σ _
      _ = (∑ p ∈ pivotsUpTo G σ n, pclSize G σ p) * n := by rw [sum_mul]
      _ ≤ n * n := Nat.mul_le_mul_right _ (sum_pclSize_le G σ _)
  have : ((mergeCost G k σ : ℕ) : ℝ) ≤ ((n * n : ℕ) : ℝ) := by exact_mod_cast h
  push_cast at this; nlinarith

/-- With at most `k` pivots, there is no merging cost. -/
lemma mergeCost_eq_zero_of_not (hk : 0 < k) (h : ¬ ∃ t, k < (pivotsUpTo G σ (t + 1)).card) :
    mergeCost G k σ = 0 := by
  rw [mergeCost_eq_late G k σ hk]
  apply sum_eq_zero
  intro p hp
  exfalso
  have hT : Tk G k σ = n := by unfold Tk; rw [dif_neg h]
  have := (mem_filter.1 hp).2
  have := arrTime_lt σ p
  omega

end CCK
