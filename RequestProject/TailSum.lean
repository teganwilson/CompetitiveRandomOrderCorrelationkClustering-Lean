module

public import Mathlib

/-!
# Appendix C: bounding a fixed tail sum by the smallest differences (Lemma C.1)
-/

@[expose] public section

open Finset

namespace CCK

/-- In a non-increasing sequence, the tail `q_{r+1}, …, q_k` has the smallest sum among all
`(k - r)`-subsets (equation (52)). -/
lemma tail_sum_le_subset_sum (q : ℕ → ℕ) (k r : ℕ) (hq : ∀ i j, i ≤ j → j < k → q j ≤ q i)
    (hr : r ≤ k) (J : Finset ℕ) (hJ : J ⊆ range k) (hJc : J.card = k - r) :
    ∑ i ∈ Ico r k, q i ≤ ∑ i ∈ J, q i := by
  set T := Ico r k
  have hsplit : ∀ A B : Finset ℕ, ∑ i ∈ A, q i = ∑ i ∈ A \ B, q i + ∑ i ∈ A ∩ B, q i := by
    intro A B
    conv_lhs => rw [← sdiff_union_inter A B]
    rw [sum_union (disjoint_sdiff_inter A B)]
  rw [hsplit T J, hsplit J T, inter_comm T J]
  gcongr ?_ + _
  rcases Nat.eq_zero_or_pos (T \ J).card with h0 | h0
  · rw [card_eq_zero.1 h0]; simp
  have hrk : r < k := by
    obtain ⟨x, hx⟩ := card_pos.1 h0
    simp only [T, mem_sdiff, mem_Ico] at hx; omega
  have h1 : ∀ i ∈ T \ J, q i ≤ q r := by
    intro i hi
    simp only [T, mem_sdiff, mem_Ico] at hi
    exact hq _ _ hi.1.1 hi.1.2
  have h2 : ∀ i ∈ J \ T, q r ≤ q i := by
    intro i hi
    simp only [T, mem_sdiff, mem_Ico, not_and, not_lt] at hi
    have hik : i < k := by simpa using hJ hi.1
    have : i < r := by
      by_contra h; push_neg at h; exact absurd (hi.2 h) (by omega)
    exact hq _ _ this.le hrk
  have hc : (T \ J).card ≤ (J \ T).card := by
    have e1 := card_sdiff_add_card_inter T J
    have e2 := card_sdiff_add_card_inter J T
    rw [inter_comm] at e2
    have : T.card = k - r := by simp [T]
    omega
  calc ∑ i ∈ T \ J, q i ≤ (T \ J).card * q r := by
        rw [← smul_eq_mul, ← sum_const]; exact sum_le_sum h1
    _ ≤ (J \ T).card * q r := Nat.mul_le_mul_right _ hc
    _ ≤ ∑ i ∈ J \ T, q i := by
        rw [← smul_eq_mul, ← sum_const]; exact sum_le_sum h2

/-- **Lemma C.1.** Let `q_1 ≥ q_2 ≥ ⋯ ≥ q_k` be nonnegative integers, let `p_i` be integers with
`0 ≤ p_i ≤ q_i / 2`, and set `c_i = q_i - p_i`.  Then for every `r` with `1 ≤ r ≤ k`,
`∑_{i = r+1}^{k} c_i ≤ 2 ∑_{j=1}^{k-r} c_{(j)}`, where the right-hand side is twice the sum of
the `k - r` smallest values among `c_1, …, c_k`.  We state the right-hand side as twice the sum of
`c` over an arbitrary set `J` of `k - r` indices (which is equivalent, since the minimum over such
`J` is attained by the `k - r` smallest values).  Indices are shifted by one (`q 0 = q_1`). -/
theorem lemma_C_1 (q p : ℕ → ℕ) (k r : ℕ) (hq : ∀ i j, i ≤ j → j < k → q j ≤ q i)
    (hp : ∀ i, 2 * p i ≤ q i) (_hr1 : 1 ≤ r) (hr : r ≤ k) (J : Finset ℕ) (hJ : J ⊆ range k)
    (hJc : J.card = k - r) :
    ∑ i ∈ Ico r k, (q i - p i) ≤ 2 * ∑ i ∈ J, (q i - p i) := by
  calc ∑ i ∈ Ico r k, (q i - p i) ≤ ∑ i ∈ Ico r k, q i := sum_le_sum (fun i _ => Nat.sub_le _ _)
    _ ≤ ∑ i ∈ J, q i := tail_sum_le_subset_sum q k r hq hr J hJ hJc
    _ ≤ ∑ i ∈ J, 2 * (q i - p i) := sum_le_sum (fun i _ => by have := hp i; omega)
    _ = 2 * ∑ i ∈ J, (q i - p i) := by rw [mul_sum]

end CCK
