module

public import RequestProject.Hyp

/-!
# Elementary probability tools on random arrival orders

Union bound, Markov's inequality, and the exact second factorial moments of hypergeometric
counts (the pair-counting identities used in Lemma 7.11, in equations (4), (5) of the proof of
Theorem 5 and in equations (35)–(37) of the proof of Theorem 4).
-/

@[expose] public section

open Finset
open scoped Classical

namespace CCK

variable {n : ℕ}

/-- Union bound. -/
lemma prob_exists_le {ι : Type*} (s : Finset ι) (P : ι → Equiv.Perm (Fin n) → Prop) :
    prob (fun σ => ∃ i ∈ s, P i σ) ≤ ∑ i ∈ s, prob (P i) := by
  unfold prob
  rw [← sum_div]
  apply div_le_div_of_nonneg_right _ card_perm_pos.le
  have : univ.filter (fun σ => ∃ i ∈ s, P i σ) = s.biUnion (fun i => univ.filter (P i)) := by
    ext σ; simp
  rw [this]
  exact_mod_cast card_biUnion_le

/-- Auxiliary result for the elementary probability tools of Section 2. -/
lemma prob_or_le (P Q : Equiv.Perm (Fin n) → Prop) :
    prob (fun σ => P σ ∨ Q σ) ≤ prob P + prob Q := by
  unfold prob
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ card_perm_pos.le
  have : univ.filter (fun σ => P σ ∨ Q σ) = univ.filter P ∪ univ.filter Q := by
    ext σ; simp
  rw [this]
  exact_mod_cast card_union_le _ _

/-- Markov's inequality. -/
lemma prob_ge_le_expect_div (f : Equiv.Perm (Fin n) → ℝ) (hf : ∀ σ, 0 ≤ f σ) {a : ℝ}
    (ha : 0 < a) : prob (fun σ => a ≤ f σ) ≤ expect f / a := by
  rw [le_div_iff₀ ha, ← expect_indicator]
  unfold expect
  rw [div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ card_perm_pos.le
  rw [sum_mul]
  apply sum_le_sum
  intro σ _
  split_ifs with h
  · linarith
  · simp [hf σ]

/-- Auxiliary result for the elementary probability tools of Section 2. -/
lemma expect_const (c : ℝ) : expect (fun _ : Equiv.Perm (Fin n) => c) = c := by
  unfold expect
  rw [sum_const, card_univ, nsmul_eq_mul]
  field_simp [card_perm_pos.ne']

/-- Auxiliary result for the elementary probability tools of Section 2. -/
lemma expect_smul (c : ℝ) (f : Equiv.Perm (Fin n) → ℝ) :
    expect (fun σ => c * f σ) = c * expect f := by
  unfold expect; rw [← mul_sum, mul_div_assoc]

/-- Auxiliary result for the elementary probability tools of Section 2. -/
lemma expect_nonneg {f : Equiv.Perm (Fin n) → ℝ} (hf : ∀ σ, 0 ≤ f σ) : 0 ≤ expect f :=
  div_nonneg (sum_nonneg (fun σ _ => hf σ)) card_perm_pos.le

/-- A random variable bounded by `M` on the complement of an event `E` and by `B` on `E`. -/
lemma expect_le_of_bound (f : Equiv.Perm (Fin n) → ℝ) (E : Equiv.Perm (Fin n) → Prop)
    {B : ℝ} (hB : ∀ σ, E σ → f σ ≤ B) (g : Equiv.Perm (Fin n) → ℝ) (hg : ∀ σ, ¬ E σ → f σ ≤ g σ)
    (hg0 : ∀ σ, 0 ≤ g σ) : expect f ≤ B * prob E + expect g := by
  rw [← expect_indicator, ← expect_smul, ← expect_add]
  apply expect_mono
  intro σ
  by_cases h : E σ
  · simp only [h, if_true, mul_one]; linarith [hB σ h, hg0 σ]
  · simp only [h, if_false, mul_zero, zero_add]; exact hg σ h

/-- The number of ordered pairs of distinct elements of `F ∩ D₀` × `F ∩ D` for `D₀ ⊆ D`. -/
lemma card_mul_card_sub_one_eq {F D₀ D : Finset (Fin n)} (h : D₀ ⊆ D) :
    ((F ∩ D₀).card : ℝ) * ((F ∩ D).card - 1) =
      ∑ x ∈ (D₀ ×ˢ D).filter (fun x => x.1 ≠ x.2),
        (if x.1 ∈ F ∧ x.2 ∈ F then (1 : ℝ) else 0) := by
  rw [sum_boole]
  have hset : ((D₀ ×ˢ D).filter (fun x => x.1 ≠ x.2)).filter (fun x => x.1 ∈ F ∧ x.2 ∈ F) =
      (F ∩ D₀).biUnion (fun u => ((F ∩ D).erase u).map ⟨fun v => (u, v), fun a b h => by
        simpa using h⟩) := by
    ext ⟨u, v⟩
    simp only [mem_filter, mem_product, mem_biUnion, mem_inter, mem_map, mem_erase,
      Function.Embedding.coeFn_mk, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨⟨hu, hv⟩, huv⟩, hFu, hFv⟩
      exact ⟨u, ⟨hFu, hu⟩, v, ⟨Ne.symm huv, hFv, hv⟩, rfl, rfl⟩
    · rintro ⟨w, ⟨hFw, hw⟩, x, ⟨hxw, hFx, hx⟩, rfl, rfl⟩
      exact ⟨⟨⟨hw, hx⟩, Ne.symm hxw⟩, hFw, hFx⟩
  rw [hset, card_biUnion]
  · have : ∀ u ∈ F ∩ D₀, (((F ∩ D).erase u).map (⟨fun v => (u, v), fun a b h => by
        simpa using h⟩ : Fin n ↪ Fin n × Fin n)).card = (F ∩ D).card - 1 := by
      intro u hu
      rw [card_map, card_erase_of_mem (mem_inter.2 ⟨(mem_inter.1 hu).1, h (mem_inter.1 hu).2⟩)]
    rw [sum_congr rfl this, sum_const, smul_eq_mul]
    by_cases hc : (F ∩ D₀).card = 0
    · rw [hc]; simp
    · have : 1 ≤ (F ∩ D).card := by
        obtain ⟨u, hu⟩ := card_pos.1 (Nat.pos_of_ne_zero hc)
        exact card_pos.2 ⟨u, mem_inter.2 ⟨(mem_inter.1 hu).1, h (mem_inter.1 hu).2⟩⟩
      push_cast [Nat.cast_sub this]; ring
  · intro u _ w _ huw
    simp only [Function.onFun]
    rw [disjoint_left]
    intro x hx1 hx2
    obtain ⟨a, _, rfl⟩ := mem_map.1 hx1
    obtain ⟨b, _, hb⟩ := mem_map.1 hx2
    simp only [Function.Embedding.coeFn_mk, Prod.mk.injEq] at hb
    exact huw hb.1.symm

/-- **Second factorial moment of hypergeometric counts.**  For fixed sets `D₀ ⊆ D` and
`F = ` the first `t` arrivals, `E[|F ∩ D₀| (|F ∩ D| - 1)] = |D₀| (|D| - 1) t (t-1) / (n (n-1))`
(equations (4), (5) in the proof of Theorem 5 and (35)–(37) in the proof of Theorem 4). -/
lemma expect_pair_count {t : ℕ} (ht : t ≤ n) {D₀ D : Finset (Fin n)} (h : D₀ ⊆ D) :
    expect (fun σ => ((firstSet σ t ∩ D₀).card : ℝ) * ((firstSet σ t ∩ D).card - 1)) =
      (D₀.card : ℝ) * (D.card - 1) * ((t : ℝ) * (t - 1) / (n * (n - 1))) := by
  have hrw : (fun σ => ((firstSet σ t ∩ D₀).card : ℝ) * ((firstSet σ t ∩ D).card - 1)) =
      fun σ => ∑ x ∈ (D₀ ×ˢ D).filter (fun x => x.1 ≠ x.2),
        (if x.1 ∈ firstSet σ t ∧ x.2 ∈ firstSet σ t then (1 : ℝ) else 0) := by
    funext σ; exact card_mul_card_sub_one_eq h
  rw [hrw, expect_sum]
  have : ∀ x ∈ (D₀ ×ˢ D).filter (fun x => x.1 ≠ x.2),
      expect (fun σ => if x.1 ∈ firstSet σ t ∧ x.2 ∈ firstSet σ t then (1 : ℝ) else 0) =
        (t : ℝ) * (t - 1) / (n * (n - 1)) := by
    intro x hx
    rw [expect_indicator, prob_pair_firstSet ht _ _ (mem_filter.1 hx).2]
  rw [sum_congr rfl this, sum_const, nsmul_eq_mul]
  have hc := card_mul_card_sub_one_eq (F := univ) h
  simp only [univ_inter, mem_univ, and_self, if_true, sum_const, nsmul_eq_mul, mul_one] at hc
  rw [← hc]

/-- `E[|F ∩ D|] = |D| t / n` for the first `t` arrivals `F`. -/
lemma expect_card_firstSet_inter {t : ℕ} (ht : t ≤ n) (D : Finset (Fin n)) :
    expect (fun σ => ((firstSet σ t ∩ D).card : ℝ)) = (D.card : ℝ) * t / n := by
  have hrw : (fun σ => ((firstSet σ t ∩ D).card : ℝ)) =
      fun σ => ∑ v ∈ D, (if v ∈ firstSet σ t then (1 : ℝ) else 0) := by
    funext σ
    rw [sum_boole]
    congr 2
    ext v; simp [and_comm]
  rw [hrw, expect_sum]
  have : ∀ v ∈ D, expect (fun σ => if v ∈ firstSet σ t then (1 : ℝ) else 0) = (t : ℝ) / n := by
    intro v _
    rw [expect_indicator, prob_mem_firstSet ht]
  rw [sum_congr rfl this, sum_const, nsmul_eq_mul]
  ring

end CCK

namespace CCK

/-- Auxiliary result for the elementary probability tools of Section 2. -/
lemma pair_ratio_nonneg (t n : ℕ) : 0 ≤ (t : ℝ) * (t - 1) / (n * (n - 1)) := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n <;> simp
  · have : (1 : ℝ) ≤ t := by exact_mod_cast ht
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    apply div_nonneg <;> nlinarith

/-- Auxiliary result for the elementary probability tools of Section 2. -/
lemma pair_ratio_le {t n : ℕ} (ht : t ≤ n) :
    (t : ℝ) * (t - 1) / (n * (n - 1)) ≤ (t : ℝ) ^ 2 / n ^ 2 := by
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n <;> simp
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have htn : (t : ℝ) ≤ n := by exact_mod_cast ht
  have ht0 : (0 : ℝ) ≤ t := by positivity
  rw [div_le_div_iff₀ (by nlinarith) (by positivity)]
  have : (t : ℝ) * (t - 1) * n ≤ t ^ 2 * (n - 1) := by nlinarith
  nlinarith

/-- `E[Z (Z - 1)] ≤ |Y|² t² / n²` for the number `Z` of vertices of `Y` among the first `t`
arrivals. -/
lemma expect_pair_count_le {n t : ℕ} (ht : t ≤ n) (Y : Finset (Fin n)) :
    expect (fun σ => ((firstSet σ t ∩ Y).card : ℝ) * ((firstSet σ t ∩ Y).card - 1)) ≤
      (Y.card : ℝ) ^ 2 * ((t : ℝ) ^ 2 / n ^ 2) := by
  rw [expect_pair_count ht (subset_refl Y)]
  have h1 : (Y.card : ℝ) * (Y.card - 1) ≤ (Y.card : ℝ) ^ 2 := by nlinarith
  have h0 : 0 ≤ (Y.card : ℝ) * (Y.card - 1) := by
    rcases Nat.eq_zero_or_pos Y.card with h | h
    · simp [h]
    · have : (1 : ℝ) ≤ Y.card := by exact_mod_cast h
      nlinarith
  exact mul_le_mul h1 (pair_ratio_le ht) (pair_ratio_nonneg t n) (by positivity)

/-- Auxiliary result for the elementary probability tools of Section 2. -/
lemma card_mul_card_sub_one_nonneg (m : ℕ) : 0 ≤ (m : ℝ) * (m - 1) := by
  rcases Nat.eq_zero_or_pos m with h | h
  · simp [h]
  · have : (1 : ℝ) ≤ m := by exact_mod_cast h
    nlinarith

end CCK
