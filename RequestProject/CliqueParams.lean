module

public import RequestProject.Cliques

/-!
# The parameters `s(I)`, `r(I)`, `a(I)` of a disjoint-cliques instance (Section 3)

We work with the list of clique sizes in non-increasing order, given as a function
`w : ℕ → ℕ` together with the number of cliques `ℓ` (the paper's `n_{i+1} = w i`, so indices are
shifted by one).  A k-clustering that keeps every clique intact is described by the cluster
`D i : Fin k` of the clique `i`.
-/

@[expose] public section

open Finset
open scoped Classical

namespace CCK

/-- Partial tail sums `S r = ∑_{r ≤ i < ℓ} w i` (with `n = S 0`). -/
def tailSum (w : ℕ → ℕ) (ℓ r : ℕ) : ℕ := ∑ i ∈ Ico r ℓ, w i

/-- **Definition 3.2.** `s(I)`: the total number of vertices not in the `k` largest cliques,
`s(I) = ∑_{i = k+1}^{ℓ} n_i`. -/
def sParam (w : ℕ → ℕ) (ℓ k : ℕ) : ℕ := tailSum w ℓ k

/-- **Definition 3.3 (index `r(I)`).** `r(I)` is the smallest index `r` such that
`n_{r+1} < (n - ∑_{i=1}^{r} n_i) / (k - r)`.  (Written multiplicatively; if no index `r < k`
satisfies the inequality we set `r(I) = k`, which can only happen when `ℓ ≤ k`.) -/
noncomputable def rParam (w : ℕ → ℕ) (ℓ k : ℕ) : ℕ :=
  Nat.find (⟨k, Or.inl le_rfl⟩ : ∃ r, k ≤ r ∨ w r * (k - r) < tailSum w ℓ r)

/-- **Definition 3.3 (value `a(I)`).** `a(I) = (n - ∑_{i=1}^{r(I)} n_i) / (k - r(I))`. -/
noncomputable def aParam (w : ℕ → ℕ) (ℓ k : ℕ) : ℝ :=
  (tailSum w ℓ (rParam w ℓ k) : ℝ) / ((k : ℝ) - rParam w ℓ k)

/-- The sizes are listed in non-increasing order. -/
def SortedDesc (w : ℕ → ℕ) (ℓ : ℕ) : Prop := ∀ i j, i ≤ j → j < ℓ → w j ≤ w i

/-- Load of cluster `j` for a clique-preserving clustering `D`. -/
noncomputable def cLoad (w : ℕ → ℕ) (ℓ : ℕ) {k : ℕ} (D : ℕ → Fin k) (j : Fin k) : ℝ :=
  ∑ i ∈ (range ℓ).filter (fun i => D i = j), (w i : ℝ)

/-- Twice the cost of a clique-preserving clustering of a disjoint-cliques instance
(equation (47)): `∑_j c_j^2 - ∑_i n_i^2`. -/
noncomputable def cCost2 (w : ℕ → ℕ) (ℓ : ℕ) {k : ℕ} (D : ℕ → Fin k) : ℝ :=
  ∑ j, cLoad w ℓ D j ^ 2 - ∑ i ∈ range ℓ, (w i : ℝ) ^ 2

section facts

variable {w : ℕ → ℕ} {ℓ k : ℕ}

/-- Auxiliary result for Definitions 3.2 and 3.3 (Section 3). -/
lemma tailSum_succ (h : r < ℓ) : tailSum w ℓ r = w r + tailSum w ℓ (r + 1) := by
  unfold tailSum
  exact Finset.sum_eq_sum_Ico_succ_bot h _

/-- Auxiliary result for Definitions 3.2 and 3.3 (Section 3). -/
lemma tailSum_eq_zero (h : ℓ ≤ r) : tailSum w ℓ r = 0 := by
  unfold tailSum; rw [Ico_eq_empty_of_le h]; rfl

/-- Auxiliary result for Definitions 3.2 and 3.3 (Section 3). -/
lemma rParam_le : rParam w ℓ k ≤ k := Nat.find_min' _ (Or.inl le_rfl)

/-- Auxiliary result for Definitions 3.2 and 3.3 (Section 3). -/
lemma rParam_spec_of_lt (h : rParam w ℓ k < k) :
    w (rParam w ℓ k) * (k - rParam w ℓ k) < tailSum w ℓ (rParam w ℓ k) := by
  have := Nat.find_spec (⟨k, Or.inl le_rfl⟩ : ∃ r, k ≤ r ∨ w r * (k - r) < tailSum w ℓ r)
  rcases this with h1 | h1
  · exact absurd h1 (not_le.2 h)
  · exact h1

/-- Auxiliary result for Definitions 3.2 and 3.3 (Section 3). -/
lemma not_spec_of_lt_rParam {i : ℕ} (h : i < rParam w ℓ k) :
    tailSum w ℓ i ≤ w i * (k - i) ∧ i < k := by
  have := Nat.find_min (⟨k, Or.inl le_rfl⟩ : ∃ r, k ≤ r ∨ w r * (k - r) < tailSum w ℓ r) h
  push_neg at this
  exact ⟨this.2, this.1⟩

/-- If there are more than `k ≥ 1` cliques, then `r(I) < k`. -/
lemma rParam_lt (hpos : ∀ i < ℓ, 0 < w i) (hk0 : 0 < k) (hk : k < ℓ) : rParam w ℓ k < k := by
  apply lt_of_le_of_lt (Nat.find_min' _ _) (Nat.sub_lt hk0 one_pos)
  right
  have h1 : k - 1 < ℓ := by omega
  rw [tailSum_succ h1, Nat.sub_sub_self (by omega), Nat.sub_add_cancel hk0,
    tailSum_succ hk]
  have := hpos k hk
  omega


/-- Auxiliary result for Definitions 3.2 and 3.3 (Section 3). -/
lemma tailSum_le_of_le {r r' : ℕ} (h : r ≤ r') : tailSum w ℓ r' ≤ tailSum w ℓ r := by
  unfold tailSum
  exact Finset.sum_le_sum_of_subset (Ico_subset_Ico_left h)

/-- `S r = (k - r) a` for `r = r(I) < k`. -/
lemma tailSum_rParam_eq (h : rParam w ℓ k < k) :
    (tailSum w ℓ (rParam w ℓ k) : ℝ) = ((k : ℝ) - rParam w ℓ k) * aParam w ℓ k := by
  unfold aParam
  have : (0 : ℝ) < (k : ℝ) - rParam w ℓ k := by
    have : ((rParam w ℓ k : ℕ) : ℝ) < k := by exact_mod_cast h
    linarith
  field_simp

/-- For `i < r(I)`, the `i`-th largest clique has size at least `a(I)` (the peeled cliques are
large). -/
lemma aParam_le_of_lt_rParam {i : ℕ} (hi : i < rParam w ℓ k) : aParam w ℓ k ≤ w i := by
  set r := rParam w ℓ k
  have hrk : r ≤ k := rParam_le
  rcases eq_or_lt_of_le hrk with hrk' | hrk'
  · unfold aParam
    rw [show ((rParam w ℓ k : ℕ) : ℝ) = k by exact_mod_cast hrk']
    simp
  -- averages are nonincreasing up to `r`
  let avg : ℕ → ℝ := fun i => (tailSum w ℓ i : ℝ) / ((k : ℝ) - i)
  have step : ∀ i, i < r → avg (i + 1) ≤ avg i := by
    intro i hi
    obtain ⟨h1, h2⟩ := not_spec_of_lt_rParam (w := w) (ℓ := ℓ) (k := k) hi
    have hik : i + 1 < k := by omega
    have hd1 : (0 : ℝ) < (k : ℝ) - (i + 1 : ℕ) := by
      have : ((i + 1 : ℕ) : ℝ) < k := by exact_mod_cast hik
      linarith
    have hd2 : (0 : ℝ) < (k : ℝ) - i := by
      have : ((i : ℕ) : ℝ) < k := by exact_mod_cast h2
      linarith
    simp only [avg]
    rw [div_le_div_iff₀ hd1 hd2]
    by_cases hiℓ : i < ℓ
    · rw [tailSum_succ (w := w) hiℓ] at h1 ⊢
      have h1' : ((w i + tailSum w ℓ (i + 1) : ℕ) : ℝ) ≤ ((w i * (k - i) : ℕ) : ℝ) := by
        exact_mod_cast h1
      push_cast [Nat.cast_sub h2.le] at h1' ⊢
      nlinarith
    · rw [tailSum_eq_zero (by omega), tailSum_eq_zero (by omega)]
      simp
  have mono : ∀ m i, i + m = r → avg r ≤ avg i := by
    intro m
    induction m with
    | zero => intro i h; simp at h; rw [h]
    | succ m ih =>
      intro i h
      exact (ih (i + 1) (by omega)).trans (step i (by omega))
  have hai : aParam w ℓ k = avg r := rfl
  rw [hai]
  refine (mono (r - i) i (by omega)).trans ?_
  obtain ⟨h1, h2⟩ := not_spec_of_lt_rParam (w := w) (ℓ := ℓ) (k := k) hi
  have hd2 : (0 : ℝ) < (k : ℝ) - i := by
    have : ((i : ℕ) : ℝ) < k := by exact_mod_cast h2
    linarith
  simp only [avg]
  rw [div_le_iff₀ hd2]
  have : ((tailSum w ℓ i : ℕ) : ℝ) ≤ ((w i * (k - i) : ℕ) : ℝ) := by exact_mod_cast h1
  push_cast [Nat.cast_sub h2.le] at this
  linarith

/-- For `i ≥ r(I)`, cliques have size strictly less than `a(I)`. -/
lemma lt_aParam_of_rParam_le (hs : SortedDesc w ℓ) (hr : rParam w ℓ k < k) {i : ℕ}
    (hi : rParam w ℓ k ≤ i) (hiℓ : i < ℓ) : (w i : ℝ) < aParam w ℓ k := by
  have h := rParam_spec_of_lt (w := w) (ℓ := ℓ) hr
  have hle : w i ≤ w (rParam w ℓ k) := hs _ _ hi hiℓ
  have hd : (0 : ℝ) < (k : ℝ) - rParam w ℓ k := by
    have : ((rParam w ℓ k : ℕ) : ℝ) < k := by exact_mod_cast hr
    linarith
  unfold aParam
  rw [lt_div_iff₀ hd]
  have h' : ((w (rParam w ℓ k) * (k - rParam w ℓ k) : ℕ) : ℝ) <
      ((tailSum w ℓ (rParam w ℓ k) : ℕ) : ℝ) := by exact_mod_cast h
  push_cast [Nat.cast_sub hr.le] at h'
  have hle' : (w i : ℝ) ≤ w (rParam w ℓ k) := by exact_mod_cast hle
  nlinarith

/-- Sum of the sizes of any `≤ k` cliques is at most the total size of the `k` largest. -/
lemma sum_le_sum_top (hs : SortedDesc w ℓ) (T : Finset ℕ) (hT : T ⊆ range ℓ)
    (hcard : T.card ≤ k) : ∑ i ∈ T, w i ≤ ∑ i ∈ range (min k ℓ), w i := by
  set P := range (min k ℓ)
  have hsplit : ∀ A B : Finset ℕ, ∑ i ∈ A, w i = ∑ i ∈ A \ B, w i + ∑ i ∈ A ∩ B, w i := by
    intro A B
    conv_lhs => rw [← sdiff_union_inter A B]
    rw [sum_union (disjoint_sdiff_inter A B)]
  rw [hsplit T P, hsplit P T, inter_comm T P]
  gcongr ?_ + _
  by_cases hkl : k < ℓ
  · have hP : P = range k := by simp [P, min_eq_left hkl.le]
    have h1 : ∀ i ∈ T \ P, w i ≤ w k := by
      intro i hi
      simp only [mem_sdiff, hP, mem_range, not_lt] at hi
      exact hs _ _ hi.2 (by simpa using hT hi.1)
    have h2 : ∀ i ∈ P \ T, w k ≤ w i := by
      intro i hi
      simp only [mem_sdiff, hP, mem_range] at hi
      exact hs _ _ hi.1.le hkl
    have hc : (T \ P).card ≤ (P \ T).card := by
      have e1 := card_sdiff_add_card_inter T P
      have e2 := card_sdiff_add_card_inter P T
      rw [inter_comm] at e2
      have : P.card = k := by simp [hP]
      omega
    calc ∑ i ∈ T \ P, w i ≤ (T \ P).card * w k := by
          rw [← smul_eq_mul, ← sum_const]; exact sum_le_sum h1
      _ ≤ (P \ T).card * w k := Nat.mul_le_mul_right _ hc
      _ ≤ ∑ i ∈ P \ T, w i := by
          rw [← smul_eq_mul, ← sum_const]; exact sum_le_sum h2
  · have hP : P = range ℓ := by simp [P, min_eq_right (not_lt.1 hkl)]
    have : T \ P = ∅ := by rw [hP]; exact sdiff_eq_empty_iff_subset.2 hT
    rw [this]; simp

/-- Auxiliary result for Definitions 3.2 and 3.3 (Section 3). -/
lemma sum_range_eq_add_tailSum {r : ℕ} (h : r ≤ ℓ) :
    ∑ i ∈ range ℓ, w i = ∑ i ∈ range r, w i + tailSum w ℓ r := by
  unfold tailSum
  rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le r) h]

end facts

end CCK
