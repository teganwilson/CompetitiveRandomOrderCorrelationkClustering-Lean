module

public import RequestProject.LBProb

/-!
# Theorem 2: an `Ω(log k)` lower bound for online correlation k-clustering

We combine the combinatorial core `lb_expCost` with Lemmas 5.1 and 5.5 (for `γ = 2/7`, as in
the paper).  The paper bounds `P(E)` by the product of the probabilities of Lemmas 5.1 and 5.5
(using a positive correlation); we instead use the elementary bound
`P(A ∩ B) ≥ P(A) - P(Bᶜ)`, which suffices for large `k`.
-/

@[expose] public section

open Finset
open scoped Classical

namespace CCK

/-- Auxiliary result for Theorem 2. -/
lemma exp_neg_sqrt_le {k : ℕ} (hk : 9408 ^ 2 ≤ k) : Real.exp (-Real.sqrt k / 16) ≤ 1 / 588 := by
  have hk' : ((9408 : ℝ)) ^ 2 ≤ k := by exact_mod_cast hk
  have hsq : 9408 ≤ Real.sqrt k := by
    rw [show (9408 : ℝ) = Real.sqrt (9408 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hk'
  have h1 := Real.add_one_le_exp (Real.sqrt k / 16)
  rw [neg_div, Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos _) (by norm_num)]
  linarith

/-- For `γ = 2/7` and all sufficiently large `k`, the event `E` of Section 5 (both singletons
arrived by `T` and some clique not yet arrived) has probability at least `1/588`. -/
lemma prob_lbEvent_ge (hCh : ChernoffBound) (hPNA : PermNegAssoc) (hClos : NegAssocClosure) :
    ∃ K : ℕ, ∀ c : ℕ, K ≤ c + 1 →
      (1 / 588 : ℝ) ≤ prob (lbEvent c (lbM (c + 1)) (lbT (2 / 7) (c + 1))) := by
  obtain ⟨K1, hK1⟩ := lemma_5_1 (2 / 7) (by norm_num) (by norm_num)
  obtain ⟨K2, hK2⟩ := lemma_5_5 hCh hPNA hClos (2 / 7) (by norm_num) (by norm_num)
  refine ⟨max (max K1 K2) (9408 ^ 2), fun c hc => ?_⟩
  have h1 := hK1 (c + 1) (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hc)
  have h2 := hK2 (c + 1) (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hc)
  have h3 := exp_neg_sqrt_le (k := c + 1) (le_trans (le_max_right _ _) hc)
  set m := lbM (c + 1)
  set T := lbT (2 / 7) (c + 1)
  have hand := prob_and_ge
    (fun σ : Equiv.Perm (Fin (c * m + 2)) =>
      lbS1 c m ∈ firstSet σ T ∧ lbS2 c m ∈ firstSet σ T)
    (fun σ : Equiv.Perm (Fin (c * m + 2)) =>
      ∃ j < c, Disjoint (firstSet σ T) (lbClique c m j))
  have hcompl := prob_compl (fun σ : Equiv.Perm (Fin (c * m + 2)) =>
      ∃ j < c, Disjoint (firstSet σ T) (lbClique c m j))
  have hmono : prob (fun σ : Equiv.Perm (Fin (c * m + 2)) =>
      (lbS1 c m ∈ firstSet σ T ∧ lbS2 c m ∈ firstSet σ T) ∧
        ∃ j < c, Disjoint (firstSet σ T) (lbClique c m j)) ≤ prob (lbEvent c m T) := by
    apply prob_mono
    rintro σ ⟨⟨hs1, hs2⟩, j, hj, hdisj⟩
    refine ⟨hs1, hs2, j, hj, fun v hv hvj => disjoint_left.1 hdisj hv ?_⟩
    simp [lbClique, hvj]
  have h1' : (2 / 7 : ℝ) ^ 2 / 24 = 1 / 294 := by norm_num
  rw [h1'] at h1
  change (1 / 294 : ℝ) ≤ prob (fun σ : Equiv.Perm (Fin (c * m + 2)) =>
      lbS1 c m ∈ firstSet σ T ∧ lbS2 c m ∈ firstSet σ T) at h1
  change 1 - Real.exp (-Real.sqrt ((c + 1 : ℕ) : ℝ) / 16) ≤
      prob (fun σ : Equiv.Perm (Fin (c * m + 2)) =>
        ∃ j < c, Disjoint (firstSet σ T) (lbClique c m j)) at h2
  linarith

/-- **Theorem 2.**  For all sufficiently large `k` there is an instance of disjoint cliques on
`n ≤ 3 k ln k` vertices (so `k = Ω(n / log n)`) with optimal `k`-clustering cost `1`, on which
every (possibly randomized) online algorithm for k-CC in the random-order model has expected
cost at least `C · ln k · OPT_k` and at least `C · ln n · OPT_k`, for an absolute constant
`C > 0`.  That is, every online algorithm is `Ω(log k)`- (and `Ω(log n)`-) competitive.
Assumes Fact 2.1 (Chernoff), Lemma 5.3 and Lemma 5.4 (negative association), used through
Lemma 5.5.  Randomized algorithms are distributions `w` over deterministic ones. -/
theorem theorem_2 (hCh : ChernoffBound) (hPNA : PermNegAssoc) (hClos : NegAssocClosure) :
    ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ, ∀ k ≥ K, ∃ (n : ℕ) (q : Fin n → ℕ),
      (n : ℝ) ≤ 3 * k * Real.log k ∧ optK (cliqueGraph q) k = 1 ∧
      ∀ (ι : Type) [Fintype ι] (w : ι → ℝ) (A : ι → OnlineAlg n k),
        (∀ i, 0 ≤ w i) → ∑ i, w i = 1 →
        C * Real.log k * optK (cliqueGraph q) k ≤ randExpCost w A (cliqueGraph q) ∧
        C * Real.log n * optK (cliqueGraph q) k ≤ randExpCost w A (cliqueGraph q) := by
  obtain ⟨K, hK⟩ := prob_lbEvent_ge hCh hPNA hClos
  refine ⟨1 / 1764, by norm_num, max K 8, fun k hk => ?_⟩
  have hk8 : 8 ≤ k := le_of_max_le_right hk
  obtain ⟨c, rfl⟩ : ∃ c, k = c + 1 := ⟨k - 1, by omega⟩
  have hk3 : 3 ≤ c + 1 := by omega
  set m := lbM (c + 1)
  have hm : 1 ≤ m := one_le_lbM hk3
  refine ⟨c * m + 2, lbComp c m, ?_, optK_lbGraph hm, ?_⟩
  · -- size of the instance
    set L := Real.log ((c + 1 : ℕ) : ℝ)
    have hkR : (8 : ℝ) ≤ ((c + 1 : ℕ) : ℝ) := by exact_mod_cast hk8
    have hL2 : 2 ≤ L := by
      rw [Real.le_log_iff_exp_le (by positivity)]
      have := Real.exp_one_lt_d9
      have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      nlinarith [Real.exp_pos 1]
    obtain ⟨-, hm2⟩ := lbM_bounds (k := c + 1) (by omega)
    set K' : ℝ := ((c + 1 : ℕ) : ℝ)
    have hn : ((c * m + 2 : ℕ) : ℝ) = (K' - 1) * m + 2 := by simp only [K']; push_cast; ring
    rw [hn]
    have h1 : (K' - 1) * m ≤ (K' - 1) * (2 * L + 1) :=
      mul_le_mul_of_nonneg_left hm2.le (by linarith)
    have h2 : K' * 2 ≤ K' * L := mul_le_mul_of_nonneg_left hL2 (by linarith)
    nlinarith
  · intro ι _ w A hw hw1
    rw [show optK (cliqueGraph (lbComp c m)) (c + 1) = 1 from optK_lbGraph hm, Nat.cast_one,
      mul_one, mul_one]
    set L := Real.log ((c + 1 : ℕ) : ℝ)
    have hL0 : 0 ≤ L := Real.log_nonneg (by norm_cast; omega)
    obtain ⟨hm1, -⟩ := lbM_bounds (k := c + 1) (by omega)
    have hdet : ∀ i, L / 588 ≤ (A i).expCost (lbGraph c m) := by
      intro i
      have h1 := lb_expCost hm (A i) (lbT (2 / 7) (c + 1))
      have h2 := hK c (le_trans (le_max_left _ _) hk)
      have : L / 588 ≤ (m : ℝ) * prob (lbEvent c m (lbT (2 / 7) (c + 1))) / 2 := by
        have : (2 * L) * (1 / 588) ≤ (m : ℝ) * prob (lbEvent c m (lbT (2 / 7) (c + 1))) :=
          mul_le_mul hm1 h2 (by norm_num) (Nat.cast_nonneg _)
        linarith
      linarith
    have hrand := le_randExpCost w A (lbGraph c m) hw hw1 (L / 588) hdet
    unfold lbGraph at hrand
    refine ⟨by linarith, ?_⟩
    -- `ln n ≤ 3 ln k`
    have hkR : (1 : ℝ) ≤ ((c + 1 : ℕ) : ℝ) := by norm_cast; omega
    have hn : ((c * m + 2 : ℕ) : ℝ) ≤ ((c + 1 : ℕ) : ℝ) ^ 3 := by
      obtain ⟨-, hm2⟩ := lbM_bounds (k := c + 1) (by omega)
      have hLk : L ≤ ((c + 1 : ℕ) : ℝ) - 1 := Real.log_le_sub_one_of_pos (by linarith)
      set K' : ℝ := ((c + 1 : ℕ) : ℝ)
      have hn : ((c * m + 2 : ℕ) : ℝ) = (K' - 1) * m + 2 := by simp only [K']; push_cast; ring
      rw [hn]
      have hk8' : (8 : ℝ) ≤ K' := by simp only [K']; exact_mod_cast hk8
      have h1 : (K' - 1) * m ≤ (K' - 1) * (2 * L + 1) :=
        mul_le_mul_of_nonneg_left hm2.le (by linarith)
      have h2 : (K' - 1) * (2 * L + 1) ≤ (K' - 1) * (2 * K') :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      nlinarith
    have hlogn : Real.log ((c * m + 2 : ℕ) : ℝ) ≤ 3 * L := by
      calc Real.log ((c * m + 2 : ℕ) : ℝ) ≤ Real.log (((c + 1 : ℕ) : ℝ) ^ 3) :=
            Real.log_le_log (by positivity) hn
        _ = 3 * L := by rw [Real.log_pow, Nat.cast_ofNat]
    linarith

end CCK
