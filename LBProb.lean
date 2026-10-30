module

public import RequestProject.LBFail
public import RequestProject.Hyp

/-!
# Probability estimates of Section 5 (Lemmas 5.1, 5.2, 5.5, 5.6)

We use the instance of Section 5 with `k - 1` cliques of size `m = ⌈2 ln k⌉` and two
singletons, and the time `T = ⌊γ k ln k⌋` (the paper uses `m = 2 ln k` and `T = c k ln k`,
ignoring integrality; we write `γ` for the paper's constant `c`).  Because of the rounding, the
explicit thresholds on `k` of the paper are replaced by "for all sufficiently large `k`".
-/

@[expose] public section

open Finset
open scoped Classical

namespace CCK

/-- Clique size of the lower-bound instance, `m = ⌈2 ln k⌉`. -/
noncomputable def lbM (k : ℕ) : ℕ := ⌈2 * Real.log k⌉₊

/-- The time `T = ⌊γ k ln k⌋` of Section 5. -/
noncomputable def lbT (γ : ℝ) (k : ℕ) : ℕ := ⌊γ * k * Real.log k⌋₊

/-- Auxiliary result for Lemmas 5.1 to 5.6 (Section 5). -/
lemma one_le_log_of_three_le {k : ℕ} (hk : 3 ≤ k) : 1 ≤ Real.log k := by
  rw [Real.le_log_iff_exp_le (by positivity)]
  have := Real.exp_one_lt_d9
  have : (3 : ℝ) ≤ k := by exact_mod_cast hk
  linarith

/-- Auxiliary result for Lemmas 5.1 to 5.6 (Section 5). -/
lemma lbM_bounds {k : ℕ} (hk : 1 ≤ k) :
    2 * Real.log k ≤ lbM k ∧ (lbM k : ℝ) < 2 * Real.log k + 1 := by
  have hL : 0 ≤ Real.log k := Real.log_nonneg (by exact_mod_cast hk)
  exact ⟨Nat.le_ceil _, Nat.ceil_lt_add_one (by linarith)⟩

/-- Auxiliary result for Lemmas 5.1 to 5.6 (Section 5). -/
lemma lbT_bounds (γ : ℝ) (hγ : 0 ≤ γ) {k : ℕ} (hk : 1 ≤ k) :
    γ * k * Real.log k - 1 < lbT γ k ∧ (lbT γ k : ℝ) ≤ γ * k * Real.log k := by
  have hL : 0 ≤ Real.log k := Real.log_nonneg (by exact_mod_cast hk)
  unfold lbT
  refine ⟨by linarith [Nat.lt_floor_add_one (γ * k * Real.log k)], Nat.floor_le ?_⟩
  positivity

/-- Auxiliary result for Lemmas 5.1 to 5.6 (Section 5). -/
lemma one_le_lbM {k : ℕ} (hk : 3 ≤ k) : 1 ≤ lbM k := by
  have := (lbM_bounds (by omega : 1 ≤ k)).1
  have := one_le_log_of_three_le hk
  have : (1 : ℝ) ≤ lbM k := by linarith
  exact_mod_cast this

/-- The number of vertices `n = (k-1) m + 2` as a real number. -/
lemma lbN_cast {k : ℕ} (hk : 1 ≤ k) :
    (((k - 1) * lbM k + 2 : ℕ) : ℝ) = ((k : ℝ) - 1) * lbM k + 2 := by
  push_cast [Nat.cast_sub hk]; ring

/-- **Lemma 5.1 (both singletons arrive).**  For any constant `0 < γ < 1` and all sufficiently
large `k`, with probability at least `γ² / 24` both singletons arrive by time `T = ⌊γ k ln k⌋`.
(The paper states the threshold `k ≥ 2/γ` for the idealized real-valued parameters.) -/
theorem lemma_5_1 (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    ∃ K : ℕ, ∀ k ≥ K, γ ^ 2 / 24 ≤
      prob (fun σ : Equiv.Perm (Fin ((k - 1) * lbM k + 2)) =>
        lbS1 (k - 1) (lbM k) ∈ firstSet σ (lbT γ k) ∧
          lbS2 (k - 1) (lbM k) ∈ firstSet σ (lbT γ k)) := by
  refine ⟨max 3 ⌈8 / γ⌉₊, fun k hk => ?_⟩
  have hk3 : 3 ≤ k := le_of_max_le_left hk
  have hk1 : 1 ≤ k := by omega
  have hkγ : 8 ≤ γ * k := by
    have h := le_of_max_le_right hk
    have : 8 / γ ≤ (k : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast h)
    rw [div_le_iff₀ hγ0] at this; linarith
  set L := Real.log k with hLdef
  have hL : 1 ≤ L := one_le_log_of_three_le hk3
  have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk3
  obtain ⟨hm1, hm2⟩ := lbM_bounds hk1
  obtain ⟨hT1, hT2⟩ := lbT_bounds γ hγ0.le hk1
  rw [← hLdef] at hm1 hm2 hT1 hT2
  set m := lbM k
  set T := lbT γ k
  set N := (k - 1) * m + 2
  have hN : (N : ℝ) = ((k : ℝ) - 1) * m + 2 := lbN_cast hk1
  have hTN : T ≤ N := by
    have : (T : ℝ) ≤ N := by
      rw [hN]
      have : γ * k * L ≤ 2 * ((k : ℝ) - 1) * L := by nlinarith
      nlinarith
    exact_mod_cast this
  rw [prob_pair_firstSet hTN _ _ lbS1_ne_lbS2, hN]
  have hb2 : (2 : ℝ) ≤ ((k : ℝ) - 1) * m + 2 := by
    have : (0 : ℝ) ≤ ((k : ℝ) - 1) * m := by
      apply mul_nonneg (by linarith) (Nat.cast_nonneg _)
    linarith
  have hbub : ((k : ℝ) - 1) * m + 2 ≤ k * (2 * L + 1) + 2 := by nlinarith
  have hkey : γ * (((k : ℝ) - 1) * m + 2) ≤ 4.5 * ((T : ℝ) - 1) := by
    have h1 : γ * (((k : ℝ) - 1) * m + 2) ≤ γ * (k * (2 * L + 1) + 2) :=
      mul_le_mul_of_nonneg_left hbub hγ0.le
    have h2 : γ * k ≤ γ * k * L := by nlinarith
    nlinarith
  have hT7 : (7 : ℝ) ≤ T := by nlinarith
  rw [le_div_iff₀ (by nlinarith)]
  set b := ((k : ℝ) - 1) * m + 2
  set a := (T : ℝ)
  have h3 : (γ * b) ^ 2 ≤ (4.5 * (a - 1)) ^ 2 := by
    apply pow_le_pow_left₀ (by positivity) hkey
  nlinarith

end CCK


/-!
# Lemmas 5.2, 5.5 and 5.6

Negative association of the indicators "clique `j` has no vertex arrived by time `T`"
(Lemma 5.2, derived from Lemmas 5.3 and 5.4), and the Chernoff-based estimates that some clique
(Lemma 5.5), resp. two cliques (Lemma 5.6), have no vertex arrived by time `T`.
-/

@[expose] public section

open Finset
open scoped Classical

namespace CCK

variable {c m : ℕ}

/-- The vertex set of clique `j` of the lower-bound instance. -/
noncomputable def lbClique (c m j : ℕ) : Finset (Fin (c * m + 2)) :=
  univ.filter (fun w => lbComp c m w = j)

/-- Every clique has exactly `m` vertices. -/
lemma card_lbClique (hm : 1 ≤ m) {j : ℕ} (hj : j < c) : (lbClique c m j).card = m := by
  apply le_antisymm
  · have := card_le_card_of_injOn (s := lbClique c m j) (t := range m)
      (fun w => (w : ℕ) % m) (by
      intro w _
      simp only [coe_range, Set.mem_Iio]
      exact Nat.mod_lt _ (by omega)) (by
      intro w hw w' hw' h
      simp only [lbClique, coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hw hw'
      have hlt : ∀ x : Fin (c * m + 2), lbComp c m x = j → (x : ℕ) < c * m := by
        intro x hx
        by_contra hc
        simp only [lbComp, hc, if_false] at hx
        omega
      have hw1 := hlt w hw
      have hw'1 := hlt w' hw'
      simp only [lbComp, hw1, hw'1, if_true] at hw hw'
      apply Fin.ext
      simp only at h
      rw [← Nat.div_add_mod (w : ℕ) m, ← Nat.div_add_mod (w' : ℕ) m, hw, hw', h])
    simpa using this
  · have h := le_card_comp (c := c) hm (u := lbRep c m j) (by
      unfold lbRep; rw [dif_pos hj]
      exact Nat.mul_lt_mul_of_pos_right hj (by omega))
    rw [lbComp_rep hm (by omega)] at h
    exact h

/-- Indicator that clique `j` has no vertex arrived by time `T` (the variable `X_j` of
Lemma 5.2). -/
noncomputable def lbX (c m T : ℕ) (j : Fin c) (σ : Equiv.Perm (Fin (c * m + 2))) : ℝ :=
  if Disjoint (firstSet σ T) (lbClique c m j) then 1 else 0

/-- **Lemma 5.2.**  The indicators `X_1, …, X_{k-1}` that clique `K_j` has no vertex arrived by
time `T` are negatively associated.  Derived from Lemma 5.3 and Lemma 5.4 (assumed). -/
theorem lemma_5_2 (hPNA : PermNegAssoc) (hClos : NegAssocClosure) (c m T : ℕ) :
    NegAssoc (lbX c m T) := by
  set x : Fin (c * m + 2) → ℝ := fun i => if (i : ℕ) < T then 1 else 0
  set Y : Fin (c * m + 2) → Equiv.Perm (Fin (c * m + 2)) → ℝ := fun v σ => x (σ.symm v)
  set F : Fin c → (Fin (c * m + 2) → ℝ) → ℝ :=
    fun j y => if ∀ v ∈ lbClique c m j, y v < 1 / 2 then 1 else 0
  have h := hClos (c * m + 2) (Fin (c * m + 2)) (Fin c) Y (hPNA _ x)
    (fun j => lbClique c m j)
    (by
      intro j j' hjj'
      rw [disjoint_left]
      intro v hv hv'
      simp only [lbClique, mem_filter, mem_univ, true_and] at hv hv'
      exact hjj' (Fin.ext (hv.symm.trans hv')))
    F
    (Or.inr (by
      intro j y y' hyy'
      simp only [F]
      split_ifs with h1 h2 h2
      · exact le_rfl
      · exact absurd (fun v hv => lt_of_le_of_lt (hyy' v) (h1 v hv)) h2
      · exact zero_le_one
      · exact le_rfl))
    (by
      intro j y y' hyy'
      simp only [F]
      congr 1
      apply propext
      constructor
      · intro h v hv; rw [← hyy' v hv]; exact h v hv
      · intro h v hv; rw [hyy' v hv]; exact h v hv)
  convert h using 2 with j
  funext σ
  simp only [lbX, F, Y, x]
  congr 1
  apply propext
  rw [disjoint_left]
  simp only [firstSet, arrTime, mem_filter, mem_univ, true_and]
  constructor
  · intro h v hv
    have := fun hvT => h hvT hv
    split_ifs with h' <;> norm_num
    exact this h'
  · intro h v hvT hv
    have := h v hv
    rw [if_pos hvT] at this
    norm_num at this

/-- `(1 - x)^T ≥ exp(-T x / (1 - x))` for `0 ≤ x < 1`. -/
lemma exp_le_one_sub_pow {x : ℝ} (hx1 : x < 1) (T : ℕ) :
    Real.exp (-(T * x / (1 - x))) ≤ (1 - x) ^ T := by
  have hpos : 0 < 1 - x := by linarith
  have hlog : -(x / (1 - x)) ≤ Real.log (1 - x) := by
    have := Real.one_sub_inv_le_log_of_pos hpos
    have e : 1 - (1 - x)⁻¹ = -(x / (1 - x)) := by field_simp; ring
    linarith
  rw [← Real.exp_log (pow_pos hpos T), Real.log_pow]
  apply Real.exp_le_exp.2
  have : -(T * x / (1 - x)) = T * (-(x / (1 - x))) := by ring
  rw [this]
  exact mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _)

/-- Lower bound on `C(N-m, T)/C(N, T)` from Fact 2.3. -/
lemma choose_ratio_ge (N a b : ℕ) (ha : a ≤ N) (hb : b ≤ N - a) (hN : 0 < N)
    (hD : (0 : ℝ) < N - b + 1 - a) :
    Real.exp (-(b * a / ((N : ℝ) - b + 1 - a))) ≤ ((N - a).choose b : ℝ) / (N.choose b) := by
  have h := (fact_2_3 N a b ha hb hN).1
  have hpos : (0 : ℝ) < N - b + 1 := by
    have : (0 : ℝ) ≤ a := Nat.cast_nonneg _
    linarith
  set x := (a : ℝ) / (N - b + 1)
  have hx0 : 0 ≤ x := div_nonneg (Nat.cast_nonneg _) hpos.le
  have hx1 : x < 1 := by rw [div_lt_one hpos]; linarith
  refine le_trans ?_ h
  convert exp_le_one_sub_pow hx1 b using 3
  simp only [x]
  field_simp

/-- The expected number of cliques with no vertex arrived by time `T`. -/
lemma expect_lbX (hm : 1 ≤ m) {T : ℕ} (hT : T ≤ c * m + 2) :
    expect (fun σ => ∑ j, lbX c m T j σ) =
      c * (((c * m + 2 - m).choose T : ℝ) / ((c * m + 2).choose T)) := by
  rw [expect_sum]
  have : ∀ j : Fin c, expect (lbX c m T j) =
      ((c * m + 2 - m).choose T : ℝ) / ((c * m + 2).choose T) := by
    intro j
    unfold lbX
    rw [expect_indicator, prob_disjoint_firstSet hT, card_lbClique hm j.2]
  rw [sum_congr rfl (fun j _ => this j), sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The key estimate behind Lemma 5.5 (equation (3)): for `0 < γ < 2/5` and all sufficiently
large `k`, the expected number of cliques with no vertex arrived by time `T` is at least
`√k / 2`. -/
lemma expect_lbX_ge (γ : ℝ) (hγ0 : 0 < γ) (hγ : γ < 2 / 5) :
    ∃ K : ℕ, ∀ k ≥ K, Real.sqrt k / 2 ≤
      expect (fun σ => ∑ j, lbX (k - 1) (lbM k) (lbT γ k) j σ) := by
  set ε := 2 - 5 * γ with hε
  have hεpos : 0 < ε := by linarith
  refine ⟨max 3 (max ⌈8 / ε⌉₊ ⌈Real.exp (4 * γ / ε)⌉₊), fun k hk => ?_⟩
  have hk3 : 3 ≤ k := le_of_max_le_left hk
  have hk1 : 1 ≤ k := by omega
  have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk3
  have hkε : 8 ≤ ε * k := by
    have h := le_of_max_le_left (le_of_max_le_right hk)
    have : 8 / ε ≤ (k : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast h)
    rw [div_le_iff₀ hεpos] at this; linarith
  set L := Real.log k with hLdef
  have hLε : 4 * γ ≤ ε * L := by
    have h := le_of_max_le_right (le_of_max_le_right hk)
    have : Real.exp (4 * γ / ε) ≤ (k : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast h)
    have := (Real.le_log_iff_exp_le (by positivity)).2 this
    rw [div_le_iff₀ hεpos] at this; linarith
  have hL : 1 ≤ L := one_le_log_of_three_le hk3
  obtain ⟨hm1, hm2⟩ := lbM_bounds hk1
  obtain ⟨hT1, hT2⟩ := lbT_bounds γ hγ0.le hk1
  rw [← hLdef] at hm1 hm2 hT1 hT2
  have hm : 1 ≤ lbM k := one_le_lbM hk3
  set m := lbM k
  set T := lbT γ k
  set N := (k - 1) * m + 2
  have hN : (N : ℝ) = ((k : ℝ) - 1) * m + 2 := lbN_cast hk1
  have hNm : N - m = (k - 2) * m + 2 := by
    simp only [N]
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
    simp only [Nat.add_sub_cancel, show k' + 2 - 1 = k' + 1 by omega]
    ring_nf; omega
  have hNmR : ((N - m : ℕ) : ℝ) = ((k : ℝ) - 2) * m + 2 := by
    rw [hNm]; push_cast [Nat.cast_sub (by omega : 2 ≤ k)]; ring
  have hTNm : T ≤ N - m := by
    have : (T : ℝ) ≤ ((N - m : ℕ) : ℝ) := by
      rw [hNmR]
      have : γ * k * L ≤ 2 * ((k : ℝ) - 2) * L := by nlinarith
      nlinarith
    exact_mod_cast this
  have hTN : T ≤ N := le_trans hTNm (Nat.sub_le _ _)
  have hmN : m ≤ N := Nat.le_add_right_of_le (Nat.le_mul_of_pos_left m (by omega))
  -- the denominator `D = N - T + 1 - m`
  have hD' : ((2 : ℝ) - γ) * k * L - 4 * L + 2 ≤ (N : ℝ) - T + 1 - m := by
    rw [hN]; nlinarith
  have hmain : 2 * γ * k * L * (2 * L + 1) ≤ L * (((2 : ℝ) - γ) * k * L - 4 * L + 2) := by
    have h1 : ε * k * L ≥ 2 * γ * k + 4 * L := by nlinarith
    nlinarith
  have hDpos : (0 : ℝ) < (N : ℝ) - T + 1 - m := by
    have : (0 : ℝ) < ((2 : ℝ) - γ) * k * L - 4 * L + 2 := by
      by_contra hc; push_neg at hc
      have : (0 : ℝ) < 2 * γ * k * L * (2 * L + 1) := by positivity
      nlinarith
    linarith
  have hratio := choose_ratio_ge N m T hmN hTNm (by omega) hDpos
  have hexp_ge : Real.exp (-(L / 2)) ≤ Real.exp (-(T * m / ((N : ℝ) - T + 1 - m))) := by
    apply Real.exp_le_exp.2
    rw [neg_le_neg_iff, div_le_iff₀ hDpos]
    have h1 : (T : ℝ) * m ≤ γ * k * L * (2 * L + 1) := by
      apply mul_le_mul hT2 hm2.le (Nat.cast_nonneg _) (by positivity)
    have h2 : L * (((2 : ℝ) - γ) * k * L - 4 * L + 2) ≤ L * ((N : ℝ) - T + 1 - m) :=
      mul_le_mul_of_nonneg_left hD' (by linarith)
    have h3 : L / 2 * ((N : ℝ) - T + 1 - m) = (L * ((N : ℝ) - T + 1 - m)) / 2 := by ring
    rw [h3]
    linarith
  rw [expect_lbX hm hTN]
  have hk1R : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by push_cast [Nat.cast_sub hk1]; ring
  rw [hk1R]
  have hsqrt : Real.sqrt k = Real.exp (L / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by positivity)]
    congr 1; ring
  have hkexp : (k : ℝ) = Real.exp (L / 2) * Real.exp (L / 2) := by
    rw [← Real.exp_add, show L / 2 + L / 2 = L by ring, hLdef, Real.exp_log (by positivity)]
  have hprod : Real.exp (L / 2) * Real.exp (-(L / 2)) = 1 := by
    rw [← Real.exp_add]; simp
  rw [hsqrt]
  have hr : Real.exp (-(L / 2)) ≤ ((N - m).choose T : ℝ) / (N.choose T) :=
    hexp_ge.trans hratio
  have hE0 : 0 < Real.exp (L / 2) := Real.exp_pos _
  have hk2 : (k : ℝ) / 2 ≤ (k : ℝ) - 1 := by linarith
  have step1 : Real.exp (L / 2) / 2 = (k : ℝ) / 2 * Real.exp (-(L / 2)) := by
    rw [hkexp, show Real.exp (L / 2) * Real.exp (L / 2) / 2 * Real.exp (-(L / 2)) =
      Real.exp (L / 2) * (Real.exp (L / 2) * Real.exp (-(L / 2))) / 2 by ring, hprod, mul_one]
  have step2 : (k : ℝ) / 2 * Real.exp (-(L / 2)) ≤ ((k : ℝ) - 1) * Real.exp (-(L / 2)) :=
    mul_le_mul_of_nonneg_right hk2 (Real.exp_pos _).le
  have step3 := mul_le_mul_of_nonneg_left hr (show (0 : ℝ) ≤ (k : ℝ) - 1 by linarith)
  rw [step1]
  exact step2.trans step3

/-- Auxiliary result for Lemmas 5.2, 5.5 and 5.6 (Section 5). -/
lemma sum_lbX (c m T : ℕ) (σ : Equiv.Perm (Fin (c * m + 2))) :
    ∑ j, lbX c m T j σ =
      ((univ.filter (fun j : Fin c => Disjoint (firstSet σ T) (lbClique c m j))).card : ℝ) := by
  unfold lbX; rw [sum_boole]

/-- Auxiliary result for Lemmas 5.2, 5.5 and 5.6 (Section 5). -/
lemma sum_lbX_nonneg (c m T : ℕ) (σ : Equiv.Perm (Fin (c * m + 2))) :
    0 ≤ ∑ j, lbX c m T j σ := by
  rw [sum_lbX]; exact Nat.cast_nonneg _

/-- Common Chernoff step of Lemmas 5.5 and 5.6: the number `X` of cliques with no vertex arrived
by time `T` satisfies `P[X ≤ E[X]/2] ≤ exp(-E[X]/8)`. -/
lemma prob_sum_lbX_le_half (hCh : ChernoffBound) (hPNA : PermNegAssoc)
    (hClos : NegAssocClosure) (c m T : ℕ) :
    prob (fun σ : Equiv.Perm (Fin (c * m + 2)) => ∑ j, lbX c m T j σ ≤
        (1 - 1 / 2) * expect (fun τ => ∑ j, lbX c m T j τ)) ≤
      Real.exp (-((1 / 2) ^ 2 * expect (fun τ => ∑ j, lbX c m T j τ)) / 2) := by
  have h01 : ∀ j σ, lbX c m T j σ = 0 ∨ lbX c m T j σ = 1 := by
    intro j σ; unfold lbX; split_ifs <;> simp
  exact (hCh (c * m + 2) (Fin c) (lbX c m T) h01 (lemma_5_2 hPNA hClos c m T)).2.1 (1 / 2)
    (by norm_num) (by norm_num)

/-- **Lemma 5.5 (at least one large clique missing).**  For `0 < γ < 2/5` and all sufficiently
large `k`, with probability at least `1 - e^{-√k/16}` some clique has no vertex arrived by time
`T = ⌊γ k ln k⌋`.  Assumes Fact 2.1, Lemma 5.3 and Lemma 5.4. -/
theorem lemma_5_5 (hCh : ChernoffBound) (hPNA : PermNegAssoc) (hClos : NegAssocClosure)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ : γ < 2 / 5) :
    ∃ K : ℕ, ∀ k ≥ K, 1 - Real.exp (-Real.sqrt k / 16) ≤
      prob (fun σ : Equiv.Perm (Fin ((k - 1) * lbM k + 2)) =>
        ∃ j < k - 1, Disjoint (firstSet σ (lbT γ k)) (lbClique (k - 1) (lbM k) j)) := by
  obtain ⟨K, hK⟩ := expect_lbX_ge γ hγ0 hγ
  refine ⟨K, fun k hk => ?_⟩
  have hμ := hK k hk
  set μ := expect (fun σ => ∑ j, lbX (k - 1) (lbM k) (lbT γ k) j σ)
  have hch := prob_sum_lbX_le_half hCh hPNA hClos (k - 1) (lbM k) (lbT γ k)
  have hsq : 0 ≤ Real.sqrt k := Real.sqrt_nonneg _
  have hcompl := prob_compl (fun σ : Equiv.Perm (Fin ((k - 1) * lbM k + 2)) =>
    ∃ j < k - 1, Disjoint (firstSet σ (lbT γ k)) (lbClique (k - 1) (lbM k) j))
  have hmono : prob (fun σ : Equiv.Perm (Fin ((k - 1) * lbM k + 2)) =>
      ¬ ∃ j < k - 1, Disjoint (firstSet σ (lbT γ k)) (lbClique (k - 1) (lbM k) j)) ≤
      prob (fun σ : Equiv.Perm (Fin ((k - 1) * lbM k + 2)) =>
        ∑ j, lbX (k - 1) (lbM k) (lbT γ k) j σ ≤ (1 - 1 / 2) * μ) := by
    apply prob_mono
    intro σ hσ
    have : ∑ j, lbX (k - 1) (lbM k) (lbT γ k) j σ = 0 := by
      rw [sum_lbX]
      norm_cast
      rw [card_eq_zero, filter_eq_empty_iff]
      intro j _ hj
      exact hσ ⟨j, j.2, hj⟩
    rw [this]; nlinarith
  have hexp : Real.exp (-((1 / 2) ^ 2 * μ) / 2) ≤ Real.exp (-Real.sqrt k / 16) := by
    apply Real.exp_le_exp.2; nlinarith
  linarith

/-- **Lemma 5.6 (two cliques arrive late).**  For `0 < γ < 2/5` and all sufficiently large `k`,
with probability at least `1 - e^{-√k/16}` at least two cliques have no vertex arrived by time
`T = ⌊γ k ln k⌋`.  Assumes Fact 2.1, Lemma 5.3 and Lemma 5.4. -/
theorem lemma_5_6 (hCh : ChernoffBound) (hPNA : PermNegAssoc) (hClos : NegAssocClosure)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ : γ < 2 / 5) :
    ∃ K : ℕ, ∀ k ≥ K, 1 - Real.exp (-Real.sqrt k / 16) ≤
      prob (fun σ : Equiv.Perm (Fin ((k - 1) * lbM k + 2)) =>
        ∃ j₁ < k - 1, ∃ j₂ < k - 1, j₁ ≠ j₂ ∧
          Disjoint (firstSet σ (lbT γ k)) (lbClique (k - 1) (lbM k) j₁) ∧
          Disjoint (firstSet σ (lbT γ k)) (lbClique (k - 1) (lbM k) j₂)) := by
  obtain ⟨K, hK⟩ := expect_lbX_ge γ hγ0 hγ
  refine ⟨max K 16, fun k hk => ?_⟩
  have hμ := hK k (le_of_max_le_left hk)
  have hk16 : (16 : ℝ) ≤ k := by exact_mod_cast le_of_max_le_right hk
  have hsq4 : 4 ≤ Real.sqrt k := by
    rw [show (4 : ℝ) = Real.sqrt 16 by
      rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hk16
  set μ := expect (fun σ => ∑ j, lbX (k - 1) (lbM k) (lbT γ k) j σ)
  have hch := prob_sum_lbX_le_half hCh hPNA hClos (k - 1) (lbM k) (lbT γ k)
  set P := fun σ : Equiv.Perm (Fin ((k - 1) * lbM k + 2)) =>
    ∃ j₁ < k - 1, ∃ j₂ < k - 1, j₁ ≠ j₂ ∧
      Disjoint (firstSet σ (lbT γ k)) (lbClique (k - 1) (lbM k) j₁) ∧
      Disjoint (firstSet σ (lbT γ k)) (lbClique (k - 1) (lbM k) j₂) with hP
  have hcompl := prob_compl P
  have hmono : prob (fun σ => ¬ P σ) ≤
      prob (fun σ : Equiv.Perm (Fin ((k - 1) * lbM k + 2)) =>
        ∑ j, lbX (k - 1) (lbM k) (lbT γ k) j σ ≤ (1 - 1 / 2) * μ) := by
    apply prob_mono
    intro σ hσ
    have : ∑ j, lbX (k - 1) (lbM k) (lbT γ k) j σ ≤ 1 := by
      rw [sum_lbX]
      norm_cast
      by_contra hc
      push_neg at hc
      obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.1 hc
      simp only [mem_filter, mem_univ, true_and] at ha hb
      exact hσ ⟨a, a.2, b, b.2, fun h => hab (Fin.ext h), ha, hb⟩
    linarith
  have hexp : Real.exp (-((1 / 2) ^ 2 * μ) / 2) ≤ Real.exp (-Real.sqrt k / 16) := by
    apply Real.exp_le_exp.2; nlinarith
  linarith

end CCK
