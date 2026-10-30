module

public import RequestProject.BPCost

/-!
# Lemma 7.8 (the least loaded cluster has bounded projected load)

Deterministic part: on the good events of Lemmas 7.5 and 7.7 and of the concentration of the
number of uncovered vertices arriving in a time interval, the projected load of the cluster
chosen by any late pivot is bounded in terms of an arbitrary non-empty set `S` of early pivot
clusters.
-/

@[expose] public section

open Finset
open scoped Classical

namespace CCK

variable {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) (σ : Equiv.Perm (Fin n))

/-! ### Current loads -/

/-- The current load of a cluster is the sum of the current sizes of its pivot clusters. -/
lemma clLoad_eq_sum (t j : ℕ) :
    clLoad G k σ t j = ∑ r ∈ (pivotsUpTo G σ t).filter (fun r => bpLabel G k σ r = j),
      pclAt G σ r t := by
  unfold clLoad pclAt
  rw [card_eq_sum_card_fiberwise (f := pivotOf G σ)
    (t := (pivotsUpTo G σ t).filter (fun r => bpLabel G k σ r = j))]
  · refine sum_congr rfl (fun r hr => ?_)
    congr 1
    ext u
    simp only [mem_filter, mem_inter, mem_univ, true_and]
    constructor
    · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, rfl⟩
      exact ⟨⟨h1, (bpLabel_pivotOf G k σ u).symm.trans (mem_filter.1 hr).2⟩, rfl⟩
  · intro u hu
    obtain ⟨hu1, hu2⟩ := mem_filter.1 (mem_coe.1 hu)
    obtain ⟨h1, h2⟩ := exists_pivot_of_mem_firstSet G k σ hu1
    simp only [coe_filter, Set.mem_setOf_eq]
    exact ⟨h1, h2.trans hu2⟩

/-- Auxiliary result for Lemma 7.8 (Section 7.3.2). -/
lemma pivotsUpTo_subset_univ_card (t : ℕ) : (pivotsUpTo G σ t).card ≤ t := by
  refine (card_le_card (pivotsUpTo_subset_firstSet G σ t)).trans ?_
  unfold firstSet
  calc ((univ : Finset (Fin n)).filter (fun v => arrTime σ v < t)).card
      ≤ ((range t).attach).card := by
        rw [card_attach]
        apply card_le_card_of_injOn (fun v => arrTime σ v)
        · intro v hv; simpa using hv
        · intro u _ v _ h; exact eq_of_arrTime_eq σ h
    _ = t := by simp

/-- `T ≥ k` (`T ≥ 1` for `k ≥ 1`) when there are more than `k` pivots. -/
lemma k_le_Tk (h : ∃ t, k < (pivotsUpTo G σ (t + 1)).card) : k ≤ Tk G k σ := by
  have := (Tk_spec G k σ h).2.1
  have := pivotsUpTo_subset_univ_card G σ (Tk G k σ)
  omega

/-- Early pivots occupy distinct clusters. -/
lemma bpLabel_injOn_early (hk : 0 < k) {q r : Fin n} (hq : q ∈ pivotsUpTo G σ (Tk G k σ))
    (hr : r ∈ pivotsUpTo G σ (Tk G k σ)) (h : bpLabel G k σ q = bpLabel G k σ r) : q = r := by
  obtain ⟨hq1, hq2⟩ := (mem_pivotsUpTo_iff G σ _ q).1 hq
  obtain ⟨hr1, hr2⟩ := (mem_pivotsUpTo_iff G σ _ r).1 hr
  by_contra hne
  have hne' : arrTime σ q ≠ arrTime σ r := fun h' => hne (eq_of_arrTime_eq σ h')
  rcases Nat.lt_or_gt_of_ne hne' with hlt | hlt
  · exact bpLabel_ne_of_early G k σ hk hr1 (card_lt_of_arrTime_lt_Tk G k σ hr1 hr2) hlt h
  · exact bpLabel_ne_of_early G k σ hk hq1 (card_lt_of_arrTime_lt_Tk G k σ hq1 hq2) hlt h.symm

/-- The late part of the current load of the cluster of an early pivot `q`. -/
noncomputable def lateLoad (t : ℕ) (q : Fin n) : ℕ :=
  ∑ r ∈ (pivotsUpTo G σ t).filter (fun r => Tk G k σ ≤ arrTime σ r ∧
    bpLabel G k σ r = bpLabel G k σ q), pclAt G σ r t

/-- For an early pivot `q` and `t ≥ T`, the current load of its cluster is `p_t(q)` plus its late
part. -/
lemma clLoad_early_eq (hk : 0 < k) {t : ℕ} (_ht : t ≤ n) (hTt : Tk G k σ ≤ t) {q : Fin n}
    (hq : q ∈ pivotsUpTo G σ (Tk G k σ)) :
    clLoad G k σ t (bpLabel G k σ q) = pclAt G σ q t + lateLoad G k σ t q := by
  rw [clLoad_eq_sum G k σ, lateLoad]
  have hqt : q ∈ pivotsUpTo G σ t := pivotsUpTo_mono G σ hTt hq
  have hsplit : (pivotsUpTo G σ t).filter (fun r => bpLabel G k σ r = bpLabel G k σ q) =
      insert q ((pivotsUpTo G σ t).filter (fun r => Tk G k σ ≤ arrTime σ r ∧
        bpLabel G k σ r = bpLabel G k σ q)) := by
    ext r
    simp only [mem_filter, mem_insert]
    constructor
    · rintro ⟨hr, hl⟩
      by_cases hTr : Tk G k σ ≤ arrTime σ r
      · exact Or.inr ⟨hr, hTr, hl⟩
      · left
        push_neg at hTr
        have hr' : r ∈ pivotsUpTo G σ (Tk G k σ) :=
          (mem_pivotsUpTo_iff G σ _ r).2 ⟨((mem_pivotsUpTo_iff G σ _ r).1 hr).1, hTr⟩
        exact bpLabel_injOn_early G k σ hk hr' hq hl
    · rintro (rfl | ⟨hr, -, hl⟩)
      · exact ⟨hqt, rfl⟩
      · exact ⟨hr, hl⟩
  have hnot : q ∉ (pivotsUpTo G σ t).filter (fun r => Tk G k σ ≤ arrTime σ r ∧
      bpLabel G k σ r = bpLabel G k σ q) := by
    intro h
    have := ((mem_pivotsUpTo_iff G σ _ q).1 hq).2
    have := (mem_filter.1 h).2.1
    omega
  rw [hsplit, sum_insert hnot]

/-- The late parts of distinct early clusters together count vertices uncovered at time `T`
arriving before `t`. -/
lemma sum_lateLoad_le (hk : 0 < k) {t : ℕ} {S : Finset (Fin n)}
    (hS : S ⊆ pivotsUpTo G σ (Tk G k σ)) :
    ∑ q ∈ S, lateLoad G k σ t q ≤ (firstSet σ t ∩ uncovered G σ (Tk G k σ)).card := by
  unfold lateLoad
  rw [← sum_biUnion]
  · set R := (pivotsUpTo G σ t).filter (fun r => Tk G k σ ≤ arrTime σ r)
    have hsub : S.biUnion (fun q => (pivotsUpTo G σ t).filter (fun r => Tk G k σ ≤ arrTime σ r ∧
        bpLabel G k σ r = bpLabel G k σ q)) ⊆ R := by
      intro r hr
      obtain ⟨q, -, hr⟩ := mem_biUnion.1 hr
      exact mem_filter.2 ⟨(mem_filter.1 hr).1, (mem_filter.1 hr).2.1⟩
    refine (sum_le_sum_of_subset hsub).trans (le_of_eq ?_)
    unfold pclAt
    rw [← card_biUnion]
    · congr 1
      ext u
      simp only [mem_biUnion, mem_inter, mem_filter, mem_univ, true_and, R]
      constructor
      · rintro ⟨r, ⟨-, hTr⟩, hu, rfl⟩
        exact ⟨hu, (mem_uncovered_iff_late G σ _ u).2 hTr⟩
      · rintro ⟨hu, hunc⟩
        refine ⟨pivotOf G σ u, ⟨(exists_pivot_of_mem_firstSet G k σ hu).1,
          (mem_uncovered_iff_late G σ _ u).1 hunc⟩, hu, rfl⟩
    · intro r _ r' _ hne
      simp only [Function.onFun]
      rw [disjoint_left]
      intro u hu hu'
      simp only [mem_inter, mem_filter, mem_univ, true_and] at hu hu'
      exact hne (hu.2.symm.trans hu'.2)
  · intro q hq q' hq' hne
    simp only [Function.onFun]
    rw [disjoint_left]
    intro r hr hr'
    simp only [mem_filter] at hr hr'
    exact hne (bpLabel_injOn_early G k σ hk (hS hq) (hS hq') (hr.2.2.symm.trans hr'.2.2))

/-- Some early cluster in `S` has a small late part. -/
lemma exists_lateLoad_le (hk : 0 < k) {t : ℕ} {S : Finset (Fin n)}
    (hS : S ⊆ pivotsUpTo G σ (Tk G k σ)) (hSne : S.Nonempty) :
    ∃ q ∈ S, (S.card : ℝ) * lateLoad G k σ t q ≤
      (firstSet σ t ∩ uncovered G σ (Tk G k σ)).card := by
  obtain ⟨q, hq, hmin⟩ := S.exists_min_image (lateLoad G k σ t) hSne
  refine ⟨q, hq, ?_⟩
  have h1 : S.card * lateLoad G k σ t q ≤ ∑ q' ∈ S, lateLoad G k σ t q' := by
    rw [← smul_eq_mul, ← sum_const]
    exact sum_le_sum (fun q' hq' => hmin q' hq')
  exact_mod_cast h1.trans (sum_lateLoad_le G k σ hk hS)

/-! ### The good events -/

/-- The good event of Lemma 7.7, for all pivots and times simultaneously. -/
def Good78 (c : ℝ) : Prop :=
  ∀ v t, arrTime σ v < t → t ≤ n → IsPivot G σ v →
    (pclAt G σ v t : ℝ) ≤ 1 + 2 * (pclSize G σ v : ℝ) * t / n + c * Real.log n

/-- The good event of Lemma 7.5, for all times simultaneously. -/
def Good76 (c : ℝ) : Prop :=
  ∀ t ≤ n, ∀ v, arrTime σ v + 1 < t → IsPivot G σ v →
    (pclSize G σ v : ℝ) < 4 * n * (pclAt G σ v t : ℝ) / t + 2 * c * n * Real.log n / t + 1

/-- Concentration of the number of vertices uncovered at time `s` arriving before time `t`. -/
def GoodX (c : ℝ) : Prop :=
  ∀ s t, s ≤ t → t ≤ n →
    ((firstSet σ t ∩ uncovered G σ s).card : ℝ) ≤
      c * Real.log n + 2 * (uncovered G σ s).card * t / n

/-- The good event used for the projected load bound (Lemma 7.8). -/
def GoodLoad (c : ℝ) : Prop := Good78 G σ c ∧ Good76 G σ c ∧ GoodX G σ c

/-! ### The deterministic bound -/

/-- Auxiliary result for Lemma 7.8 (Section 7.3.2). -/
lemma pclAt_succ_of_pivot {p r : Fin n} (hp : IsPivot G σ p) (hr : arrTime σ r < arrTime σ p) :
    pclAt G σ r (arrTime σ p + 1) = pclAt G σ r (arrTime σ p) := by
  unfold pclAt
  congr 1
  ext u
  simp only [mem_inter, mem_filter, mem_univ, true_and, firstSet]
  constructor
  · rintro ⟨hu1, hu2⟩
    refine ⟨?_, hu2⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hu1 with h | h
    · exact h
    · exfalso
      have hup : u = p := eq_of_arrTime_eq σ h
      rw [hup, pivotOf_of_isPivot G σ hp] at hu2
      rw [hu2] at hr
      exact lt_irrefl _ hr
  · rintro ⟨hu1, hu2⟩; exact ⟨by omega, hu2⟩

/-- Step 1 of the proof of Lemma 7.8: on the good event of Lemma 7.5, the projected load of a
cluster at the arrival time `t` of a pivot `p` is at most its current load times
`4n/t + 2cn ln n/t + 1`. -/
lemma projLoad_le_clLoad_mul {c : ℝ} (hc : 0 ≤ c) (hn : 2 ≤ n) (hG76 : Good76 G σ c)
    {p : Fin n} (hp : IsPivot G σ p) (ht1 : 1 ≤ arrTime σ p) (j : ℕ) :
    (projLoad G k σ (arrTime σ p) j : ℝ) ≤ (clLoad G k σ (arrTime σ p) j : ℝ) *
      (4 * n / arrTime σ p + 2 * c * n * Real.log n / arrTime σ p + 1) := by
  have htn : arrTime σ p < n := arrTime_lt σ p
  have htR : (1 : ℝ) ≤ arrTime σ p := by exact_mod_cast ht1
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  unfold projLoad
  rw [clLoad_eq_sum G k σ]
  push_cast
  rw [sum_mul]
  apply sum_le_sum
  intro r hr
  obtain ⟨hrpiv, hrarr⟩ := (mem_pivotsUpTo_iff G σ _ r).1 (mem_filter.1 hr).1
  have h76 := hG76 (arrTime σ p + 1) (by omega) r (by omega) hrpiv
  rw [pclAt_succ_of_pivot G σ hp hrarr] at h76
  have hone : (1 : ℝ) ≤ pclAt G σ r (arrTime σ p) := by
    exact_mod_cast one_le_pclAt G σ hrpiv hrarr
  set a : ℝ := (pclAt G σ r (arrTime σ p) : ℝ)
  set t : ℝ := (arrTime σ p : ℝ)
  have ht' : (((arrTime σ p + 1 : ℕ) : ℝ)) = t + 1 := by push_cast; rfl
  rw [ht'] at h76
  have e1 : 4 * (n : ℝ) * a / (t + 1) ≤ a * (4 * n / t) := by
    rw [mul_div_assoc', mul_comm a]
    exact div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)
  have e2 : 2 * c * (n : ℝ) * Real.log n / (t + 1) ≤ a * (2 * c * n * Real.log n / t) := by
    have h0 : 0 ≤ 2 * c * (n : ℝ) * Real.log n / t := by positivity
    calc 2 * c * (n : ℝ) * Real.log n / (t + 1) ≤ 2 * c * (n : ℝ) * Real.log n / t :=
          div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)
      _ ≤ _ := le_mul_of_one_le_left h0 hone
  nlinarith

/-- Step 2 of the proof of Lemma 7.8: on the good events of Lemma 7.7 and of the concentration of
uncovered arrivals, the current load of the cluster chosen by a late pivot is small. -/
lemma clLoad_le_of_good (hk : 0 < k) {c : ℝ} (hG78 : Good78 G σ c) (hGX : GoodX G σ c)
    {p : Fin n} (hp : IsPivot G σ p) (hpT : Tk G k σ ≤ arrTime σ p)
    {S : Finset (Fin n)} (hS : S ⊆ pivotsUpTo G σ (Tk G k σ)) (hSne : S.Nonempty) :
    (clLoad G k σ (arrTime σ p) (bpLabel G k σ p) : ℝ) ≤
      1 + 2 * ((S.sup (pclSize G σ) : ℕ) : ℝ) * arrTime σ p / n + c * Real.log n +
        (c * Real.log n + 2 * (uncovered G σ (Tk G k σ)).card * arrTime σ p / n) / S.card := by
  have htn : arrTime σ p < n := arrTime_lt σ p
  have hScard : (0 : ℝ) < S.card := by exact_mod_cast hSne.card_pos
  obtain ⟨q, hqS, hq⟩ := exists_lateLoad_le G k σ hk hS hSne (t := arrTime σ p)
  have hqT := hS hqS
  obtain ⟨hqpiv, hqarr⟩ := (mem_pivotsUpTo_iff G σ _ q).1 hqT
  have h1 := clLoad_bpLabel_le G k σ hk hp (bpLabel_lt G k σ hk q)
  rw [clLoad_early_eq G k σ hk htn.le hpT hqT] at h1
  have h1' : (clLoad G k σ (arrTime σ p) (bpLabel G k σ p) : ℝ) ≤
      pclAt G σ q (arrTime σ p) + lateLoad G k σ (arrTime σ p) q := by exact_mod_cast h1
  have hq78 := hG78 q (arrTime σ p) (by omega) htn.le hqpiv
  have hqμ' : pclSize G σ q ≤ S.sup (pclSize G σ) := le_sup hqS
  have hqμ : (pclSize G σ q : ℝ) ≤ ((S.sup (pclSize G σ) : ℕ) : ℝ) := by exact_mod_cast hqμ'
  have hXb := hGX (Tk G k σ) (arrTime σ p) hpT htn.le
  have hlate : (lateLoad G k σ (arrTime σ p) q : ℝ) ≤
      (c * Real.log n + 2 * (uncovered G σ (Tk G k σ)).card * arrTime σ p / n) / S.card := by
    rw [le_div_iff₀ hScard, mul_comm]; linarith
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have ht0 : (0 : ℝ) ≤ arrTime σ p := Nat.cast_nonneg _
  have : 2 * (pclSize G σ q : ℝ) * arrTime σ p / n ≤
      2 * ((S.sup (pclSize G σ) : ℕ) : ℝ) * arrTime σ p / n := by
    apply div_le_div_of_nonneg_right _ hn0
    nlinarith
  linarith

/-- Step 3 of the proof of Lemma 7.8: the arithmetic. -/
lemma lemma79_arith {n t T c μ U s x P : ℝ} (hc : 0 ≤ c) (hl : 0 ≤ Real.log n) (hT1 : 1 ≤ T)
    (hTt : T ≤ t) (htn : t ≤ n) (hs : 1 ≤ s) (_hμ : 0 ≤ μ) (_hU : 0 ≤ U) (hx0 : 0 ≤ x)
    (hP : P ≤ x * (4 * n / t + 2 * c * n * Real.log n / t + 1))
    (hx : x ≤ 1 + 2 * μ * t / n + c * Real.log n + (c * Real.log n + 2 * U * t / n) / s) :
    P ≤ (5 + 2 * c * Real.log n) * (n / T * (1 + 2 * c * Real.log n) + 2 * μ + 2 * U / s) := by
  have ht0 : 0 < t := by linarith
  have hn0 : 0 < n := by linarith
  have hcl : 0 ≤ c * Real.log n := mul_nonneg hc hl
  have hnt : 1 ≤ n / t := by rw [le_div_iff₀ ht0]; linarith
  have hntT : n / t ≤ n / T := div_le_div_of_nonneg_left hn0.le (by linarith) hTt
  have hK : 4 * n / t + 2 * c * n * Real.log n / t + 1 ≤ n / t * (5 + 2 * c * Real.log n) := by
    have e : 4 * n / t + 2 * c * n * Real.log n / t = n / t * (4 + 2 * c * Real.log n) := by
      field_simp
    rw [e]; nlinarith
  have hnx : n / t * x ≤ n / t * (1 + 2 * c * Real.log n) + 2 * μ + 2 * U / s := by
    have h1 := mul_le_mul_of_nonneg_left hx (show 0 ≤ n / t by positivity)
    have e : n / t * (1 + 2 * μ * t / n + c * Real.log n + (c * Real.log n + 2 * U * t / n) / s) =
        n / t * (1 + c * Real.log n) + 2 * μ + (n / t * (c * Real.log n) + 2 * U) / s := by
      have hs0 : s ≠ 0 := by linarith
      field_simp
      ring
    rw [e] at h1
    have h2 : (n / t * (c * Real.log n) + 2 * U) / s ≤ n / t * (c * Real.log n) + 2 * U / s := by
      rw [add_div]
      have : n / t * (c * Real.log n) / s ≤ n / t * (c * Real.log n) :=
        div_le_self (by positivity) hs
      linarith
    nlinarith
  have hfin : n / t * (1 + 2 * c * Real.log n) ≤ n / T * (1 + 2 * c * Real.log n) :=
    mul_le_mul_of_nonneg_right hntT (by linarith)
  calc P ≤ x * (4 * n / t + 2 * c * n * Real.log n / t + 1) := hP
    _ ≤ x * (n / t * (5 + 2 * c * Real.log n)) := mul_le_mul_of_nonneg_left hK hx0
    _ = (5 + 2 * c * Real.log n) * (n / t * x) := by ring
    _ ≤ (5 + 2 * c * Real.log n) * (n / T * (1 + 2 * c * Real.log n) + 2 * μ + 2 * U / s) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        linarith

/-- **Lemma 7.8 (deterministic part).**  On the good event, for every late pivot `p` (arriving at
time `t ≥ T`) and every non-empty set `S` of early pivots, the projected load of the cluster in
which `p` is placed (a least loaded cluster at time `t`) is at most
`(5 + 2c ln n) ((n/T)(1 + 2c ln n) + 2 μ(S) + 2 |U| / |S|)`, where `μ(S)` is the maximum final
size of a pivot cluster of `S` and `U` is the set of vertices uncovered at time `T`. -/
theorem projLoad_le_of_good (hk : 0 < k) {c : ℝ} (hc : 0 ≤ c) (hn : 2 ≤ n)
    (hG : GoodLoad G σ c) {p : Fin n} (hp : IsPivot G σ p) (hpT : Tk G k σ ≤ arrTime σ p)
    {S : Finset (Fin n)} (hS : S ⊆ pivotsUpTo G σ (Tk G k σ)) (hSne : S.Nonempty) :
    (projLoad G k σ (arrTime σ p) (bpLabel G k σ p) : ℝ) ≤
      (5 + 2 * c * Real.log n) * ((n : ℝ) / Tk G k σ * (1 + 2 * c * Real.log n) +
        2 * ((S.sup (pclSize G σ) : ℕ) : ℝ) + 2 * (uncovered G σ (Tk G k σ)).card / S.card) := by
  obtain ⟨hG78, hG76, hGX⟩ := hG
  have htn : arrTime σ p < n := arrTime_lt σ p
  have hex : ∃ t, k < (pivotsUpTo G σ (t + 1)).card := by
    by_contra hex
    have : Tk G k σ = n := by unfold Tk; rw [dif_neg hex]
    omega
  have hkT := k_le_Tk G k σ hex
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  apply lemma79_arith hc (Real.log_nonneg (by linarith)) (by exact_mod_cast (by omega : 1 ≤ Tk G k σ))
    (by exact_mod_cast hpT) (by exact_mod_cast htn.le) (by exact_mod_cast hSne.card_pos)
    (by positivity) (by positivity) (by positivity)
    (projLoad_le_clLoad_mul G k σ hc hn hG76 hp (by omega) _)
    (clLoad_le_of_good G k σ hk hG78 hGX hp hpT hS hSne)

end CCK
