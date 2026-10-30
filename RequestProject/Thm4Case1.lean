module

public import RequestProject.Lemma78Prob

/-!
# The clique instance `J_σ` of the pivot clusters (proof of Theorem 4)

`J_σ = cliqueGraph (pivotOf G σ)`: its cliques are the pivot clusters.  We relate the sorted
clique sizes `cw`, indices `cidx` and the parameters `r(J_σ), a(J_σ), s(J_σ)` of Definition 3.3
to the pivots, and prove the threshold test (15) of the water-filling characterization of
`a(J_σ)`.
-/

@[expose] public section

open Finset
open scoped Classical

namespace CCK

/-! ### The threshold test (15) -/

section threshold

variable {w : ℕ → ℕ} {ℓ k : ℕ}

/-- **Threshold test (15).**  If `∑_h min(w_h, b) > k b` (for `b ≥ 0`, `0 < k < ℓ`), then
`a(I) > b`. -/
lemma lt_aParam_of_sum_min (hs : SortedDesc w ℓ) (hpos : ∀ i < ℓ, 0 < w i) (hk0 : 0 < k)
    (hk : k < ℓ) {b : ℝ} (_hb : 0 ≤ b)
    (h : (k : ℝ) * b < ∑ i ∈ range ℓ, min (w i : ℝ) b) : b < aParam w ℓ k := by
  by_contra hab
  push_neg at hab
  set r := rParam w ℓ k with hr
  have hrk : r < k := rParam_lt hpos hk0 hk
  have hsplit := sum_range_add_sum_Ico (fun i => min (w i : ℝ) b) (show r ≤ ℓ by omega)
  have h1 : ∑ i ∈ range r, min (w i : ℝ) b ≤ r * b := by
    calc ∑ i ∈ range r, min (w i : ℝ) b ≤ ∑ i ∈ range r, b :=
          sum_le_sum (fun i _ => min_le_right _ _)
      _ = r * b := by rw [sum_const, card_range, nsmul_eq_mul]
  have h2 : ∑ i ∈ Ico r ℓ, min (w i : ℝ) b = (tailSum w ℓ r : ℝ) := by
    unfold tailSum
    push_cast
    apply sum_congr rfl
    intro i hi
    obtain ⟨hri, hiℓ⟩ := mem_Ico.1 hi
    have := lt_aParam_of_rParam_le hs hrk hri hiℓ
    exact min_eq_left (by linarith)
  have h3 := tailSum_rParam_eq (w := w) (ℓ := ℓ) hrk
  rw [← hr] at h3
  have hrR : ((r : ℕ) : ℝ) < k := by exact_mod_cast hrk
  have : ∑ i ∈ range ℓ, min (w i : ℝ) b ≤ k * b := by
    rw [← hsplit, h2, h3]
    have : ((k : ℝ) - r) * aParam w ℓ k ≤ ((k : ℝ) - r) * b :=
      mul_le_mul_of_nonneg_left hab (by linarith)
    nlinarith
  linarith

end threshold

/-! ### Pivot clusters as cliques -/

variable {n : ℕ} (G : SimpleGraph (Fin n)) (σ : Equiv.Perm (Fin n))

/-- Auxiliary result for the proof of Theorem 4 (Section 7.3.4, water-filling characterization of a(J_σ)). -/
lemma pivotOf_eq_iff_of_pivot {p : Fin n} (hp : IsPivot G σ p) (u : Fin n) :
    pivotOf G σ u = pivotOf G σ p ↔ pivotOf G σ u = p := by
  rw [pivotOf_of_isPivot G σ hp]

/-- The size of the clique of a pivot in `J_σ` is its pivot cluster size. -/
lemma cw_cidx_pivot {p : Fin n} (hp : IsPivot G σ p) :
    cw (pivotOf G σ) (cidx (pivotOf G σ) p) = pclSize G σ p := by
  rw [← card_cidx_fiber (pivotOf G σ) (cidx_lt _ p), pclSize]
  congr 1
  ext u
  simp only [mem_filter, mem_univ, true_and]
  rw [cidx_eq_iff, pivotOf_eq_iff_of_pivot G σ hp]

/-- Auxiliary result for the proof of Theorem 4 (Section 7.3.4, water-filling characterization of a(J_σ)). -/
lemma cidx_pivotOf_eq (u : Fin n) :
    cidx (pivotOf G σ) (pivotOf G σ u) = cidx (pivotOf G σ) u := by
  rw [cidx_eq_iff, pivotOf_pivotOf]

/-- Auxiliary result for the proof of Theorem 4 (Section 7.3.4, water-filling characterization of a(J_σ)). -/
lemma cidx_pivotOf_inj {p p' : Fin n} (hp : IsPivot G σ p) (hp' : IsPivot G σ p')
    (h : cidx (pivotOf G σ) p = cidx (pivotOf G σ) p') : p = p' := by
  rw [cidx_eq_iff, pivotOf_of_isPivot G σ hp, pivotOf_of_isPivot G σ hp'] at h
  exact h

/-- Auxiliary result for the proof of Theorem 4 (Section 7.3.4, water-filling characterization of a(J_σ)). -/
lemma exists_pivot_cidx {j : ℕ} (hj : j < numCliques (pivotOf G σ)) :
    ∃ p, IsPivot G σ p ∧ cidx (pivotOf G σ) p = j := by
  have := cw_pos (pivotOf G σ) hj
  rw [← card_cidx_fiber (pivotOf G σ) hj] at this
  obtain ⟨u, hu⟩ := card_pos.1 this
  refine ⟨pivotOf G σ u, isPivot_pivotOf G σ u, ?_⟩
  rw [cidx_pivotOf_eq]; exact (mem_filter.1 hu).2

/-- Reindexing sums over the cliques of `J_σ` as sums over pivots. -/
lemma sum_filter_cidx_eq (f : ℕ → ℝ) (P : ℕ → Prop) [DecidablePred P] :
    ∑ j ∈ (range (numCliques (pivotOf G σ))).filter P, f (cw (pivotOf G σ) j) =
      ∑ p ∈ (pivotsUpTo G σ n).filter (fun p => P (cidx (pivotOf G σ) p)),
        f (pclSize G σ p) := by
  symm
  apply sum_nbij (fun p => cidx (pivotOf G σ) p)
  · intro p hp
    obtain ⟨hp1, hp2⟩ := mem_filter.1 hp
    exact mem_filter.2 ⟨mem_range.2 (cidx_lt _ p), hp2⟩
  · intro p hp p' hp' h
    exact cidx_pivotOf_inj G σ (mem_filter.1 hp).1 (mem_filter.1 hp').1 h
  · intro j hj
    obtain ⟨hj1, hj2⟩ := mem_filter.1 (mem_coe.1 hj)
    obtain ⟨p, hp, rfl⟩ := exists_pivot_cidx G σ (mem_range.1 hj1)
    exact ⟨p, mem_filter.2 ⟨hp, hj2⟩, rfl⟩
  · intro p hp
    rw [cw_cidx_pivot G σ (mem_filter.1 hp).1]

/-- Auxiliary result for the proof of Theorem 4 (Section 7.3.4, water-filling characterization of a(J_σ)). -/
lemma sum_range_cw_eq (f : ℕ → ℝ) :
    ∑ j ∈ range (numCliques (pivotOf G σ)), f (cw (pivotOf G σ) j) =
      ∑ p ∈ pivotsUpTo G σ n, f (pclSize G σ p) := by
  have := sum_filter_cidx_eq G σ f (fun _ => True)
  simpa using this

/-- Auxiliary result for the proof of Theorem 4 (Section 7.3.4, water-filling characterization of a(J_σ)). -/
lemma numCliques_pivotOf : numCliques (pivotOf G σ) = (pivotsUpTo G σ n).card := by
  have := sum_range_cw_eq G σ (fun _ => 1)
  simp only [sum_const, card_range, nsmul_eq_mul, mul_one] at this
  exact_mod_cast this

/-- Tail sums of `J_σ` as sums over pivots. -/
lemma tailSum_pivotOf (i : ℕ) :
    (tailSum (cw (pivotOf G σ)) (numCliques (pivotOf G σ)) i : ℝ) =
      ∑ p ∈ (pivotsUpTo G σ n).filter (fun p => i ≤ cidx (pivotOf G σ) p),
        (pclSize G σ p : ℝ) := by
  rw [← sum_filter_cidx_eq G σ (fun x => (x : ℝ)) (fun j => i ≤ j)]
  unfold tailSum
  push_cast
  apply sum_congr
  · ext j; simp only [mem_Ico, mem_filter, mem_range]; tauto
  · intro _ _; rfl

/-- A strictly larger clique has a strictly smaller index. -/
lemma cidx_lt_of_pclSize_lt {p p' : Fin n} (hp : IsPivot G σ p) (hp' : IsPivot G σ p')
    (h : pclSize G σ p < pclSize G σ p') :
    cidx (pivotOf G σ) p' < cidx (pivotOf G σ) p := by
  by_contra hle
  push_neg at hle
  have := cw_sorted (pivotOf G σ) _ _ hle (cidx_lt _ p')
  rw [cw_cidx_pivot G σ hp, cw_cidx_pivot G σ hp'] at this
  omega

end CCK


/-!
# Pivot cluster size estimation (proof of Theorem 4)

Good events (with failure probabilities from Lemmas 7.11 and 7.9):
* `GoodLate`: pivot clusters whose pivot has not arrived by time `2^i` are small (property (a));
* `GoodHeavy`: pivot clusters with many early arrivals remain large (property (c)).

Consequences, with `θ = n ln n / T`: late pivot clusters have size `< 2 c_L θ`; early pivot
clusters with at least `β ln n + 1` arrivals by time `T` have size `≥ (β/4) θ`; and (on the good
event of Lemma 7.5) early pivot clusters with fewer arrivals have size `≤ (4β + 2c + 10) θ`.
-/

@[expose] public section

open Finset
open scoped Classical

namespace CCK

variable {n : ℕ} (G : SimpleGraph (Fin n))

/-- The closed neighbourhood `N[r]`. -/
noncomputable def closedNbhd (r : Fin n) : Finset (Fin n) := insert r (G.neighborFinset r)

/-- Property (a) of the proof of Theorem 4, for all windows simultaneously. -/
def GoodLate (σ : Equiv.Perm (Fin n)) (cL : ℝ) : Prop :=
  ∀ i ≤ Nat.log 2 n, ∀ r : Fin n, (∀ p ∈ pivotsUpTo G σ (2 ^ i), p ∉ closedNbhd G r) →
    ((uncovered G σ (2 ^ i) ∩ closedNbhd G r).card : ℝ) < cL * n * Real.log n / 2 ^ i

/-- Property (c) of the proof of Theorem 4 (Lemma 7.9). -/
def GoodHeavy (σ : Equiv.Perm (Fin n)) (β : ℝ) : Prop :=
  ∀ v, ∀ i ∈ range (Nat.log 2 n + 1), IsPivot G σ v → β * Real.log n + 1 ≤ pclAt G σ v (2 ^ i) →
    β * n * Real.log n / 2 ^ (i + 1) ≤ (pclSize G σ v : ℝ)

/-- Auxiliary result for the proof of Theorem 4 (Section 7.3.4, pivot cluster size estimation). -/
lemma prob_not_goodLate (cL : ℝ) :
    prob (fun σ => ¬ GoodLate G σ cL) ≤ ((Nat.log 2 n + 1) * n : ℕ) * (n : ℝ) ^ (-cL) := by
  have hsub : ∀ σ, ¬ GoodLate G σ cL → ∃ i ∈ range (Nat.log 2 n + 1), ∃ r ∈ (univ : Finset (Fin n)),
      (∀ p ∈ pivotsUpTo G σ (2 ^ i), p ∉ closedNbhd G r) ∧
        cL * n * Real.log n / 2 ^ i ≤ ((uncovered G σ (2 ^ i) ∩ closedNbhd G r).card : ℝ) := by
    intro σ h
    unfold GoodLate at h
    push_neg at h
    obtain ⟨i, hi, r, h1, h2⟩ := h
    exact ⟨i, mem_range.2 (by omega), r, mem_univ _, h1, h2⟩
  have key := prob_mono hsub
  refine key.trans ?_
  refine le_trans (le_of_eq (prob_congr fun σ => Iff.rfl)) ((prob_exists_le _ _).trans ?_)
  have hper : ∀ i ∈ range (Nat.log 2 n + 1), prob (fun σ => ∃ r ∈ (univ : Finset (Fin n)),
      (∀ p ∈ pivotsUpTo G σ (2 ^ i), p ∉ closedNbhd G r) ∧
        cL * n * Real.log n / 2 ^ i ≤ ((uncovered G σ (2 ^ i) ∩ closedNbhd G r).card : ℝ)) ≤
      n * (n : ℝ) ^ (-cL) := by
    intro i hi
    refine le_trans (le_of_eq (prob_congr fun σ => Iff.rfl)) ((prob_exists_le _ _).trans ?_)
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    have h2i : 2 ^ i ≤ n :=
      (Nat.pow_le_pow_right (by norm_num) (Nat.lt_succ_iff.1 (mem_range.1 hi))).trans
        (Nat.pow_log_le_self 2 (by omega))
    refine (sum_le_sum (fun r _ => (le_of_eq (prob_congr fun σ => Iff.rfl)).trans
      (lemma_7_12 G (closedNbhd G r) cL h2i))).trans (le_of_eq ?_)
    simp
  refine le_trans (sum_le_sum fun i hi => (le_of_eq (prob_congr fun σ => Iff.rfl)).trans
    (hper i hi)) (le_of_eq ?_)
  simp [sum_const, card_range, nsmul_eq_mul, mul_assoc]

/-- Auxiliary result for the proof of Theorem 4 (Section 7.3.4, pivot cluster size estimation). -/
lemma prob_not_goodHeavy (hH : HypergeomChernoff) {β : ℝ} (hβ : 0 < β) :
    prob (fun σ => ¬ GoodHeavy G σ β) ≤ n * (Nat.log 2 n + 1) / (n : ℝ) ^ (β / 6) := by
  have hsub : ∀ σ, ¬ GoodHeavy G σ β → ∃ v, ∃ i ∈ range (Nat.log 2 n + 1), IsPivot G σ v ∧
      β * Real.log n + 1 ≤ pclAt G σ v (2 ^ i) ∧
      (pclSize G σ v : ℝ) < β * n * Real.log n / 2 ^ (i + 1) := by
    intro σ h
    unfold GoodHeavy at h
    push_neg at h
    obtain ⟨v, i, hi, h1, h2, h3⟩ := h
    exact ⟨v, i, hi, h1, h2, h3⟩
  exact (prob_mono hsub).trans ((le_of_eq (prob_congr fun σ => Iff.rfl)).trans
    (lemma_7_10 G hH hβ))

/-! ### Deterministic consequences -/

variable (k : ℕ) (σ : Equiv.Perm (Fin n))

/-- Auxiliary result for the proof of Theorem 4 (Section 7.3.4, pivot cluster size estimation). -/
lemma uncovered_antitone {s t : ℕ} (h : s ≤ t) : uncovered G σ t ⊆ uncovered G σ s := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  induction m with
  | zero => exact subset_refl _
  | succ m ih => exact (uncovered_succ_subset G σ (s + m)).trans (ih (by omega))

/-- Auxiliary result for the proof of Theorem 4 (Section 7.3.4, pivot cluster size estimation). -/
lemma pclAt_mono (v : Fin n) {s t : ℕ} (h : s ≤ t) : pclAt G σ v s ≤ pclAt G σ v t :=
  card_le_card (inter_subset_inter_right (firstSet_mono σ h))

/-- The pivot cluster of a pivot `r` is contained in `N[r]` and uncovered at the arrival of `r`. -/
lemma pivotCluster_subset {r : Fin n} (hr : IsPivot G σ r) :
    univ.filter (fun u => pivotOf G σ u = r) ⊆ uncovered G σ (arrTime σ r) ∩ closedNbhd G r := by
  intro u hu
  by_cases hur : u = r
  · subst hur
    refine mem_inter.2 ⟨?_, mem_insert_self _ _⟩
    simp only [uncovered, mem_filter, mem_univ, true_and]
    exact ⟨le_rfl, (isPivot_iff G σ u).1 hr⟩
  · have : u ∈ (univ.filter (fun u => pivotOf G σ u = r)).erase r := mem_erase.2 ⟨hur, hu⟩
    rw [pivotCluster_erase_eq G σ hr] at this
    simp only [uncNbrs, mem_inter] at this
    exact mem_inter.2 ⟨this.1, mem_insert_of_mem this.2⟩

/-- **Property (a).**  On `GoodLate`, a pivot arriving at or after time `2^i` (with
`i ≤ ⌊log₂ n⌋`) has pivot cluster size `< c_L n ln n / 2^i`. -/
lemma pclSize_lt_of_goodLate {cL : ℝ} (hG : GoodLate G σ cL) {i : ℕ} (hi : i ≤ Nat.log 2 n)
    {r : Fin n} (hr : IsPivot G σ r) (hri : 2 ^ i ≤ arrTime σ r) :
    (pclSize G σ r : ℝ) < cL * n * Real.log n / 2 ^ i := by
  have hno : ∀ p ∈ pivotsUpTo G σ (2 ^ i), p ∉ closedNbhd G r := by
    intro p hp hpN
    obtain ⟨hpp, hpt⟩ := (mem_pivotsUpTo_iff G σ _ p).1 hp
    rcases mem_insert.1 hpN with rfl | hadj
    · omega
    · rw [SimpleGraph.mem_neighborFinset] at hadj
      exact not_adj_of_isPivot G σ hr hpp hadj
  have h1 := hG i hi r hno
  have h2 : pclSize G σ r ≤ (uncovered G σ (2 ^ i) ∩ closedNbhd G r).card := by
    unfold pclSize
    refine (card_le_card (pivotCluster_subset G σ hr)).trans (card_le_card ?_)
    exact inter_subset_inter_right (uncovered_antitone G σ hri)
  calc (pclSize G σ r : ℝ) ≤ ((uncovered G σ (2 ^ i) ∩ closedNbhd G r).card : ℝ) := by
        exact_mod_cast h2
    _ < _ := h1

/-- The window of `T`: `2^i ≤ T < 2^{i+1}` with `i = ⌊log₂ T⌋ ≤ ⌊log₂ n⌋`. -/
lemma window_of_pos {T : ℕ} (hT : 1 ≤ T) (hTn : T ≤ n) :
    Nat.log 2 T ≤ Nat.log 2 n ∧ 2 ^ Nat.log 2 T ≤ T ∧ T < 2 ^ (Nat.log 2 T + 1) :=
  ⟨Nat.log_mono_right hTn, Nat.pow_log_le_self 2 (by omega), Nat.lt_pow_succ_log_self (by norm_num) _⟩

/-- Late pivot clusters are small: `p_n(r) < 2 c_L n ln n / T`. -/
lemma pclSize_late_lt {cL : ℝ} (hcL : 0 ≤ cL) (hn : 2 ≤ n) (hG : GoodLate G σ cL) {T : ℕ}
    (hT : 1 ≤ T) (hTn : T ≤ n) {r : Fin n} (hr : IsPivot G σ r) (hrT : T ≤ arrTime σ r) :
    (pclSize G σ r : ℝ) < 2 * cL * (n * Real.log n / T) := by
  obtain ⟨hi, h1, h2⟩ := window_of_pos hT hTn
  have h := pclSize_lt_of_goodLate G σ hG hi hr (h1.trans hrT)
  refine h.trans_le ?_
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hl : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  have hTR : (0 : ℝ) < T := by exact_mod_cast hT
  have h2R : (T : ℝ) < 2 ^ (Nat.log 2 T + 1) := by exact_mod_cast h2
  have hpow : (0 : ℝ) < 2 ^ Nat.log 2 T := by positivity
  rw [div_le_iff₀ hpow]
  have e : 2 * cL * (n * Real.log n / T) * 2 ^ Nat.log 2 T =
      cL * n * Real.log n * (2 ^ (Nat.log 2 T + 1) / T) := by
    rw [pow_succ]; field_simp
  rw [e]
  have : 1 ≤ (2 : ℝ) ^ (Nat.log 2 T + 1) / T := by rw [le_div_iff₀ hTR]; linarith
  have h0 : 0 ≤ cL * n * Real.log n := by positivity
  nlinarith

/-- **Property (c).**  On `GoodHeavy`, a pivot cluster with at least `β ln n + 1` arrivals by
time `T` has size at least `(β/4) n ln n / T`. -/
lemma pclSize_heavy_ge {β : ℝ} (hβ : 0 ≤ β) (hn : 2 ≤ n) (hG : GoodHeavy G σ β) {T : ℕ}
    (hT : 1 ≤ T) (hTn : T ≤ n) {q : Fin n} (hq : IsPivot G σ q)
    (hheavy : β * Real.log n + 1 ≤ pclAt G σ q T) :
    β / 4 * (n * Real.log n / T) ≤ (pclSize G σ q : ℝ) := by
  obtain ⟨hi, h1, h2⟩ := window_of_pos hT hTn
  set i := Nat.log 2 T
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hl : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  have hTR : (0 : ℝ) < T := by exact_mod_cast hT
  have h1R : (2 : ℝ) ^ i ≤ T := by exact_mod_cast h1
  by_cases hi1 : i + 1 ≤ Nat.log 2 n
  · have hmono : (pclAt G σ q T : ℝ) ≤ pclAt G σ q (2 ^ (i + 1)) := by
      exact_mod_cast pclAt_mono G σ q h2.le
    have := hG q (i + 1) (mem_range.2 (by omega)) hq (by linarith)
    refine le_trans ?_ this
    rw [le_div_iff₀ (by positivity)]
    have e : β / 4 * (n * Real.log n / T) * 2 ^ (i + 1 + 1) = β * n * Real.log n * (2 ^ i / T) := by
      rw [pow_succ, pow_succ]; field_simp; ring
    rw [e]
    have : (2 : ℝ) ^ i / T ≤ 1 := div_le_one_of_le₀ h1R hTR.le
    have h0 : 0 ≤ β * n * Real.log n := by positivity
    nlinarith
  · -- `2^{i+1} > n`, so `n / T < 2`
    have hn2 : n < 2 ^ (i + 1) := by
      by_contra hcon
      push_neg at hcon
      exact hi1 (Nat.le_log_of_pow_le (by norm_num) hcon)
    have hnT : (n : ℝ) < 2 * T := by
      have : (n : ℝ) < 2 ^ (i + 1) := by exact_mod_cast hn2
      rw [pow_succ] at this; linarith
    have hle : (pclAt G σ q T : ℝ) ≤ pclSize G σ q := by exact_mod_cast pclAt_le_pclSize G σ q T
    have : β / 4 * (n * Real.log n / T) ≤ β * Real.log n := by
      rw [show β / 4 * (n * Real.log n / T) = β * Real.log n * (n / (4 * T)) by
        field_simp]
      have : (n : ℝ) / (4 * T) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
      have h0 : 0 ≤ β * Real.log n := by positivity
      nlinarith
    linarith

/-- On the good event of Lemma 7.5, an early pivot cluster with fewer than `β ln n + 1` arrivals
by time `T` (where `T < n` is the arrival time of a pivot outside it) has size at most
`(4β + 2c + 10) n ln n / T`. -/
lemma pclSize_light_le {β c : ℝ} (hβ : 0 ≤ β) (hc : 0 ≤ c) (hn : 2 ≤ n) (hG : Good76 G σ c)
    {T : ℕ} (hT : 1 ≤ T) (hTn : T < n) {q : Fin n} (hq : IsPivot G σ q) (hqT : arrTime σ q < T)
    (hpiv : IsPivot G σ (σ ⟨T, hTn⟩))
    (hlight : (pclAt G σ q T : ℝ) < β * Real.log n + 1) :
    (pclSize G σ q : ℝ) ≤ (4 * β + 2 * c + 10) * (n * Real.log n / T) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hl2 := Real.log_two_gt_d9
  have hl : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hnR
  have hTR : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hTn' : (T : ℝ) ≤ n := by exact_mod_cast hTn.le
  have h76 := hG (T + 1) (by omega) q (by omega) hq
  have hpT : arrTime σ (σ ⟨T, hTn⟩) = T := arrTime_apply σ T hTn
  have hsame : pclAt G σ q (T + 1) = pclAt G σ q T := by
    have := pclAt_succ_of_pivot G σ hpiv (p := σ ⟨T, hTn⟩) (r := q) (by rw [hpT]; exact hqT)
    rwa [hpT] at this
  rw [hsame] at h76
  push_cast at h76
  set θ := (n : ℝ) * Real.log n / T with hθ
  have hnT : 0 ≤ (n : ℝ) / T := by positivity
  have hθ' : θ = (n / T) * Real.log n := by rw [hθ]; ring
  have hθ1 : (n : ℝ) / T ≤ 2 * θ := by rw [hθ']; nlinarith
  have hθ0 : 1 ≤ 2 * θ := by
    have : (1 : ℝ) ≤ n / T := by rw [le_div_iff₀ (by linarith)]; linarith
    linarith
  have e1 : 4 * (n : ℝ) * (pclAt G σ q T : ℝ) / (T + 1) ≤ 4 * (n / T) * (β * Real.log n + 1) := by
    rw [div_le_iff₀ (by linarith)]
    have : (0 : ℝ) ≤ pclAt G σ q T := Nat.cast_nonneg _
    have : 4 * (n / T) * (β * Real.log n + 1) * (T + 1) ≥ 4 * (n / T) * (β * Real.log n + 1) * T := by
      have : 0 ≤ 4 * (n / T) * (β * Real.log n + 1) := by positivity
      nlinarith
    have : 4 * (n / T) * (β * Real.log n + 1) * T = 4 * n * (β * Real.log n + 1) := by field_simp
    nlinarith
  have e2 : 2 * c * (n : ℝ) * Real.log n / (T + 1) ≤ 2 * c * θ := by
    rw [hθ, div_le_iff₀ (by linarith)]
    have : 2 * c * (n * Real.log n / T) * (T + 1) = 2 * c * n * Real.log n * ((T + 1) / T) := by
      field_simp
    rw [this]
    have : 1 ≤ ((T : ℝ) + 1) / T := by rw [le_div_iff₀ (by linarith)]; linarith
    have h0 : 0 ≤ 2 * c * n * Real.log n := by positivity
    nlinarith
  have e3 : 4 * (n / T) * (β * Real.log n + 1) = 4 * β * θ + 4 * (n / T) := by
    rw [hθ]; ring
  have hθpos : 0 ≤ θ := by positivity
  nlinarith

end CCK


/-!
# Theorem 4, Case 1 (large `U`)

Deterministic part of the "Large `U`" case of the proof of Theorem 4: on the good events, if
`|U| > c₂ m θ` (with `θ = n ln n / T` and `m = |S₁|`), then the merging cost is at most
`O(ln n) · s(J_σ) a(J_σ)`, inequality (22).
-/

@[expose] public section

open Finset
open scoped Classical

namespace CCK

variable {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) (σ : Equiv.Perm (Fin n))

/-- `θ = n ln n / T` (proof of Theorem 4). -/
noncomputable def thetaT : ℝ := (n : ℝ) * Real.log n / Tk G k σ

/-- The early pivots (pivots arriving before time `T`; one per algorithm cluster at time `T`). -/
noncomputable def earlyPiv : Finset (Fin n) := pivotsUpTo G σ (Tk G k σ)

/-- The late pivots (arriving at time `T` or later). -/
noncomputable def latePiv : Finset (Fin n) :=
  (pivotsUpTo G σ n).filter (fun p => Tk G k σ ≤ arrTime σ p)

/-- The set `S₁` of the proof of Theorem 4: early pivot clusters with fewer than `β ln n + 1`
arrivals by time `T`. -/
noncomputable def S1set (β : ℝ) : Finset (Fin n) :=
  (earlyPiv G k σ).filter (fun q => (pclAt G σ q (Tk G k σ) : ℝ) < β * Real.log n + 1)

/-! ### Generic counting facts -/

/-- Auxiliary result for the proof of Theorem 4 (Section 7.3.4, Large-U case). -/
lemma card_pivots_filter_cidx (P : ℕ → Prop) [DecidablePred P] :
    ((pivotsUpTo G σ n).filter (fun p => P (cidx (pivotOf G σ) p))).card =
      ((range (numCliques (pivotOf G σ))).filter P).card := by
  have := sum_filter_cidx_eq G σ (fun _ => (1 : ℝ)) P
  simp only [sum_const, nsmul_eq_mul, mul_one] at this
  exact_mod_cast this.symm

/-- Auxiliary result for the proof of Theorem 4 (Section 7.3.4, Large-U case). -/
lemma earlyPiv_subset : earlyPiv G k σ ⊆ pivotsUpTo G σ n :=
  pivotsUpTo_mono G σ (Tk_le G k σ)

/-- Auxiliary result for the proof of Theorem 4 (Section 7.3.4, Large-U case). -/
lemma mem_earlyPiv {p : Fin n} : p ∈ earlyPiv G k σ ↔ IsPivot G σ p ∧ arrTime σ p < Tk G k σ :=
  mem_pivotsUpTo_iff G σ _ p

/-- Auxiliary result for the proof of Theorem 4 (Section 7.3.4, Large-U case). -/
lemma mem_latePiv {p : Fin n} : p ∈ latePiv G k σ ↔ IsPivot G σ p ∧ Tk G k σ ≤ arrTime σ p := by
  unfold latePiv; rw [mem_filter]; rfl

/-- Auxiliary result for the proof of Theorem 4 (Section 7.3.4, Large-U case). -/
lemma pivots_eq_union : pivotsUpTo G σ n = earlyPiv G k σ ∪ latePiv G k σ := by
  ext p
  rw [mem_union, mem_earlyPiv, mem_latePiv]
  constructor
  · intro hp
    by_cases h : arrTime σ p < Tk G k σ
    · exact Or.inl ⟨hp, h⟩
    · exact Or.inr ⟨hp, by omega⟩
  · rintro (h | h) <;> exact h.1

/-- Auxiliary result for the proof of Theorem 4 (Section 7.3.4, Large-U case). -/
lemma disjoint_early_late : Disjoint (earlyPiv G k σ) (latePiv G k σ) := by
  rw [disjoint_left]
  intro p h1 h2
  rw [mem_earlyPiv] at h1; rw [mem_latePiv] at h2
  omega

/-- Auxiliary result for the proof of Theorem 4 (Section 7.3.4, Large-U case). -/
lemma sum_latePiv_pclSize :
    ∑ p ∈ latePiv G k σ, (pclSize G σ p : ℝ) = (uncovered G σ (Tk G k σ)).card := by
  have := sum_late_pclSize G k σ
  unfold latePiv
  exact_mod_cast this

/-- A pivot arriving at time `T < n` exists (it is the `(k+1)`-th pivot). -/
lemma isPivot_at_Tk (h : ∃ t, k < (pivotsUpTo G σ (t + 1)).card) (hT : Tk G k σ < n) :
    IsPivot G σ (σ ⟨Tk G k σ, hT⟩) := by
  obtain ⟨-, h1, h2⟩ := Tk_spec G k σ h
  by_contra hnp
  have : pivotsUpTo G σ (Tk G k σ + 1) = pivotsUpTo G σ (Tk G k σ) := by
    ext v
    rw [mem_pivotsUpTo_succ G σ hT]
    constructor
    · rintro (hv | ⟨rfl, hv⟩)
      · exact hv
      · exact absurd ((isPivot_iff G σ _).2 (by rwa [arrTime_apply])) hnp
    · exact Or.inl
  rw [this] at h2
  omega

/-- `U` is non-empty when `T < n`. -/
lemma uncovered_Tk_nonempty (h : ∃ t, k < (pivotsUpTo G σ (t + 1)).card) (hT : Tk G k σ < n) :
    (uncovered G σ (Tk G k σ)).Nonempty := by
  have hp := isPivot_at_Tk G k σ h hT
  refine ⟨σ ⟨Tk G k σ, hT⟩, ?_⟩
  rw [mem_uncovered_iff_late, pivotOf_of_isPivot G σ hp, arrTime_apply]

/-- Auxiliary result for the proof of Theorem 4 (Section 7.3.4, Large-U case). -/
lemma card_earlyPiv (h : ∃ t, k < (pivotsUpTo G σ (t + 1)).card) : (earlyPiv G k σ).card = k :=
  (Tk_spec G k σ h).2.1

/-- Auxiliary result for the proof of Theorem 4 (Section 7.3.4, Large-U case). -/
lemma lt_numCliques (h : ∃ t, k < (pivotsUpTo G σ (t + 1)).card) :
    k < numCliques (pivotOf G σ) := by
  rw [numCliques_pivotOf]
  have h2 := (Tk_spec G k σ h).2.2
  have := card_le_card (pivotsUpTo_mono G σ (show Tk G k σ + 1 ≤ n from (Tk_spec G k σ h).1))
  omega

/-- Auxiliary result for the proof of Theorem 4 (Section 7.3.4, Large-U case). -/
lemma one_le_Tk (hk : 0 < k) (h : ∃ t, k < (pivotsUpTo G σ (t + 1)).card) : 1 ≤ Tk G k σ :=
  le_trans hk (k_le_Tk G k σ h)

/-- The number of pivots whose cluster has index `< j` (for `j ≤` the number of pivot clusters)
is `j`. -/
lemma card_pivots_cidx_lt {j : ℕ} (hj : j ≤ numCliques (pivotOf G σ)) :
    ((pivotsUpTo G σ n).filter (fun p => cidx (pivotOf G σ) p < j)).card = j := by
  rw [card_pivots_filter_cidx G σ (fun i => i < j)]
  have : (range (numCliques (pivotOf G σ))).filter (fun i => i < j) = range j := by
    ext i; simp only [mem_filter, mem_range]; omega
  rw [this, card_range]

/-! ### Case 1 -/

/-- **Lower bound (16) on `a(J_σ)`** (proof of Theorem 4, Case 1, via the threshold test (15)).
If late pivot clusters have size `< b`, the pivot clusters outside `S₁` have size `≥ b`, and
`|U| > m b` where `m = |S₁|`, then `a(J_σ) > b`. -/
lemma lt_aOf_case1 (hk : 0 < k) (h : ∃ t, k < (pivotsUpTo G σ (t + 1)).card) {β b : ℝ}
    (hb : 0 ≤ b)
    (hlate : ∀ p ∈ latePiv G k σ, (pclSize G σ p : ℝ) < b)
    (hheavy : ∀ q ∈ earlyPiv G k σ, q ∉ S1set G k σ β → b ≤ pclSize G σ q)
    (hU : (S1set G k σ β).card * b < (uncovered G σ (Tk G k σ)).card) :
    b < aOf (pivotOf G σ) k := by
  unfold aOf
  apply lt_aParam_of_sum_min (cw_sorted _) (fun i hi => cw_pos _ hi) hk (lt_numCliques G k σ h) hb
  rw [sum_range_cw_eq G σ (fun x => min (x : ℝ) b), pivots_eq_union G k σ,
    sum_union (disjoint_early_late G k σ)]
  have hlateS : ∑ p ∈ latePiv G k σ, min (pclSize G σ p : ℝ) b =
      (uncovered G σ (Tk G k σ)).card := by
    rw [← sum_latePiv_pclSize]
    exact sum_congr rfl (fun p hp => min_eq_left (hlate p hp).le)
  rw [hlateS]
  have hS1 : S1set G k σ β ⊆ earlyPiv G k σ := filter_subset _ _
  rw [← sum_sdiff hS1]
  have h2 : ∑ q ∈ earlyPiv G k σ \ S1set G k σ β, min (pclSize G σ q : ℝ) b =
      ((earlyPiv G k σ \ S1set G k σ β).card : ℝ) * b := by
    rw [← nsmul_eq_mul, ← sum_const]
    refine sum_congr rfl (fun q hq => ?_)
    obtain ⟨h1, h2⟩ := mem_sdiff.1 hq
    exact min_eq_right (hheavy q h1 h2)
  have h3 : 0 ≤ ∑ q ∈ S1set G k σ β, min (pclSize G σ q : ℝ) b :=
    sum_nonneg (fun q _ => le_min (Nat.cast_nonneg _) hb)
  rw [h2, card_sdiff_of_subset hS1, card_earlyPiv G k σ h]
  have hle : (S1set G k σ β).card ≤ k := by
    have := card_le_card hS1; rwa [card_earlyPiv G k σ h] at this
  push_cast [hle]
  nlinarith

/-- The comparison set `A` of the proof of Theorem 4 (Case 1): early pivot clusters which are not
peeled off in the computation of `a(J_σ)` (index `≥ r(J_σ)`). -/
noncomputable def Aset : Finset (Fin n) :=
  (earlyPiv G k σ).filter (fun q => rOf (pivotOf G σ) k ≤ cidx (pivotOf G σ) q)

/-- **Properties (17)–(18) of the comparison set `A`** (proof of Theorem 4, Case 1).  If every
late pivot cluster is smaller than `a(J_σ)`, then `|A| = k - r(J_σ) ≥ 1`, every member of `A` has
size `< a(J_σ)`, and `∑_{X ∈ A} |X| + |U| = |A| a(J_σ)`. -/
lemma Aset_props (hk : 0 < k) (h : ∃ t, k < (pivotsUpTo G σ (t + 1)).card)
    (hlate : ∀ p ∈ latePiv G k σ, (pclSize G σ p : ℝ) < aOf (pivotOf G σ) k) :
    (Aset G k σ).card = k - rOf (pivotOf G σ) k ∧ rOf (pivotOf G σ) k < k ∧
      (∀ q ∈ Aset G k σ, (pclSize G σ q : ℝ) < aOf (pivotOf G σ) k) ∧
      ∑ q ∈ Aset G k σ, (pclSize G σ q : ℝ) + (uncovered G σ (Tk G k σ)).card =
        (Aset G k σ).card * aOf (pivotOf G σ) k := by
  set r := rOf (pivotOf G σ) k with hr
  set a := aOf (pivotOf G σ) k with ha
  have hkl := lt_numCliques G k σ h
  have hrk : r < k := rParam_lt (fun i hi => cw_pos _ hi) hk hkl
  -- pivots with index `< r` are large, hence early
  have hsmall : ∀ p, IsPivot G σ p → cidx (pivotOf G σ) p < r → p ∈ earlyPiv G k σ := by
    intro p hp hpr
    have h1 : a ≤ cw (pivotOf G σ) (cidx (pivotOf G σ) p) := aParam_le_of_lt_rParam hpr
    rw [cw_cidx_pivot G σ hp] at h1
    by_contra hne
    have : p ∈ latePiv G k σ := by
      rw [mem_latePiv]; rw [mem_earlyPiv] at hne; push_neg at hne; exact ⟨hp, hne hp⟩
    linarith [hlate p this]
  have hlate_r : ∀ p ∈ latePiv G k σ, r ≤ cidx (pivotOf G σ) p := by
    intro p hp
    by_contra hlt; push_neg at hlt
    exact disjoint_left.1 (disjoint_early_late G k σ) (hsmall p ((mem_latePiv G k σ).1 hp).1 hlt) hp
  -- cardinality of `A`
  have hcardlt : ((earlyPiv G k σ).filter (fun p => cidx (pivotOf G σ) p < r)).card = r := by
    refine Eq.trans ?_ (card_pivots_cidx_lt G σ (show r ≤ numCliques (pivotOf G σ) by omega))
    congr 1
    ext p
    simp only [mem_filter]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨earlyPiv_subset G k σ h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨hsmall p h1 h2, h2⟩
  have hcardA : (Aset G k σ).card = k - r := by
    have := card_filter_add_card_filter_not (s := earlyPiv G k σ)
      (fun p => cidx (pivotOf G σ) p < r)
    rw [card_earlyPiv G k σ h, hcardlt] at this
    unfold Aset
    have e : (earlyPiv G k σ).filter (fun q => r ≤ cidx (pivotOf G σ) q) =
        (earlyPiv G k σ).filter (fun p => ¬ cidx (pivotOf G σ) p < r) := by
      congr 1; ext p; omega
    rw [e]; omega
  refine ⟨hcardA, hrk, ?_, ?_⟩
  · intro q hq
    obtain ⟨hq1, hq2⟩ := mem_filter.1 hq
    have hqp := ((mem_earlyPiv G k σ).1 hq1).1
    have := lt_aParam_of_rParam_le (cw_sorted (pivotOf G σ)) hrk hq2 (cidx_lt (pivotOf G σ) q)
    rwa [cw_cidx_pivot G σ hqp] at this
  · have htail := tailSum_pivotOf G σ r
    rw [show (tailSum (cw (pivotOf G σ)) (numCliques (pivotOf G σ)) r : ℝ) = ((k : ℝ) - r) * a from
      tailSum_rParam_eq hrk] at htail
    have hsplit : (pivotsUpTo G σ n).filter (fun p => r ≤ cidx (pivotOf G σ) p) =
        Aset G k σ ∪ latePiv G k σ := by
      ext p
      simp only [mem_filter, mem_union, Aset]
      constructor
      · rintro ⟨hp, hpr⟩
        rw [pivots_eq_union G k σ, mem_union] at hp
        rcases hp with hp | hp
        · exact Or.inl ⟨hp, hpr⟩
        · exact Or.inr hp
      · rintro (⟨hp, hpr⟩ | hp)
        · exact ⟨earlyPiv_subset G k σ hp, hpr⟩
        · exact ⟨((mem_latePiv G k σ).1 hp).1, hlate_r p hp⟩
    have hdisj : Disjoint (Aset G k σ) (latePiv G k σ) :=
      disjoint_of_subset_left (filter_subset _ _) (disjoint_early_late G k σ)
    rw [hsplit, sum_union hdisj, sum_latePiv_pclSize] at htail
    rw [hcardA]
    push_cast [hrk.le]
    linarith

/-- **Inequality (19)** (proof of Theorem 4, Case 1): `s(J_σ) ≥ |U| - m L`, where `L` bounds the
sizes of the late pivot clusters and all pivot clusters outside `S₁` are larger than all late
pivot clusters. -/
lemma sOf_ge_case1 (h : ∃ t, k < (pivotsUpTo G σ (t + 1)).card) {β L : ℝ}
    (hlate : ∀ p ∈ latePiv G k σ, (pclSize G σ p : ℝ) ≤ L)
    (hsep : ∀ p ∈ latePiv G k σ, ∀ q ∈ earlyPiv G k σ, q ∉ S1set G k σ β →
      pclSize G σ p < pclSize G σ q) :
    ((uncovered G σ (Tk G k σ)).card : ℝ) - (S1set G k σ β).card * L ≤ sOf (pivotOf G σ) k := by
  have hkl := lt_numCliques G k σ h
  have hs : (sOf (pivotOf G σ) k : ℝ) = ∑ p ∈ (pivotsUpTo G σ n).filter (fun p => k ≤ cidx (pivotOf G σ) p),
      (pclSize G σ p : ℝ) := tailSum_pivotOf G σ k
  set LL := (latePiv G k σ).filter (fun p => cidx (pivotOf G σ) p < k)
  set LH := (latePiv G k σ).filter (fun p => ¬ cidx (pivotOf G σ) p < k)
  have hsum := sum_filter_add_sum_filter_not (latePiv G k σ) (fun p => cidx (pivotOf G σ) p < k)
    (fun p => (pclSize G σ p : ℝ))
  rw [sum_latePiv_pclSize] at hsum
  have hLH : ∑ p ∈ LH, (pclSize G σ p : ℝ) ≤ sOf (pivotOf G σ) k := by
    rw [hs]
    apply sum_le_sum_of_subset_of_nonneg
    · intro p hp
      obtain ⟨hp1, hp2⟩ := mem_filter.1 hp
      exact mem_filter.2 ⟨((mem_latePiv G k σ).1 hp1).1, by omega⟩
    · intro _ _ _; exact Nat.cast_nonneg _
  have hLL : ∑ p ∈ LL, (pclSize G σ p : ℝ) ≤ LL.card * L := by
    rw [← nsmul_eq_mul, ← sum_const]
    exact sum_le_sum (fun p hp => hlate p (mem_filter.1 hp).1)
  have hLLcard : LL.card ≤ (S1set G k σ β).card := by
    by_cases hex : ∃ q ∈ earlyPiv G k σ, q ∉ S1set G k σ β ∧ k ≤ cidx (pivotOf G σ) q
    · obtain ⟨q, hq1, hq2, hq3⟩ := hex
      have : LL = ∅ := by
        apply eq_empty_of_forall_notMem
        intro p hp
        obtain ⟨hp1, hp2⟩ := mem_filter.1 hp
        have := cidx_lt_of_pclSize_lt G σ ((mem_latePiv G k σ).1 hp1).1
          ((mem_earlyPiv G k σ).1 hq1).1 (hsep p hp1 q hq1 hq2)
        omega
      rw [this]; exact Nat.zero_le _
    · push_neg at hex
      have hsub : (earlyPiv G k σ \ S1set G k σ β) ∪ LL ⊆
          (pivotsUpTo G σ n).filter (fun p => cidx (pivotOf G σ) p < k) := by
        intro p hp
        rcases mem_union.1 hp with hp | hp
        · obtain ⟨h1, h2⟩ := mem_sdiff.1 hp
          exact mem_filter.2 ⟨earlyPiv_subset G k σ h1, by have := hex p h1 h2; omega⟩
        · obtain ⟨h1, h2⟩ := mem_filter.1 hp
          exact mem_filter.2 ⟨((mem_latePiv G k σ).1 h1).1, h2⟩
      have hdisj : Disjoint (earlyPiv G k σ \ S1set G k σ β) LL :=
        disjoint_of_subset_left sdiff_subset
          (disjoint_of_subset_right (filter_subset _ _) (disjoint_early_late G k σ))
      have := card_le_card hsub
      rw [card_union_of_disjoint hdisj, card_pivots_cidx_lt G σ hkl.le,
        card_sdiff_of_subset (show S1set G k σ β ⊆ earlyPiv G k σ from filter_subset _ _),
        card_earlyPiv G k σ h] at this
      have : (S1set G k σ β).card ≤ k := by
        have := card_le_card (filter_subset (fun q => (pclAt G σ q (Tk G k σ) : ℝ) <
          β * Real.log n + 1) (earlyPiv G k σ))
        rw [card_earlyPiv G k σ h] at this; exact this
      omega
  have hL0 : 0 ≤ L := by
    rcases (uncovered_Tk_nonempty G k σ h (Tk_spec G k σ h).1) with ⟨u, hu⟩
    have hp := isPivot_pivotOf G σ u
    have : pivotOf G σ u ∈ latePiv G k σ :=
      (mem_latePiv G k σ).2 ⟨hp, (mem_uncovered_iff_late G σ _ u).1 hu⟩
    exact le_trans (Nat.cast_nonneg _) (hlate _ this)
  have : (LL.card : ℝ) * L ≤ (S1set G k σ β).card * L :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hLLcard) hL0
  linarith

/-- Auxiliary result for the proof of Theorem 4 (Section 7.3.4, Large-U case). -/
lemma sup_pclSize_le {S : Finset (Fin n)} (hS : S.Nonempty) {a : ℝ}
    (h : ∀ q ∈ S, (pclSize G σ q : ℝ) < a) : ((S.sup (pclSize G σ) : ℕ) : ℝ) ≤ a := by
  obtain ⟨q, hq, he⟩ := exists_mem_eq_sup S hS (pclSize G σ)
  rw [he]; exact (h q hq).le

/-- Auxiliary result for the proof of Theorem 4 (Section 7.3.4, Large-U case). -/
lemma n_div_T_le_two_theta (hn : 2 ≤ n) {T : ℝ} (hT : 0 < T) :
    (n : ℝ) / T ≤ 2 * ((n : ℝ) * Real.log n / T) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hl2 := Real.log_two_gt_d9
  have hl : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hnR
  have e : 2 * ((n : ℝ) * Real.log n / T) = (n / T) * (2 * Real.log n) := by ring
  rw [e]
  have : 0 ≤ (n : ℝ) / T := by positivity
  nlinarith

/-- **Theorem 4, Case 1 (Large `U`), inequality (22).**  On the good events (Lemma 7.8 with
constant `48`; properties (a) and (c) with `c_L = 6`, `β = 60`), if `T < n` and
`|U| > 24 |S₁| θ` with `θ = n ln n / T`, then the merging cost is at most
`2400 ln n · s(J_σ) a(J_σ)`. -/
theorem mergeCost_case1 (hk : 0 < k) (hn : 2 ≤ n) (h : ∃ t, k < (pivotsUpTo G σ (t + 1)).card)
    (hGL : GoodLoad G σ 48) (hLate : GoodLate G σ 6) (hHeavy : GoodHeavy G σ 60)
    (hU : 24 * (S1set G k σ 60).card * thetaT G k σ < (uncovered G σ (Tk G k σ)).card) :
    (mergeCost G k σ : ℝ) ≤
      2400 * Real.log n * sOf (pivotOf G σ) k * aOf (pivotOf G σ) k := by
  obtain ⟨hTn, -, -⟩ := Tk_spec G k σ h
  have hT1 := one_le_Tk G k σ hk h
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hl : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  have hl2 := Real.log_two_gt_d9
  have hlog2 : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hnR
  have hTR : (0 : ℝ) < Tk G k σ := by exact_mod_cast hT1
  set θ := thetaT G k σ with hθ
  have hθ0 : 0 ≤ θ := by rw [hθ, thetaT]; positivity
  set U := uncovered G σ (Tk G k σ)
  set m := (S1set G k σ 60).card
  have hlate : ∀ p ∈ latePiv G k σ, (pclSize G σ p : ℝ) < 12 * θ := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := (mem_latePiv G k σ).1 hp
    have := pclSize_late_lt G σ (by norm_num : (0 : ℝ) ≤ 6) hn hLate hT1 (Tk_le G k σ) hp1 hp2
    rw [hθ, thetaT]; linarith
  have hheavy : ∀ q ∈ earlyPiv G k σ, q ∉ S1set G k σ 60 → 15 * θ ≤ pclSize G σ q := by
    intro q hq hq2
    have hq' : 60 * Real.log n + 1 ≤ pclAt G σ q (Tk G k σ) := by
      simp only [S1set, mem_filter, not_and, not_lt] at hq2
      exact hq2 hq
    have := pclSize_heavy_ge G σ (by norm_num : (0 : ℝ) ≤ 60) hn hHeavy hT1 (Tk_le G k σ)
      ((mem_earlyPiv G k σ).1 hq).1 hq'
    rw [hθ, thetaT]; linarith
  have hmθ : 0 ≤ (m : ℝ) * θ := by positivity
  have ha := lt_aOf_case1 G k σ hk h (b := 15 * θ) (by positivity)
    (fun p hp => (hlate p hp).trans_le (by linarith)) hheavy (by linarith)
  set a := aOf (pivotOf G σ) k
  obtain ⟨hcardA, hrk, hAlt, hAsum⟩ := Aset_props G k σ hk h
    (fun p hp => (hlate p hp).trans (by linarith))
  have hAne : (Aset G k σ).Nonempty := by
    rw [← card_pos, hcardA]; omega
  have hAcard : (0 : ℝ) < (Aset G k σ).card := by exact_mod_cast card_pos.2 hAne
  have hs := sOf_ge_case1 G k σ h (β := 60) (L := 12 * θ) (fun p hp => (hlate p hp).le)
    (by
      intro p hp q hq hq2
      have h1 := hlate p hp
      have h2 := hheavy q hq hq2
      exact_mod_cast (show (pclSize G σ p : ℝ) < pclSize G σ q by linarith))
  have hmerge := mergeCost_le_of_good G hk σ (by norm_num : (0 : ℝ) ≤ 48) hn hGL
    (filter_subset _ _ : Aset G k σ ⊆ pivotsUpTo G σ (Tk G k σ)) hAne
  -- bounding the load
  have hmu := sup_pclSize_le G σ hAne hAlt
  have hUA : (U.card : ℝ) / (Aset G k σ).card ≤ a := by
    rw [div_le_iff₀ hAcard]
    have : 0 ≤ ∑ q ∈ Aset G k σ, (pclSize G σ q : ℝ) := sum_nonneg (fun _ _ => Nat.cast_nonneg _)
    linarith
  have hnT := n_div_T_le_two_theta hn hTR
  rw [← thetaT, ← hθ] at hnT
  have hinner : (n : ℝ) / Tk G k σ * (1 + 2 * 48 * Real.log n) +
      2 * ((Aset G k σ).sup (pclSize G σ) : ℕ) + 2 * (U.card : ℝ) / (Aset G k σ).card ≤ 11 * a := by
    have e : (n : ℝ) / Tk G k σ * (1 + 2 * 48 * Real.log n) = n / Tk G k σ + 96 * θ := by
      rw [hθ, thetaT]; ring
    rw [e, mul_div_assoc]
    linarith
  have hfac : 5 + 2 * 48 * Real.log n ≤ 104 * Real.log n := by linarith
  have ha0 : 0 ≤ a := by linarith
  have hLB : loadBound G k σ 48 (Aset G k σ) ≤ 104 * Real.log n * (11 * a) := by
    unfold loadBound
    have h0 : 0 ≤ (n : ℝ) / Tk G k σ * (1 + 2 * 48 * Real.log n) +
        2 * ((Aset G k σ).sup (pclSize G σ) : ℕ) + 2 * (U.card : ℝ) / (Aset G k σ).card := by
      positivity
    exact mul_le_mul hfac hinner h0 (by positivity)
  have hU0 : (0 : ℝ) ≤ U.card := Nat.cast_nonneg _
  have hsU : (U.card : ℝ) ≤ 2 * sOf (pivotOf G σ) k := by linarith
  calc (mergeCost G k σ : ℝ) ≤ U.card * loadBound G k σ 48 (Aset G k σ) := hmerge
    _ ≤ U.card * (104 * Real.log n * (11 * a)) := mul_le_mul_of_nonneg_left hLB hU0
    _ ≤ (2 * sOf (pivotOf G σ) k) * (104 * Real.log n * (11 * a)) :=
        mul_le_mul_of_nonneg_right hsU (by positivity)
    _ ≤ 2400 * Real.log n * sOf (pivotOf G σ) k * a := by
        have : 0 ≤ Real.log n * (sOf (pivotOf G σ) k : ℝ) * a := by positivity
        nlinarith

/-- **Theorem 4, Case 2 (Small `U`), projected-load bound and (25).**  On the good event of
Lemma 7.8 (constant `48`), if `T < n` and `|U| ≤ 24 |S₁| θ` (with `β = 60`), then the merging cost
is at most `90000 ln n · θ · |U|` (here `S = S₁`, `μ(S₁) ≤ 346 θ` and `|U|/|S₁| ≤ 24 θ`). -/
theorem mergeCost_case2 (hk : 0 < k) (hn : 2 ≤ n) (h : ∃ t, k < (pivotsUpTo G σ (t + 1)).card)
    (hGL : GoodLoad G σ 48)
    (hU : ((uncovered G σ (Tk G k σ)).card : ℝ) ≤ 24 * (S1set G k σ 60).card * thetaT G k σ) :
    (mergeCost G k σ : ℝ) ≤
      90000 * Real.log n * thetaT G k σ * (uncovered G σ (Tk G k σ)).card := by
  obtain ⟨hTn, -, -⟩ := Tk_spec G k σ h
  have hT1 := one_le_Tk G k σ hk h
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hl : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  have hl2 := Real.log_two_gt_d9
  have hlog2 : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hnR
  have hTR : (0 : ℝ) < Tk G k σ := by exact_mod_cast hT1
  set θ := thetaT G k σ with hθ
  have hθ0 : 0 ≤ θ := by rw [hθ, thetaT]; positivity
  set U := uncovered G σ (Tk G k σ)
  set S := S1set G k σ 60
  have hUne : U.Nonempty := uncovered_Tk_nonempty G k σ h hTn
  have hU0 : (0 : ℝ) < U.card := by exact_mod_cast card_pos.2 hUne
  have hSne : S.Nonempty := by
    rw [← card_pos]
    by_contra h0
    push_neg at h0
    have : S.card = 0 := by omega
    rw [this] at hU
    simp only [CharP.cast_eq_zero, mul_zero, zero_mul] at hU
    linarith
  have hScard : (0 : ℝ) < S.card := by exact_mod_cast card_pos.2 hSne
  have hpiv := isPivot_at_Tk G k σ h hTn
  have hlight : ∀ q ∈ S, (pclSize G σ q : ℝ) < 347 * θ := by
    intro q hq
    obtain ⟨hq1, hq2⟩ := mem_filter.1 hq
    obtain ⟨hqp, hqT⟩ := (mem_earlyPiv G k σ).1 hq1
    have := pclSize_light_le G σ (by norm_num : (0 : ℝ) ≤ 60) (by norm_num : (0 : ℝ) ≤ 48) hn
      hGL.2.1 hT1 hTn hqp hqT hpiv hq2
    have hpos : (0 : ℝ) < 347 * θ ∨ θ = 0 := by
      rcases eq_or_lt_of_le hθ0 with h0 | h0
      · exact Or.inr h0.symm
      · exact Or.inl (by linarith)
    rcases hpos with hpos | h0
    · rw [hθ, thetaT]; rw [hθ, thetaT] at hpos; nlinarith
    · exfalso
      have : (0 : ℝ) < Real.log n := lt_of_lt_of_le (by linarith) hlog2
      have : 0 < θ := by rw [hθ, thetaT]; positivity
      linarith
  have hmerge := mergeCost_le_of_good G hk σ (by norm_num : (0 : ℝ) ≤ 48) hn hGL
    (filter_subset _ _ : S ⊆ pivotsUpTo G σ (Tk G k σ)) hSne
  have hmu := sup_pclSize_le G σ hSne hlight
  have hUS : (U.card : ℝ) / S.card ≤ 24 * θ := by
    rw [div_le_iff₀ hScard]; linarith
  have hnT := n_div_T_le_two_theta hn hTR
  rw [← thetaT, ← hθ] at hnT
  have hinner : (n : ℝ) / Tk G k σ * (1 + 2 * 48 * Real.log n) +
      2 * (S.sup (pclSize G σ) : ℕ) + 2 * (U.card : ℝ) / S.card ≤ 850 * θ := by
    have e : (n : ℝ) / Tk G k σ * (1 + 2 * 48 * Real.log n) = n / Tk G k σ + 96 * θ := by
      rw [hθ, thetaT]; ring
    rw [e, mul_div_assoc]
    linarith
  have hfac : 5 + 2 * 48 * Real.log n ≤ 104 * Real.log n := by linarith
  have hLB : loadBound G k σ 48 S ≤ 104 * Real.log n * (850 * θ) := by
    unfold loadBound
    have h0 : 0 ≤ (n : ℝ) / Tk G k σ * (1 + 2 * 48 * Real.log n) +
        2 * (S.sup (pclSize G σ) : ℕ) + 2 * (U.card : ℝ) / S.card := by
      positivity
    exact mul_le_mul hfac hinner h0 (by positivity)
  calc (mergeCost G k σ : ℝ) ≤ U.card * loadBound G k σ 48 S := hmerge
    _ ≤ U.card * (104 * Real.log n * (850 * θ)) := mul_le_mul_of_nonneg_left hLB hU0.le
    _ ≤ 90000 * Real.log n * θ * U.card := by
        have : 0 ≤ Real.log n * θ * (U.card : ℝ) := by positivity
        nlinarith

end CCK
