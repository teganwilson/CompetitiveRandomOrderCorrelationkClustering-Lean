module

public import RequestProject.Lemma79

/-!
# Lemma 7.9: probability of the good event

The good event `GoodLoad` of Lemma 7.9 fails with probability at most
`n (n+1) n^{-c/3} + (n+1) n^{2-c/8} + (n+1)² n^{-c/3}` (union bounds over Lemma 7.8, Lemma 7.6
and the hypergeometric concentration of the number of uncovered vertices arriving in an interval,
Fact 2.2).
-/

@[expose] public section

open Finset
open scoped Classical

namespace CCK

variable {n : ℕ} (G : SimpleGraph (Fin n))

/-- Auxiliary result for Lemma 7.9 (Section 7.3.2). -/
lemma ratio_le_of_le {s t : ℕ} (hst : s ≤ t) (ht : t ≤ n) :
    ((t : ℝ) - s) / ((n : ℝ) - s) ≤ (t : ℝ) / n := by
  rcases Nat.eq_or_lt_of_le (hst.trans ht) with hsn | hsn
  · have : (n : ℝ) - s = 0 := by rw [hsn]; ring
    rw [this, div_zero]; positivity
  · have h1 : (0 : ℝ) < (n : ℝ) - s := by
      have : (s : ℝ) < n := by exact_mod_cast hsn
      linarith
    have h2 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    rw [div_le_div_iff₀ h1 h2]
    have : (t : ℝ) ≤ n := by exact_mod_cast ht
    have : (0 : ℝ) ≤ s := Nat.cast_nonneg s
    nlinarith

/-- Auxiliary result for Lemma 7.9 (Section 7.3.2). -/
lemma exp_neg_log_div (hn : 0 < n) (c : ℝ) :
    Real.exp (-(c * Real.log n) / 3) = (n : ℝ) ^ (-c / 3) := by
  rw [Real.rpow_def_of_pos (by exact_mod_cast hn)]; congr 1; ring

/-- The per-pair estimate for the concentration of uncovered arrivals. -/
lemma prob_badX_le (hH : HypergeomChernoff) {s t : ℕ} (hst : s ≤ t) (ht : t ≤ n) {c : ℝ}
    (hc : 0 < c) (hn : 2 ≤ n) :
    prob (fun σ => c * Real.log n + 2 * (uncovered G σ s).card * t / n <
      ((firstSet σ t ∩ uncovered G σ s).card : ℝ)) ≤ (n : ℝ) ^ (-c / 3) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hL : 0 < c * Real.log n := mul_pos hc (Real.log_pos (by linarith))
  set θ : Equiv.Perm (Fin n) → ℝ := fun σ => c * Real.log n + 2 * (uncovered G σ s).card * t / n
    with hθ
  have hmono : prob (fun σ => c * Real.log n + 2 * (uncovered G σ s).card * t / n <
      ((firstSet σ t ∩ uncovered G σ s).card : ℝ)) ≤
      prob (fun σ => True ∧ θ σ ≤ ((firstSet σ t ∩ uncovered G σ s).card : ℝ)) :=
    prob_mono (fun σ h => ⟨trivial, h.le⟩)
  refine hmono.trans ?_
  rw [← exp_neg_log_div (by omega) c]
  have key := prob_cond_upper hH (j := s) hst ht (fun _ => True) (fun _ _ _ _ => trivial)
    (fun σ => uncovered G σ s)
    (fun σ ρ hρ _ => uncovered_mul (G := G) (fixOutside_posGe_lt hρ))
    (fun σ _ u hu => arrTime_ge_of_mem_uncovered G hu)
    θ
    (fun σ ρ hρ _ => by simp only [hθ, uncovered_mul (G := G) (fixOutside_posGe_lt hρ)])
    (Real.exp (-(c * Real.log n) / 3)) (Real.exp_pos _).le (by
      intro σ _
      set r := (uncovered G σ s).card
      have hμ0 : 0 ≤ (r : ℝ) * ((t : ℝ) - s) / ((n : ℝ) - s) := by
        have h1 : (s : ℝ) ≤ t := by exact_mod_cast hst
        have h2 : (s : ℝ) ≤ n := by exact_mod_cast (hst.trans ht)
        apply div_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith)) (by linarith)
      have hμle : (r : ℝ) * ((t : ℝ) - s) / ((n : ℝ) - s) ≤ (r : ℝ) * t / n := by
        rw [mul_div_assoc, mul_div_assoc]
        exact mul_le_mul_of_nonneg_left (ratio_le_of_le hst ht) (Nat.cast_nonneg _)
      have hθ0 : 0 < θ σ := by
        simp only [hθ]; positivity
      have e : 2 * (r : ℝ) * t / n = 2 * ((r : ℝ) * t / n) := by ring
      exact chernoff_choice_upper hμ0 hL.le (by simp only [hθ]; rw [e]; linarith) hθ0)
  refine (le_of_eq (prob_congr (fun σ => Iff.rfl))).trans (key.trans ?_)
  have h0 : 0 ≤ Real.exp (-(c * Real.log n) / 3) := (Real.exp_pos _).le
  exact (mul_le_mul_of_nonneg_left ((le_of_eq (prob_congr fun σ => Iff.rfl)).trans
    (prob_le_one (fun _ => True))) h0).trans (le_of_eq (mul_one _))

/-- Probability that the good event of Lemma 7.8 fails. -/
lemma prob_not_good78 (hH : HypergeomChernoff) {c : ℝ} (hc : 0 < c) :
    prob (fun σ => ¬ Good78 G σ c) ≤ (n * (n + 1) : ℕ) * (n : ℝ) ^ (-c / 3) := by
  have hε : (0 : ℝ) ≤ (n : ℝ) ^ (-c / 3) := by positivity
  have hsub : ∀ σ, ¬ Good78 G σ c → ∃ v ∈ (univ : Finset (Fin n)), ∃ t ∈ range (n + 1),
      IsPivot G σ v ∧ (arrTime σ v < t ∧
        1 + 2 * (pclSize G σ v : ℝ) * t / n + c * Real.log n < pclAt G σ v t) := by
    intro σ h
    unfold Good78 at h
    push_neg at h
    obtain ⟨v, t, h1, h2, h3, h4⟩ := h
    exact ⟨v, mem_univ _, t, mem_range.2 (by omega), h3, h1, h4⟩
  have key := prob_mono hsub
  refine key.trans ?_
  refine le_trans (le_of_eq (prob_congr fun σ => Iff.rfl)) ((prob_exists_le _ _).trans ?_)
  have hper : ∀ v : Fin n, ∀ t ∈ range (n + 1), prob (fun σ => IsPivot G σ v ∧
      (arrTime σ v < t ∧
        1 + 2 * (pclSize G σ v : ℝ) * t / n + c * Real.log n < pclAt G σ v t)) ≤
      (n : ℝ) ^ (-c / 3) := by
    intro v t ht
    apply prob_le_of_arrTime_cond v _ _ hε
    intro j _
    by_cases hjt : j < t
    · refine le_trans (prob_mono ?_) (lemma_7_8 G hH v hjt (by simpa [Nat.lt_succ_iff] using ht) hc)
      rintro σ ⟨h1, -, h2⟩; exact ⟨h1, h2⟩
    · have : prob (fun σ => (arrTime σ v = j ∧ IsPivot G σ v) ∧ (arrTime σ v < t ∧
          1 + 2 * (pclSize G σ v : ℝ) * t / n + c * Real.log n < pclAt G σ v t)) = 0 := by
        rw [← prob_false_eq (n := n)]
        apply prob_congr
        intro σ
        simp only [iff_false, not_and]
        intro h1 _ h2; omega
      rw [this]; exact mul_nonneg hε (prob_nonneg _)
  calc ∑ v, prob (fun σ => ∃ t ∈ range (n + 1), IsPivot G σ v ∧ (arrTime σ v < t ∧
          1 + 2 * (pclSize G σ v : ℝ) * t / n + c * Real.log n < pclAt G σ v t))
      ≤ ∑ v : Fin n, ∑ t ∈ range (n + 1), (n : ℝ) ^ (-c / 3) := by
        refine sum_le_sum (fun v _ => ?_)
        refine le_trans (le_of_eq (prob_congr fun σ => Iff.rfl)) ((prob_exists_le _ _).trans ?_)
        exact sum_le_sum (fun t ht => (le_of_eq (prob_congr fun σ => Iff.rfl)).trans (hper v t ht))
    _ = (n * (n + 1) : ℕ) * (n : ℝ) ^ (-c / 3) := by
        simp [sum_const, card_range, nsmul_eq_mul, mul_assoc]

/-- Probability that the good event of Lemma 7.6 fails. -/
lemma prob_not_good76 (hH : HypergeomChernoff) {c : ℝ} (hc : 0 < c) :
    prob (fun σ => ¬ Good76 G σ c) ≤ ((n + 1 : ℕ) : ℝ) * (n : ℝ) ^ (2 - c / 8) := by
  have hsub : ∀ σ, ¬ Good76 G σ c → ∃ t ∈ range (n + 1), ∃ v, arrTime σ v + 1 < t ∧
      IsPivot G σ v ∧
      4 * n * (pclAt G σ v t : ℝ) / t + 2 * c * n * Real.log n / t + 1 ≤ pclSize G σ v := by
    intro σ h
    unfold Good76 at h
    push_neg at h
    obtain ⟨t, ht, v, h1, h2, h3⟩ := h
    exact ⟨t, mem_range.2 (by omega), v, h1, h2, h3⟩
  have key := prob_mono hsub
  refine key.trans ?_
  refine le_trans (le_of_eq (prob_congr fun σ => Iff.rfl)) ((prob_exists_le _ _).trans ?_)
  refine (sum_le_sum (fun t ht => (le_of_eq (prob_congr fun σ => Iff.rfl)).trans
    (lemma_7_6 G hH (by simpa [Nat.lt_succ_iff] using ht) hc))).trans (le_of_eq ?_)
  simp [sum_const, card_range, nsmul_eq_mul]

/-- Probability that the concentration of uncovered arrivals fails. -/
lemma prob_not_goodX (hH : HypergeomChernoff) {c : ℝ} (hc : 0 < c) (hn : 2 ≤ n) :
    prob (fun σ => ¬ GoodX G σ c) ≤ ((n + 1) * (n + 1) : ℕ) * (n : ℝ) ^ (-c / 3) := by
  have hsub : ∀ σ, ¬ GoodX G σ c → ∃ s ∈ range (n + 1), ∃ t ∈ range (n + 1),
      s ≤ t ∧ c * Real.log n + 2 * (uncovered G σ s).card * t / n <
        ((firstSet σ t ∩ uncovered G σ s).card : ℝ) := by
    intro σ h
    unfold GoodX at h
    push_neg at h
    obtain ⟨s, t, h1, h2, h3⟩ := h
    exact ⟨s, mem_range.2 (by omega), t, mem_range.2 (by omega), h1, h3⟩
  have key := prob_mono hsub
  refine key.trans ?_
  refine le_trans (le_of_eq (prob_congr fun σ => Iff.rfl)) ((prob_exists_le _ _).trans ?_)
  have hε : (0 : ℝ) ≤ (n : ℝ) ^ (-c / 3) := by positivity
  have hper : ∀ s ∈ range (n + 1), ∀ t ∈ range (n + 1), prob (fun σ => s ≤ t ∧
      c * Real.log n + 2 * (uncovered G σ s).card * t / n <
        ((firstSet σ t ∩ uncovered G σ s).card : ℝ)) ≤ (n : ℝ) ^ (-c / 3) := by
    intro s _ t ht
    by_cases hst : s ≤ t
    · exact (prob_mono (fun σ h => h.2)).trans
        (prob_badX_le G hH hst (by simpa [Nat.lt_succ_iff] using ht) hc hn)
    · refine le_trans (le_of_eq ?_) hε
      rw [← prob_false_eq (n := n)]
      exact prob_congr (fun σ => by simp [hst])
  calc ∑ s ∈ range (n + 1), prob (fun σ => ∃ t ∈ range (n + 1), s ≤ t ∧
        c * Real.log n + 2 * (uncovered G σ s).card * t / n <
          ((firstSet σ t ∩ uncovered G σ s).card : ℝ))
      ≤ ∑ s ∈ range (n + 1), ∑ t ∈ range (n + 1), (n : ℝ) ^ (-c / 3) := by
        refine sum_le_sum (fun s hs => ?_)
        refine le_trans (le_of_eq (prob_congr fun σ => Iff.rfl)) ((prob_exists_le _ _).trans ?_)
        exact sum_le_sum (fun t ht => (le_of_eq (prob_congr fun σ => Iff.rfl)).trans
          (hper s hs t ht))
    _ = _ := by simp [sum_const, card_range, nsmul_eq_mul, mul_assoc]

/-- Probability that the good event of Lemma 7.9 fails. -/
lemma prob_not_goodLoad (hH : HypergeomChernoff) {c : ℝ} (hc : 0 < c) (hn : 2 ≤ n) :
    prob (fun σ => ¬ GoodLoad G σ c) ≤
      (n * (n + 1) : ℕ) * (n : ℝ) ^ (-c / 3) + ((n + 1 : ℕ) : ℝ) * (n : ℝ) ^ (2 - c / 8) +
        ((n + 1) * (n + 1) : ℕ) * (n : ℝ) ^ (-c / 3) := by
  have h1 := prob_not_good78 G hH hc
  have h2 := prob_not_good76 G hH hc
  have h3 := prob_not_goodX G hH hc hn
  have hsub : ∀ σ, ¬ GoodLoad G σ c → (¬ Good78 G σ c ∨ ¬ Good76 G σ c) ∨ ¬ GoodX G σ c := by
    intro σ h
    by_cases h1 : Good78 G σ c
    · by_cases h2 : Good76 G σ c
      · exact Or.inr (fun h3 => h ⟨h1, h2, h3⟩)
      · exact Or.inl (Or.inr h2)
    · exact Or.inl (Or.inl h1)
  have key := prob_mono hsub
  have k2 := prob_or_le (fun σ => ¬ Good78 G σ c ∨ ¬ Good76 G σ c) (fun σ => ¬ GoodX G σ c)
  have k3 := prob_or_le (fun σ => ¬ Good78 G σ c) (fun σ => ¬ Good76 G σ c)
  refine key.trans ?_
  refine (le_of_eq (prob_congr fun σ => Iff.rfl)).trans (k2.trans ?_)
  refine (add_le_add ((le_of_eq (prob_congr fun σ => Iff.rfl)).trans (k3.trans
    (add_le_add ((le_of_eq (prob_congr fun σ => Iff.rfl)).trans h1)
      ((le_of_eq (prob_congr fun σ => Iff.rfl)).trans h2))))
    ((le_of_eq (prob_congr fun σ => Iff.rfl)).trans h3)).trans ?_
  exact le_rfl

/-- The bound of Lemma 7.9 (as a function of the arrival order and the set `S`). -/
noncomputable def loadBound (k : ℕ) (σ : Equiv.Perm (Fin n)) (c : ℝ) (S : Finset (Fin n)) : ℝ :=
  (5 + 2 * c * Real.log n) * ((n : ℝ) / Tk G k σ * (1 + 2 * c * Real.log n) +
    2 * ((S.sup (pclSize G σ) : ℕ) : ℝ) + 2 * (uncovered G σ (Tk G k σ)).card / S.card)

/-- **Lemma 7.9 (the least loaded cluster has bounded projected load).**  Let `T` be the time
before the arrival of the `(k+1)`-th pivot and `U` the set of vertices uncovered at time `T`.
With probability at least `1 - (n(n+1) n^{-c/3} + (n+1) n^{2-c/8} + (n+1)² n^{-c/3})`, the
following holds simultaneously for every late pivot `p` (arriving at a time `t ≥ T`) and every
non-empty set `S` of the clusters present at time `T` (each containing one early pivot cluster):
when `p` is assigned to a least loaded cluster, that cluster has projected load at most
`(5 + 2c ln n) ((n/T)(1 + 2c ln n) + 2 μ(S) + 2 |U|/|S|) = O(μ(S) ln n + n ln² n / T + |U| ln n/|S|)`
(for constant `c`), where `μ(S)` is the maximum projected load (final size) of the pivot clusters
of `S`.  (Assumes Fact 2.2, as the hypothesis `HypergeomChernoff`.) -/
theorem lemma_7_9 (hH : HypergeomChernoff) {k : ℕ} (hk : 0 < k) {c : ℝ} (hc : 0 < c)
    (hn : 2 ≤ n) :
    prob (fun σ => ∃ p, IsPivot G σ p ∧ Tk G k σ ≤ arrTime σ p ∧
      ∃ S ⊆ pivotsUpTo G σ (Tk G k σ), S.Nonempty ∧
        loadBound G k σ c S < projLoad G k σ (arrTime σ p) (bpLabel G k σ p)) ≤
      (n * (n + 1) : ℕ) * (n : ℝ) ^ (-c / 3) + ((n + 1 : ℕ) : ℝ) * (n : ℝ) ^ (2 - c / 8) +
        ((n + 1) * (n + 1) : ℕ) * (n : ℝ) ^ (-c / 3) := by
  have key : ∀ σ, (∃ p, IsPivot G σ p ∧ Tk G k σ ≤ arrTime σ p ∧
      ∃ S ⊆ pivotsUpTo G σ (Tk G k σ), S.Nonempty ∧
        loadBound G k σ c S < projLoad G k σ (arrTime σ p) (bpLabel G k σ p)) →
      ¬ GoodLoad G σ c := by
    rintro σ ⟨p, hp, hpT, S, hS, hSne, hlt⟩ hG
    have := projLoad_le_of_good G k σ hk hc.le hn hG hp hpT hS hSne
    unfold loadBound at hlt
    linarith
  exact (prob_mono key).trans ((le_of_eq (prob_congr fun σ => Iff.rfl)).trans
    (prob_not_goodLoad G hH hc hn))

/-- The late pivot clusters partition the vertices uncovered at time `T`. -/
lemma sum_late_pclSize (k : ℕ) (σ : Equiv.Perm (Fin n)) :
    ∑ p ∈ (pivotsUpTo G σ n).filter (fun p => Tk G k σ ≤ arrTime σ p), pclSize G σ p =
      (uncovered G σ (Tk G k σ)).card := by
  unfold pclSize
  rw [← card_biUnion]
  · congr 1
    ext u
    simp only [mem_biUnion, mem_filter, mem_univ, true_and]
    rw [mem_uncovered_iff_late]
    constructor
    · rintro ⟨p, ⟨-, hp⟩, rfl⟩; exact hp
    · intro h; exact ⟨pivotOf G σ u, ⟨isPivot_pivotOf G σ u, h⟩, rfl⟩
  · intro p _ q _ hne
    simp only [Function.onFun]
    rw [disjoint_left]
    intro u hu hu'
    simp only [mem_filter, mem_univ, true_and] at hu hu'
    exact hne (hu.symm.trans hu')

/-- **Merging cost on the good event (consequence of Lemma 7.9).**  On the good event, for every
non-empty set `S` of early pivots, the merging cost is at most `|U|` times the bound of
Lemma 7.9. -/
theorem mergeCost_le_of_good {k : ℕ} (hk : 0 < k) (σ : Equiv.Perm (Fin n)) {c : ℝ} (hc : 0 ≤ c)
    (hn : 2 ≤ n) (hG : GoodLoad G σ c) {S : Finset (Fin n)}
    (hS : S ⊆ pivotsUpTo G σ (Tk G k σ)) (hSne : S.Nonempty) :
    (mergeCost G k σ : ℝ) ≤ (uncovered G σ (Tk G k σ)).card * loadBound G k σ c S := by
  rw [mergeCost_eq_late G k σ hk, ← sum_late_pclSize G k σ]
  push_cast
  rw [sum_mul]
  apply sum_le_sum
  intro p hp
  obtain ⟨hp1, hp2⟩ := mem_filter.1 hp
  exact mul_le_mul_of_nonneg_left (projLoad_le_of_good G k σ hk hc hn hG hp1 hp2 hS hSne)
    (Nat.cast_nonneg _)

end CCK
