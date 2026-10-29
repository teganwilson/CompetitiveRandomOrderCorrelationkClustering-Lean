module

public import RequestProject.Theorem5Expect

/-!
# Theorem 5: UNIFORM PIVOT is `O(log³ n)`-competitive on disjoint cliques

We run UNIFORM PIVOT with threshold `L = c₀ ln n`, `c₀ = 128` (Lemma 6.2 with `c = 32`), and use
the good event `G₁` with `c₁ = 256` (so that `c₁ ln n / 2 = L`, Lemma 6.1).
-/

@[expose] public section

open Finset
open scoped Classical

namespace CCK

variable {n : ℕ} {ι : Type*} {q : Fin n → ι} {k : ℕ}

/-- If there are at most `k` cliques, no vertex is uncovered at time `T₀`. -/
lemma lateSet_eq_empty (hk : numCliques q ≤ k) (σ : Equiv.Perm (Fin n)) :
    lateSet q σ k = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  intro v hv
  have hv' := (mem_lateSet_iff q k σ v).1 hv
  by_cases hex : ∃ t, k ≤ (pivotsUpTo (cliqueGraph q) σ t).card
  · have hT0 : kthPivotTime (cliqueGraph q) σ k = Nat.find hex := by
      unfold kthPivotTime; rw [dif_pos hex]
    have hk' : k ≤ (pivotsUpTo (cliqueGraph q) σ (kthPivotTime (cliqueGraph q) σ k)).card := by
      rw [hT0]; exact Nat.find_spec hex
    have himg : (pivotsUpTo (cliqueGraph q) σ (kthPivotTime (cliqueGraph q) σ k)).image (cidx q)
        = range (numCliques q) := by
      apply eq_of_subset_of_card_le
      · intro j hj; obtain ⟨p, -, rfl⟩ := mem_image.1 hj; exact mem_range.2 (cidx_lt q p)
      · rw [card_range, card_image_of_injOn (cidx_injOn_pivots q σ _)]
        exact le_trans hk hk'
    have : cidx q v ∈ (pivotsUpTo (cliqueGraph q) σ (kthPivotTime (cliqueGraph q) σ k)).image
        (cidx q) := by rw [himg]; exact mem_range.2 (cidx_lt q v)
    obtain ⟨p, hp, hpv⟩ := mem_image.1 this
    have h1 := hv' p hpv
    have h2 := ((mem_pivotsUpTo_iff _ σ _ p).1 hp).2
    omega
  · have hT0 : kthPivotTime (cliqueGraph q) σ k = n := by
      unfold kthPivotTime; rw [dif_neg hex]
    have h1 := hv' v rfl
    have h2 : arrTime σ v < n := Fin.isLt _
    omega

/-- The bound on `P[Ḡ₁]` (Lemma 6.1 and a union bound). -/
lemma prob_not_goodG1 (hCh : ChernoffBound) (hPNA : PermNegAssoc) (c₁ : ℝ) :
    prob (fun σ => ¬ GoodG1 q c₁ σ) ≤
      (Nat.log 2 n + 1 : ℕ) * numCliques q * (n : ℝ) ^ (-c₁ / 8) := by
  have hsub : ∀ σ, ¬ GoodG1 q c₁ σ → ∃ i ∈ range (Nat.log 2 n + 1), ∃ j ∈ range (numCliques q),
      bPar c₁ n i ≤ cw q j ∧ ((firstSet σ (2 ^ i) ∩ fib q j).card : ℝ) ≤ c₁ * Real.log n / 2 := by
    intro σ h
    unfold GoodG1 at h
    push_neg at h
    obtain ⟨i, hi, j, hj, h1, h2⟩ := h
    exact ⟨i, mem_range.2 (by omega), j, mem_range.2 hj, h1, h2⟩
  have hn : n ≠ 0 ∨ n = 0 := by tauto
  rcases hn with hn | hn
  swap
  · subst hn
    have : prob (fun σ : Equiv.Perm (Fin 0) => ¬ GoodG1 q c₁ σ) ≤ 0 := by
      have hall : ∀ σ : Equiv.Perm (Fin 0), GoodG1 q c₁ σ := by
        intro σ i _ j hj
        have : numCliques q = 0 := by have := numCliques_le q; omega
        omega
      calc prob (fun σ : Equiv.Perm (Fin 0) => ¬ GoodG1 q c₁ σ)
          ≤ prob (fun _ : Equiv.Perm (Fin 0) => False) := prob_mono (fun σ h => h (hall σ))
        _ = 0 := prob_false_eq
    refine this.trans ?_
    have : numCliques q = 0 := by have := numCliques_le q; omega
    simp [this]
  have hper : ∀ i ∈ range (Nat.log 2 n + 1), ∀ j ∈ range (numCliques q),
      prob (fun σ => bPar c₁ n i ≤ cw q j ∧
        ((firstSet σ (2 ^ i) ∩ fib q j).card : ℝ) ≤ c₁ * Real.log n / 2) ≤
        (n : ℝ) ^ (-c₁ / 8) := by
    intro i hi j hj
    have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    by_cases hB : bPar c₁ n i ≤ cw q j
    · have ht0 : 0 < 2 ^ i := by positivity
      have ht : 2 ^ i ≤ n := by
        have := Nat.pow_log_le_self 2 hn
        exact le_trans (Nat.pow_le_pow_right (by norm_num) (by simpa using mem_range.1 hi |>
          Nat.lt_succ_iff.1)) this
      have hK : c₁ * n * Real.log n / ((2 ^ i : ℕ) : ℝ) ≤ (fib q j).card := by
        rw [card_fib q (mem_range.1 hj)]
        push_cast
        exact hB
      refine le_trans (prob_mono (fun σ h => h.2)) ?_
      exact lemma_6_1 hCh hPNA ht0 ht c₁ (fib q j) hK
    · calc prob (fun σ => bPar c₁ n i ≤ cw q j ∧
            ((firstSet σ (2 ^ i) ∩ fib q j).card : ℝ) ≤ c₁ * Real.log n / 2)
          ≤ prob (fun _ : Equiv.Perm (Fin n) => False) := prob_mono (fun σ h => hB h.1)
        _ = 0 := prob_false_eq
        _ ≤ _ := Real.rpow_nonneg hnR _
  have key := prob_mono hsub
  refine le_trans (le_of_eq (prob_congr fun σ => Iff.rfl)) (key.trans ?_)
  refine le_trans (le_of_eq (prob_congr fun σ => Iff.rfl)) ((prob_exists_le _ _).trans ?_)
  have hstep : ∀ i ∈ range (Nat.log 2 n + 1), prob (fun σ => ∃ j ∈ range (numCliques q),
      bPar c₁ n i ≤ cw q j ∧
        ((firstSet σ (2 ^ i) ∩ fib q j).card : ℝ) ≤ c₁ * Real.log n / 2) ≤
      ∑ j ∈ range (numCliques q), (n : ℝ) ^ (-c₁ / 8) := by
    intro i hi
    refine ((le_of_eq (prob_congr fun σ => Iff.rfl)).trans (prob_exists_le _ _)).trans ?_
    exact sum_le_sum (fun j hj =>
      (le_of_eq (prob_congr fun σ => Iff.rfl)).trans (hper i hi j hj))
  refine (sum_le_sum (fun i hi => (le_of_eq (prob_congr fun σ => Iff.rfl)).trans
    (hstep i hi))).trans ?_
  simp [sum_const, card_range, nsmul_eq_mul, mul_assoc]

/-- At most one window event `T_i` occurs. -/
lemma sum_window_le_one (σ : Equiv.Perm (Fin n)) (m : ℕ) :
    ∑ i ∈ range m, (if InWindow q k σ i then (1 : ℝ) else 0) ≤ 1 := by
  rw [sum_boole]
  have : (range m).filter (fun i => InWindow q k σ i) ⊆
      {Nat.log 2 (kthPivotTime (cliqueGraph q) σ k)} := by
    intro i hi
    obtain ⟨-, h1, h2⟩ := mem_filter.1 hi
    rw [mem_singleton]
    exact (Nat.log_eq_of_pow_le_of_lt_pow h1 h2).symm
  have := card_le_card this
  rw [card_singleton] at this
  exact_mod_cast this

/-- `B_i ρ_i ≤ 2 c₁ ln n`. -/
lemma bPar_mul_rhoW_le {c₁ : ℝ} (hc : 0 ≤ c₁ * Real.log n) (i : ℕ) :
    bPar c₁ n i * rhoW n i ≤ 2 * (c₁ * Real.log n) := by
  unfold bPar rhoW
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h2 : (0 : ℝ) < 2 ^ i := by positivity
  have ht : (tWin n i : ℝ) ≤ 2 ^ (i + 1) := by
    unfold tWin; exact_mod_cast min_le_left _ _
  rw [div_mul_div_comm, div_le_iff₀ (by positivity)]
  have : c₁ * n * Real.log n * (tWin n i : ℝ) ≤ c₁ * n * Real.log n * 2 ^ (i + 1) :=
    mul_le_mul_of_nonneg_left ht (by have := hnR.le; nlinarith)
  calc c₁ * n * Real.log n * (tWin n i : ℝ) ≤ c₁ * n * Real.log n * 2 ^ (i + 1) := this
    _ = 2 * (c₁ * Real.log n) * (2 ^ i * n) := by ring

end CCK


/-!
# Theorem 5: assembling the proof

We run UNIFORM PIVOT with threshold `L = c₀ ln n`, `c₀ = 128` (Lemma 6.2 with `c = 32`), and use
the good event `G₁` with `c₁ = 256` (so that `c₁ ln n / 2 = L`), and the good event
`G₂ = {|S| ≥ k - r}`.
-/

@[expose] public section

open Finset
open scoped Classical

namespace CCK

variable {n : ℕ} {ι : Type*} {q : Fin n → ι} {k : ℕ}

/-- The conditional cost bound of UNIFORM PIVOT given the arrival order `σ`
(`W · max_{p∈S} |K(p)| + F/|S|`, see `expectω_cost_le`). -/
noncomputable def upBound (q : Fin n → ι) (k : ℕ) (L : ℝ) (σ : Equiv.Perm (Fin n)) : ℝ :=
  (lateSet q σ k).card * maxLead q σ k L +
    (latePairs q σ k : ℝ) / (2 * (lightPivots (cliqueGraph q) σ k L).card)

/-- Auxiliary result for the proof of Theorem 5 (Section 6). -/
lemma upBound_nonneg (L : ℝ) (σ : Equiv.Perm (Fin n)) : 0 ≤ upBound q k L σ := by
  unfold upBound; positivity

/-- Auxiliary result for the proof of Theorem 5 (Section 6). -/
lemma upBound_le_sq (L : ℝ) (σ : Equiv.Perm (Fin n)) : upBound q k L σ ≤ 2 * (n : ℝ) ^ 2 := by
  unfold upBound
  have hW : ((lateSet q σ k).card : ℝ) ≤ n := by
    have := card_le_univ (lateSet q σ k); simp only [Fintype.card_fin] at this; exact_mod_cast this
  have hM : (maxLead q σ k L : ℝ) ≤ n := by
    have : maxLead q σ k L ≤ n := by
      unfold maxLead
      apply Finset.sup_le
      intro p _
      have := card_le_univ (univ.filter (fun u => cidx q u = cidx q p))
      simpa using this
    exact_mod_cast this
  have hLP : (latePairs q σ k : ℝ) ≤ (n : ℝ) ^ 2 := by
    have : latePairs q σ k ≤ n ^ 2 := by
      unfold latePairs
      refine (card_filter_le _ _).trans ?_
      rw [card_product, sq]
      have := card_le_univ (lateSet q σ k); simp only [Fintype.card_fin] at this
      exact Nat.mul_le_mul this this
    exact_mod_cast this
  have hLP0 : (0 : ℝ) ≤ latePairs q σ k := Nat.cast_nonneg _
  have hdiv : (latePairs q σ k : ℝ) / (2 * (lightPivots (cliqueGraph q) σ k L).card) ≤
      (n : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos (lightPivots (cliqueGraph q) σ k L).card with h0 | h0
    · rw [h0]; simp
    · refine (div_le_self hLP0 ?_).trans hLP
      have : (1 : ℝ) ≤ (lightPivots (cliqueGraph q) σ k L).card := by exact_mod_cast h0
      linarith
  have hW0 : (0 : ℝ) ≤ (lateSet q σ k).card := Nat.cast_nonneg _
  have hM0 : (0 : ℝ) ≤ maxLead q σ k L := Nat.cast_nonneg _
  nlinarith [mul_le_mul hW hM hM0 (Nat.cast_nonneg n)]

/-- Auxiliary result for the proof of Theorem 5 (Section 6). -/
lemma upBound_eq_zero (hk : numCliques q ≤ k) (L : ℝ) (σ : Equiv.Perm (Fin n)) :
    upBound q k L σ = 0 := by
  have h1 : lateSet q σ k = ∅ := lateSet_eq_empty hk σ
  have h2 : latePairs q σ k = 0 := by unfold latePairs; rw [h1]; simp
  unfold upBound; rw [h1, h2]; simp

/-- Auxiliary result for the proof of Theorem 5 (Section 6). -/
lemma exists_window (hk0 : 0 < k) (hk : k ≤ numCliques q) (σ : Equiv.Perm (Fin n)) :
    ∃ i ≤ Nat.log 2 n, InWindow q k σ i := by
  have h1 := one_le_kthPivotTime q k σ hk0 hk
  have h2 := kthPivotTime_le q k σ hk
  refine ⟨Nat.log 2 (kthPivotTime (cliqueGraph q) σ k), Nat.log_mono_right h2, ?_, ?_⟩
  · exact Nat.pow_log_le_self 2 (by omega)
  · exact Nat.lt_pow_succ_log_self (by norm_num) _

/-- Auxiliary result for the proof of Theorem 5 (Section 6). -/
lemma maxLead_le (σ : Equiv.Perm (Fin n)) {L c₁ : ℝ} {i : ℕ} (hG1 : GoodG1 q c₁ σ)
    (hT : InWindow q k σ i) (hi : i ≤ Nat.log 2 n) (hL : L ≤ c₁ * Real.log n / 2)
    (hB : 0 ≤ bPar c₁ n i) :
    (maxLead q σ k L : ℝ) ≤ bPar c₁ n i := by
  rcases (lightPivots (cliqueGraph q) σ k L).eq_empty_or_nonempty with h0 | hne
  · unfold maxLead; rw [h0]; simpa using hB
  · obtain ⟨p, hp, hpe⟩ := Finset.exists_mem_eq_sup _ hne
      (fun p => (univ.filter (fun u => cidx q u = cidx q p)).card)
    have h := claim_6_3_a hG1 hT hi hL p hp
    unfold maxLead
    rw [hpe]
    have : (univ.filter (fun u => cidx q u = cidx q p)).card = cw q (cidx q p) :=
      card_fib q (cidx_lt q p)
    rw [this]; exact h.le

/-- The pointwise decomposition of the conditional cost bound on `G₁ ∩ G₂`. -/
lemma upBound_good (hk0 : 0 < k) (hk : k < numCliques q) {L c₁ : ℝ}
    (hL : L ≤ c₁ * Real.log n / 2) (hc : 0 ≤ c₁ * Real.log n / 2) (σ : Equiv.Perm (Fin n))
    (hG1 : GoodG1 q c₁ σ) (hG2 : k - rOf q k ≤ (lightPivots (cliqueGraph q) σ k L).card) :
    upBound q k L σ ≤ ∑ i ∈ range (Nat.log 2 n + 1),
      (bPar c₁ n i * (if GoodG1 q c₁ σ ∧ InWindow q k σ i then ((lateSet q σ k).card : ℝ)
        else 0) +
       (if GoodG1 q c₁ σ ∧ InWindow q k σ i then (latePairs q σ k : ℝ) else 0) /
        (2 * ((k : ℝ) - rOf q k))) := by
  obtain ⟨i0, hi0, hT⟩ := exists_window hk0 hk.le σ
  have hr := rOf_lt hk0 hk
  have hkr : (0 : ℝ) < (k : ℝ) - rOf q k := by
    have : ((rOf q k : ℕ) : ℝ) < k := by exact_mod_cast hr
    linarith
  have hS : (k : ℝ) - rOf q k ≤ (lightPivots (cliqueGraph q) σ k L).card := by
    have : (((k - rOf q k : ℕ)) : ℝ) ≤ (lightPivots (cliqueGraph q) σ k L).card := by
      exact_mod_cast hG2
    rwa [Nat.cast_sub hr.le] at this
  have hterm_nonneg : ∀ i ∈ range (Nat.log 2 n + 1), 0 ≤
      (bPar c₁ n i * (if GoodG1 q c₁ σ ∧ InWindow q k σ i then ((lateSet q σ k).card : ℝ)
        else 0) +
       (if GoodG1 q c₁ σ ∧ InWindow q k σ i then (latePairs q σ k : ℝ) else 0) /
        (2 * ((k : ℝ) - rOf q k))) := by
    intro i _
    have := bPar_nonneg (i := i) hc
    apply add_nonneg
    · apply mul_nonneg this; split_ifs <;> positivity
    · apply div_nonneg _ (by linarith); split_ifs <;> positivity
  refine le_trans ?_ (single_le_sum hterm_nonneg (mem_range.2 (Nat.lt_succ_of_le hi0)))
  simp only [hG1, hT, and_self, if_true]
  unfold upBound
  have hB := bPar_nonneg (i := i0) hc
  have hM := maxLead_le σ hG1 hT hi0 hL hB
  have hW0 : (0 : ℝ) ≤ (lateSet q σ k).card := Nat.cast_nonneg _
  apply add_le_add
  · rw [mul_comm]; exact mul_le_mul_of_nonneg_right hM hW0
  · apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by linarith) (by linarith)

/-- The expected cost of UNIFORM PIVOT is at most `E[upBound]`. -/
lemma uniformPivotExpCost_le (L : ℝ) :
    uniformPivotExpCost (cliqueGraph q) k L ≤ expect (fun σ => upBound q k L σ) :=
  expect_mono (fun σ => expectω_cost_le q σ k L)

/-- The main estimate: `E[upBound] ≤ 2n²(P[Ḡ₁] + P[Ḡ₂]) + ∑_i (…)`. -/
lemma expect_upBound_le (hk0 : 0 < k) (hk : k < numCliques q) {L c₁ : ℝ}
    (hL : L ≤ c₁ * Real.log n / 2) (hc : 0 ≤ c₁ * Real.log n / 2) :
    expect (fun σ => upBound q k L σ) ≤
      2 * (n : ℝ) ^ 2 * (prob (fun σ => ¬ GoodG1 q c₁ σ) +
        prob (fun σ => (lightPivots (cliqueGraph q) σ k L).card < k - rOf q k)) +
      ∑ i ∈ range (Nat.log 2 n + 1),
        (bPar c₁ n i * (3 * sOf q k * aOf q k * rhoW n i +
          2 * bPar c₁ n i * sOf q k * aOf q k * rhoW n i ^ 2) +
        ((sOf q k : ℝ) ^ 2 * expect (fun σ => if InWindow q k σ i then (1 : ℝ) else 0) +
          2 * (sOf q k : ℝ) ^ 2 * bPar c₁ n i * rhoW n i +
          bPar c₁ n i ^ 2 * (sOf q k : ℝ) ^ 2 * rhoW n i ^ 2) / (2 * ((k : ℝ) - rOf q k))) := by
  set D : ℝ := 2 * ((k : ℝ) - rOf q k) with hD
  have hr := rOf_lt hk0 hk
  have hD0 : 0 < D := by
    have : ((rOf q k : ℕ) : ℝ) < k := by exact_mod_cast hr
    rw [hD]; linarith
  set X : ℕ → Equiv.Perm (Fin n) → ℝ := fun i σ =>
    if GoodG1 q c₁ σ ∧ InWindow q k σ i then ((lateSet q σ k).card : ℝ) else 0 with hX
  set Y : ℕ → Equiv.Perm (Fin n) → ℝ := fun i σ =>
    if GoodG1 q c₁ σ ∧ InWindow q k σ i then (latePairs q σ k : ℝ) else 0 with hY
  set P1 : Equiv.Perm (Fin n) → Prop := fun σ => ¬ GoodG1 q c₁ σ with hP1
  set P2 : Equiv.Perm (Fin n) → Prop :=
    fun σ => (lightPivots (cliqueGraph q) σ k L).card < k - rOf q k with hP2
  have hpt : ∀ σ, upBound q k L σ ≤
      2 * (n : ℝ) ^ 2 * ((if P1 σ then (1 : ℝ) else 0) + (if P2 σ then (1 : ℝ) else 0)) +
      ∑ i ∈ range (Nat.log 2 n + 1), (bPar c₁ n i * X i σ + (1 / D) * Y i σ) := by
    intro σ
    have hsum0 : 0 ≤ ∑ i ∈ range (Nat.log 2 n + 1), (bPar c₁ n i * X i σ + (1 / D) * Y i σ) := by
      apply sum_nonneg
      intro i _
      have := bPar_nonneg (i := i) hc
      apply add_nonneg
      · apply mul_nonneg this; simp only [hX]; split_ifs <;> positivity
      · apply mul_nonneg (by positivity); simp only [hY]; split_ifs <;> positivity
    by_cases h1 : P1 σ
    · have := upBound_le_sq (q := q) (k := k) L σ
      simp only [h1, if_true]
      have : (0 : ℝ) ≤ (if P2 σ then (1 : ℝ) else 0) := by split_ifs <;> norm_num
      nlinarith [sq_nonneg (n : ℝ)]
    by_cases h2 : P2 σ
    · have := upBound_le_sq (q := q) (k := k) L σ
      simp only [h2, if_true]
      have : (0 : ℝ) ≤ (if P1 σ then (1 : ℝ) else 0) := by split_ifs; norm_num
      nlinarith [sq_nonneg (n : ℝ)]
    simp only [h1, h2, if_false, add_zero, mul_zero, zero_add]
    have hG1 : GoodG1 q c₁ σ := by simpa [hP1] using h1
    have hG2 : k - rOf q k ≤ (lightPivots (cliqueGraph q) σ k L).card := by
      simp only [hP2, not_lt] at h2; exact h2
    refine (upBound_good hk0 hk hL hc σ hG1 hG2).trans (le_of_eq ?_)
    apply sum_congr rfl
    intro i _
    simp only [hX, hY, hD]; ring
  refine (expect_mono hpt).trans ?_
  rw [expect_add, expect_smul, expect_add, expect_indicator, expect_indicator, expect_sum]
  apply add_le_add le_rfl
  apply sum_le_sum
  intro i hi
  have hi' : i ≤ Nat.log 2 n := Nat.lt_succ_iff.1 (mem_range.1 hi)
  rw [expect_add, expect_smul, expect_smul]
  have hB := bPar_nonneg (i := i) hc
  have h1 := expect_W_window (q := q) (k := k) hk0 hk hi' hc
  have h2 := expect_LP_window (q := q) (k := k) hk hi' hc
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left h1 hB
  · rw [one_div_mul_eq_div]
    exact div_le_div_of_nonneg_right h2 hD0.le

/-- Auxiliary result for the proof of Theorem 5 (Section 6). -/
lemma one_le_sOf (hk : k < numCliques q) : (1 : ℝ) ≤ sOf q k := by
  have : 1 ≤ sOf q k := by
    unfold sOf sParam
    rw [tailSum_succ hk]
    have := cw_pos q hk
    omega
  exact_mod_cast this

/-- Auxiliary result for the proof of Theorem 5 (Section 6). -/
lemma one_lt_aOf (hk0 : 0 < k) (hk : k < numCliques q) : (1 : ℝ) < aOf q k := by
  have hr : rParam (cw q) (numCliques q) k < k := rOf_lt hk0 hk
  have h := lt_aParam_of_rParam_le (cw_sorted q) hr le_rfl (by omega)
  have h1 : (1 : ℝ) ≤ cw q (rParam (cw q) (numCliques q) k) := by
    exact_mod_cast cw_pos q (by omega : rParam (cw q) (numCliques q) k < numCliques q)
  unfold aOf; linarith

/-- Auxiliary result for the proof of Theorem 5 (Section 6). -/
lemma natLog_le_three_log (hn : 2 ≤ n) : ((Nat.log 2 n : ℕ) : ℝ) + 1 ≤ 3 * Real.log n := by
  have hl2 := Real.log_two_gt_d9
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog2 : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hnR
  have hpow : ((2 ^ Nat.log 2 n : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.pow_log_le_self 2 (by omega)
  have h1 : (Nat.log 2 n : ℝ) * Real.log 2 ≤ Real.log n := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) (by exact_mod_cast hpow)
  have h0 : (0 : ℝ) ≤ Nat.log 2 n := Nat.cast_nonneg _
  nlinarith

/-- The contribution of the bad events: `2n²(P[Ḡ₁] + P[Ḡ₂]) ≤ 8`. -/
lemma bad_events_le (hCh : ChernoffBound) (hPNA : PermNegAssoc) (hn : 2 ≤ n) (hk0 : 0 < k)
    (hk : k < numCliques q) :
    2 * (n : ℝ) ^ 2 * (prob (fun σ => ¬ GoodG1 q 256 σ) +
      prob (fun σ => (lightPivots (cliqueGraph q) σ k (128 * Real.log n)).card < k - rOf q k))
      ≤ 8 := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have h1 := prob_not_goodG1 (q := q) hCh hPNA 256
  have h2 := lemma_6_2 hCh hPNA q hk0 hk (c := 32) (by norm_num)
  have e2 : (4 * 32 * Real.log n) = 128 * Real.log n := by ring
  rw [e2] at h2
  have hm : ((Nat.log 2 n + 1 : ℕ) : ℝ) ≤ n := by
    have : Nat.log 2 n < n := Nat.log_lt_self 2 (by omega)
    exact_mod_cast (by omega : Nat.log 2 n + 1 ≤ n)
  have hl : (numCliques q : ℝ) ≤ n := by exact_mod_cast numCliques_le q
  have r1 : (n : ℝ) ^ (-(256 : ℝ) / 8) = 1 / (n : ℝ) ^ (32 : ℕ) := by
    rw [show -(256 : ℝ) / 8 = -((32 : ℕ) : ℝ) by norm_num, Real.rpow_neg hn0.le,
      Real.rpow_natCast, one_div]
  have r2 : (n : ℝ) ^ (-(32 : ℝ) / 8) = 1 / (n : ℝ) ^ (4 : ℕ) := by
    rw [show -(32 : ℝ) / 8 = -((4 : ℕ) : ℝ) by norm_num, Real.rpow_neg hn0.le,
      Real.rpow_natCast, one_div]
  have r3 : ∀ e : ℝ, e ≤ -4 → (n : ℝ) ^ e ≤ 1 / (n : ℝ) ^ (4 : ℕ) := by
    intro e he
    calc (n : ℝ) ^ e ≤ (n : ℝ) ^ (-((4 : ℕ) : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by push_cast; linarith)
      _ = 1 / (n : ℝ) ^ (4 : ℕ) := by rw [Real.rpow_neg hn0.le, Real.rpow_natCast, one_div]
  rw [r1] at h1
  have h2' := h2
  rw [r2] at h2'
  have h2a := r3 (1 - 32) (by norm_num)
  have h2b := r3 (1 - 32 / 4) (by norm_num)
  have h2c := r3 (1 - 32 / 3) (by norm_num)
  have hP1 : 2 * (n : ℝ) ^ 2 * prob (fun σ => ¬ GoodG1 q 256 σ) ≤ 2 := by
    have hpos : (0 : ℝ) < (n : ℝ) ^ (32 : ℕ) := by positivity
    have : 2 * (n : ℝ) ^ 2 * prob (fun σ => ¬ GoodG1 q 256 σ) ≤
        2 * (n : ℝ) ^ 2 * (n * n * (1 / (n : ℝ) ^ (32 : ℕ))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      refine h1.trans ?_
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul hm hl (Nat.cast_nonneg _) (by positivity)
    refine this.trans ?_
    rw [mul_one_div, ← mul_div_assoc, div_le_iff₀ hpos]
    have h4 : (n : ℝ) ^ 4 ≤ (n : ℝ) ^ 32 := pow_le_pow_right₀ (by linarith) (by norm_num)
    nlinarith
  have hP2 : 2 * (n : ℝ) ^ 2 * prob (fun σ =>
      (lightPivots (cliqueGraph q) σ k (128 * Real.log n)).card < k - rOf q k) ≤ 6 := by
    have : 2 * (n : ℝ) ^ 2 * prob (fun σ =>
        (lightPivots (cliqueGraph q) σ k (128 * Real.log n)).card < k - rOf q k) ≤
        2 * (n : ℝ) ^ 2 * (4 * (1 / (n : ℝ) ^ (4 : ℕ))) :=
      mul_le_mul_of_nonneg_left (h2'.trans (by linarith)) (by positivity)
    refine this.trans ?_
    have e : 2 * (n : ℝ) ^ 2 * (4 * (1 / (n : ℝ) ^ (4 : ℕ))) = 8 / (n : ℝ) ^ 2 := by
      field_simp; ring
    rw [e]
    have a1 : 8 / (n : ℝ) ^ 2 ≤ 8 := div_le_self (by norm_num) (one_le_pow₀ (by linarith))
    have a2 : 8 / (n : ℝ) ^ 2 ≤ 6 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    exact a2
  linarith

/-- The window sum is at most `s(I) a(I) (1/2 + m (4λ + 3λ²))` with `λ = 2 c₁ ln n` and
`m = ⌊log₂ n⌋ + 1`. -/
lemma window_sum_le (hk0 : 0 < k) (hk : k < numCliques q) {c₁ : ℝ}
    (hc : 0 ≤ c₁ * Real.log n / 2) :
    ∑ i ∈ range (Nat.log 2 n + 1),
        (bPar c₁ n i * (3 * sOf q k * aOf q k * rhoW n i +
          2 * bPar c₁ n i * sOf q k * aOf q k * rhoW n i ^ 2) +
        ((sOf q k : ℝ) ^ 2 * expect (fun σ => if InWindow q k σ i then (1 : ℝ) else 0) +
          2 * (sOf q k : ℝ) ^ 2 * bPar c₁ n i * rhoW n i +
          bPar c₁ n i ^ 2 * (sOf q k : ℝ) ^ 2 * rhoW n i ^ 2) / (2 * ((k : ℝ) - rOf q k))) ≤
      sOf q k * aOf q k * (1 / 2 + ((Nat.log 2 n : ℕ) + 1 : ℝ) *
        (4 * (2 * (c₁ * Real.log n)) + 3 * (2 * (c₁ * Real.log n)) ^ 2)) := by
  set lam := 2 * (c₁ * Real.log n) with hlam
  set s : ℝ := (sOf q k : ℝ) with hs
  set a := aOf q k with ha
  set D : ℝ := 2 * ((k : ℝ) - rOf q k) with hD
  set P : ℕ → ℝ := fun i => expect (fun σ => if InWindow q k σ i then (1 : ℝ) else 0) with hP
  have hr := rOf_lt hk0 hk
  have hkr : (0 : ℝ) < (k : ℝ) - rOf q k := by
    have : ((rOf q k : ℕ) : ℝ) < k := by exact_mod_cast hr
    linarith
  have hs1 : 1 ≤ s := one_le_sOf hk
  have ha1 : 1 < a := one_lt_aOf hk0 hk
  have hlam0 : 0 ≤ lam := by rw [hlam]; linarith
  have hsD : s ^ 2 / D ≤ s * a / 2 := by
    have := s_le_ka hk0 hk
    rw [div_le_iff₀ (by rw [hD]; linarith), hD]
    nlinarith
  have hP0 : ∀ i, 0 ≤ P i := fun i => expect_nonneg (fun σ => by split_ifs <;> norm_num)
  have hPsum : ∑ i ∈ range (Nat.log 2 n + 1), P i ≤ 1 := by
    simp only [hP]
    rw [← expect_sum]
    calc expect (fun σ => ∑ i ∈ range (Nat.log 2 n + 1),
          (if InWindow q k σ i then (1 : ℝ) else 0))
        ≤ expect (fun _ => (1 : ℝ)) := expect_mono (fun σ => sum_window_le_one σ _)
      _ = 1 := expect_const 1
  have hterm : ∀ i ∈ range (Nat.log 2 n + 1),
      bPar c₁ n i * (3 * s * a * rhoW n i + 2 * bPar c₁ n i * s * a * rhoW n i ^ 2) +
        (s ^ 2 * P i + 2 * s ^ 2 * bPar c₁ n i * rhoW n i +
          bPar c₁ n i ^ 2 * s ^ 2 * rhoW n i ^ 2) / D ≤
      s * a * (3 * lam + 2 * lam ^ 2) + s * a / 2 * (P i + 2 * lam + lam ^ 2) := by
    intro i _
    set t := bPar c₁ n i * rhoW n i with ht
    have ht0 : 0 ≤ t := mul_nonneg (bPar_nonneg hc) (rhoW_nonneg i)
    have htl : t ≤ lam := by rw [hlam]; exact bPar_mul_rhoW_le (by linarith) i
    have e1 : bPar c₁ n i * (3 * s * a * rhoW n i + 2 * bPar c₁ n i * s * a * rhoW n i ^ 2) =
        s * a * (3 * t + 2 * t ^ 2) := by rw [ht]; ring
    have e2 : (s ^ 2 * P i + 2 * s ^ 2 * bPar c₁ n i * rhoW n i +
          bPar c₁ n i ^ 2 * s ^ 2 * rhoW n i ^ 2) / D = s ^ 2 / D * (P i + 2 * t + t ^ 2) := by
      rw [ht]; ring
    rw [e1, e2]
    have hsa : 0 ≤ s * a := by nlinarith
    have hQ : 0 ≤ P i + 2 * t + t ^ 2 := by have := hP0 i; positivity
    have k1 : s * a * (3 * t + 2 * t ^ 2) ≤ s * a * (3 * lam + 2 * lam ^ 2) :=
      mul_le_mul_of_nonneg_left (by nlinarith) hsa
    have k2 : s ^ 2 / D * (P i + 2 * t + t ^ 2) ≤ s * a / 2 * (P i + 2 * t + t ^ 2) :=
      mul_le_mul_of_nonneg_right hsD hQ
    have k3 : s * a / 2 * (P i + 2 * t + t ^ 2) ≤ s * a / 2 * (P i + 2 * lam + lam ^ 2) :=
      mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
    linarith
  refine (sum_le_sum hterm).trans ?_
  rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul, ← mul_sum, sum_add_distrib,
    sum_add_distrib, sum_const, sum_const, card_range, nsmul_eq_mul, nsmul_eq_mul]
  push_cast
  have hsa : 0 ≤ s * a := by nlinarith
  have hm0 : (0 : ℝ) ≤ (Nat.log 2 n : ℝ) := Nat.cast_nonneg _
  have := mul_le_mul_of_nonneg_left hPsum (by positivity : 0 ≤ s * a / 2)
  nlinarith [mul_nonneg hsa (mul_nonneg hm0 hlam0), mul_nonneg hsa hlam0,
    mul_nonneg hsa (mul_nonneg hm0 (sq_nonneg lam)), mul_nonneg hsa (sq_nonneg lam)]

/-- The final numerical estimate in the proof of Theorem 5. -/
lemma theorem5_numeric {u X m O : ℝ} (hu0 : (0.69 : ℝ) ≤ u) (hX1 : 1 ≤ X)
    (hm : m ≤ 3 * u) (hXopt : X ≤ 4 * O) :
    8 + X * (1 / 2 + m * (4 * (2 * (256 * u)) + 3 * (2 * (256 * u)) ^ 2)) ≤
      10 ^ 7 * u ^ 3 * O := by
  have hu3 : (0.3 : ℝ) ≤ u ^ 3 := by
    have h1 : (0.69 : ℝ) ^ 3 ≤ u ^ 3 := pow_le_pow_left₀ (by norm_num) hu0 3
    norm_num at h1 ⊢; linarith
  have key : 8 + X * (1 / 2 + m * (4 * (2 * (256 * u)) + 3 * (2 * (256 * u)) ^ 2)) ≤
      2500000 * X * u ^ 3 := by
    have a1 : 8 + X / 2 ≤ 30 * X * u ^ 3 := by nlinarith
    have a2 : m * (2048 * u) ≤ 6144 * u ^ 2 := by nlinarith
    have a3 : 6144 * u ^ 2 ≤ 9000 * u ^ 3 := by nlinarith
    have a4 : m * (786432 * u ^ 2) ≤ 2359296 * u ^ 3 := by nlinarith
    have e : X * (1 / 2 + m * (4 * (2 * (256 * u)) + 3 * (2 * (256 * u)) ^ 2)) =
        X / 2 + X * (m * (2048 * u)) + X * (m * (786432 * u ^ 2)) := by ring
    rw [e]
    have b2 : X * (m * (2048 * u)) ≤ X * (9000 * u ^ 3) :=
      mul_le_mul_of_nonneg_left (a2.trans a3) (by linarith)
    have b4 : X * (m * (786432 * u ^ 2)) ≤ X * (2359296 * u ^ 3) :=
      mul_le_mul_of_nonneg_left a4 (by linarith)
    have hXu : 0 ≤ X * u ^ 3 := by positivity
    linarith
  refine key.trans ?_
  have hu30 : 0 ≤ u ^ 3 := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hXopt hu30]

/-- **Theorem 5.**  UNIFORM PIVOT (with threshold `L = 128 ln n`) is `O(log³ n)`-competitive for
correlation `k`-clustering of disjoint cliques under random-order arrivals: for `n ≥ 2` its
expected cost is at most `10⁷ · ln³ n · OPT_k`.  The Chernoff bound (Fact 2.1) and negative
association of permutation distributions (Lemma 5.3) are assumed as hypotheses. -/
theorem theorem_5 (hCh : ChernoffBound) (hPNA : PermNegAssoc) (hn : 2 ≤ n) (q : Fin n → ι)
    {k : ℕ} (hk : 0 < k) :
    uniformPivotExpCost (cliqueGraph q) k (128 * Real.log n) ≤
      10 ^ 7 * Real.log n ^ 3 * optK (cliqueGraph q) k := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hl2 := Real.log_two_gt_d9
  have hu : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hnR
  set u := Real.log n with hu_def
  have hu0 : (0.69 : ℝ) ≤ u := by linarith
  have hopt0 : (0 : ℝ) ≤ optK (cliqueGraph q) k := Nat.cast_nonneg _
  refine (uniformPivotExpCost_le _).trans ?_
  by_cases hkl : numCliques q ≤ k
  · rw [show (fun σ => upBound q k (128 * u) σ) = fun _ => (0 : ℝ) from
      funext (fun σ => upBound_eq_zero hkl _ σ), expect_const]
    positivity
  push_neg at hkl
  have hc : 0 ≤ (256 : ℝ) * u / 2 := by positivity
  have hL : 128 * u ≤ (256 : ℝ) * u / 2 := by linarith
  have hE := expect_upBound_le (q := q) hk hkl hL hc
  have hbad := bad_events_le (q := q) hCh hPNA hn hk hkl
  have hwin := window_sum_le (q := q) hk hkl hc
  have h34 := (lemma_3_4 q hk).1
  have hm := natLog_le_three_log hn
  rw [← hu_def] at hm hbad
  set X : ℝ := (sOf q k : ℝ) * aOf q k with hX
  have hX1 : 1 ≤ X := by
    have := one_le_sOf hkl; have := one_lt_aOf hk hkl; rw [hX]; nlinarith
  set m : ℝ := ((Nat.log 2 n : ℕ) : ℝ) + 1 with hm_def
  have htot : expect (fun σ => upBound q k (128 * u) σ) ≤
      8 + X * (1 / 2 + m * (4 * (2 * (256 * u)) + 3 * (2 * (256 * u)) ^ 2)) := by
    linarith
  refine htot.trans ?_
  have hXopt : X ≤ 4 * optK (cliqueGraph q) k := by rw [hX]; linarith
  exact theorem5_numeric hu0 hX1 hm hXopt

end CCK
