module

public import RequestProject.LB3W2
public import RequestProject.Theorem2

/-!
# Theorem 3: an `Ω(log² k)` lower bound for online algorithms which never split cliques
-/

@[expose] public section

open Finset
open scoped Classical

namespace CCK

variable {c m : ℕ}

/-- On the event of Theorem 3, `W` implies `E''` (at least four isolated positions at `tstar`,
including both singletons). -/
lemma lbEvent''_of_W (hm : 1 ≤ m) {T : ℕ} {σ : Equiv.Perm (Fin (c * m + 2))}
    (hE : lbEvent3 c m T σ) (hW : lbW c m σ) : lbEvent'' c m σ := by
  obtain ⟨p₀, hp₀J, hmin, hunhit⟩ := hW
  have hT := le_lbT1 hm hE
  have hp₀J' := hp₀J
  simp only [lbJ, mem_filter, mem_univ, true_and] at hp₀J'
  have ht1p₀ : lbT1 c m σ < p₀ := hp₀J'.1
  obtain ⟨x₀, hx₀, hux₀, huniq⟩ := exists_unique_unhit hm σ
  have hcx : lbComp c m (σ p₀) = x₀ := huniq _ (lbComp_lt hm _) hunhit
  -- no other vertex of the last component arrives before `p₀`
  have hbefore : ∀ q : Fin (c * m + 2), q < p₀ → lbComp c m (σ q) ≠ lbComp c m (σ p₀) := by
    intro q hq hqc
    by_cases hqt : (q : ℕ) ≤ lbT1 c m σ
    · exact hunhit q hqt hqc
    · have hqJ : q ∈ lbJ c m σ := by
        simp only [lbJ, mem_filter, mem_univ, true_and]
        exact ⟨not_le.1 hqt, Or.inr (hqc ▸ hunhit)⟩
      exact absurd (hmin q hqJ) (not_le.2 hq)
  -- `tstar = p₀`
  set ts := tstar (lbGraph c m) (c + 2) σ with hts
  have hts_eq : ts = p₀ := by
    apply le_antisymm
    · apply Nat.sInf_le
      show c + 2 ≤ (leaders (view (lbGraph c m) σ p₀) p₀).card
      have := card_le_card_leaders_of_hit σ p₀ (range (c + 2)) (by
        intro x hx
        by_cases hux : Unhit c m σ x
        · refine ⟨p₀, le_rfl, ?_⟩
          rw [hcx, huniq x (mem_range.1 hx) hux]
        · simp only [Unhit, not_forall, not_not] at hux
          obtain ⟨q, hq, hqx⟩ := hux
          exact ⟨q, by omega, hqx⟩)
      rwa [card_range] at this
    · by_contra hlt
      push_neg at hlt
      have hspec := tstar_spec (lbGraph c m) (c + 2) σ (exists_leaders_lb hm σ)
      rw [← hts] at hspec
      have := card_leaders_lt_of_missing hm σ (t := ts) (j := lbComp c m (σ p₀))
        (lbComp_lt hm _) (by
          intro q hq
          exact hbefore q (Fin.lt_def.2 (by omega)))
      omega
  have hisoiff := fun p => @mem_isoSet_iff c m σ p
  rw [← hts] at hisoiff
  -- the four isolated positions
  have hp₀I : p₀ ∈ isoSet (lbGraph c m) (c + 2) σ := by
    rw [hisoiff]
    refine ⟨by omega, fun q hq hqp => ?_⟩
    have : q < p₀ := Fin.lt_def.2 (by
      rcases lt_or_gt_of_ne (fun h : (q : ℕ) = p₀ => hqp (Fin.ext h)) with h | h
      · exact h
      · omega)
    exact hbefore q this
  set t₁ := lbT1pos c m σ
  have ht₁v : (t₁ : ℕ) = lbT1 c m σ := lbT1pos_val hm σ
  have hfirst : IsFirst c m σ t₁ := by
    have := isFirst_tstar hm (L := c + 1) (by omega) σ
    have e : t₁ = ⟨tstar (lbGraph c m) (c + 1) σ,
        by have := tstar_le_L hm (L := c + 1) (by omega) σ; omega⟩ := Fin.ext ht₁v
    rw [e]; exact this
  have ht₁I : t₁ ∈ isoSet (lbGraph c m) (c + 2) σ := by
    rw [hisoiff]
    refine ⟨by omega, fun q hq hqt => ?_⟩
    rcases lt_or_gt_of_ne hqt with h | h
    · exact hfirst q h
    · intro hqc
      have hqJ : q ∈ lbJ c m σ := by
        simp only [lbJ, mem_filter, mem_univ, true_and]
        exact ⟨by rw [← ht₁v]; exact h, Or.inl hqc⟩
      have hq0 : q = p₀ := Fin.ext (le_antisymm (by omega) (hmin q hqJ))
      rw [hq0] at hqc
      exact hunhit t₁ (by omega) hqc.symm
  have h1 : (σ.symm (lbS1 c m) : ℕ) < T := mem_firstSet_iff.1 hE.1
  have h2 : (σ.symm (lbS2 c m) : ℕ) < T := mem_firstSet_iff.1 hE.2.1
  have hs1 := singleton_mem_isoSet hm (Or.inl rfl) (σ := σ) (by omega)
  have hs2 := singleton_mem_isoSet hm (Or.inr rfl) (σ := σ) (by omega)
  refine ⟨hs1, hs2, ?_⟩
  have hsub : ({p₀, t₁, σ.symm (lbS1 c m), σ.symm (lbS2 c m)} : Finset _) ⊆
      isoSet (lbGraph c m) (c + 2) σ := by
    intro y hy
    simp only [mem_insert, mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl <;> assumption
  have hne12 : σ.symm (lbS1 c m) ≠ σ.symm (lbS2 c m) :=
    fun h => lbS1_ne_lbS2 (σ.symm.injective h)
  have := card_le_card hsub
  rw [card_insert_of_notMem, card_insert_of_notMem, card_pair hne12] at this
  · exact this
  · simp only [mem_insert, mem_singleton, not_or]
    refine ⟨fun h => ?_, fun h => ?_⟩ <;>
    · have := congrArg Fin.val h; omega
  · simp only [mem_insert, mem_singleton, not_or]
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
    · have := congrArg Fin.val h; omega

/-- The "probability at least `1/2`" step of the proof of Theorem 3: `P(E'') ≥ P(E₃)/2`, where
`E₃` is the event that both singletons arrive by `T` and at least two cliques have no vertex
arrived by `T`. -/
lemma prob_lbEvent''_ge (hm : 1 ≤ m) (T : ℕ) :
    prob (lbEvent3 c m T) / 2 ≤ prob (lbEvent'' c m) := by
  set S := (univ : Finset (Equiv.Perm (Fin (c * m + 2)))).filter (lbEvent3 c m T)
  have hex := exchange_count S (lbJ c m) (lbW c m) (1 / 2)
    (by
      intro σ hσ ρ hρ
      have hE := (mem_filter.1 hσ).2
      refine ⟨?_, lbJ_mul hm σ ρ hρ⟩
      simp only [S, mem_filter, mem_univ, true_and]
      have hfs := firstSet_mul σ ρ hρ (le_lbT1 hm hE)
      unfold lbEvent3
      rw [hfs]
      exact hE)
    (fun σ hσ => half_W hm σ (mem_filter.1 hσ).2)
  have hsub : S.filter (lbW c m) ⊆ univ.filter (lbEvent'' c m) := by
    intro σ hσ
    simp only [S, mem_filter, mem_univ, true_and] at hσ ⊢
    exact lbEvent''_of_W hm hσ.1 hσ.2
  have hcard := card_le_card hsub
  have hcardpos := card_perm_pos (n := c * m + 2)
  unfold prob
  rw [div_div, div_le_div_iff₀ (by positivity) hcardpos]
  have : ((S.filter (lbW c m)).card : ℝ) ≤ ((univ.filter (lbEvent'' c m)).card : ℝ) := by
    exact_mod_cast hcard
  have hS : (S.card : ℝ) = ((univ.filter (lbEvent3 c m T)).card : ℝ) := rfl
  nlinarith

/-- For `γ = 2/7` and all sufficiently large `k`, the event of Theorem 3 (both singletons and
at least two cliques missing at time `T`) has probability at least `1/588`. -/
lemma prob_lbEvent3_ge (hCh : ChernoffBound) (hPNA : PermNegAssoc) (hClos : NegAssocClosure) :
    ∃ K : ℕ, ∀ c : ℕ, K ≤ c + 1 →
      (1 / 588 : ℝ) ≤ prob (lbEvent3 c (lbM (c + 1)) (lbT (2 / 7) (c + 1))) := by
  obtain ⟨K1, hK1⟩ := lemma_5_1 (2 / 7) (by norm_num) (by norm_num)
  obtain ⟨K2, hK2⟩ := lemma_5_6 hCh hPNA hClos (2 / 7) (by norm_num) (by norm_num)
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
      ∃ j₁ < c, ∃ j₂ < c, j₁ ≠ j₂ ∧ Disjoint (firstSet σ T) (lbClique c m j₁) ∧
        Disjoint (firstSet σ T) (lbClique c m j₂))
  have hcompl := prob_compl (fun σ : Equiv.Perm (Fin (c * m + 2)) =>
      ∃ j₁ < c, ∃ j₂ < c, j₁ ≠ j₂ ∧ Disjoint (firstSet σ T) (lbClique c m j₁) ∧
        Disjoint (firstSet σ T) (lbClique c m j₂))
  have hmono : prob (fun σ : Equiv.Perm (Fin (c * m + 2)) =>
      (lbS1 c m ∈ firstSet σ T ∧ lbS2 c m ∈ firstSet σ T) ∧
        ∃ j₁ < c, ∃ j₂ < c, j₁ ≠ j₂ ∧ Disjoint (firstSet σ T) (lbClique c m j₁) ∧
          Disjoint (firstSet σ T) (lbClique c m j₂)) ≤ prob (lbEvent3 c m T) := by
    apply prob_mono
    rintro σ ⟨⟨hs1, hs2⟩, h⟩
    exact ⟨hs1, hs2, h⟩
  have h1' : (2 / 7 : ℝ) ^ 2 / 24 = 1 / 294 := by norm_num
  rw [h1'] at h1
  change (1 / 294 : ℝ) ≤ prob (fun σ : Equiv.Perm (Fin (c * m + 2)) =>
      lbS1 c m ∈ firstSet σ T ∧ lbS2 c m ∈ firstSet σ T) at h1
  change 1 - Real.exp (-Real.sqrt ((c + 1 : ℕ) : ℝ) / 16) ≤
      prob (fun σ : Equiv.Perm (Fin (c * m + 2)) =>
        ∃ j₁ < c, ∃ j₂ < c, j₁ ≠ j₂ ∧ Disjoint (firstSet σ T) (lbClique c m j₁) ∧
          Disjoint (firstSet σ T) (lbClique c m j₂)) at h2
  linarith

/-- **Theorem 3.**  For all sufficiently large `k` there is an instance of disjoint cliques on
`n ≤ 3 k ln k` vertices with optimal `k`-clustering cost `1`, on which every (possibly randomized)
online algorithm for k-CC which never splits the cliques has expected cost at least
`C · ln² k · OPT_k` and at least `C · ln² n · OPT_k`, for an absolute constant `C > 0`.
Assumes Fact 2.1 (Chernoff), Lemma 5.3 and Lemma 5.4 (negative association), used through
Lemma 5.6. -/
theorem theorem_3 (hCh : ChernoffBound) (hPNA : PermNegAssoc) (hClos : NegAssocClosure) :
    ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ, ∀ k ≥ K, ∃ (n : ℕ) (q : Fin n → ℕ),
      (n : ℝ) ≤ 3 * k * Real.log k ∧ optK (cliqueGraph q) k = 1 ∧
      ∀ (ι : Type) [Fintype ι] (w : ι → ℝ) (A : ι → OnlineAlg n k),
        (∀ i, 0 ≤ w i) → ∑ i, w i = 1 →
        (∀ i σ, CliquePreserving q ((A i).run (cliqueGraph q) σ)) →
        C * Real.log k ^ 2 * optK (cliqueGraph q) k ≤ randExpCost w A (cliqueGraph q) ∧
        C * Real.log n ^ 2 * optK (cliqueGraph q) k ≤ randExpCost w A (cliqueGraph q) := by
  obtain ⟨K, hK⟩ := prob_lbEvent3_ge hCh hPNA hClos
  refine ⟨1 / 15876, by norm_num, max K 8, fun k hk => ?_⟩
  have hk8 : 8 ≤ k := le_of_max_le_right hk
  obtain ⟨c, rfl⟩ : ∃ c, k = c + 1 := ⟨k - 1, by omega⟩
  have hk3 : 3 ≤ c + 1 := by omega
  set m := lbM (c + 1)
  have hm : 1 ≤ m := one_le_lbM hk3
  set L := Real.log ((c + 1 : ℕ) : ℝ)
  have hkR : (8 : ℝ) ≤ ((c + 1 : ℕ) : ℝ) := by exact_mod_cast hk8
  have hL1 : 1 ≤ L := one_le_log_of_three_le hk3
  obtain ⟨hm1, hm2⟩ := lbM_bounds (k := c + 1) (by omega)
  set K'' : ℝ := ((c + 1 : ℕ) : ℝ)
  have hn : ((c * m + 2 : ℕ) : ℝ) = (K'' - 1) * m + 2 := by simp only [K'']; push_cast; ring
  refine ⟨c * m + 2, lbComp c m, ?_, optK_lbGraph hm, ?_⟩
  · have hL2 : 2 ≤ L := by
      rw [Real.le_log_iff_exp_le (by positivity)]
      have := Real.exp_one_lt_d9
      have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      nlinarith [Real.exp_pos 1]
    rw [hn]
    have h1 : (K'' - 1) * m ≤ (K'' - 1) * (2 * L + 1) :=
      mul_le_mul_of_nonneg_left hm2.le (by linarith)
    have h2 : K'' * 2 ≤ K'' * L := mul_le_mul_of_nonneg_left hL2 (by linarith)
    nlinarith
  · intro ι _ w A hw hw1 hpres
    rw [show optK (cliqueGraph (lbComp c m)) (c + 1) = 1 from optK_lbGraph hm, Nat.cast_one,
      mul_one, mul_one]
    have hdet : ∀ i, L ^ 2 / 1764 ≤ (A i).expCost (lbGraph c m) := by
      intro i
      have h1 := lb3_expCost hm (A i) (hpres i)
      have h2 := hK c (le_trans (le_max_left _ _) hk)
      have h3 := prob_lbEvent''_ge (c := c) hm (lbT (2 / 7) (c + 1))
      have hmm : (2 * L) * (2 * L) ≤ (m : ℝ) * m := mul_le_mul hm1 hm1 (by linarith) (by linarith)
      have hP : (1 / 1176 : ℝ) ≤ prob (lbEvent'' c m) := by linarith
      have : (2 * L) * (2 * L) * (1 / 1176) ≤ ((m : ℝ) * m) * prob (lbEvent'' c m) :=
        mul_le_mul hmm hP (by norm_num) (by positivity)
      nlinarith
    have hrand := le_randExpCost w A (lbGraph c m) hw hw1 (L ^ 2 / 1764) hdet
    unfold lbGraph at hrand
    have hL0 : 0 ≤ L := by linarith
    refine ⟨by nlinarith, ?_⟩
    have hn3 : ((c * m + 2 : ℕ) : ℝ) ≤ K'' ^ 3 := by
      have hLk : L ≤ K'' - 1 := Real.log_le_sub_one_of_pos (by linarith)
      rw [hn]
      have h1 : (K'' - 1) * m ≤ (K'' - 1) * (2 * L + 1) :=
        mul_le_mul_of_nonneg_left hm2.le (by linarith)
      have h2 : (K'' - 1) * (2 * L + 1) ≤ (K'' - 1) * (2 * K'') :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      nlinarith
    have hlogn : Real.log ((c * m + 2 : ℕ) : ℝ) ≤ 3 * L := by
      calc Real.log ((c * m + 2 : ℕ) : ℝ) ≤ Real.log (K'' ^ 3) :=
            Real.log_le_log (by positivity) hn3
        _ = 3 * L := by rw [Real.log_pow, Nat.cast_ofNat]
    have hlogn0 : 0 ≤ Real.log ((c * m + 2 : ℕ) : ℝ) :=
      Real.log_nonneg (by norm_cast; omega)
    have : Real.log ((c * m + 2 : ℕ) : ℝ) ^ 2 ≤ 9 * L ^ 2 := by nlinarith
    nlinarith

end CCK
