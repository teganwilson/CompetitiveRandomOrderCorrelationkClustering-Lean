module

public import RequestProject.PivotPrefix

/-!
# Lemma 7.7

The final pivot cluster of a pivot arriving late is unlikely to be large.
-/

@[expose] public section

open Finset
open scoped Classical

namespace CCK

variable {n : ℕ} (G : SimpleGraph (Fin n))

/-- Auxiliary result for Lemma 7.7 (Section 7.3.2). -/
lemma card_Ipos_single_le {s : ℕ} {q : Fin n} (hsq : s ≤ (q : ℕ)) :
    (Ipos s {q}).card ≤ n - s - 1 := by
  have h1 : Ipos s {q} ⊆ (Ipos s (∅ : Finset (Fin n))).erase q := by
    intro p hp
    simp only [Ipos, mem_filter, mem_univ, true_and, mem_singleton, mem_erase,
      notMem_empty, not_false_eq_true, and_true] at hp ⊢
    exact ⟨hp.2, hp.1⟩
  have h2 : q ∈ Ipos s (∅ : Finset (Fin n)) := by simp [Ipos, hsq]
  have := card_le_card h1
  rw [card_erase_of_mem h2] at this
  have := card_Ipos_le s (∅ : Finset (Fin n))
  omega

/-- The final pivot cluster of a pivot `v`, apart from `v`, consists of neighbours of `v` which
are uncovered at the arrival time of `v`: `p_n(v) ≤ 1 + |R_{t_v - 1}(v)|` (proof of Lemma 7.7). -/
lemma pivotCluster_erase_subset (σ : Equiv.Perm (Fin n)) {v : Fin n} (_hv : IsPivot G σ v) :
    (univ.filter (fun u => pivotOf G σ u = v)).erase v ⊆
      uncovered G σ (arrTime σ v) ∩ G.neighborFinset v := by
  intro u hu
  simp only [mem_erase, mem_filter, mem_univ, true_and] at hu
  obtain ⟨huv, hpu⟩ := hu
  have hnp : ¬ IsPivot G σ u := fun h => huv (by rw [← pivotOf_of_isPivot G σ h]; exact hpu)
  obtain ⟨_, hadj, hmin⟩ := pivotOf_spec_of_not_isPivot G σ hnp
  rw [hpu] at hadj hmin
  refine mem_inter.2 ⟨?_, (G.mem_neighborFinset _ _).2 hadj⟩
  simp only [uncovered, mem_filter, mem_univ, true_and]
  constructor
  · by_contra hlt
    push_neg at hlt
    obtain ⟨p, hp, hplt, hpadj⟩ := exists_pivot_adj_of_not_isPivot G σ hnp
    have := hmin p hp hpadj
    omega
  · intro p hp hpadj
    have hp' := (mem_pivotsUpTo_iff G σ _ p).1 hp
    have := hmin p hp'.1 hpadj
    omega

/-- Auxiliary result for Lemma 7.7 (Section 7.3.2). -/
lemma pclSize_le (σ : Equiv.Perm (Fin n)) {v : Fin n} (hv : IsPivot G σ v) :
    pclSize G σ v ≤ 1 + (uncovered G σ (arrTime σ v) ∩ G.neighborFinset v).card := by
  have h1 := card_le_card (pivotCluster_erase_subset G σ hv)
  have h2 : v ∈ univ.filter (fun u => pivotOf G σ u = v) := by
    simp [pivotOf_of_isPivot G σ hv]
  rw [card_erase_of_mem h2] at h1
  unfold pclSize
  omega

/-- **Lemma 7.7.**  For any `m ≥ 0` and any vertex `v`, conditioned on `v` being the `j`-th
arrival (`t_v = j`, times counted from `1`), the probability that `v` is a pivot whose final
pivot cluster has at least `m + 1` vertices is at most `exp(-m (j-1)/(n-1))`.  The conditional
probability is written as `Pr[A ∧ t_v = j] ≤ bound · Pr[t_v = j]`.  (The hypothesis `m ≥ 0` turns
out to be unnecessary.) -/
theorem lemma_7_7 (v : Fin n) (m : ℝ) (j : ℕ) :
    prob (fun σ => arrTime σ v + 1 = j ∧ IsPivot G σ v ∧ m + 1 ≤ (pclSize G σ v : ℝ)) ≤
      Real.exp (-(m * (j - 1) / (n - 1))) * prob (fun σ => arrTime σ v + 1 = j) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · have : prob (fun σ : Equiv.Perm (Fin n) => arrTime σ v + 1 = 0 ∧ IsPivot G σ v ∧
        m + 1 ≤ (pclSize G σ v : ℝ)) = 0 := by
      unfold prob; simp
    rw [this]; exact mul_nonneg (Real.exp_pos _).le (prob_nonneg _)
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  by_cases hj' : j' < n
  swap
  · have : prob (fun σ : Equiv.Perm (Fin n) => arrTime σ v + 1 = j' + 1 ∧ IsPivot G σ v ∧
        m + 1 ≤ (pclSize G σ v : ℝ)) = 0 := by
      unfold prob
      simp only [div_eq_zero_iff, Nat.cast_eq_zero, card_eq_zero, filter_eq_empty_iff]
      left; intro σ _ h
      have := Fin.isLt (σ.symm v); unfold arrTime at h; omega
    rw [this]; exact mul_nonneg (Real.exp_pos _).le (prob_nonneg _)
  set q : Fin n := ⟨j', hj'⟩ with hq
  set R : ℕ → Equiv.Perm (Fin n) → Finset (Fin n) :=
    fun s σ => uncovered G σ s ∩ G.neighborFinset v with hR
  set B : ℕ → Equiv.Perm (Fin n) → Prop := fun s σ => arrTime σ v = j' ∧
    (∀ p ∈ pivotsUpTo G σ s, ¬ G.Adj p v) ∧ m ≤ ((R s σ).card : ℝ) with hB
  set x : ℝ := m / (n - 1) with hx
  have hn1 : (0 : ℝ) ≤ (n : ℝ) - 1 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    linarith
  have chain : ∀ s ≤ j', prob (B s) ≤ Real.exp (-(x * s)) * prob (B 0) := by
    intro s
    induction s with
    | zero => intro _; simp
    | succ s ih =>
      intro hs
      have hsn : s < n := by omega
      have h1 : prob (B (s + 1)) ≤ prob (fun σ => B s σ ∧ σ ⟨s, hsn⟩ ∉ R s σ) := by
        apply prob_mono
        rintro σ ⟨ha, hp, hm⟩
        refine ⟨⟨ha, fun p hp' => hp p (pivotsUpTo_mono G σ (Nat.le_succ s) hp'), ?_⟩, ?_⟩
        · refine hm.trans ?_
          exact_mod_cast card_le_card (inter_subset_inter_right (uncovered_succ_subset G σ s))
        · intro hmem
          exact hp _ (mem_pivotsUpTo_of_uncovered G σ hsn (mem_inter.1 hmem).1)
            ((G.mem_neighborFinset _ _).1 (mem_inter.1 hmem).2).symm
      have hsq : (⟨s, hsn⟩ : Fin n) ∉ ({q} : Finset (Fin n)) := by
        simp only [mem_singleton, hq, Fin.mk.injEq]; omega
      have h2 := prob_step hsn {q} hsq (B s)
        (by
          rintro σ ρ hρ ⟨ha, hp, hm⟩
          have hρ' := fixOutside_Ipos_lt hρ
          refine ⟨?_, ?_, ?_⟩
          · unfold arrTime at ha ⊢
            rw [mul_symm_apply]
            have hσv : σ.symm v = q := Fin.ext ha
            rw [hσv]
            have := fixOutside_Ipos_mem hρ (mem_singleton_self q)
            rw [(Equiv.symm_apply_eq ρ).2 this.symm]
          · rw [pivotsUpTo_mul hρ']; exact hp
          · simp only [hR, uncovered_mul hρ']; exact hm)
        (R s)
        (by
          intro σ ρ hρ _
          simp only [hR, uncovered_mul (fixOutside_Ipos_lt hρ)])
        (by
          rintro σ ⟨ha, -, -⟩ u hu
          have h1 := arrTime_ge_of_mem_uncovered G (mem_inter.1 hu).1
          have hadj := (G.mem_neighborFinset _ _).1 (mem_inter.1 hu).2
          have hne : σ.symm u ≠ q := by
            intro h
            have : u = v := by
              have hσv : σ.symm v = q := Fin.ext ha
              exact σ.symm.injective (h.trans hσv.symm)
            exact G.loopless.irrefl _ (this ▸ hadj)
          simp only [Ipos, mem_filter, mem_univ, true_and, mem_singleton]
          exact ⟨h1, hne⟩)
        x
        (by
          rintro σ ⟨-, -, hm⟩
          have hI : ((Ipos s {q}).card : ℝ) ≤ (n : ℝ) - 1 := by
            have := card_Ipos_single_le (n := n) (s := s) (q := q) (by simp [hq]; omega)
            have h' : (Ipos s {q}).card ≤ n - 1 := by omega
            have : (((Ipos s {q}).card : ℕ) : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast h'
            rwa [Nat.cast_sub (by omega), Nat.cast_one] at this
          rcases le_or_gt m 0 with hm0 | hm0
          · have : x * ((Ipos s {q}).card : ℝ) ≤ 0 :=
              mul_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonpos_of_nonneg hm0 hn1)
                (by positivity)
            linarith [(Nat.cast_nonneg _ : (0 : ℝ) ≤ ((R s σ).card : ℝ))]
          · rcases eq_or_lt_of_le hn1 with h0 | h0
            · rw [hx, ← h0, div_zero, zero_mul]; positivity
            · calc x * ((Ipos s {q}).card : ℝ) ≤ x * ((n : ℝ) - 1) := by
                    gcongr
                _ = m := by rw [hx]; field_simp
                _ ≤ _ := hm)
      have h3 := ih (by omega)
      calc prob (B (s + 1)) ≤ _ := h1
        _ ≤ Real.exp (-x) * prob (B s) := by convert h2
        _ ≤ Real.exp (-x) * (Real.exp (-(x * s)) * prob (B 0)) := by gcongr
        _ = Real.exp (-(x * ↑(s + 1))) * prob (B 0) := by
            rw [← mul_assoc, ← Real.exp_add]; congr 2; push_cast; ring
  have hfin : prob (fun σ => arrTime σ v + 1 = j' + 1 ∧ IsPivot G σ v ∧
      m + 1 ≤ (pclSize G σ v : ℝ)) ≤ prob (B j') := by
    apply prob_mono
    rintro σ ⟨ha, hp, hm⟩
    have ha' : arrTime σ v = j' := by omega
    refine ⟨ha', ?_, ?_⟩
    · rw [← ha']; exact (isPivot_iff G σ v).1 hp
    · have := pclSize_le G σ hp
      rw [ha'] at this
      have : (pclSize G σ v : ℝ) ≤ 1 + ((R j' σ).card : ℝ) := by exact_mod_cast this
      linarith
  have hB0 : prob (B 0) ≤ prob (fun σ => arrTime σ v + 1 = j' + 1) :=
    prob_mono (fun σ h => by have := h.1; omega)
  calc _ ≤ prob (B j') := hfin
    _ ≤ Real.exp (-(x * j')) * prob (B 0) := chain j' le_rfl
    _ ≤ Real.exp (-(x * j')) * prob (fun σ => arrTime σ v + 1 = j' + 1) := by gcongr
    _ = _ := by
        congr 2
        rw [hx]; push_cast; ring
end CCK
