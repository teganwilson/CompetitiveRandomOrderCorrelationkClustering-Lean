module

public import RequestProject.Pivot
public import RequestProject.Chain

/-!
# Pivots along the arrival process: Lemmas 7.7 and 7.12

We show that the state of PIVOT after `t` arrivals only depends on the first `t` arrivals, define
the set of *uncovered* vertices at time `t` (Definition 7.2 / Section 6: vertices that have not
arrived and are not adjacent to any pivot arrived so far), and prove Lemma 7.7 and Lemma 7.12 by
the sequential arrival argument of `RequestProject/Chain.lean`.
-/

@[expose] public section

open Finset
open scoped Classical

namespace CCK

variable {n : ℕ} (G : SimpleGraph (Fin n))

/-- The vertices *uncovered* at time `t` (Section 6 and Definition 7.2): vertices which have not
arrived among the first `t` arrivals and are not adjacent to any pivot among them. -/
noncomputable def uncovered (σ : Equiv.Perm (Fin n)) (t : ℕ) : Finset (Fin n) :=
  univ.filter (fun v => t ≤ arrTime σ v ∧ ∀ p ∈ pivotsUpTo G σ t, ¬ G.Adj p v)

/-- The final size `p_n(v)` of the pivot cluster of `v` (Section 7.3.2). -/
noncomputable def pclSize (σ : Equiv.Perm (Fin n)) (v : Fin n) : ℕ :=
  (univ.filter (fun u => pivotOf G σ u = v)).card

section invariance

variable {G}

/-- Auxiliary result for Lemmas 7.7 and 7.12 (Section 7.3). -/
lemma mul_apply_of_lt {σ ρ : Equiv.Perm (Fin n)} {t : ℕ} (hρ : ∀ p : Fin n, (p : ℕ) < t → ρ p = p)
    (p : Fin n) (hp : (p : ℕ) < t) : (σ * ρ) p = σ p := by
  rw [Equiv.Perm.mul_apply, hρ p hp]

/-- Auxiliary result for Lemmas 7.7 and 7.12 (Section 7.3). -/
lemma pivotsUpTo_mul {σ ρ : Equiv.Perm (Fin n)} {t : ℕ}
    (hρ : ∀ p : Fin n, (p : ℕ) < t → ρ p = p) : pivotsUpTo G (σ * ρ) t = pivotsUpTo G σ t := by
  have : ∀ s ≤ t, pivotsUpTo G (σ * ρ) s = pivotsUpTo G σ s := by
    intro s hs
    induction s with
    | zero => rfl
    | succ s ih =>
      have ih := ih (by omega)
      by_cases hsn : s < n
      · ext v
        rw [mem_pivotsUpTo_succ G _ hsn, mem_pivotsUpTo_succ G _ hsn, ih,
          mul_apply_of_lt hρ ⟨s, hsn⟩ (by simp; omega)]
      · rw [pivotsUpTo_succ_of_ge G _ (by omega), pivotsUpTo_succ_of_ge G _ (by omega), ih]
  exact this t le_rfl

/-- Auxiliary result for Lemmas 7.7 and 7.12 (Section 7.3). -/
lemma symm_lt_iff {ρ : Equiv.Perm (Fin n)} {t : ℕ} (hρ : ∀ p : Fin n, (p : ℕ) < t → ρ p = p)
    (q : Fin n) : (ρ.symm q : ℕ) < t ↔ (q : ℕ) < t := by
  constructor
  · intro h
    have e : ρ.symm q = q := by
      have := hρ _ h; rw [Equiv.apply_symm_apply] at this; exact this.symm
    rwa [e] at h
  · intro h
    have e : ρ.symm q = q := (Equiv.symm_apply_eq ρ).2 (hρ q h).symm
    rwa [e]

/-- Auxiliary result for Lemmas 7.7 and 7.12 (Section 7.3). -/
lemma mul_symm_apply (σ ρ : Equiv.Perm (Fin n)) (v : Fin n) :
    (σ * ρ).symm v = ρ.symm (σ.symm v) := rfl

/-- Auxiliary result for Lemmas 7.7 and 7.12 (Section 7.3). -/
lemma arrTime_mul_lt_iff {σ ρ : Equiv.Perm (Fin n)} {t : ℕ}
    (hρ : ∀ p : Fin n, (p : ℕ) < t → ρ p = p) (v : Fin n) :
    arrTime (σ * ρ) v < t ↔ arrTime σ v < t := by
  unfold arrTime
  rw [mul_symm_apply]
  exact symm_lt_iff hρ _

/-- Auxiliary result for Lemmas 7.7 and 7.12 (Section 7.3). -/
lemma fixOutside_Ipos_lt {t : ℕ} {E : Finset (Fin n)} {ρ : Equiv.Perm (Fin n)}
    (hρ : ρ ∈ fixOutside (Ipos t E)) : ∀ p : Fin n, (p : ℕ) < t → ρ p = p := by
  intro p hp
  apply fixOutside_mem_iff.1 hρ
  simp [Ipos]; omega

/-- Auxiliary result for Lemmas 7.7 and 7.12 (Section 7.3). -/
lemma fixOutside_Ipos_mem {t : ℕ} {E : Finset (Fin n)} {ρ : Equiv.Perm (Fin n)}
    (hρ : ρ ∈ fixOutside (Ipos t E)) {p : Fin n} (hp : p ∈ E) : ρ p = p := by
  apply fixOutside_mem_iff.1 hρ
  simp [Ipos, hp]

/-- Auxiliary result for Lemmas 7.7 and 7.12 (Section 7.3). -/
lemma uncovered_mul {σ ρ : Equiv.Perm (Fin n)} {t : ℕ}
    (hρ : ∀ p : Fin n, (p : ℕ) < t → ρ p = p) : uncovered G (σ * ρ) t = uncovered G σ t := by
  ext v
  simp only [uncovered, mem_filter, mem_univ, true_and, pivotsUpTo_mul hρ]
  have := arrTime_mul_lt_iff (σ := σ) hρ v
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by omega, h2⟩

end invariance

/-- Auxiliary result for Lemmas 7.7 and 7.12 (Section 7.3). -/
lemma uncovered_succ_subset (σ : Equiv.Perm (Fin n)) (t : ℕ) :
    uncovered G σ (t + 1) ⊆ uncovered G σ t := by
  intro v hv
  simp only [uncovered, mem_filter, mem_univ, true_and] at hv ⊢
  exact ⟨by omega, fun p hp => hv.2 p (pivotsUpTo_mono G σ (Nat.le_succ t) hp)⟩

/-- The vertex arriving at time `t`, if uncovered at time `t`, becomes a pivot. -/
lemma mem_pivotsUpTo_of_uncovered (σ : Equiv.Perm (Fin n)) {t : ℕ} (ht : t < n)
    (h : σ ⟨t, ht⟩ ∈ uncovered G σ t) : σ ⟨t, ht⟩ ∈ pivotsUpTo G σ (t + 1) := by
  rw [mem_pivotsUpTo_succ G σ ht]
  exact Or.inr ⟨rfl, (mem_filter.1 h).2.2⟩

/-- Auxiliary result for Lemmas 7.7 and 7.12 (Section 7.3). -/
lemma arrTime_ge_of_mem_uncovered {σ : Equiv.Perm (Fin n)} {t : ℕ} {v : Fin n}
    (h : v ∈ uncovered G σ t) : t ≤ (σ.symm v : ℕ) := (mem_filter.1 h).2.1

/-! ### Lemma 7.12 -/

/-- The sequential estimate behind Lemma 7.12: for any set `Q` of vertices and any `x`, the
probability that no pivot of `Q` arrives among the first `t` arrivals while at least `x` vertices
of `Q` are still uncovered at time `t` is at most `exp(-x t / n)`. -/
lemma prob_noPivot_uncovered_le (Q : Finset (Fin n)) (x : ℝ) :
    ∀ t ≤ n, prob (fun σ => (∀ p ∈ pivotsUpTo G σ t, p ∉ Q) ∧
      x ≤ ((uncovered G σ t ∩ Q).card : ℝ)) ≤ Real.exp (-(x * t / n)) := by
  intro t
  induction t with
  | zero => intro _; simpa using prob_le_one _
  | succ t ih =>
    intro ht
    have htn : t < n := by omega
    have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    set B : Equiv.Perm (Fin n) → Prop := fun σ => (∀ p ∈ pivotsUpTo G σ t, p ∉ Q) ∧
      x ≤ ((uncovered G σ t ∩ Q).card : ℝ) with hB
    have h1 : prob (fun σ => (∀ p ∈ pivotsUpTo G σ (t + 1), p ∉ Q) ∧
        x ≤ ((uncovered G σ (t + 1) ∩ Q).card : ℝ)) ≤
        prob (fun σ => B σ ∧ σ ⟨t, htn⟩ ∉ uncovered G σ t ∩ Q) := by
      apply prob_mono
      rintro σ ⟨hp, hx⟩
      refine ⟨⟨fun p hp' => hp p (pivotsUpTo_mono G σ (Nat.le_succ t) hp'), ?_⟩, ?_⟩
      · refine hx.trans ?_
        exact_mod_cast card_le_card (inter_subset_inter_right (uncovered_succ_subset G σ t))
      · intro hmem
        exact hp _ (mem_pivotsUpTo_of_uncovered G σ htn (mem_inter.1 hmem).1)
          (mem_inter.1 hmem).2
    have h2 := prob_step htn ∅ (by simp) B
      (by
        rintro σ ρ hρ ⟨hp, hx⟩
        have hρ' := fixOutside_Ipos_lt hρ
        refine ⟨?_, ?_⟩
        · rw [pivotsUpTo_mul hρ']; exact hp
        · rw [uncovered_mul hρ']; exact hx)
      (fun σ => uncovered G σ t ∩ Q)
      (by
        intro σ ρ hρ _
        simp only [uncovered_mul (fixOutside_Ipos_lt hρ)])
      (by
        intro σ _ v hv
        have := arrTime_ge_of_mem_uncovered G (mem_inter.1 hv).1
        simp [Ipos]; exact this)
      (x / n)
      (by
        rintro σ ⟨-, hx⟩
        rcases le_or_gt x 0 with hx0 | hx0
        · have : x / n * ((Ipos t (∅ : Finset (Fin n))).card : ℝ) ≤ 0 :=
            mul_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonpos_of_nonneg hx0 hn.le)
              (by positivity)
          linarith [(Nat.cast_nonneg _ : (0 : ℝ) ≤ ((uncovered G σ t ∩ Q).card : ℝ))]
        · have hI : ((Ipos t (∅ : Finset (Fin n))).card : ℝ) ≤ n := by
            have := card_Ipos_le t (∅ : Finset (Fin n))
            exact_mod_cast this.trans (Nat.sub_le n t)
          calc x / n * ((Ipos t (∅ : Finset (Fin n))).card : ℝ) ≤ x / n * n := by gcongr
            _ = x := by field_simp
            _ ≤ _ := hx)
    have h3 := ih (by omega)
    calc _ ≤ _ := h1
      _ ≤ Real.exp (-(x / n)) * prob B := by convert h2
      _ ≤ Real.exp (-(x / n)) * Real.exp (-(x * t / n)) := by gcongr
      _ = Real.exp (-(x * ↑(t + 1) / n)) := by
          rw [← Real.exp_add]; congr 1; push_cast; ring

/-- **Lemma 7.12 (almost-cliques without early pivots have few uncovered vertices).**  Fix an
almost-clique `Q_j` (the statement and proof hold for an arbitrary set `Q` of vertices) and let
`Q_j^u` be the set of vertices of `Q_j` uncovered at time `2^i`.  Then for any constant `c`, with
probability at least `1 - n^{-c}`, either a pivot from `Q_j` arrives by time `2^i` or
`|Q_j^u| < c n ln n / 2^i`.  (We assume `2^i ≤ n`, so that time `2^i` exists.) -/
theorem lemma_7_12 (Q : Finset (Fin n)) (c : ℝ) {i : ℕ} (hi : 2 ^ i ≤ n) :
    prob (fun σ => (∀ p ∈ pivotsUpTo G σ (2 ^ i), p ∉ Q) ∧
      c * n * Real.log n / 2 ^ i ≤ ((uncovered G σ (2 ^ i) ∩ Q).card : ℝ)) ≤
      (n : ℝ) ^ (-c) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n from lt_of_lt_of_le (by positivity) hi)
  refine (prob_noPivot_uncovered_le G Q _ (2 ^ i) hi).trans (le_of_eq ?_)
  rw [Real.rpow_def_of_pos hn]
  congr 1
  push_cast
  field_simp

end CCK
