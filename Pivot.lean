module

public import RequestProject.Hyp
public import RequestProject.Offline
public import RequestProject.CliqueInstance

/-!
# The Pivot algorithm and Lemma 7.4

The (online, random-order) PIVOT algorithm of [ACN05] (recalled at the beginning of Section 6 of
the paper): when a vertex arrives, if none of its previously arrived neighbours is a pivot, it
becomes a pivot and opens a new pivot cluster; otherwise it joins the pivot cluster of its
earliest arrived pivot neighbour.

The 3-approximation guarantee of PIVOT ([ACN05]) is an external result; following the
instructions it is *not* proved but taken as the explicit hypothesis `PivotThreeApprox`.

We then prove Lemma 7.5 (the lower bound on `Cost(OPT_k)` through the clique instance `J_σ`
obtained by turning the pivot clusters into cliques).
-/

@[expose] public section

open Finset
open scoped Classical

namespace CCK

variable {n : ℕ}

/-- The set of pivots among the first `t` arrivals of the PIVOT algorithm run on `G` with arrival
order `σ` (Section 6: a vertex becomes a pivot iff none of its previously arrived neighbours is a
pivot). -/
noncomputable def pivotsUpTo (G : SimpleGraph (Fin n)) (σ : Equiv.Perm (Fin n)) :
    ℕ → Finset (Fin n)
  | 0 => ∅
  | t + 1 =>
    if h : t < n then
      (if ∀ p ∈ pivotsUpTo G σ t, ¬ G.Adj p (σ ⟨t, h⟩) then
        insert (σ ⟨t, h⟩) (pivotsUpTo G σ t) else pivotsUpTo G σ t)
    else pivotsUpTo G σ t

/-- `v` is a pivot of the PIVOT algorithm on `G` with arrival order `σ` (Section 6). -/
def IsPivot (G : SimpleGraph (Fin n)) (σ : Equiv.Perm (Fin n)) (v : Fin n) : Prop :=
  v ∈ pivotsUpTo G σ n

/-- The pivot of the pivot cluster containing `v` in the PIVOT algorithm (Section 6): `v` itself
if `v` is a pivot, and otherwise its earliest arrived pivot neighbour. -/
noncomputable def pivotOf (G : SimpleGraph (Fin n)) (σ : Equiv.Perm (Fin n)) (v : Fin n) :
    Fin n :=
  if h : ((pivotsUpTo G σ n).filter (fun p => G.Adj p v)).Nonempty ∧ ¬ IsPivot G σ v then
    σ ((((pivotsUpTo G σ n).filter (fun p => G.Adj p v)).image σ.symm).min' (h.1.image _))
  else v

/-- **[ACN05] (PIVOT is a 3-approximation in expectation)**, used in Lemma 7.4, Lemma 7.5 and the
proof of Theorem 4.  This is an external result of Ailon, Charikar and Newman; following the
instructions it is not formalized but stated as a hypothesis: for every graph, the expected cost
of the PIVOT clustering under a uniformly random arrival order is at most `3 Cost(OPT_CC)`. -/
def PivotThreeApprox : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    expect (fun σ => (cost G (pivotOf G σ) : ℝ)) ≤ 3 * optCC G

/-! ### Basic properties of the pivots -/

section basic

variable (G : SimpleGraph (Fin n)) (σ : Equiv.Perm (Fin n))

/-- Auxiliary result for the PIVOT algorithm (Section 6) and Lemma 7.5. -/
lemma pivotsUpTo_succ_of_ge {t : ℕ} (ht : n ≤ t) : pivotsUpTo G σ (t + 1) = pivotsUpTo G σ t := by
  simp [pivotsUpTo, show ¬ t < n by omega]

/-- Auxiliary result for the PIVOT algorithm (Section 6) and Lemma 7.5. -/
lemma mem_pivotsUpTo_succ {t : ℕ} (ht : t < n) (v : Fin n) :
    v ∈ pivotsUpTo G σ (t + 1) ↔ v ∈ pivotsUpTo G σ t ∨
      (v = σ ⟨t, ht⟩ ∧ ∀ p ∈ pivotsUpTo G σ t, ¬ G.Adj p v) := by
  simp only [pivotsUpTo, ht, dif_pos]
  split_ifs with h
  · rw [mem_insert]
    constructor
    · rintro (rfl | h') <;> [exact Or.inr ⟨rfl, h⟩; exact Or.inl h']
    · rintro (h' | ⟨rfl, _⟩) <;> [exact Or.inr h'; exact Or.inl rfl]
  · constructor
    · exact Or.inl
    · rintro (h' | ⟨rfl, h'⟩)
      · exact h'
      · exact absurd h' h

/-- Auxiliary result for the PIVOT algorithm (Section 6) and Lemma 7.5. -/
lemma pivotsUpTo_subset_firstSet (t : ℕ) : pivotsUpTo G σ t ⊆ firstSet σ t := by
  induction t with
  | zero => simp [pivotsUpTo]
  | succ t ih =>
    intro v hv
    by_cases ht : t < n
    · rcases (mem_pivotsUpTo_succ G σ ht v).1 hv with h | ⟨rfl, _⟩
      · have := ih h
        simp only [firstSet, mem_filter, mem_univ, true_and] at this ⊢; omega
      · simp [firstSet, arrTime]
    · rw [pivotsUpTo_succ_of_ge G σ (by omega)] at hv
      have := ih hv
      simp only [firstSet, mem_filter, mem_univ, true_and] at this ⊢; omega

/-- Auxiliary result for the PIVOT algorithm (Section 6) and Lemma 7.5. -/
lemma pivotsUpTo_mono {s t : ℕ} (hst : s ≤ t) : pivotsUpTo G σ s ⊆ pivotsUpTo G σ t := by
  induction hst with
  | refl => exact Finset.Subset.refl _
  | step h ih =>
    rename_i m
    refine ih.trans ?_
    intro v hv
    by_cases hm : m < n
    · exact (mem_pivotsUpTo_succ G σ hm v).2 (Or.inl hv)
    · rwa [pivotsUpTo_succ_of_ge G σ (by omega)]

/-- Auxiliary result for the PIVOT algorithm (Section 6) and Lemma 7.5. -/
lemma pivotsUpTo_eq_of_ge {m : ℕ} (hm : n ≤ m) : pivotsUpTo G σ m = pivotsUpTo G σ n := by
  induction hm with
  | refl => rfl
  | step h ih => rw [pivotsUpTo_succ_of_ge G σ h, ih]

/-- A vertex is among the pivots of the first `t` arrivals iff it is a pivot and arrives before
`t`. -/
lemma mem_pivotsUpTo_iff (t : ℕ) (v : Fin n) :
    v ∈ pivotsUpTo G σ t ↔ IsPivot G σ v ∧ arrTime σ v < t := by
  induction t with
  | zero => simp [pivotsUpTo]
  | succ t ih =>
    constructor
    · intro hv
      have h1 : arrTime σ v < t + 1 := by
        have := pivotsUpTo_subset_firstSet G σ (t + 1) hv
        simpa [firstSet] using this
      refine ⟨?_, h1⟩
      unfold IsPivot
      rcases le_or_gt (t + 1) n with h | h
      · exact pivotsUpTo_mono G σ h hv
      · rwa [pivotsUpTo_eq_of_ge G σ h.le] at hv
    · rintro ⟨hp, hlt⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hlt with h | h
      · exact pivotsUpTo_mono G σ (Nat.le_succ t) (ih.2 ⟨hp, h⟩)
      · -- `v` arrives exactly at time `t`
        have ht : t < n := by rw [← h]; exact Fin.isLt _
        -- `v` is not in `pivotsUpTo t`; being a pivot it must be inserted at step `t + 1`
        have hmono : ∀ m, t + 1 ≤ m → (v ∈ pivotsUpTo G σ m → v ∈ pivotsUpTo G σ (t + 1)) := by
          intro m hm
          induction hm with
          | refl => exact id
          | step hle ih' =>
            rename_i m'
            intro hm'
            apply ih'
            by_cases hm'n : m' < n
            · rcases (mem_pivotsUpTo_succ G σ hm'n v).1 hm' with h' | ⟨h', _⟩
              · exact h'
              · exfalso
                have : arrTime σ v = m' := by rw [h']; simp [arrTime]
                have hle' : t + 1 ≤ m' := hle
                omega
            · rwa [pivotsUpTo_succ_of_ge G σ (by omega)] at hm'
        exact hmono n ht hp

/-- Auxiliary result for the PIVOT algorithm (Section 6) and Lemma 7.5. -/
lemma isPivot_iff (v : Fin n) :
    IsPivot G σ v ↔ ∀ p ∈ pivotsUpTo G σ (arrTime σ v), ¬ G.Adj p v := by
  have ht : arrTime σ v < n := Fin.isLt _
  have hv : v = σ ⟨arrTime σ v, ht⟩ := by
    show v = σ ⟨(σ.symm v : ℕ), ht⟩; simp
  have hnot : v ∉ pivotsUpTo G σ (arrTime σ v) := by
    intro h; have := ((mem_pivotsUpTo_iff G σ _ v).1 h).2; omega
  constructor
  · intro hp
    have := (mem_pivotsUpTo_iff G σ (arrTime σ v + 1) v).2 ⟨hp, by omega⟩
    rcases (mem_pivotsUpTo_succ G σ ht v).1 this with h | ⟨_, h⟩
    · exact absurd h hnot
    · exact h
  · intro h
    have := (mem_pivotsUpTo_succ G σ ht v).2 (Or.inr ⟨hv, h⟩)
    exact ((mem_pivotsUpTo_iff G σ _ v).1 this).1

/-- Pivots are pairwise non-adjacent. -/
lemma not_adj_of_isPivot {u v : Fin n} (hu : IsPivot G σ u) (hv : IsPivot G σ v) :
    ¬ G.Adj u v := by
  intro huv
  have hne : u ≠ v := G.ne_of_adj huv
  have hne' : arrTime σ u ≠ arrTime σ v := by
    intro h; apply hne; unfold arrTime at h
    exact σ.symm.injective (Fin.ext h)
  rcases Nat.lt_or_gt_of_ne hne' with h | h
  · exact (isPivot_iff G σ v).1 hv u ((mem_pivotsUpTo_iff G σ _ u).2 ⟨hu, h⟩) huv
  · exact (isPivot_iff G σ u).1 hu v ((mem_pivotsUpTo_iff G σ _ v).2 ⟨hv, h⟩) huv.symm

/-- A non-pivot has a pivot neighbour arriving before it. -/
lemma exists_pivot_adj_of_not_isPivot {v : Fin n} (hv : ¬ IsPivot G σ v) :
    ∃ p, IsPivot G σ p ∧ arrTime σ p < arrTime σ v ∧ G.Adj p v := by
  rw [isPivot_iff] at hv
  push_neg at hv
  obtain ⟨p, hp, hadj⟩ := hv
  exact ⟨p, ((mem_pivotsUpTo_iff G σ _ p).1 hp).1, ((mem_pivotsUpTo_iff G σ _ p).1 hp).2, hadj⟩

/-- Auxiliary result for the PIVOT algorithm (Section 6) and Lemma 7.5. -/
lemma pivotOf_of_isPivot {v : Fin n} (hv : IsPivot G σ v) : pivotOf G σ v = v := by
  unfold pivotOf; rw [dif_neg (fun h => h.2 hv)]

/-- The pivot of a non-pivot vertex `v` is a pivot neighbour of `v` arriving no later than every
other pivot neighbour of `v` (in particular before `v`). -/
lemma pivotOf_spec_of_not_isPivot {v : Fin n} (hv : ¬ IsPivot G σ v) :
    IsPivot G σ (pivotOf G σ v) ∧ G.Adj (pivotOf G σ v) v ∧
      ∀ p, IsPivot G σ p → G.Adj p v → arrTime σ (pivotOf G σ v) ≤ arrTime σ p := by
  obtain ⟨p₀, hp₀, -, hadj₀⟩ := exists_pivot_adj_of_not_isPivot G σ hv
  have hne : ((pivotsUpTo G σ n).filter (fun p => G.Adj p v)).Nonempty :=
    ⟨p₀, mem_filter.2 ⟨hp₀, hadj₀⟩⟩
  have hdef : pivotOf G σ v =
      σ ((((pivotsUpTo G σ n).filter (fun p => G.Adj p v)).image σ.symm).min' (hne.image _)) := by
    unfold pivotOf; rw [dif_pos ⟨hne, hv⟩]
  set m := (((pivotsUpTo G σ n).filter (fun p => G.Adj p v)).image σ.symm).min' (hne.image _)
  have hm : m ∈ ((pivotsUpTo G σ n).filter (fun p => G.Adj p v)).image σ.symm := min'_mem _ _
  obtain ⟨u, hu, hum⟩ := mem_image.1 hm
  have hu' : σ m = u := by rw [← hum]; simp
  rw [hdef, hu']
  refine ⟨(mem_filter.1 hu).1, (mem_filter.1 hu).2, ?_⟩
  intro p hp hpv
  have : m ≤ σ.symm p := min'_le _ _ (mem_image.2 ⟨p, mem_filter.2 ⟨hp, hpv⟩, rfl⟩)
  rw [← hum] at this
  exact this

/-- `pivotOf v` is always a pivot. -/
lemma isPivot_pivotOf (v : Fin n) : IsPivot G σ (pivotOf G σ v) := by
  by_cases hv : IsPivot G σ v
  · rw [pivotOf_of_isPivot G σ hv]; exact hv
  · exact (pivotOf_spec_of_not_isPivot G σ hv).1

/-- Auxiliary result for the PIVOT algorithm (Section 6) and Lemma 7.5. -/
lemma pivotOf_pivotOf (v : Fin n) : pivotOf G σ (pivotOf G σ v) = pivotOf G σ v :=
  pivotOf_of_isPivot G σ (isPivot_pivotOf G σ v)

/-- The pivot of `v` arrives no later than `v`. -/
lemma arrTime_pivotOf_le (v : Fin n) : arrTime σ (pivotOf G σ v) ≤ arrTime σ v := by
  by_cases hv : IsPivot G σ v
  · rw [pivotOf_of_isPivot G σ hv]
  · obtain ⟨p, hp, hlt, hadj⟩ := exists_pivot_adj_of_not_isPivot G σ hv
    exact ((pivotOf_spec_of_not_isPivot G σ hv).2.2 p hp hadj).trans hlt.le

/-- `pivotOf v = v` iff `v` is a pivot. -/
lemma pivotOf_eq_self_iff (v : Fin n) : pivotOf G σ v = v ↔ IsPivot G σ v := by
  constructor
  · intro h; rw [← h]; exact isPivot_pivotOf G σ v
  · exact pivotOf_of_isPivot G σ

end basic

/-! ### Lemma 7.4 -/

/-- **Lemma 7.4 (lower bound on the optimal cost using Pivot).**  Let `J_σ` be the clique instance
obtained by running PIVOT with arrival order `σ` and turning all pivot clusters into disjoint
cliques (`J_σ = cliqueGraph (pivotOf G σ)`).  Assuming the 3-approximation guarantee of PIVOT
([ACN05], hypothesis `PivotThreeApprox`), `E[s(J_σ) a(J_σ)] ≤ 16 Cost(OPT_k(I))`, i.e.
`Ω(E[s(J_σ) a(J_σ)]) ≤ Cost(OPT_k(I))`. -/
theorem lemma_7_5 (hPiv : PivotThreeApprox) (G : SimpleGraph (Fin n)) {k : ℕ} (hk : 0 < k) :
    expect (fun σ => (sOf (pivotOf G σ) k : ℝ) * aOf (pivotOf G σ) k) ≤ 16 * optK G k := by
  haveI : Nonempty (Fin n → Fin k) := ⟨fun _ => ⟨0, hk⟩⟩
  have hpt : ∀ σ : Equiv.Perm (Fin n), (sOf (pivotOf G σ) k : ℝ) * aOf (pivotOf G σ) k ≤
      4 * ((optK G k : ℝ) + cost G (pivotOf G σ)) := by
    intro σ
    have h1 := (lemma_3_4 (pivotOf G σ) hk).1
    have h2 := optK_cliqueGraph_le G (pivotOf G σ) k
    have h2' : (optK (cliqueGraph (pivotOf G σ)) k : ℝ) ≤ optK G k + cost G (pivotOf G σ) := by
      exact_mod_cast h2
    linarith
  have hE := expect_mono hpt
  have hlin : expect (fun σ => 4 * ((optK G k : ℝ) + cost G (pivotOf G σ))) =
      4 * optK G k + 4 * expect (fun σ => (cost G (pivotOf G σ) : ℝ)) := by
    unfold expect
    rw [← mul_sum, sum_add_distrib, sum_const, card_univ, nsmul_eq_mul]
    have := card_perm_pos (n := n)
    field_simp
  have h3 := hPiv n G
  have h4 : (optCC G : ℝ) ≤ optK G k := by exact_mod_cast optCC_le_optK G k
  rw [hlin] at hE
  linarith

end CCK
