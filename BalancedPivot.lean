module

public import RequestProject.Claim63
public import RequestProject.Lemma75

/-!
# The algorithm BALANCED PIVOT (Section 7.1, Algorithm 1)

BALANCED PIVOT runs PIVOT; a non-pivot joins the cluster of its earliest arrived pivot neighbour,
and a new pivot is placed in a currently least loaded cluster among the `k` clusters
(ties broken by smallest index).  Clusters are labelled by natural numbers `< k`.

We define the state of the algorithm after `t` arrivals by recursion on `t`, and prove the basic
structural facts used in the proof of Theorem 4: labels never change, every vertex has the label
of its pivot, labels are `< k`, and the first `k` pivots occupy distinct clusters.  We also define
the projected load of Definition 7.3.
-/

@[expose] public section

open Finset
open scoped Classical

namespace CCK

variable {n : ℕ}

/-- The index of a least loaded cluster among `0, …, k-1` (smallest such index). -/
noncomputable def argminLoad (load : ℕ → ℕ) (k : ℕ) : ℕ :=
  if h : ∃ j, j < k ∧ ∀ j' < k, load j ≤ load j' then Nat.find h else 0

/-- Auxiliary result for Algorithm 1 (BALANCED PIVOT, Section 7.1), used in the proof of Theorem 4. -/
lemma exists_argmin_load (load : ℕ → ℕ) {k : ℕ} (hk : 0 < k) :
    ∃ j, j < k ∧ ∀ j' < k, load j ≤ load j' := by
  obtain ⟨j, hj, hmin⟩ := (range k).exists_min_image load ⟨0, mem_range.2 hk⟩
  exact ⟨j, mem_range.1 hj, fun j' hj' => hmin j' (mem_range.2 hj')⟩

/-- Auxiliary result for Algorithm 1 (BALANCED PIVOT, Section 7.1), used in the proof of Theorem 4. -/
lemma argminLoad_spec (load : ℕ → ℕ) {k : ℕ} (hk : 0 < k) :
    argminLoad load k < k ∧ ∀ j' < k, load (argminLoad load k) ≤ load j' := by
  have h := exists_argmin_load load hk
  unfold argminLoad
  rw [dif_pos h]
  exact (Nat.find_spec h)

/-- The state of BALANCED PIVOT after `t` arrivals: the cluster label of every vertex arrived so
far (unarrived vertices carry the dummy label `0`). -/
noncomputable def bpState (G : SimpleGraph (Fin n)) (k : ℕ) (σ : Equiv.Perm (Fin n)) :
    ℕ → Fin n → ℕ
  | 0 => fun _ => 0
  | t + 1 =>
    if h : t < n then
      Function.update (bpState G k σ t) (σ ⟨t, h⟩)
        (if IsPivot G σ (σ ⟨t, h⟩) then
          argminLoad (fun j => ((firstSet σ t).filter (fun u => bpState G k σ t u = j)).card) k
        else bpState G k σ t (pivotOf G σ (σ ⟨t, h⟩)))
    else bpState G k σ t

/-- **Algorithm 1 (BALANCED PIVOT).**  The cluster label of each vertex in the final clustering
produced by BALANCED PIVOT with `k` clusters on graph `G` and arrival order `σ`. -/
noncomputable def bpLabel (G : SimpleGraph (Fin n)) (k : ℕ) (σ : Equiv.Perm (Fin n)) :
    Fin n → ℕ :=
  bpState G k σ n

/-- The load (number of vertices) of cluster `j` after `t` arrivals. -/
noncomputable def clLoad (G : SimpleGraph (Fin n)) (k : ℕ) (σ : Equiv.Perm (Fin n)) (t j : ℕ) :
    ℕ :=
  ((firstSet σ t).filter (fun u => bpLabel G k σ u = j)).card

/-- **Definition 7.3 (projected load).**  The projected load of cluster `j` after `t` arrivals:
the total final size of the pivot clusters already assigned to cluster `j`. -/
noncomputable def projLoad (G : SimpleGraph (Fin n)) (k : ℕ) (σ : Equiv.Perm (Fin n))
    (t j : ℕ) : ℕ :=
  ∑ q ∈ (pivotsUpTo G σ t).filter (fun q => bpLabel G k σ q = j), pclSize G σ q

/-- The expected cost of BALANCED PIVOT under a uniformly random arrival order. -/
noncomputable def balancedPivotExpCost (G : SimpleGraph (Fin n)) (k : ℕ) : ℝ :=
  expect (fun σ => (cost G (bpLabel G k σ) : ℝ))

section basic

variable (G : SimpleGraph (Fin n)) (k : ℕ) (σ : Equiv.Perm (Fin n))

/-- Auxiliary result for Algorithm 1 (BALANCED PIVOT, Section 7.1), used in the proof of Theorem 4. -/
lemma arrTime_lt (v : Fin n) : arrTime σ v < n := Fin.isLt _

/-- Auxiliary result for Algorithm 1 (BALANCED PIVOT, Section 7.1), used in the proof of Theorem 4. -/
lemma arrTime_apply (t : ℕ) (h : t < n) : arrTime σ (σ ⟨t, h⟩) = t := by
  simp [arrTime]

/-- Auxiliary result for Algorithm 1 (BALANCED PIVOT, Section 7.1), used in the proof of Theorem 4. -/
lemma eq_of_arrTime_eq {u v : Fin n} (h : arrTime σ u = arrTime σ v) : u = v :=
  σ.symm.injective (Fin.ext h)

/-- Auxiliary result for Algorithm 1 (BALANCED PIVOT, Section 7.1), used in the proof of Theorem 4. -/
lemma bpState_succ_of_lt {u : Fin n} {s : ℕ} (hu : arrTime σ u < s) :
    bpState G k σ (s + 1) u = bpState G k σ s u := by
  by_cases h : s < n
  · have hne : u ≠ σ ⟨s, h⟩ := by
      intro hu'
      have := arrTime_apply σ s h
      rw [← hu'] at this
      omega
    simp only [bpState, dif_pos h]
    exact Function.update_of_ne hne _ _
  · simp only [bpState, dif_neg h]

/-- Labels of arrived vertices never change. -/
lemma bpState_stable {u : Fin n} {t : ℕ} (hu : arrTime σ u < t) :
    ∀ m, bpState G k σ (t + m) u = bpState G k σ t u := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [← add_assoc, bpState_succ_of_lt G k σ (by omega), ih]

/-- Auxiliary result for Algorithm 1 (BALANCED PIVOT, Section 7.1), used in the proof of Theorem 4. -/
lemma bpState_eq_bpLabel {u : Fin n} {t : ℕ} (hu : arrTime σ u < t) (ht : t ≤ n) :
    bpState G k σ t u = bpLabel G k σ u := by
  unfold bpLabel
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le ht
  exact (bpState_stable G k σ hu m).symm

/-- Auxiliary result for Algorithm 1 (BALANCED PIVOT, Section 7.1), used in the proof of Theorem 4. -/
lemma bpLabel_eq_step (v : Fin n) :
    bpLabel G k σ v =
      (if IsPivot G σ v then
          argminLoad (fun j => ((firstSet σ (arrTime σ v)).filter
            (fun u => bpState G k σ (arrTime σ v) u = j)).card) k
        else bpState G k σ (arrTime σ v) (pivotOf G σ v)) := by
  have ht := arrTime_lt σ v
  rw [← bpState_eq_bpLabel G k σ (Nat.lt_succ_self _) ht]
  have hv : σ ⟨arrTime σ v, ht⟩ = v := by simp [arrTime]
  simp only [bpState, dif_pos ht, hv, Function.update_self]

/-- Auxiliary result for Algorithm 1 (BALANCED PIVOT, Section 7.1), used in the proof of Theorem 4. -/
lemma arrTime_pivotOf_lt {v : Fin n} (hv : ¬ IsPivot G σ v) :
    arrTime σ (pivotOf G σ v) < arrTime σ v := by
  have h1 := arrTime_pivotOf_le G σ v
  have hne : pivotOf G σ v ≠ v := fun h => hv ((pivotOf_eq_self_iff G σ v).1 h)
  rcases lt_or_eq_of_le h1 with h | h
  · exact h
  · exact absurd (eq_of_arrTime_eq σ h) hne

/-- Every vertex has the label of its pivot. -/
lemma bpLabel_pivotOf (v : Fin n) : bpLabel G k σ (pivotOf G σ v) = bpLabel G k σ v := by
  by_cases hv : IsPivot G σ v
  · rw [pivotOf_of_isPivot G σ hv]
  · rw [bpLabel_eq_step G k σ v, if_neg hv]
    exact (bpState_eq_bpLabel G k σ (arrTime_pivotOf_lt G σ hv) (arrTime_lt σ v).le).symm

/-- Auxiliary result for Algorithm 1 (BALANCED PIVOT, Section 7.1), used in the proof of Theorem 4. -/
lemma firstSet_filter_bpState (t : ℕ) (ht : t ≤ n) (j : ℕ) :
    (firstSet σ t).filter (fun u => bpState G k σ t u = j) =
      (firstSet σ t).filter (fun u => bpLabel G k σ u = j) := by
  apply filter_congr
  intro u hu
  have : arrTime σ u < t := by simpa [firstSet] using hu
  rw [bpState_eq_bpLabel G k σ this ht]

/-- A pivot is placed in a least loaded cluster at its arrival time. -/
lemma bpLabel_of_isPivot {p : Fin n} (hp : IsPivot G σ p) :
    bpLabel G k σ p = argminLoad (fun j => clLoad G k σ (arrTime σ p) j) k := by
  rw [bpLabel_eq_step G k σ p, if_pos hp]
  congr 1
  funext j
  rw [firstSet_filter_bpState G k σ _ (arrTime_lt σ p).le]
  rfl

/-- Auxiliary result for Algorithm 1 (BALANCED PIVOT, Section 7.1), used in the proof of Theorem 4. -/
lemma bpLabel_lt (hk : 0 < k) (v : Fin n) : bpLabel G k σ v < k := by
  rw [← bpLabel_pivotOf]
  rw [bpLabel_of_isPivot G k σ (isPivot_pivotOf G σ v)]
  exact (argminLoad_spec _ hk).1

/-- Auxiliary result for Algorithm 1 (BALANCED PIVOT, Section 7.1), used in the proof of Theorem 4. -/
lemma clLoad_bpLabel_le (hk : 0 < k) {p : Fin n} (hp : IsPivot G σ p) {j : ℕ} (hj : j < k) :
    clLoad G k σ (arrTime σ p) (bpLabel G k σ p) ≤ clLoad G k σ (arrTime σ p) j := by
  rw [bpLabel_of_isPivot G k σ hp]
  exact (argminLoad_spec _ hk).2 j hj

/-- The labels used by the vertices arrived before time `t` are labels of pivots arrived before
time `t`. -/
lemma exists_pivot_of_mem_firstSet {u : Fin n} {t : ℕ} (hu : u ∈ firstSet σ t) :
    pivotOf G σ u ∈ pivotsUpTo G σ t ∧ bpLabel G k σ (pivotOf G σ u) = bpLabel G k σ u := by
  refine ⟨?_, bpLabel_pivotOf G k σ u⟩
  have h1 : arrTime σ u < t := by simpa [firstSet] using hu
  exact (mem_pivotsUpTo_iff G σ t _).2
    ⟨isPivot_pivotOf G σ u, lt_of_le_of_lt (arrTime_pivotOf_le G σ u) h1⟩

/-- **The first `k` pivots occupy distinct clusters.**  If fewer than `k` pivots arrived before
the pivot `p`, then `p` is placed in a cluster containing no previously arrived vertex. -/
lemma clLoad_eq_zero_of_early (hk : 0 < k) {p : Fin n} (hp : IsPivot G σ p)
    (hearly : (pivotsUpTo G σ (arrTime σ p)).card < k) :
    clLoad G k σ (arrTime σ p) (bpLabel G k σ p) = 0 := by
  set t := arrTime σ p
  have hsub : ((range k).filter (fun j => ∃ u ∈ firstSet σ t, bpLabel G k σ u = j)) ⊆
      (pivotsUpTo G σ t).image (bpLabel G k σ) := by
    intro j hj
    obtain ⟨-, u, hu, rfl⟩ := mem_filter.1 hj
    obtain ⟨h1, h2⟩ := exists_pivot_of_mem_firstSet G k σ hu
    exact mem_image.2 ⟨_, h1, h2⟩
  have hcard := (card_le_card hsub).trans card_image_le
  obtain ⟨j, hj, hjn⟩ : ∃ j ∈ range k, j ∉ (range k).filter
      (fun j => ∃ u ∈ firstSet σ t, bpLabel G k σ u = j) := by
    by_contra hcon
    push_neg at hcon
    have : range k ⊆ (range k).filter (fun j => ∃ u ∈ firstSet σ t, bpLabel G k σ u = j) :=
      fun j hj => hcon j hj
    have := card_le_card this
    rw [card_range] at this
    omega
  have hj0 : clLoad G k σ t j = 0 := by
    unfold clLoad
    rw [card_eq_zero, filter_eq_empty_iff]
    intro u hu hlab
    exact hjn (mem_filter.2 ⟨hj, u, hu, hlab⟩)
  have h2 : clLoad G k σ t (bpLabel G k σ p) ≤ clLoad G k σ t j :=
    clLoad_bpLabel_le G k σ hk hp (mem_range.1 hj)
  omega

/-- Auxiliary result for Algorithm 1 (BALANCED PIVOT, Section 7.1), used in the proof of Theorem 4. -/
lemma bpLabel_ne_of_early (hk : 0 < k) {p q : Fin n} (hp : IsPivot G σ p)
    (hearly : (pivotsUpTo G σ (arrTime σ p)).card < k) (hq : arrTime σ q < arrTime σ p) :
    bpLabel G k σ q ≠ bpLabel G k σ p := by
  intro heq
  have h0 := clLoad_eq_zero_of_early G k σ hk hp hearly
  unfold clLoad at h0
  rw [card_eq_zero, filter_eq_empty_iff] at h0
  exact h0 (by simpa [firstSet] using hq) heq

end basic

end CCK
