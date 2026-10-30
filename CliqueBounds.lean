module

public import RequestProject.CliqueParams

/-!
# Bounds on the optimal k-clustering of disjoint cliques (Lemma 3.4, clique level)

Here we prove, at the level of clique sizes, the two bounds of Lemma 3.4:
for every clique-preserving clustering `D`, `cCost2 D ≥ s(I) a(I)` (i.e. `Cost ≥ s a / 2`),
and there is a (greedy) clique-preserving clustering with `cCost2 D ≤ 2 s(I) a(I)`
(i.e. `Cost ≤ s a`).
-/

@[expose] public section

open Finset
open scoped Classical

namespace CCK

variable {w : ℕ → ℕ} {ℓ k : ℕ}

/-- Auxiliary result for Lemma 3.4 (Section 3). -/
lemma sum_cLoad (D : ℕ → Fin k) (f : ℕ → ℝ) (s : Finset ℕ) :
    ∑ j, ∑ i ∈ s.filter (fun i => D i = j), f i = ∑ i ∈ s, f i :=
  Finset.sum_fiberwise s D f

/-- Auxiliary result for Lemma 3.4 (Section 3). -/
lemma cCost2_eq_sum (D : ℕ → Fin k) :
    cCost2 w ℓ D = ∑ i ∈ range ℓ, (w i : ℝ) * (cLoad w ℓ D (D i) - w i) := by
  unfold cCost2
  have h1 : ∑ j, cLoad w ℓ D j ^ 2 = ∑ i ∈ range ℓ, (w i : ℝ) * cLoad w ℓ D (D i) := by
    rw [← sum_cLoad D (fun i => (w i : ℝ) * cLoad w ℓ D (D i)) (range ℓ)]
    apply sum_congr rfl; intro j _
    rw [sq]
    conv_lhs => rw [show cLoad w ℓ D j = ∑ i ∈ (range ℓ).filter (fun i => D i = j), (w i : ℝ)
      from rfl]
    rw [sum_mul]
    apply sum_congr rfl; intro i hi
    rw [(mem_filter.1 hi).2]; rfl
  rw [h1, ← sum_sub_distrib]
  apply sum_congr rfl; intro i _; ring

/-- Auxiliary result for Lemma 3.4 (Section 3). -/
lemma cLoad_ge_self (D : ℕ → Fin k) {i : ℕ} (hi : i < ℓ) : (w i : ℝ) ≤ cLoad w ℓ D (D i) := by
  unfold cLoad
  apply single_le_sum (f := fun i => (w i : ℝ)) (fun _ _ => Nat.cast_nonneg _)
  simp [hi]

/-- Two distinct cliques in the same cluster. -/
lemma cLoad_ge_two (D : ℕ → Fin k) {i i' : ℕ} (hi : i < ℓ) (hi' : i' < ℓ) (hne : i ≠ i')
    (hD : D i = D i') : (w i : ℝ) + w i' ≤ cLoad w ℓ D (D i) := by
  unfold cLoad
  have hsub : ({i, i'} : Finset ℕ) ⊆ (range ℓ).filter (fun x => D x = D i) := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp [hi, hi', hD]
  have := sum_le_sum_of_subset_of_nonneg (f := fun i => (w i : ℝ)) hsub
    (fun _ _ _ => Nat.cast_nonneg _)
  rw [sum_pair hne] at this
  exact this

/-- Auxiliary result for Lemma 3.4 (Section 3). -/
lemma cLoad_ge_three (D : ℕ → Fin k) {i u v : ℕ} (hi : i < ℓ) (hu : u < ℓ) (hv : v < ℓ)
    (h1 : i ≠ u) (h2 : i ≠ v) (h3 : u ≠ v) (hDu : D u = D i) (hDv : D v = D i) :
    (w i : ℝ) + w u + w v ≤ cLoad w ℓ D (D i) := by
  unfold cLoad
  have hsub : ({i, u, v} : Finset ℕ) ⊆ (range ℓ).filter (fun x => D x = D i) := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> simp [*]
  have := sum_le_sum_of_subset_of_nonneg (f := fun i => (w i : ℝ)) hsub
    (fun _ _ _ => Nat.cast_nonneg _)
  rw [sum_insert (by simp [h1, h2]), sum_pair h3] at this
  linarith

/-- Auxiliary result for Lemma 3.4 (Section 3). -/
lemma cCost2_nonneg (D : ℕ → Fin k) : 0 ≤ cCost2 w ℓ D := by
  rw [cCost2_eq_sum]
  apply sum_nonneg; intro i hi
  have := cLoad_ge_self (w := w) D (mem_range.1 hi)
  exact mul_nonneg (Nat.cast_nonneg _) (by linarith)

/-- `(∑ x)^2 ≥ ∑ x^2 + |T|(|T|-1) a^2` when all `x ≥ a ≥ 0`. -/
lemma sq_sum_ge (T : Finset ℕ) (x : ℕ → ℝ) (a : ℝ) (ha : 0 ≤ a) (hx : ∀ i ∈ T, a ≤ x i) :
    ∑ i ∈ T, x i ^ 2 + (T.card : ℝ) * (T.card - 1) * a ^ 2 ≤ (∑ i ∈ T, x i) ^ 2 := by
  induction T using Finset.induction_on with
  | empty => simp
  | insert t T ht ih =>
    rw [sum_insert ht, sum_insert ht, card_insert_of_notMem ht]
    have ih' := ih (fun i hi => hx i (mem_insert_of_mem hi))
    have hxt : a ≤ x t := hx t (mem_insert_self _ _)
    have hsum : (T.card : ℝ) * a ≤ ∑ i ∈ T, x i := by
      have := Finset.card_nsmul_le_sum T x a (fun i hi => hx i (mem_insert_of_mem hi))
      simpa [nsmul_eq_mul] using this
    have hca : 0 ≤ (T.card : ℝ) * a := mul_nonneg (Nat.cast_nonneg _) ha
    push_cast
    nlinarith [mul_le_mul hxt hsum hca (by linarith)]

/-- The fractional lower bound used in the proof of Lemma 3.4: in any clique-preserving
clustering, `∑_j c_j^2 ≥ ∑_{i < r} n_i^2 + (k - r) a^2`. -/
lemma sum_sq_cLoad_ge (D : ℕ → Fin k) (r : ℕ) (a : ℝ) (ha : 0 ≤ a) (hrℓ : r ≤ ℓ)
    (hbig : ∀ i < r, a ≤ w i)
    (htail : (tailSum w ℓ r : ℝ) = ((k : ℝ) - r) * a) :
    ∑ i ∈ range r, (w i : ℝ) ^ 2 + ((k : ℝ) - r) * a ^ 2 ≤ ∑ j, cLoad w ℓ D j ^ 2 := by
  -- per-cluster inequality
  set R : Fin k → Finset ℕ := fun j => (range r).filter (fun i => D i = j)
  set O : Fin k → Finset ℕ := fun j => (Ico r ℓ).filter (fun i => D i = j)
  have hload : ∀ j, cLoad w ℓ D j = ∑ i ∈ R j, (w i : ℝ) + ∑ i ∈ O j, (w i : ℝ) := by
    intro j
    unfold cLoad
    rw [← sum_union]
    · congr 1
      ext i; simp only [R, O, mem_filter, mem_range, mem_union, mem_Ico]; omega
    · rw [disjoint_left]; intro i h1 h2
      simp only [R, O, mem_filter, mem_range, mem_Ico] at h1 h2; omega
  have per : ∀ j, ∑ i ∈ R j, (w i : ℝ) ^ 2 + a ^ 2 * ((R j).card - 1) +
      2 * a * ∑ i ∈ O j, (w i : ℝ) ≤ cLoad w ℓ D j ^ 2 := by
    intro j
    rw [hload j]
    set b := ∑ i ∈ R j, (w i : ℝ)
    set y := ∑ i ∈ O j, (w i : ℝ)
    have hy : 0 ≤ y := sum_nonneg (fun _ _ => Nat.cast_nonneg _)
    have hsq := sq_sum_ge (R j) (fun i => (w i : ℝ)) a ha
      (fun i hi => hbig i (by simpa [R] using (mem_filter.1 hi).1))
    rcases Nat.eq_zero_or_pos (R j).card with h0 | h0
    · rw [card_eq_zero] at h0
      have hb : b = 0 := by simp [b, h0]
      rw [hb, h0]; simp
      nlinarith [sq_nonneg (y - a)]
    · have hb : (R j).card * a ≤ b := by
        have := Finset.card_nsmul_le_sum (R j) (fun i => (w i : ℝ)) a
          (fun i hi => hbig i (by simpa [R] using (mem_filter.1 hi).1))
        simpa [nsmul_eq_mul] using this
      have h1 : (1 : ℝ) ≤ (R j).card := by exact_mod_cast h0
      have hba : a ≤ b := by nlinarith
      have : ((R j).card : ℝ) - 1 ≤ ((R j).card : ℝ) * ((R j).card - 1) := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left this (sq_nonneg a)]
  have hsum := sum_le_sum (fun j (_ : j ∈ (univ : Finset (Fin k))) => per j)
  rw [sum_add_distrib, sum_add_distrib] at hsum
  have e1 : ∑ j, ∑ i ∈ R j, (w i : ℝ) ^ 2 = ∑ i ∈ range r, (w i : ℝ) ^ 2 :=
    sum_cLoad D _ _
  have e2 : ∑ j, (a ^ 2 * ((R j).card - 1) : ℝ) = a ^ 2 * (r - k) := by
    rw [← mul_sum, sum_sub_distrib]
    congr 1
    have : ∑ j, ((R j).card : ℝ) = r := by
      have := sum_cLoad D (fun _ => (1 : ℝ)) (range r)
      simp only [sum_const, nsmul_eq_mul, mul_one, card_range] at this
      exact this
    rw [this]; simp
  have e3 : ∑ j, 2 * a * ∑ i ∈ O j, (w i : ℝ) = 2 * a * (((k : ℝ) - r) * a) := by
    rw [← mul_sum, sum_cLoad D (fun i => (w i : ℝ)) (Ico r ℓ), ← htail]
    unfold tailSum; push_cast; rfl
  rw [e1, e2, e3] at hsum
  nlinarith


/-- Auxiliary result for Lemma 3.4 (Section 3). -/
lemma sum_range_split (f : ℕ → ℝ) {r : ℕ} (h : r ≤ ℓ) :
    ∑ i ∈ range ℓ, f i = ∑ i ∈ range r, f i + ∑ i ∈ Ico r ℓ, f i :=
  (Finset.sum_range_add_sum_Ico f h).symm

/-- Lemma 3.4, lower bound, case `n_{k+1} ≤ a(I)/2`. -/
lemma cCost2_lower_case1 (hs : SortedDesc w ℓ) (hpos : ∀ i < ℓ, 0 < w i) (hk0 : 0 < k)
    (hkl : k < ℓ) (hwk : (w k : ℝ) ≤ aParam w ℓ k / 2) (D : ℕ → Fin k) :
    (sParam w ℓ k : ℝ) * aParam w ℓ k / 2 ≤ cCost2 w ℓ D := by
  set r := rParam w ℓ k
  set a := aParam w ℓ k
  have hr : r < k := rParam_lt hpos hk0 hkl
  have ha : 0 < a := lt_of_le_of_lt (Nat.cast_nonneg _)
    (lt_aParam_of_rParam_le hs hr le_rfl (by omega))
  have htail := tailSum_rParam_eq (w := w) (ℓ := ℓ) hr
  have hfrac := sum_sq_cLoad_ge (w := w) (ℓ := ℓ) D r a ha.le (by omega)
    (fun i hi => aParam_le_of_lt_rParam hi) htail
  have hsplit := sum_range_split (ℓ := ℓ) (fun i => (w i : ℝ) ^ 2) (r := r) (by omega)
  have htail' : ∑ i ∈ Ico r ℓ, (w i : ℝ) = ((k : ℝ) - r) * a := by
    rw [← htail]; unfold tailSum; push_cast; rfl
  -- `cCost2 ≥ ∑_{i ≥ r} w_i (a - w_i)`
  have h1 : ∑ i ∈ Ico r ℓ, (w i : ℝ) * (a - w i) ≤ cCost2 w ℓ D := by
    unfold cCost2
    have : ∑ i ∈ Ico r ℓ, (w i : ℝ) * (a - w i) =
        a * ∑ i ∈ Ico r ℓ, (w i : ℝ) - ∑ i ∈ Ico r ℓ, (w i : ℝ) ^ 2 := by
      rw [mul_sum, ← sum_sub_distrib]; apply sum_congr rfl; intro i _; ring
    rw [this, htail', hsplit]
    nlinarith
  have h2 : ∑ i ∈ Ico k ℓ, (w i : ℝ) * (a / 2) ≤ ∑ i ∈ Ico r ℓ, (w i : ℝ) * (a - w i) := by
    calc ∑ i ∈ Ico k ℓ, (w i : ℝ) * (a / 2) ≤ ∑ i ∈ Ico k ℓ, (w i : ℝ) * (a - w i) := by
          apply sum_le_sum; intro i hi
          simp only [mem_Ico] at hi
          have : (w i : ℝ) ≤ w k := by exact_mod_cast hs _ _ hi.1 hi.2
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
          linarith
      _ ≤ ∑ i ∈ Ico r ℓ, (w i : ℝ) * (a - w i) := by
          apply sum_le_sum_of_subset_of_nonneg (Ico_subset_Ico_left hr.le)
          intro i hi _
          simp only [mem_Ico] at hi
          have := lt_aParam_of_rParam_le hs hr hi.1 hi.2
          exact mul_nonneg (Nat.cast_nonneg _) (by linarith)
  have h3 : ∑ i ∈ Ico k ℓ, (w i : ℝ) * (a / 2) = (sParam w ℓ k : ℝ) * a / 2 := by
    rw [← sum_mul]; unfold sParam tailSum; push_cast; ring
  linarith

/-- Load bookkeeping when two cliques in different clusters are swapped. -/
lemma cLoad_swap (D : ℕ → Fin k) {i v : ℕ} (hi : i < ℓ) (hv : v < ℓ) (hne : i ≠ v)
    (j : Fin k) :
    cLoad w ℓ (fun x => if x = i then D v else if x = v then D i else D x) j =
      cLoad w ℓ D j + ((if D v = j then (w i : ℝ) else 0) - (if D i = j then (w i : ℝ) else 0))
        + ((if D i = j then (w v : ℝ) else 0) - (if D v = j then (w v : ℝ) else 0)) := by
  unfold cLoad
  rw [sum_filter, sum_filter]
  have hpt : ∀ x, (if (if x = i then D v else if x = v then D i else D x) = j then (w x : ℝ)
      else 0) = (if D x = j then (w x : ℝ) else 0) +
        (if x = i then ((if D v = j then (w i : ℝ) else 0) - (if D i = j then (w i : ℝ) else 0))
          else 0) +
        (if x = v then ((if D i = j then (w v : ℝ) else 0) - (if D v = j then (w v : ℝ) else 0))
          else 0) := by
    intro x
    by_cases h1 : x = i
    · subst h1; simp [hne]
    · by_cases h2 : x = v
      · subst h2; simp [h1]
      · simp [h1, h2]
  rw [sum_congr rfl (fun x _ => hpt x), sum_add_distrib, sum_add_distrib, sum_ite_eq',
    sum_ite_eq']
  simp [hi, hv]

/-- Optimality under a swap: if `D` is optimal, swapping a clique `i` in cluster `P` with a
larger clique `v` in a different cluster `Q` cannot help, which gives `c_P - n_i ≥ c_Q - n_v`. -/
lemma swap_ineq (D : ℕ → Fin k) (hopt : ∀ D' : ℕ → Fin k, cCost2 w ℓ D ≤ cCost2 w ℓ D')
    {i v : ℕ} (hi : i < ℓ) (hv : v < ℓ) (hne : D i ≠ D v) (hlt : w i < w v) :
    cLoad w ℓ D (D v) - w v ≤ cLoad w ℓ D (D i) - w i := by
  have hiv : i ≠ v := fun h => hne (h ▸ rfl)
  set D' : ℕ → Fin k := fun x => if x = i then D v else if x = v then D i else D x
  have h := hopt D'
  unfold cCost2 at h
  set d : ℝ := (w v : ℝ) - w i
  have hd : 0 < d := by
    have : (w i : ℝ) < w v := by exact_mod_cast hlt
    simp only [d]; linarith
  have hload : ∀ j, cLoad w ℓ D' j = cLoad w ℓ D j +
      ((if j = D i then d else 0) - (if j = D v then d else 0)) := by
    intro j
    rw [cLoad_swap D hi hv hiv j]
    by_cases hP : j = D i
    · subst hP
      simp [Ne.symm hne, hne, d]; ring
    · by_cases hQ : j = D v
      · subst hQ; simp [hne, Ne.symm hne, d]; ring
      · simp [Ne.symm hP, Ne.symm hQ, hP, hQ]
  have hdiff : ∑ j, cLoad w ℓ D' j ^ 2 - ∑ j, cLoad w ℓ D j ^ 2 =
      ((cLoad w ℓ D (D i) + d) ^ 2 - cLoad w ℓ D (D i) ^ 2) +
      ((cLoad w ℓ D (D v) - d) ^ 2 - cLoad w ℓ D (D v) ^ 2) := by
    rw [← sum_sub_distrib]
    rw [← sum_subset (subset_univ ({D i, D v} : Finset (Fin k)))]
    · rw [sum_pair hne, hload, hload]
      simp [Ne.symm hne, hne]; ring
    · intro j _ hj
      simp only [mem_insert, mem_singleton, not_or] at hj
      rw [hload]; simp [hj.1, hj.2]
  have : 0 ≤ 2 * d * (cLoad w ℓ D (D i) - cLoad w ℓ D (D v) + d) := by nlinarith
  have h2 : 0 ≤ cLoad w ℓ D (D i) - cLoad w ℓ D (D v) + d := by
    by_contra hc; push_neg at hc; nlinarith
  simp only [d] at h2
  linarith


/-- Auxiliary result for Lemma 3.4 (Section 3). -/
lemma cLoad_congr {D D' : ℕ → Fin k} (h : ∀ i < ℓ, D i = D' i) (j : Fin k) :
    cLoad w ℓ D j = cLoad w ℓ D' j := by
  unfold cLoad
  congr 1
  ext i; simp only [mem_filter, mem_range]
  constructor
  · rintro ⟨hi, h'⟩; exact ⟨hi, (h i hi) ▸ h'⟩
  · rintro ⟨hi, h'⟩; exact ⟨hi, (h i hi).symm ▸ h'⟩

/-- Auxiliary result for Lemma 3.4 (Section 3). -/
lemma cCost2_congr {D D' : ℕ → Fin k} (h : ∀ i < ℓ, D i = D' i) :
    cCost2 w ℓ D = cCost2 w ℓ D' := by
  unfold cCost2
  simp_rw [cLoad_congr h]

/-- Existence of an optimal clique-preserving clustering. -/
lemma exists_cCost2_min (hk0 : 0 < k) :
    ∃ D : ℕ → Fin k, ∀ D' : ℕ → Fin k, cCost2 w ℓ D ≤ cCost2 w ℓ D' := by
  let ext : (Fin ℓ → Fin k) → ℕ → Fin k :=
    fun E i => if h : i < ℓ then E ⟨i, h⟩ else ⟨0, hk0⟩
  obtain ⟨E, -, hE⟩ := exists_min_image (univ : Finset (Fin ℓ → Fin k))
    (fun E => cCost2 w ℓ (ext E)) ⟨fun _ => ⟨0, hk0⟩, mem_univ _⟩
  refine ⟨ext E, fun D' => ?_⟩
  have := hE (fun i => D' i.val) (mem_univ _)
  refine this.trans (le_of_eq (cCost2_congr ?_))
  intro i hi; simp [ext, hi]

/-- Lemma 3.4, lower bound, case `n_{k+1} > a(I)/2` (for an optimal clustering). -/
lemma cCost2_lower_case2 (hs : SortedDesc w ℓ) (hpos : ∀ i < ℓ, 0 < w i) (hk0 : 0 < k)
    (hkl : k < ℓ) (hwk : aParam w ℓ k / 2 < (w k : ℝ)) (D : ℕ → Fin k)
    (hopt : ∀ D' : ℕ → Fin k, cCost2 w ℓ D ≤ cCost2 w ℓ D') :
    (sParam w ℓ k : ℝ) * aParam w ℓ k / 2 ≤ cCost2 w ℓ D := by
  set a := aParam w ℓ k
  -- pigeonhole among the `k + 1` largest cliques
  obtain ⟨u, hu, v, hv, huv, hDuv⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := range (k + 1)) (t := (univ : Finset (Fin k))) (f := D) (by simp)
    (fun _ _ => by simp)
  simp only [mem_range] at hu hv
  have hwu : a / 2 < w u := lt_of_lt_of_le hwk (by exact_mod_cast hs _ _ (by omega) hkl)
  have hwv : a / 2 < w v := lt_of_lt_of_le hwk (by exact_mod_cast hs _ _ (by omega) hkl)
  have huℓ : u < ℓ := by omega
  have hvℓ : v < ℓ := by omega
  -- leaders
  set F : Fin k → Finset ℕ := fun j => (range ℓ).filter (fun i => D i = j)
  have hlead : ∀ j, ∃ m, (F j).Nonempty → m ∈ F j ∧ ∀ x ∈ F j, w x ≤ w m := by
    intro j
    by_cases h : (F j).Nonempty
    · obtain ⟨m, hm, hmax⟩ := exists_max_image (F j) w h
      exact ⟨m, fun _ => ⟨hm, hmax⟩⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose lead hlead using hlead
  set Lset := (univ.image lead) ∩ range ℓ
  have hLcard : Lset.card ≤ k := by
    calc Lset.card ≤ (univ.image lead).card := card_le_card inter_subset_left
      _ ≤ (univ : Finset (Fin k)).card := card_image_le
      _ = k := by simp
  -- key claim
  have claim : ∀ i ∈ range ℓ \ Lset, a / 2 ≤ cLoad w ℓ D (D i) - w i := by
    intro i hi
    simp only [mem_sdiff, mem_range] at hi
    obtain ⟨hiℓ, hiL⟩ := hi
    have hne : (F (D i)).Nonempty := ⟨i, by simp [F, hiℓ]⟩
    obtain ⟨hm, hmax⟩ := hlead (D i) hne
    set m := lead (D i)
    have hmF : m < ℓ ∧ D m = D i := by simpa [F] using hm
    have hmL : m ∈ Lset := by simp [Lset, hmF.1, m]
    have hmi : i ≠ m := fun h => hiL (h ▸ hmL)
    have hwim : (w i : ℝ) ≤ w m := by exact_mod_cast hmax i (by simp [F, hiℓ])
    have h2 := cLoad_ge_two (w := w) D hiℓ hmF.1 hmi hmF.2.symm
    by_cases hwi : a / 2 ≤ w i
    · linarith
    push_neg at hwi
    have hiu : i ≠ u := by rintro rfl; linarith
    have hiv : i ≠ v := by rintro rfl; linarith
    by_cases hDi : D u = D i
    · have h3 := cLoad_ge_three (w := w) D hiℓ huℓ hvℓ hiu hiv huv hDi (hDuv ▸ hDi)
      have : (0 : ℝ) ≤ w v := Nat.cast_nonneg _
      linarith
    · have hsw := swap_ineq (w := w) D hopt hiℓ hvℓ (fun h => hDi (hDuv.trans h.symm))
        (by exact_mod_cast (show (w i : ℝ) < w v by linarith))
      have h4 := cLoad_ge_two (w := w) D huℓ hvℓ huv hDuv
      rw [hDuv] at h4
      linarith
  -- sum up
  rw [cCost2_eq_sum]
  have hNL : (sParam w ℓ k : ℝ) ≤ ∑ i ∈ range ℓ \ Lset, (w i : ℝ) := by
    have hsub : Lset ⊆ range ℓ := inter_subset_right
    have htop := sum_le_sum_top hs Lset hsub hLcard
    rw [min_eq_left hkl.le] at htop
    have hspl := sum_range_eq_add_tailSum (w := w) (ℓ := ℓ) (r := k) hkl.le
    have e : ∑ i ∈ range ℓ \ Lset, w i + ∑ i ∈ Lset, w i = ∑ i ∈ range ℓ, w i :=
      sum_sdiff hsub
    have : sParam w ℓ k ≤ ∑ i ∈ range ℓ \ Lset, w i := by
      unfold sParam; omega
    exact_mod_cast this
  have ha : 0 ≤ a := by
    have hr := rParam_lt hpos hk0 hkl
    exact le_of_lt (lt_of_le_of_lt (Nat.cast_nonneg _)
      (lt_aParam_of_rParam_le hs hr le_rfl (by omega)))
  calc (sParam w ℓ k : ℝ) * a / 2 ≤ (∑ i ∈ range ℓ \ Lset, (w i : ℝ)) * (a / 2) := by
        nlinarith
    _ = ∑ i ∈ range ℓ \ Lset, (w i : ℝ) * (a / 2) := by rw [sum_mul]
    _ ≤ ∑ i ∈ range ℓ \ Lset, (w i : ℝ) * (cLoad w ℓ D (D i) - w i) :=
        sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (claim i hi) (Nat.cast_nonneg _))
    _ ≤ ∑ i ∈ range ℓ, (w i : ℝ) * (cLoad w ℓ D (D i) - w i) := by
        apply sum_le_sum_of_subset_of_nonneg sdiff_subset
        intro i hi _
        have := cLoad_ge_self (w := w) D (mem_range.1 hi)
        exact mul_nonneg (Nat.cast_nonneg _) (by linarith)

/-- Auxiliary result for Lemma 3.4 (Section 3): the sum of squares of the sizes of the cliques
`K_{r+1}, …, K_ℓ` is at most `a(I)` times the total size of the cliques `K_{r+1}, …, K_k`. -/
lemma sum_sq_tail_le (hs : SortedDesc w ℓ) (hpos : ∀ i < ℓ, 0 < w i) (hk0 : 0 < k)
    (hkl : k < ℓ) :
    ∑ i ∈ Ico (rParam w ℓ k) ℓ, (w i : ℝ) ^ 2 ≤
      aParam w ℓ k * ∑ i ∈ Ico (rParam w ℓ k) k, (w i : ℝ) := by
  set r := rParam w ℓ k
  set a := aParam w ℓ k
  have hr : r < k := rParam_lt hpos hk0 hkl
  have htail := tailSum_rParam_eq (w := w) (ℓ := ℓ) hr
  have htail' : ∑ i ∈ Ico r ℓ, (w i : ℝ) = ((k : ℝ) - r) * a := by
    rw [← htail]; unfold tailSum; push_cast; rfl
  have hsplit := sum_Ico_consecutive (fun i => (w i : ℝ)) hr.le hkl.le
  have hsplit2 := sum_Ico_consecutive (fun i => (w i : ℝ) ^ 2) hr.le hkl.le
  set A := ∑ i ∈ Ico r k, (w i : ℝ)
  set s := ∑ i ∈ Ico k ℓ, (w i : ℝ)
  have hAs : A + s = ((k : ℝ) - r) * a := by rw [hsplit]; exact htail'
  have hwk : (w k : ℝ) ≤ w (k - 1) := by exact_mod_cast hs (k - 1) k (by omega) hkl
  have hs0 : 0 ≤ s := sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  -- cliques `K_{k+1}, …`
  have hQ2 : ∑ i ∈ Ico k ℓ, (w i : ℝ) ^ 2 ≤ (w (k - 1) : ℝ) * s := by
    calc ∑ i ∈ Ico k ℓ, (w i : ℝ) ^ 2 ≤ ∑ i ∈ Ico k ℓ, (w i : ℝ) * w (k - 1) := by
          apply sum_le_sum; intro i hi
          simp only [mem_Ico] at hi
          have : (w i : ℝ) ≤ w k := by exact_mod_cast hs k i hi.1 hi.2
          rw [sq]
          exact mul_le_mul_of_nonneg_left (this.trans hwk) (Nat.cast_nonneg _)
      _ = (w (k - 1) : ℝ) * s := by rw [← sum_mul]; ring
  -- cliques `K_{r+1}, …, K_k`
  have hQ1 : (w (k - 1) : ℝ) * (((k : ℝ) - r) * a - A) ≤
      ∑ i ∈ Ico r k, (a - w i) * (w i : ℝ) := by
    have e : ((k : ℝ) - r) * a - A = ∑ i ∈ Ico r k, (a - (w i : ℝ)) := by
      rw [sum_sub_distrib, sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hr.le]
    rw [e, mul_sum]
    apply sum_le_sum; intro i hi
    simp only [mem_Ico] at hi
    have h1 := lt_aParam_of_rParam_le hs hr hi.1 (by omega)
    have h2 : (w (k - 1) : ℝ) ≤ w i := by exact_mod_cast hs i (k - 1) (by omega) (by omega)
    nlinarith
  have hQ1' : ∑ i ∈ Ico r k, (a - w i) * (w i : ℝ) =
      a * A - ∑ i ∈ Ico r k, (w i : ℝ) ^ 2 := by
    simp only [A, mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl; intro i _; ring
  rw [← hsplit2]
  rw [← hAs, add_sub_cancel_left] at hQ1
  nlinarith

/-- **Lemma 3.4 (lower bound, clique level).** For every clique-preserving k-clustering of a
disjoint-cliques instance, twice its cost is at least `2 s(I) a(I) / 2 = s(I) a(I)`; that is, its
cost is at least `s(I) a(I) / 2`. -/
theorem cCost2_lower (hs : SortedDesc w ℓ) (hpos : ∀ i < ℓ, 0 < w i) (hk0 : 0 < k)
    (D : ℕ → Fin k) : (sParam w ℓ k : ℝ) * aParam w ℓ k ≤ cCost2 w ℓ D := by
  by_cases hkl : k < ℓ
  · set r := rParam w ℓ k
    set a := aParam w ℓ k
    have hr : r < k := rParam_lt hpos hk0 hkl
    have ha : 0 < a := lt_of_le_of_lt (Nat.cast_nonneg _)
      (lt_aParam_of_rParam_le hs hr le_rfl (by omega))
    have htail := tailSum_rParam_eq (w := w) (ℓ := ℓ) hr
    have hfrac := sum_sq_cLoad_ge (w := w) (ℓ := ℓ) D r a ha.le (by omega)
      (fun i hi => aParam_le_of_lt_rParam hi) htail
    have hsplit := sum_range_split (ℓ := ℓ) (fun i => (w i : ℝ) ^ 2) (r := r) (by omega)
    have hup := sum_sq_tail_le hs hpos hk0 hkl
    have hsplit1 := sum_Ico_consecutive (fun i => (w i : ℝ)) hr.le hkl.le
    have htail' : ∑ i ∈ Ico r ℓ, (w i : ℝ) = ((k : ℝ) - r) * a := by
      rw [← htail]; unfold tailSum; push_cast; rfl
    have hs' : ∑ i ∈ Ico k ℓ, (w i : ℝ) = sParam w ℓ k := by
      unfold sParam tailSum; push_cast; rfl
    unfold cCost2
    rw [hsplit]
    rw [← hsplit1, hs'] at htail'
    nlinarith
  · have : sParam w ℓ k = 0 := tailSum_eq_zero (not_lt.1 hkl)
    rw [this]; simpa using cCost2_nonneg D

/-- The greedy load-balancing step used in the proof of Lemma 3.4 (upper bound): items placed one
by one into a least-loaded bin of `B`; every item meets a load of at most the final average `A`. -/
lemma greedy_assign (B : Finset (Fin k)) (hB : B.Nonempty) (A : ℝ) (x : ℕ → ℝ)
    (I : Finset ℕ) (hx : ∀ i ∈ I, 0 ≤ x i) :
    ∀ b : Fin k → ℝ, ∑ j ∈ B, b j + ∑ i ∈ I, x i ≤ B.card * A →
    ∃ f : ℕ → Fin k, (∀ i ∈ I, f i ∈ B) ∧
      ∑ j ∈ B, ((b j + ∑ i ∈ I.filter (fun i => f i = j), x i) ^ 2 - b j ^ 2)
        - ∑ i ∈ I, x i ^ 2 ≤ 2 * A * ∑ i ∈ I, x i := by
  induction I using Finset.induction_on with
  | empty =>
    intro b _
    obtain ⟨j0, hj0⟩ := hB
    exact ⟨fun _ => j0, by simp, by simp⟩
  | insert t I ht ih =>
    intro b hb
    have hxI : ∀ i ∈ I, 0 ≤ x i := fun i hi => hx i (mem_insert_of_mem hi)
    have hxt : 0 ≤ x t := hx t (mem_insert_self _ _)
    obtain ⟨j0, hj0B, hj0⟩ := exists_min_image B b hB
    rw [sum_insert ht] at hb
    -- the least loaded bin has load at most `A`
    have hcard : (0 : ℝ) < B.card := by exact_mod_cast hB.card_pos
    have hmin : (B.card : ℝ) * b j0 ≤ ∑ j ∈ B, b j := by
      have := Finset.card_nsmul_le_sum B b (b j0) hj0
      simpa [nsmul_eq_mul] using this
    have hIx : 0 ≤ ∑ i ∈ I, x i := sum_nonneg hxI
    have hbj0 : b j0 ≤ A := by
      by_contra hc; push_neg at hc
      have : (B.card : ℝ) * A < B.card * b j0 := mul_lt_mul_of_pos_left hc hcard
      linarith
    set b' : Fin k → ℝ := Function.update b j0 (b j0 + x t)
    have hb'sum : ∑ j ∈ B, b' j = ∑ j ∈ B, b j + x t := by
      rw [sum_update_of_mem hj0B, ← add_sum_erase B b hj0B, sdiff_singleton_eq_erase]; ring
    obtain ⟨f, hfB, hf⟩ := ih hxI b' (by rw [hb'sum]; linarith)
    refine ⟨fun i => if i = t then j0 else f i, ?_, ?_⟩
    · intro i hi
      by_cases hit : i = t
      · simp [hit, hj0B]
      · simp only [hit, if_false]; exact hfB i ((mem_insert.1 hi).resolve_left hit)
    · have hload : ∀ j ∈ B, b j + ∑ i ∈ (insert t I).filter
          (fun i => (if i = t then j0 else f i) = j), x i =
          b' j + ∑ i ∈ I.filter (fun i => f i = j), x i := by
        intro j _
        rw [filter_insert]
        have hI : I.filter (fun i => (if i = t then j0 else f i) = j) =
            I.filter (fun i => f i = j) := by
          apply filter_congr; intro i hi
          have : i ≠ t := fun h => ht (h ▸ hi)
          simp [this]
        by_cases hj : j0 = j
        · subst hj
          rw [if_pos (by simp), sum_insert (by simp [ht]), hI]
          simp [b']; ring
        · rw [if_neg (by simp [hj]), hI]
          simp [b', Function.update_of_ne (Ne.symm hj)]
      rw [sum_congr rfl (fun j hj => by rw [hload j hj]), sum_insert ht, sum_insert ht]
      have hsq : ∑ j ∈ B, (b' j ^ 2 - b j ^ 2) = 2 * b j0 * x t + x t ^ 2 := by
        rw [← sum_subset (singleton_subset_iff.2 hj0B)]
        · simp [b']; ring
        · intro j _ hj
          have : j ≠ j0 := by simpa using hj
          simp [b', Function.update_of_ne this]
      have e : ∑ j ∈ B, ((b' j + ∑ i ∈ I.filter (fun i => f i = j), x i) ^ 2 - b j ^ 2) =
          ∑ j ∈ B, ((b' j + ∑ i ∈ I.filter (fun i => f i = j), x i) ^ 2 - b' j ^ 2) +
          ∑ j ∈ B, (b' j ^ 2 - b j ^ 2) := by
        rw [← sum_add_distrib]; apply sum_congr rfl; intro j _; ring
      rw [e, hsq]
      nlinarith

/-- **Lemma 3.4 (upper bound, clique level).** There is a clique-preserving k-clustering (the
greedy one: the `k` largest cliques in distinct clusters, the `r(I)` largest alone, the remaining
cliques placed greedily into a least loaded available cluster) whose cost is at most
`s(I) a(I)`, i.e. `cCost2 ≤ 2 s(I) a(I)`. -/
theorem cCost2_upper (hpos : ∀ i < ℓ, 0 < w i) (hk0 : 0 < k) :
    ∃ D : ℕ → Fin k, cCost2 w ℓ D ≤ 2 * (sParam w ℓ k : ℝ) * aParam w ℓ k := by
  set toFin : ℕ → Fin k := fun i => if h : i < k then ⟨i, h⟩ else ⟨0, hk0⟩
  have htoFin : ∀ i, i < k → ((toFin i : Fin k) : ℕ) = i := by
    intro i hi; simp [toFin, hi]
  have hinj : ∀ i, i < k → ∀ i', i' < k → toFin i = toFin i' → i = i' := by
    intro i hi i' hi' h
    have := congrArg (fun x : Fin k => (x : ℕ)) h
    simpa [htoFin i hi, htoFin i' hi'] using this
  by_cases hkl : k < ℓ
  · set r := rParam w ℓ k
    set a := aParam w ℓ k
    have hr : r < k := rParam_lt hpos hk0 hkl
    set B : Finset (Fin k) := (Ico r k).image toFin
    have hinjB : Set.InjOn toFin (Ico r k : Set ℕ) := by
      intro i hi i' hi' h
      simp only [coe_Ico, Set.mem_Ico] at hi hi'
      exact hinj i hi.2 i' hi'.2 h
    have hBne : B.Nonempty := ⟨toFin r, mem_image_of_mem _ (by simp [hr])⟩
    have hBcard : (B.card : ℝ) = (k : ℝ) - r := by
      rw [card_image_of_injOn hinjB]; simp [Nat.cast_sub hr.le]
    set b : Fin k → ℝ := fun j => (w j : ℝ)
    have htail := tailSum_rParam_eq (w := w) (ℓ := ℓ) hr
    have hBsum : ∑ j ∈ B, b j = ∑ i ∈ Ico r k, (w i : ℝ) := by
      rw [sum_image (fun i hi i' hi' h => hinjB hi hi' h)]
      apply sum_congr rfl; intro i hi
      simp only [mem_Ico] at hi
      simp [b, htoFin i hi.2]
    set I := Ico k ℓ
    have hItot : ∑ j ∈ B, b j + ∑ i ∈ I, (w i : ℝ) ≤ B.card * a := by
      rw [hBsum, hBcard, ← htail]
      unfold tailSum
      rw [← sum_Ico_consecutive _ hr.le hkl.le]; push_cast; rfl
    obtain ⟨f, hfB, hf⟩ := greedy_assign B hBne a (fun i => (w i : ℝ)) I
      (fun _ _ => Nat.cast_nonneg _) b hItot
    refine ⟨fun i => if i < k then toFin i else f i, ?_⟩
    set D : ℕ → Fin k := fun i => if i < k then toFin i else f i
    set Y : Fin k → ℝ := fun j => ∑ i ∈ I.filter (fun i => f i = j), (w i : ℝ)
    have hload : ∀ j, cLoad w ℓ D j = b j + Y j := by
      intro j
      unfold cLoad
      rw [sum_filter, sum_range_split _ hkl.le]
      congr 1
      · rw [sum_eq_single (j : ℕ)]
        · simp [D, j.2, b, toFin]
        · intro i hi hij
          simp only [mem_range] at hi
          have : D i ≠ j := by
            simp only [D, hi, if_true]
            intro h; apply hij; rw [← h, htoFin i hi]
          simp [this]
        · intro h; exact absurd (mem_range.2 j.2) h
      · simp only [Y]; rw [sum_filter]
        apply sum_congr rfl; intro i hi
        simp only [mem_Ico] at hi
        simp [D, show ¬ i < k by omega]
    have hYout : ∀ j ∉ B, Y j = 0 := by
      intro j hj
      apply sum_eq_zero; intro i hi
      have := hfB i (mem_filter.1 hi).1
      rw [(mem_filter.1 hi).2] at this
      exact absurd this hj
    have hsqsplit : ∑ i ∈ range ℓ, (w i : ℝ) ^ 2 = ∑ j, b j ^ 2 + ∑ i ∈ I, (w i : ℝ) ^ 2 := by
      rw [sum_range_split _ hkl.le, Fin.sum_univ_eq_sum_range (fun i => (w i : ℝ) ^ 2)]
    have hcost : cCost2 w ℓ D = ∑ j ∈ B, ((b j + Y j) ^ 2 - b j ^ 2) -
        ∑ i ∈ I, (w i : ℝ) ^ 2 := by
      unfold cCost2
      simp_rw [hload]
      rw [hsqsplit]
      have : ∑ j, (b j + Y j) ^ 2 - ∑ j, b j ^ 2 = ∑ j ∈ B, ((b j + Y j) ^ 2 - b j ^ 2) := by
        rw [← sum_sub_distrib]
        symm
        apply sum_subset (subset_univ _)
        intro j _ hj; rw [hYout j hj]; ring
      linarith
    rw [hcost]
    have hs' : ∑ i ∈ I, (w i : ℝ) = sParam w ℓ k := by
      unfold sParam tailSum; push_cast; rfl
    calc _ ≤ 2 * a * ∑ i ∈ I, (w i : ℝ) := hf
      _ = _ := by rw [hs']; ring
  · refine ⟨toFin, ?_⟩
    have hs0 : sParam w ℓ k = 0 := tailSum_eq_zero (not_lt.1 hkl)
    rw [hs0, cCost2_eq_sum]
    simp only [Nat.cast_zero, mul_zero, zero_mul]
    apply le_of_eq
    apply sum_eq_zero; intro i hi
    simp only [mem_range] at hi
    have : cLoad w ℓ toFin (toFin i) = w i := by
      unfold cLoad
      rw [sum_eq_single i]
      · intro i' hi' hne
        simp only [mem_filter, mem_range] at hi'
        exact absurd (hinj i' (by omega) i (by omega) hi'.2) hne
      · intro h; simp [hi] at h
    rw [this]; ring

end CCK
