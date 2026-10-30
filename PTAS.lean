module

public import RequestProject.CliqueBounds

/-!
# Appendix B: the PTAS for offline k-CC on disjoint cliques

We formalize the mathematical content of Claims B.1–B.5 and Lemma B.4 at the level of clique
sizes.  As in `CliqueBounds`, cliques are `0, …, ℓ-1` with sizes `w i`, a clique-preserving
clustering is `D : ℕ → Fin k`, and `cCost2 w ℓ D = ∑_j c_j^2 - ∑_i n_i^2` is twice its cost.
The total size is `n = ∑_i w i` and the average load is `L = n / k`; we avoid division by
writing e.g. `n_i ≥ L` as `k * n_i ≥ n`.

The running-time analysis of the enumeration in Claim B.5 (and of the whole PTAS) is not
formalized; we formalize the structural facts it relies on.
-/

@[expose] public section

open Finset
open scoped Classical

namespace CCK

variable {w : ℕ → ℕ} {ℓ k : ℕ}

/-- Moving a set `S` of cliques, all in cluster `P`, to cluster `Q`. -/
lemma cLoad_move (D : ℕ → Fin k) (S : Finset ℕ) (hS : S ⊆ range ℓ) (P Q : Fin k)
    (hSP : ∀ i ∈ S, D i = P) (j : Fin k) :
    cLoad w ℓ (fun i => if i ∈ S then Q else D i) j =
      cLoad w ℓ D j + (if Q = j then ∑ i ∈ S, (w i : ℝ) else 0) -
        (if P = j then ∑ i ∈ S, (w i : ℝ) else 0) := by
  unfold cLoad
  rw [sum_filter, sum_filter]
  have hpt : ∀ i, (if (if i ∈ S then Q else D i) = j then (w i : ℝ) else 0) =
      (if D i = j then (w i : ℝ) else 0) +
        (if i ∈ S then ((if Q = j then (w i : ℝ) else 0) - (if P = j then (w i : ℝ) else 0))
          else 0) := by
    intro i
    by_cases hi : i ∈ S
    · simp [hi, hSP i hi]
    · simp [hi]
  rw [sum_congr rfl (fun i _ => hpt i), sum_add_distrib, sum_ite_mem, inter_eq_right.2 hS,
    sum_sub_distrib]
  by_cases hQ : Q = j <;> by_cases hP : P = j <;> simp [hQ, hP]; ring

/-- Change of `cCost2` when moving a set `S` of cliques from cluster `P` to cluster `Q ≠ P`:
`Δ = 2 s (c_Q - c_P + s)` where `s = ∑_{i∈S} n_i`. -/
lemma cCost2_move (D : ℕ → Fin k) (S : Finset ℕ) (hS : S ⊆ range ℓ) {P Q : Fin k}
    (hPQ : P ≠ Q) (hSP : ∀ i ∈ S, D i = P) :
    cCost2 w ℓ (fun i => if i ∈ S then Q else D i) = cCost2 w ℓ D +
      2 * (∑ i ∈ S, (w i : ℝ)) * (cLoad w ℓ D Q - cLoad w ℓ D P + ∑ i ∈ S, (w i : ℝ)) := by
  unfold cCost2
  set s := ∑ i ∈ S, (w i : ℝ)
  have hdiff : ∑ j, cLoad w ℓ (fun i => if i ∈ S then Q else D i) j ^ 2 -
      ∑ j, cLoad w ℓ D j ^ 2 = ((cLoad w ℓ D P - s) ^ 2 - cLoad w ℓ D P ^ 2) +
        ((cLoad w ℓ D Q + s) ^ 2 - cLoad w ℓ D Q ^ 2) := by
    rw [← sum_sub_distrib, ← sum_subset (subset_univ ({P, Q} : Finset (Fin k)))]
    · rw [sum_pair hPQ, cLoad_move D S hS P Q hSP, cLoad_move D S hS P Q hSP]
      simp [hPQ, Ne.symm hPQ]; ring
    · intro j _ hj
      simp only [mem_insert, mem_singleton, not_or] at hj
      rw [cLoad_move D S hS P Q hSP]
      simp [Ne.symm hj.1, Ne.symm hj.2]
  linarith

/-- Auxiliary result for Appendix B (the PTAS of Theorem 1 for disjoint cliques). -/
lemma sum_cLoad_eq (D : ℕ → Fin k) : ∑ j, cLoad w ℓ D j = ∑ i ∈ range ℓ, (w i : ℝ) :=
  sum_cLoad D _ _

/-- Auxiliary result for Appendix B (the PTAS of Theorem 1 for disjoint cliques). -/
lemma cLoad_nonneg (D : ℕ → Fin k) (j : Fin k) : 0 ≤ cLoad w ℓ D j :=
  sum_nonneg (fun _ _ => Nat.cast_nonneg _)

/-- A positive load means the cluster contains a clique. -/
lemma exists_mem_of_cLoad_pos (D : ℕ → Fin k) (j : Fin k) (h : 0 < cLoad w ℓ D j) :
    ∃ i < ℓ, D i = j := by
  by_contra hc
  push_neg at hc
  have : cLoad w ℓ D j = 0 := by
    unfold cLoad
    apply sum_eq_zero; intro i hi
    simp only [mem_filter, mem_range] at hi
    exact absurd hi.2 (hc i hi.1)
  linarith

/-- Optimality applied to moving a single clique `i` to cluster `Q`: `c_P - n_i ≤ c_Q`. -/
lemma move_one_ineq (D : ℕ → Fin k) (hopt : ∀ D' : ℕ → Fin k, cCost2 w ℓ D ≤ cCost2 w ℓ D')
    (hpos : ∀ i < ℓ, 0 < w i) {i : ℕ} (hi : i < ℓ) {Q : Fin k} (hQ : D i ≠ Q) :
    cLoad w ℓ D (D i) - w i ≤ cLoad w ℓ D Q := by
  have h := hopt (fun x => if x ∈ ({i} : Finset ℕ) then Q else D x)
  rw [cCost2_move D {i} (by simp [hi]) hQ (by simp)] at h
  simp only [sum_singleton] at h
  have hw : (0 : ℝ) < w i := by exact_mod_cast hpos i hi
  nlinarith

/-- A cluster other than `P` with load at most the average of the other clusters. -/
lemma exists_other_le_avg (D : ℕ → Fin k) (hk : 2 ≤ k) (P : Fin k) :
    ∃ Q, Q ≠ P ∧ ((k : ℝ) - 1) * cLoad w ℓ D Q ≤ ∑ i ∈ range ℓ, (w i : ℝ) - cLoad w ℓ D P := by
  have hne : (univ.erase P).Nonempty := by
    obtain ⟨Q, hQ⟩ : ∃ Q : Fin k, Q ≠ P := by
      by_cases h : (P : ℕ) = 0
      · exact ⟨⟨1, by omega⟩, fun h' => by simp [Fin.ext_iff] at h'; omega⟩
      · exact ⟨⟨0, by omega⟩, fun h' => h (by simp [Fin.ext_iff] at h'; omega)⟩
    exact ⟨Q, by simp [hQ]⟩
  obtain ⟨Q, hQ, hmin⟩ := exists_min_image (univ.erase P) (cLoad w ℓ D) hne
  refine ⟨Q, (mem_erase.1 hQ).1, ?_⟩
  have h1 : ((univ.erase P).card : ℝ) * cLoad w ℓ D Q ≤ ∑ j ∈ univ.erase P, cLoad w ℓ D j := by
    have := Finset.card_nsmul_le_sum _ _ _ hmin
    simpa [nsmul_eq_mul] using this
  have h2 : ∑ j ∈ univ.erase P, cLoad w ℓ D j = ∑ i ∈ range ℓ, (w i : ℝ) - cLoad w ℓ D P := by
    rw [← sum_cLoad_eq D, ← add_sum_erase univ _ (mem_univ P)]; ring
  have h3 : ((univ.erase P).card : ℝ) = k - 1 := by
    rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin, Nat.cast_sub (by omega)]
    simp
  rw [h3, h2] at h1; exact h1

/-- **Claim B.1.** If a clique has size `n_i ≥ L = n/k`, then in any optimal solution it
occupies its own cluster: no other clique is placed in the same cluster.  (Hence, after peeling
off such cliques, without loss of generality every clique has size `< L`.) -/
theorem claim_B_1 (hpos : ∀ i < ℓ, 0 < w i) (D : ℕ → Fin k)
    (hopt : ∀ D' : ℕ → Fin k, cCost2 w ℓ D ≤ cCost2 w ℓ D') {i : ℕ} (hi : i < ℓ)
    (hL : (∑ i ∈ range ℓ, (w i : ℝ)) ≤ k * w i) {i' : ℕ} (hi' : i' < ℓ) (hne : i' ≠ i) :
    D i' ≠ D i := by
  intro hD
  have hk : 0 < k := Fin.pos (D i)
  have h2 := cLoad_ge_two (w := w) D hi hi' (Ne.symm hne) hD.symm
  have hw' : (0 : ℝ) < w i' := by exact_mod_cast hpos i' hi'
  have hn : cLoad w ℓ D (D i) ≤ ∑ i ∈ range ℓ, (w i : ℝ) := by
    rw [← sum_cLoad_eq D]
    exact single_le_sum (fun j _ => cLoad_nonneg D j) (mem_univ _)
  rcases Nat.lt_or_ge k 2 with hk1 | hk2
  · have : k = 1 := by omega
    subst this
    simp at hL
    linarith
  · obtain ⟨Q, hQ, hQavg⟩ := exists_other_le_avg (w := w) (ℓ := ℓ) D hk2 (D i)
    have hmove := move_one_ineq D hopt hpos hi' (Q := Q) (by rw [hD]; exact Ne.symm hQ)
    rw [hD] at hmove
    have hk1 : (1 : ℝ) ≤ (k : ℝ) - 1 := by
      have : (2 : ℝ) ≤ k := by exact_mod_cast hk2
      linarith
    have hcQ : (w i : ℝ) ≤ cLoad w ℓ D Q := by linarith
    have : ((k : ℝ) - 1) * w i ≤ ((k : ℝ) - 1) * cLoad w ℓ D Q :=
      mul_le_mul_of_nonneg_left hcQ (by linarith)
    nlinarith

/-- **Claim B.2.** If every clique has size `< L = n/k` (and there is at least one clique), then
every optimal k-clustering has all cluster loads strictly between `L/2` and `2L`. -/
theorem claim_B_2 (hpos : ∀ i < ℓ, 0 < w i) (hℓ : 0 < ℓ) (D : ℕ → Fin k)
    (hopt : ∀ D' : ℕ → Fin k, cCost2 w ℓ D ≤ cCost2 w ℓ D')
    (hsmall : ∀ i < ℓ, (k : ℝ) * w i < ∑ i ∈ range ℓ, (w i : ℝ)) (j : Fin k) :
    (∑ i ∈ range ℓ, (w i : ℝ)) < 2 * k * cLoad w ℓ D j ∧
      (k : ℝ) * cLoad w ℓ D j < 2 * ∑ i ∈ range ℓ, (w i : ℝ) := by
  set n := ∑ i ∈ range ℓ, (w i : ℝ)
  have hk : (0 : ℝ) < k := by exact_mod_cast Fin.pos j
  have hn : 0 < n := by
    have := hsmall 0 hℓ
    have : (0 : ℝ) < w 0 := by exact_mod_cast hpos 0 hℓ
    nlinarith
  -- a cluster with load at most average and one with load at least average
  obtain ⟨jmin, -, hjmin⟩ := exists_min_image univ (cLoad w ℓ D) ⟨j, mem_univ _⟩
  obtain ⟨jmax, -, hjmax⟩ := exists_max_image univ (cLoad w ℓ D) ⟨j, mem_univ _⟩
  have hsum := sum_cLoad_eq (w := w) (ℓ := ℓ) D
  have hminavg : (k : ℝ) * cLoad w ℓ D jmin ≤ n := by
    have := Finset.card_nsmul_le_sum univ (cLoad w ℓ D) _ (fun j _ => hjmin j (mem_univ _))
    simp only [card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    linarith
  constructor
  · by_contra hc
    push_neg at hc
    -- cluster `j` is small; some cluster has load `> L`
    have hmaxavg : n < (k : ℝ) * cLoad w ℓ D jmax := by
      by_contra hc'
      push_neg at hc'
      -- all loads ≤ L, and load of j ≤ L/2 < L, so total < n
      have hlt : ∑ j', cLoad w ℓ D j' < ∑ _j' : Fin k, n / k := by
        apply sum_lt_sum
        · intro j' _
          have := hjmax j' (mem_univ _)
          rw [le_div_iff₀ hk]; nlinarith
        · refine ⟨j, mem_univ _, ?_⟩
          rw [lt_div_iff₀ hk]; nlinarith
      simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hlt
      rw [mul_div_cancel₀ _ hk.ne'] at hlt
      linarith
    have hpj : 0 < cLoad w ℓ D jmax := by
      by_contra h; push_neg at h; nlinarith
    -- the smallest clique in cluster `jmax`
    set F := (range ℓ).filter (fun i => D i = jmax)
    obtain ⟨i0, hi0⟩ := exists_mem_of_cLoad_pos D jmax hpj
    have hFne : F.Nonempty := ⟨i0, by simp [F, hi0.1, hi0.2]⟩
    obtain ⟨i, hiF, himin⟩ := exists_min_image F w hFne
    have hiF' : i < ℓ ∧ D i = jmax := by simpa [F] using hiF
    -- cluster `jmax` contains another clique
    have hother : ∃ i' ∈ F, i' ≠ i := by
      by_contra h
      push_neg at h
      have hceq : cLoad w ℓ D jmax = w i := by
        unfold cLoad
        rw [sum_eq_single i]
        · intro b hb hbi; exact absurd (h b hb) hbi
        · intro h'; exact absurd hiF h'
      have := hsmall i hiF'.1
      rw [hceq] at hmaxavg
      linarith
    obtain ⟨i', hi'F, hi'i⟩ := hother
    have hi'F' : i' < ℓ ∧ D i' = jmax := by simpa [F] using hi'F
    have h2 := cLoad_ge_two (w := w) D hiF'.1 hi'F'.1 (Ne.symm hi'i)
      (hiF'.2.trans hi'F'.2.symm)
    rw [hiF'.2] at h2
    have hwii' : (w i : ℝ) ≤ w i' := by exact_mod_cast himin i' hi'F
    have hjne : jmax ≠ j := by
      rintro rfl; nlinarith
    have hmove := move_one_ineq D hopt hpos hiF'.1 (Q := j) (by rw [hiF'.2]; exact hjne)
    rw [hiF'.2] at hmove
    nlinarith
  · by_contra hc
    push_neg at hc
    have hpj : 0 < cLoad w ℓ D j := by
      by_contra h; push_neg at h; nlinarith
    obtain ⟨i, hi, hDi⟩ := exists_mem_of_cLoad_pos D j hpj
    have hjne : j ≠ jmin := by rintro rfl; nlinarith
    have hmove := move_one_ineq D hopt hpos hi (Q := jmin) (by rw [hDi]; exact hjne)
    rw [hDi] at hmove
    have := hsmall i hi
    nlinarith

/-- **Claim B.5 (load bound).** In any optimal packing (for any positive object sizes), every
cluster has load at most the average load plus the largest object size: `c_B ≤ L + w_max`. -/
theorem claim_B_5_load_bound (hpos : ∀ i < ℓ, 0 < w i) (D : ℕ → Fin k)
    (hopt : ∀ D' : ℕ → Fin k, cCost2 w ℓ D ≤ cCost2 w ℓ D') (wmax : ℝ) (hwm0 : 0 ≤ wmax)
    (hwmax : ∀ i < ℓ, (w i : ℝ) ≤ wmax) (j : Fin k) :
    (k : ℝ) * cLoad w ℓ D j ≤ ∑ i ∈ range ℓ, (w i : ℝ) + k * wmax := by
  have hk : (0 : ℝ) < k := by exact_mod_cast Fin.pos j
  by_contra hc
  push_neg at hc
  obtain ⟨jmin, -, hjmin⟩ := exists_min_image univ (cLoad w ℓ D) ⟨j, mem_univ _⟩
  have hsum := sum_cLoad_eq (w := w) (ℓ := ℓ) D
  have hminavg : (k : ℝ) * cLoad w ℓ D jmin ≤ ∑ i ∈ range ℓ, (w i : ℝ) := by
    have := Finset.card_nsmul_le_sum univ (cLoad w ℓ D) _ (fun j _ => hjmin j (mem_univ _))
    simp only [card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    linarith
  have hpj : 0 < cLoad w ℓ D j := by
    by_contra h'; push_neg at h'
    have : 0 ≤ ∑ i ∈ range ℓ, (w i : ℝ) := sum_nonneg (fun _ _ => Nat.cast_nonneg _)
    nlinarith
  obtain ⟨i, hi, hDi⟩ := exists_mem_of_cLoad_pos D j hpj
  have hjne : j ≠ jmin := by
    rintro rfl
    have := hwmax i hi
    have : (0 : ℝ) < w i := by exact_mod_cast hpos i hi
    nlinarith
  have hmove := move_one_ineq D hopt hpos hi (Q := jmin) (by rw [hDi]; exact hjne)
  rw [hDi] at hmove
  have := hwmax i hi
  nlinarith

end CCK
