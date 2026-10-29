module

public import RequestProject.PTAS

/-!
# Appendix B (continued): Lemma B.4, Claim B.3 and Claim B.5
-/

@[expose] public section

open Finset
open scoped Classical

namespace CCK

variable {w : ℕ → ℕ} {ℓ k : ℕ}

/-- **Lemma B.4.** In a clique-preserving clustering, let `G₁, G₂` be disjoint unions of whole
cliques lying in two different clusters `Q` and `P`, with loads excluding them `x = c_Q - g₁`
and `y = c_P - g₂`.  Moving `G₂` into `G₁`'s cluster (if `x ≤ y`; otherwise `G₁` into `G₂`'s)
changes the cost by at most `|G₁| |G₂|` (i.e. `cCost2` by at most `2 |G₁| |G₂|`), the result is
again clique-preserving, and only cliques of `G₁ ∪ G₂` move. -/
theorem lemma_B_4 (D : ℕ → Fin k) (G₁ G₂ : Finset ℕ) (h₁ : G₁ ⊆ range ℓ) (h₂ : G₂ ⊆ range ℓ)
    {P Q : Fin k} (hPQ : P ≠ Q) (hG₁ : ∀ i ∈ G₁, D i = Q) (hG₂ : ∀ i ∈ G₂, D i = P) :
    ∃ D' : ℕ → Fin k, (∀ i, i ∉ G₁ ∪ G₂ → D' i = D i) ∧
      (∀ i ∈ G₁ ∪ G₂, ∀ i' ∈ G₁ ∪ G₂, D' i = D' i') ∧
      cCost2 w ℓ D' ≤ cCost2 w ℓ D +
        2 * (∑ i ∈ G₁, (w i : ℝ)) * (∑ i ∈ G₂, (w i : ℝ)) := by
  set g₁ := ∑ i ∈ G₁, (w i : ℝ)
  set g₂ := ∑ i ∈ G₂, (w i : ℝ)
  have hg₁ : 0 ≤ g₁ := sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have hg₂ : 0 ≤ g₂ := sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have hdisj : Disjoint G₁ G₂ := by
    rw [disjoint_left]; intro i hi1 hi2
    exact hPQ ((hG₂ i hi2).symm.trans (hG₁ i hi1))
  by_cases hxy : cLoad w ℓ D Q - g₁ ≤ cLoad w ℓ D P - g₂
  · refine ⟨fun i => if i ∈ G₂ then Q else D i, ?_, ?_, ?_⟩
    · intro i hi; simp only [mem_union, not_or] at hi; simp [hi.2]
    · intro i hi i' hi'
      have e : ∀ x ∈ G₁ ∪ G₂, (if x ∈ G₂ then Q else D x) = Q := by
        intro x hx
        by_cases hx2 : x ∈ G₂
        · simp [hx2]
        · simp only [hx2, if_false]
          exact hG₁ x ((mem_union.1 hx).resolve_right hx2)
      exact (e i hi).trans (e i' hi').symm
    · rw [cCost2_move D G₂ h₂ hPQ hG₂]
      nlinarith
  · push_neg at hxy
    refine ⟨fun i => if i ∈ G₁ then P else D i, ?_, ?_, ?_⟩
    · intro i hi; simp only [mem_union, not_or] at hi; simp [hi.1]
    · intro i hi i' hi'
      have e : ∀ x ∈ G₁ ∪ G₂, (if x ∈ G₁ then P else D x) = P := by
        intro x hx
        by_cases hx1 : x ∈ G₁
        · simp [hx1]
        · simp only [hx1, if_false]
          exact hG₂ x ((mem_union.1 hx).resolve_left hx1)
      exact (e i hi).trans (e i' hi').symm
    · rw [cCost2_move D G₁ h₁ (Ne.symm hPQ) hG₁]
      nlinarith

/-- Merging all cliques of a set `T` into one cluster by repeated application of Lemma B.4
(proof of (49)): the increase of `cCost2` is at most `(∑_T n_i)^2 - ∑_T n_i^2`, i.e. the cost
increases by at most `Δ_T = ∑_{i<j ∈ T} n_i n_j`. -/
lemma merge_finset (T : Finset ℕ) (hT : T ⊆ range ℓ) :
    ∀ D : ℕ → Fin k, ∃ D' : ℕ → Fin k, (∀ i, i ∉ T → D' i = D i) ∧
      (∀ i ∈ T, ∀ i' ∈ T, D' i = D' i') ∧
      cCost2 w ℓ D' ≤ cCost2 w ℓ D + ((∑ i ∈ T, (w i : ℝ)) ^ 2 - ∑ i ∈ T, (w i : ℝ) ^ 2) := by
  induction T using Finset.induction_on with
  | empty => intro D; exact ⟨D, fun _ _ => rfl, by simp, by simp⟩
  | insert x T hx ih =>
    intro D
    have hT' : T ⊆ range ℓ := (subset_insert _ _).trans hT
    have hxl : x ∈ range ℓ := hT (mem_insert_self _ _)
    obtain ⟨D₁, hD₁out, hD₁const, hD₁cost⟩ := ih hT' D
    have hD₁x : D₁ x = D x := hD₁out x hx
    rcases T.eq_empty_or_nonempty with hTe | ⟨y, hy⟩
    · subst hTe
      refine ⟨D, fun _ _ => rfl, ?_, by simp⟩
      intro i hi i' hi'; simp only [insert_empty_eq, mem_singleton] at hi hi'; rw [hi, hi']
    · have hsq : ((∑ i ∈ insert x T, (w i : ℝ)) ^ 2 - ∑ i ∈ insert x T, (w i : ℝ) ^ 2) =
          ((∑ i ∈ T, (w i : ℝ)) ^ 2 - ∑ i ∈ T, (w i : ℝ) ^ 2) +
            2 * (∑ i ∈ T, (w i : ℝ)) * (w x : ℝ) := by
        rw [sum_insert hx, sum_insert hx]; ring
      by_cases hco : D₁ x = D₁ y
      · refine ⟨D₁, ?_, ?_, ?_⟩
        · intro i hi; exact hD₁out i (fun h => hi (mem_insert_of_mem h))
        · intro i hi i' hi'
          have e : ∀ z ∈ insert x T, D₁ z = D₁ y := by
            intro z hz
            rcases mem_insert.1 hz with rfl | hz
            · exact hco
            · exact hD₁const z hz y hy
          rw [e i hi, e i' hi']
        · rw [hsq]
          have : 0 ≤ 2 * (∑ i ∈ T, (w i : ℝ)) * (w x : ℝ) := by positivity
          linarith
      · obtain ⟨D₂, hD₂out, hD₂const, hD₂cost⟩ := lemma_B_4 (w := w) D₁ T {x} hT'
          (by simpa using hxl) (P := D₁ x) (Q := D₁ y) hco
          (fun i hi => hD₁const i hi y hy) (by simp)
        refine ⟨D₂, ?_, ?_, ?_⟩
        · intro i hi
          have h1 : i ∉ T ∪ {x} := by simp only [mem_union, mem_singleton]; intro h
                                      rcases h with h | h
                                      · exact hi (mem_insert_of_mem h)
                                      · exact hi (h ▸ mem_insert_self _ _)
          rw [hD₂out i h1]; exact hD₁out i (fun h => hi (mem_insert_of_mem h))
        · intro i hi i' hi'
          apply hD₂const
          · rcases mem_insert.1 hi with rfl | h
            · simp
            · simp [h]
          · rcases mem_insert.1 hi' with rfl | h
            · simp
            · simp [h]
        · rw [hsq]
          simp only [sum_singleton] at hD₂cost
          linarith

/-- The clustering respects the grouping `g` (cliques with the same label share a cluster). -/
def Respects (ℓ : ℕ) (g : ℕ → ℕ) {k : ℕ} (D : ℕ → Fin k) : Prop :=
  ∀ i < ℓ, ∀ i' < ℓ, g i = g i' → D i = D i'

/-- Total size of the group (macro-clique) of clique `i`. -/
noncomputable def groupLoad (w : ℕ → ℕ) (ℓ : ℕ) (g : ℕ → ℕ) (i : ℕ) : ℝ :=
  ∑ i' ∈ (range ℓ).filter (fun i' => g i' = g i), (w i' : ℝ)

/-- Twice `Δ = ∑_M Δ_M`, the number of vertex pairs lying in two different constituent cliques of
a common macro-clique (proof of Claim B.3). -/
noncomputable def twoDelta (w : ℕ → ℕ) (ℓ : ℕ) (g : ℕ → ℕ) : ℝ :=
  ∑ i ∈ range ℓ, (w i : ℝ) * (groupLoad w ℓ g i - w i)

/-- Proof of (49): there is a k-clustering respecting the macro-cliques whose cost exceeds the
cost of any given clustering by at most `Δ`. -/
lemma exists_respects_le (g : ℕ → ℕ) (D : ℕ → Fin k) :
    ∃ D' : ℕ → Fin k, Respects ℓ g D' ∧ cCost2 w ℓ D' ≤ cCost2 w ℓ D + twoDelta w ℓ g := by
  set M : ℕ → Finset ℕ := fun m => (range ℓ).filter (fun i => g i = m)
  have hMsub : ∀ m, M m ⊆ range ℓ := fun m => filter_subset _ _
  have key : ∀ labels : Finset ℕ, ∃ D' : ℕ → Fin k,
      (∀ m ∈ labels, ∀ i ∈ M m, ∀ i' ∈ M m, D' i = D' i') ∧
      cCost2 w ℓ D' ≤ cCost2 w ℓ D +
        ∑ m ∈ labels, ((∑ i ∈ M m, (w i : ℝ)) ^ 2 - ∑ i ∈ M m, (w i : ℝ) ^ 2) := by
    intro labels
    induction labels using Finset.induction_on with
    | empty => exact ⟨D, by simp, by simp⟩
    | insert m labels hm ih =>
      obtain ⟨D₁, hD₁, hD₁c⟩ := ih
      obtain ⟨D₂, hD₂out, hD₂const, hD₂c⟩ := merge_finset (w := w) (M m) (hMsub m) D₁
      refine ⟨D₂, ?_, ?_⟩
      · intro m' hm' i hi i' hi'
        rcases mem_insert.1 hm' with rfl | hm'
        · exact hD₂const i hi i' hi'
        · have hne : m' ≠ m := fun h => hm (h ▸ hm')
          have hio : ∀ z ∈ M m', z ∉ M m := by
            intro z hz hz'
            simp only [M, mem_filter] at hz hz'
            exact hne (hz.2.symm.trans hz'.2)
          rw [hD₂out i (hio i hi), hD₂out i' (hio i' hi')]
          exact hD₁ m' hm' i hi i' hi'
      · rw [sum_insert hm]; linarith
  obtain ⟨D', hD', hc⟩ := key ((range ℓ).image g)
  refine ⟨D', ?_, ?_⟩
  · intro i hi i' hi' hg
    exact hD' (g i) (mem_image_of_mem _ (mem_range.2 hi)) i (by simp [M, hi])
      i' (by simp [M, hi', hg])
  · refine hc.trans (le_of_eq ?_)
    congr 1
    unfold twoDelta
    rw [← sum_fiberwise_of_maps_to (g := g) (t := (range ℓ).image g)
      (fun i hi => mem_image_of_mem _ hi)]
    apply sum_congr rfl; intro m _
    have hgl : ∀ i ∈ (range ℓ).filter (fun i => g i = m),
        groupLoad w ℓ g i = ∑ i ∈ M m, (w i : ℝ) := by
      intro i hi
      simp only [mem_filter] at hi
      unfold groupLoad; rw [hi.2]
    symm
    calc ∑ i ∈ (range ℓ).filter (fun i => g i = m), (w i : ℝ) * (groupLoad w ℓ g i - w i)
        = ∑ i ∈ M m, (w i : ℝ) * (∑ i ∈ M m, (w i : ℝ) - w i) :=
          sum_congr rfl (fun i hi => by rw [hgl i hi])
      _ = _ := by
          simp only [mul_sub, sum_sub_distrib, ← sum_mul, sq]

/-- **Claim B.3 (Part 2).**  Let `ε ∈ (0, 1/8]` and suppose every clique has size `< L = n/k`.
Let `g` group the cliques into macro-cliques such that every clique lying in a macro-clique with
at least two constituent cliques is small (size `< εL`) and every such macro-clique has total
size `< 2εL` (cliques of size `≥ εL` are kept unchanged, i.e. form their own group).  Then
the optimal k-clustering of the grouped instance `J` (clusterings that keep every macro-clique
together) is at most `(1 + 8ε)` times the optimum of `I`: `OPT(J) ≤ (1 + O(ε)) OPT(I)`.
(Part 1 of Claim B.3 — a clustering of `J` is a clustering of `I` with the same cost — holds by
construction, since we measure the cost of `J`-clusterings with `cCost2` of `I`.) -/
theorem claim_B_3 (hpos : ∀ i < ℓ, 0 < w i) (hℓ : 0 < ℓ) (hk : 0 < k) {ε : ℝ} (hε0 : 0 < ε)
    (hε : ε ≤ 1 / 8) (hsmall : ∀ i < ℓ, (k : ℝ) * w i < ∑ i ∈ range ℓ, (w i : ℝ))
    (g : ℕ → ℕ)
    (hg_small : ∀ i < ℓ, ∀ i' < ℓ, i' ≠ i → g i' = g i →
      (k : ℝ) * w i < ε * ∑ i ∈ range ℓ, (w i : ℝ))
    (hg_size : ∀ i < ℓ, ∀ i' < ℓ, i' ≠ i → g i' = g i →
      (k : ℝ) * groupLoad w ℓ g i < 2 * ε * ∑ i ∈ range ℓ, (w i : ℝ)) :
    ∃ D : ℕ → Fin k, Respects ℓ g D ∧ ∀ D' : ℕ → Fin k, cCost2 w ℓ D ≤ (1 + 8 * ε) * cCost2 w ℓ D' := by
  set n := ∑ i ∈ range ℓ, (w i : ℝ)
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  obtain ⟨D₀, hD₀⟩ := exists_cCost2_min (w := w) (ℓ := ℓ) hk
  obtain ⟨D, hDr, hDc⟩ := exists_respects_le (w := w) (ℓ := ℓ) g D₀
  refine ⟨D, hDr, fun D' => ?_⟩
  -- (50): `2Δ ≤ 8 ε cCost2(D₀)`
  set S := (range ℓ).filter (fun i => ∃ i' < ℓ, i' ≠ i ∧ g i' = g i)
  have hgl_self : ∀ i < ℓ, (w i : ℝ) ≤ groupLoad w ℓ g i := by
    intro i hi
    unfold groupLoad
    exact single_le_sum (f := fun i => (w i : ℝ)) (fun _ _ => Nat.cast_nonneg _)
      (by simp [hi])
  have hgl_triv : ∀ i < ℓ, i ∉ S → groupLoad w ℓ g i = w i := by
    intro i hi hiS
    unfold groupLoad
    rw [sum_eq_single i]
    · intro b hb hbi
      simp only [mem_filter, mem_range] at hb
      have h' := hiS
      simp only [S, mem_filter, mem_range, hi, true_and, not_exists, not_and] at h'
      exact absurd hb.2 (h' b hb.1 hbi)
    · intro h; simp [hi] at h
  have h2Δ : twoDelta w ℓ g ≤ ∑ i ∈ S, (w i : ℝ) * (2 * ε * n / k) := by
    unfold twoDelta
    rw [← sum_filter_add_sum_filter_not (range ℓ) (fun i => ∃ i' < ℓ, i' ≠ i ∧ g i' = g i)]
    have h0 : ∑ i ∈ (range ℓ).filter (fun i => ¬ ∃ i' < ℓ, i' ≠ i ∧ g i' = g i),
        (w i : ℝ) * (groupLoad w ℓ g i - w i) = 0 := by
      apply sum_eq_zero; intro i hi
      simp only [mem_filter, mem_range] at hi
      rw [hgl_triv i hi.1 (by simp [S, hi.2])]; ring
    rw [h0, add_zero]
    apply sum_le_sum; intro i hi
    simp only [mem_filter, mem_range] at hi
    obtain ⟨hi, i', hi', hne, hg⟩ := hi
    have := hg_size i hi i' hi' hne hg
    have hb : groupLoad w ℓ g i ≤ 2 * ε * n / k := by
      rw [le_div_iff₀ hkr]; linarith
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    have : (0 : ℝ) ≤ w i := Nat.cast_nonneg _
    linarith
  have hopt : ∑ i ∈ S, (w i : ℝ) * ((1 / 2 - ε) * n / k) ≤ cCost2 w ℓ D₀ := by
    rw [cCost2_eq_sum]
    calc ∑ i ∈ S, (w i : ℝ) * ((1 / 2 - ε) * n / k)
        ≤ ∑ i ∈ S, (w i : ℝ) * (cLoad w ℓ D₀ (D₀ i) - w i) := by
          apply sum_le_sum; intro i hi
          simp only [S, mem_filter, mem_range] at hi
          obtain ⟨hi, i', hi', hne, hg⟩ := hi
          have hB2 := (claim_B_2 hpos hℓ D₀ hD₀ hsmall (D₀ i)).1
          have hsm := hg_small i hi i' hi' hne hg
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
          rw [div_le_iff₀ hkr]
          nlinarith
      _ ≤ ∑ i ∈ range ℓ, (w i : ℝ) * (cLoad w ℓ D₀ (D₀ i) - w i) := by
          apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          intro i hi _
          have := cLoad_ge_self (w := w) D₀ (mem_range.1 hi)
          exact mul_nonneg (Nat.cast_nonneg _) (by linarith)
  set W := ∑ i ∈ S, (w i : ℝ)
  have hW : 0 ≤ W := sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have hn : 0 ≤ n := sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  rw [← sum_mul] at h2Δ hopt
  have hfinal : twoDelta w ℓ g ≤ 8 * ε * cCost2 w ℓ D₀ := by
    have h1 : W * (2 * ε * n / k) = (4 * ε / (1 - 2 * ε)) * (W * ((1 / 2 - ε) * n / k)) := by
      have h12 : (1 - 2 * ε) ≠ 0 := by intro h; linarith
      field_simp
      ring
    have h2 : 4 * ε / (1 - 2 * ε) ≤ 8 * ε := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    have h3 : 0 ≤ W * ((1 / 2 - ε) * n / k) := by
      apply mul_nonneg hW; apply div_nonneg _ hkr.le; nlinarith
    calc twoDelta w ℓ g ≤ W * (2 * ε * n / k) := h2Δ
      _ = (4 * ε / (1 - 2 * ε)) * (W * ((1 / 2 - ε) * n / k)) := h1
      _ ≤ (8 * ε) * (W * ((1 / 2 - ε) * n / k)) := mul_le_mul_of_nonneg_right h2 h3
      _ ≤ 8 * ε * cCost2 w ℓ D₀ := mul_le_mul_of_nonneg_left hopt (by linarith)
  have hD₀' := hD₀ D'
  have hnn := cCost2_nonneg (w := w) (ℓ := ℓ) D₀
  nlinarith

end CCK

namespace CCK

/-- Twice the packing cost for real-valued object sizes `x` (used for the rounded instance `K`
of Claim B.5): `∑_j (∑_{i ∈ B_j} x_i)^2 - ∑_i x_i^2`, i.e. twice the sum over pairs of distinct
objects in a common cluster of the product of their sizes. -/
noncomputable def rCost2 (x : ℕ → ℝ) (ℓ : ℕ) {k : ℕ} (D : ℕ → Fin k) : ℝ :=
  ∑ j, (∑ i ∈ (Finset.range ℓ).filter (fun i => D i = j), x i) ^ 2 -
    ∑ i ∈ Finset.range ℓ, x i ^ 2

open Finset in
/-- Auxiliary result for Appendix B (Lemma B.4, Claims B.3 and B.5). -/
lemma rCost2_eq_pairs (x : ℕ → ℝ) (ℓ : ℕ) {k : ℕ} (D : ℕ → Fin k) :
    rCost2 x ℓ D = ∑ i ∈ range ℓ, ∑ i' ∈ (range ℓ).filter (fun i' => i' ≠ i ∧ D i' = D i),
      x i * x i' := by
  unfold rCost2
  have h1 : ∑ j, (∑ i ∈ (range ℓ).filter (fun i => D i = j), x i) ^ 2 =
      ∑ i ∈ range ℓ, x i * ∑ i' ∈ (range ℓ).filter (fun i' => D i' = D i), x i' := by
    rw [← Finset.sum_fiberwise (range ℓ) D
      (fun i => x i * ∑ i' ∈ (range ℓ).filter (fun i' => D i' = D i), x i')]
    apply sum_congr rfl; intro j _
    rw [sq, sum_mul]
    apply sum_congr rfl; intro i hi
    rw [(mem_filter.1 hi).2]
  rw [h1, ← sum_sub_distrib]
  apply sum_congr rfl; intro i hi
  rw [mul_sum, ← sum_erase_add _ _ (show i ∈ (range ℓ).filter (fun i' => D i' = D i) by
    simp [mem_range.1 hi])]
  have : ((range ℓ).filter (fun i' => D i' = D i)).erase i =
      (range ℓ).filter (fun i' => i' ≠ i ∧ D i' = D i) := by
    ext i'; simp only [mem_erase, mem_filter]; tauto
  rw [this]; ring

open Finset in
/-- **Claim B.5 (rounding).** Let every object size be rounded up from `x_M` to `y_M` with
`x_M ≤ y_M ≤ (1 + ε) x_M` (`0 ≤ ε ≤ 1`).  For every packing `D`, with
`F_J(D) = Δ + (1/2) rCost2 x D` and `F_K(D) = Δ + (1/2) rCost2 y D` (where `Δ ≥ 0` is the
packing-independent number of pairs inside macro-cliques), we have
`F_J(D) ≤ F_K(D) ≤ (1 + ε)^2 F_J(D) ≤ (1 + 3ε) F_J(D)`; consequently every `F_K`-optimal packing
is `(1 + 3ε)`-optimal for `J`: `OPT(K) ≤ (1 + 3ε) OPT(J)` and `F_J(D_K) ≤ (1 + 3ε) OPT(J)`. -/
theorem claim_B_5 (x y : ℕ → ℝ) (ℓ : ℕ) {k : ℕ} {ε Δ : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hΔ : 0 ≤ Δ) (hx : ∀ i < ℓ, 0 ≤ x i) (hxy : ∀ i < ℓ, x i ≤ y i)
    (hyx : ∀ i < ℓ, y i ≤ (1 + ε) * x i) :
    (∀ D : ℕ → Fin k, Δ + rCost2 x ℓ D / 2 ≤ Δ + rCost2 y ℓ D / 2 ∧
      Δ + rCost2 y ℓ D / 2 ≤ (1 + ε) ^ 2 * (Δ + rCost2 x ℓ D / 2) ∧
      (1 + ε) ^ 2 * (Δ + rCost2 x ℓ D / 2) ≤ (1 + 3 * ε) * (Δ + rCost2 x ℓ D / 2)) ∧
    (∀ DK : ℕ → Fin k, (∀ D' : ℕ → Fin k, rCost2 y ℓ DK ≤ rCost2 y ℓ D') →
      ∀ D' : ℕ → Fin k, Δ + rCost2 x ℓ DK / 2 ≤ (1 + 3 * ε) * (Δ + rCost2 x ℓ D' / 2)) := by
  have hpair : ∀ D : ℕ → Fin k, rCost2 x ℓ D ≤ rCost2 y ℓ D ∧
      rCost2 y ℓ D ≤ (1 + ε) ^ 2 * rCost2 x ℓ D ∧ 0 ≤ rCost2 x ℓ D := by
    intro D
    rw [rCost2_eq_pairs, rCost2_eq_pairs, mul_sum]
    refine ⟨?_, ?_, ?_⟩
    · apply sum_le_sum; intro i hi; apply sum_le_sum; intro i' hi'
      have hi := mem_range.1 hi
      have hi' := mem_range.1 (mem_filter.1 hi').1
      exact mul_le_mul (hxy i hi) (hxy i' hi') (hx i' hi') ((hx i hi).trans (hxy i hi))
    · apply sum_le_sum; intro i hi; rw [mul_sum]; apply sum_le_sum; intro i' hi'
      have hi := mem_range.1 hi
      have hi' := mem_range.1 (mem_filter.1 hi').1
      have := mul_le_mul (hyx i hi) (hyx i' hi') ((hx i' hi').trans (hxy i' hi'))
        (by have := hx i hi; positivity)
      nlinarith
    · apply sum_nonneg; intro i hi; apply sum_nonneg; intro i' hi'
      exact mul_nonneg (hx i (mem_range.1 hi)) (hx i' (mem_range.1 (mem_filter.1 hi').1))
  have hF : ∀ D : ℕ → Fin k, Δ + rCost2 x ℓ D / 2 ≤ Δ + rCost2 y ℓ D / 2 ∧
      Δ + rCost2 y ℓ D / 2 ≤ (1 + ε) ^ 2 * (Δ + rCost2 x ℓ D / 2) ∧
      (1 + ε) ^ 2 * (Δ + rCost2 x ℓ D / 2) ≤ (1 + 3 * ε) * (Δ + rCost2 x ℓ D / 2) := by
    intro D
    obtain ⟨h1, h2, h3⟩ := hpair D
    have hsq : 1 ≤ (1 + ε) ^ 2 := by nlinarith
    refine ⟨by linarith, by nlinarith [mul_le_mul_of_nonneg_right hsq hΔ], ?_⟩
    apply mul_le_mul_of_nonneg_right _ (by linarith)
    nlinarith
  refine ⟨hF, fun DK hDK D' => ?_⟩
  obtain ⟨h1, -, -⟩ := hF DK
  obtain ⟨-, h2, h3⟩ := hF D'
  have := hDK D'
  linarith

end CCK
