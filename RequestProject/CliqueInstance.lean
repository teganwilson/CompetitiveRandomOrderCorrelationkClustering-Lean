module

public import RequestProject.CliqueBounds

/-!
# Lemma 3.4 for disjoint-cliques graphs

For a disjoint-cliques graph `cliqueGraph q` we sort its cliques by non-increasing size and define
the parameters `s(I)`, `r(I)`, `a(I)` of Definitions 3.2 and 3.3.  We then prove Lemma 3.4:
`s(I) a(I) / 2 ≤ Cost(OPT_k) ≤ s(I) a(I)`.
-/

@[expose] public section

open Finset
open scoped Classical

namespace CCK

variable {V : Type*} [Fintype V] {ι : Type*}

/-- The set of (nonempty) cliques of the disjoint-cliques instance given by `q`. -/
noncomputable def cliqueSet (q : V → ι) : Finset ι := univ.image q

/-- Size of clique `i`. -/
noncomputable def csize (q : V → ι) (i : ι) : ℕ := (univ.filter (fun v => q v = i)).card

/-- The cliques listed in non-increasing order of size: `K_1, K_2, …, K_ℓ` in the paper. -/
noncomputable def sortedCliques (q : V → ι) : List ι :=
  (cliqueSet q).toList.mergeSort (fun a b => decide (csize q b ≤ csize q a))

/-- The clique sizes in non-increasing order: `cw q i = n_{i+1}` in the paper. -/
noncomputable def cw (q : V → ι) (i : ℕ) : ℕ := ((sortedCliques q).map (csize q)).getD i 0

/-- The number of cliques `ℓ`. -/
noncomputable def numCliques (q : V → ι) : ℕ := (cliqueSet q).card

/-- **Definition 3.2** for a disjoint-cliques graph: `s(I)`. -/
noncomputable def sOf (q : V → ι) (k : ℕ) : ℕ := sParam (cw q) (numCliques q) k

/-- **Definition 3.3** for a disjoint-cliques graph: `r(I)`. -/
noncomputable def rOf (q : V → ι) (k : ℕ) : ℕ := rParam (cw q) (numCliques q) k

/-- **Definition 3.3** for a disjoint-cliques graph: `a(I)`. -/
noncomputable def aOf (q : V → ι) (k : ℕ) : ℝ := aParam (cw q) (numCliques q) k

/-- Position of the clique of `v` in the sorted list. -/
noncomputable def cidx (q : V → ι) (v : V) : ℕ := (sortedCliques q).idxOf (q v)

section lemmas

variable (q : V → ι)

/-- Auxiliary result for Lemma 3.4 and Definitions 3.2, 3.3 (Section 3). -/
lemma sortedCliques_perm : (sortedCliques q).Perm (cliqueSet q).toList :=
  List.mergeSort_perm _ _

/-- Auxiliary result for Lemma 3.4 and Definitions 3.2, 3.3 (Section 3). -/
lemma sortedCliques_nodup : (sortedCliques q).Nodup :=
  (sortedCliques_perm q).nodup_iff.2 (Finset.nodup_toList _)

/-- Auxiliary result for Lemma 3.4 and Definitions 3.2, 3.3 (Section 3). -/
lemma mem_sortedCliques {i : ι} : i ∈ sortedCliques q ↔ i ∈ cliqueSet q := by
  rw [(sortedCliques_perm q).mem_iff, Finset.mem_toList]

/-- Auxiliary result for Lemma 3.4 and Definitions 3.2, 3.3 (Section 3). -/
lemma length_sortedCliques : (sortedCliques q).length = numCliques q := by
  rw [(sortedCliques_perm q).length_eq, Finset.length_toList]; rfl

/-- Auxiliary result for Lemma 3.4 and Definitions 3.2, 3.3 (Section 3). -/
lemma cw_eq {i : ℕ} (hi : i < numCliques q) :
    cw q i = csize q ((sortedCliques q)[i]'(by rw [length_sortedCliques]; exact hi)) := by
  unfold cw
  rw [List.getD_eq_getElem _ _ (by simp [length_sortedCliques, hi])]
  simp

/-- Auxiliary result for Lemma 3.4 and Definitions 3.2, 3.3 (Section 3). -/
lemma cw_sorted : SortedDesc (cw q) (numCliques q) := by
  intro i j hij hj
  have hpw := List.pairwise_mergeSort (le := fun a b => decide (csize q b ≤ csize q a))
    (by intro a b c h1 h2; simp only [decide_eq_true_eq] at *; omega)
    (by intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; omega)
    (cliqueSet q).toList
  rw [cw_eq q hj, cw_eq q (lt_of_le_of_lt hij hj)]
  rcases eq_or_lt_of_le hij with rfl | hlt
  · exact le_rfl
  · have := List.pairwise_iff_getElem.1 hpw i j (by
      rw [show (cliqueSet q).toList.mergeSort _ = sortedCliques q from rfl,
        length_sortedCliques]; omega) (by
      rw [show (cliqueSet q).toList.mergeSort _ = sortedCliques q from rfl,
        length_sortedCliques]; omega) hlt
    simpa using this

/-- Auxiliary result for Lemma 3.4 and Definitions 3.2, 3.3 (Section 3). -/
lemma cidx_lt (v : V) : cidx q v < numCliques q := by
  unfold cidx
  rw [← length_sortedCliques q, List.idxOf_lt_length_iff, mem_sortedCliques]
  simp [cliqueSet]

/-- Auxiliary result for Lemma 3.4 and Definitions 3.2, 3.3 (Section 3). -/
lemma getElem_cidx (v : V) :
    (sortedCliques q)[cidx q v]'(by rw [length_sortedCliques]; exact cidx_lt q v) = q v :=
  List.getElem_idxOf _

/-- Auxiliary result for Lemma 3.4 and Definitions 3.2, 3.3 (Section 3). -/
lemma cidx_eq_iff (u v : V) : cidx q u = cidx q v ↔ q u = q v := by
  constructor
  · intro h
    rw [← getElem_cidx q u, ← getElem_cidx q v]
    simp only [h]
  · intro h; unfold cidx; rw [h]

/-- Auxiliary result for Lemma 3.4 and Definitions 3.2, 3.3 (Section 3). -/
lemma card_cidx_fiber {i : ℕ} (hi : i < numCliques q) :
    (univ.filter (fun v => cidx q v = i)).card = cw q i := by
  rw [cw_eq q hi]
  unfold csize
  congr 1
  ext v
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · rintro rfl; exact (getElem_cidx q v).symm
  · intro h
    have hmem : (sortedCliques q)[i]'(by rw [length_sortedCliques]; exact hi) ∈
        sortedCliques q := List.getElem_mem _
    unfold cidx
    rw [h]
    exact (sortedCliques_nodup q).idxOf_getElem _ _

/-- Auxiliary result for Lemma 3.4 and Definitions 3.2, 3.3 (Section 3). -/
lemma cw_pos {i : ℕ} (hi : i < numCliques q) : 0 < cw q i := by
  rw [← card_cidx_fiber q hi]
  have hmem : (sortedCliques q)[i]'(by rw [length_sortedCliques]; exact hi) ∈ cliqueSet q :=
    (mem_sortedCliques q).1 (List.getElem_mem _)
  obtain ⟨v, -, hv⟩ := mem_image.1 hmem
  refine card_pos.2 ⟨v, ?_⟩
  simp only [mem_filter, mem_univ, true_and]
  unfold cidx; rw [hv]
  exact (sortedCliques_nodup q).idxOf_getElem _ _

/-- Number of ordered pairs in a common class, as a sum of squared class sizes. -/
lemma samePairs_eq_sum_sq {κ : Type*} (f : V → κ) (s : Finset κ)
    (hs : ∀ v, f v ∈ s) :
    samePairs f = ∑ j ∈ s, ((univ.filter (fun v => f v = j)).card) ^ 2 := by
  unfold samePairs
  rw [card_eq_sum_card_fiberwise (f := fun p : V × V => f p.1) (t := s)
    (fun p _ => hs p.1)]
  apply sum_congr rfl; intro j _
  rw [sq, ← card_product]
  congr 1
  ext ⟨a, b⟩
  simp only [mem_filter, mem_univ, true_and, mem_product]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h2, h1 ▸ h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1.trans h2.symm, h1⟩

/-- The bridge between graph costs and the clique-level cost `cCost2`: for the clustering
`v ↦ D (index of the clique of v)`, twice the cost equals `cCost2`. -/
lemma disagreeCount_comp_cidx {k : ℕ} (D : ℕ → Fin k) :
    (disagreeCount (cliqueGraph q) (fun v => D (cidx q v)) : ℝ) =
      cCost2 (cw q) (numCliques q) D := by
  have hpres : CliquePreserving q (fun v => D (cidx q v)) := by
    intro u v h; simp only [(cidx_eq_iff q u v).2 h]
  have h := disagreeCount_cliquePreserving q _ hpres
  have hq : samePairs q = samePairs (cidx q) := by
    unfold samePairs
    congr 1; ext p; simp [cidx_eq_iff]
  have h1 : samePairs (cidx q) = ∑ i ∈ range (numCliques q), (cw q i) ^ 2 := by
    rw [samePairs_eq_sum_sq (cidx q) (range (numCliques q)) (fun v => mem_range.2 (cidx_lt q v))]
    apply sum_congr rfl; intro i hi
    congr 1
    convert card_cidx_fiber q (mem_range.1 hi)
  have h2 : samePairs (fun v => D (cidx q v)) =
      ∑ j : Fin k, ((univ.filter (fun v => D (cidx q v) = j)).card) ^ 2 := by
    convert samePairs_eq_sum_sq (fun v => D (cidx q v)) univ (fun _ => mem_univ _)
  have h3 : ∀ j : Fin k, ((univ.filter (fun v => D (cidx q v) = j)).card : ℝ) =
      cLoad (cw q) (numCliques q) D j := by
    intro j
    unfold cLoad
    rw [card_eq_sum_card_fiberwise (f := cidx q) (t := (range (numCliques q)).filter
      (fun i => D i = j)) (by
        intro v hv
        simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq, mem_range] at hv ⊢
        exact ⟨cidx_lt q v, hv⟩)]
    push_cast
    apply sum_congr rfl; intro i hi
    simp only [mem_filter, mem_range] at hi
    rw [← card_cidx_fiber q hi.1]
    congr 2
    ext v; simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨-, h⟩; exact h
    · intro h; exact ⟨by rw [h]; exact hi.2, h⟩
  unfold cCost2
  have : (disagreeCount (cliqueGraph q) (fun v => D (cidx q v)) : ℝ) =
      (samePairs (fun v => D (cidx q v)) : ℝ) - samePairs q := by
    rw [← h]; push_cast; ring
  rw [this, h2, hq, h1]
  push_cast
  simp_rw [h3]

/-- Every clique-preserving clustering factors through the clique index. -/
lemma exists_factor_cidx {k : ℕ} (C : V → Fin k) (hC : CliquePreserving q C) (hk : 0 < k) :
    ∃ D : ℕ → Fin k, ∀ v, C v = D (cidx q v) := by
  refine ⟨fun i => if h : ∃ v, cidx q v = i then C h.choose else ⟨0, hk⟩, fun v => ?_⟩
  have h : ∃ u, cidx q u = cidx q v := ⟨v, rfl⟩
  simp only [h, dif_pos]
  exact hC _ _ ((cidx_eq_iff q _ _).1 h.choose_spec).symm

end lemmas

/-- **Lemma 3.4.** For a disjoint-cliques instance `I` (the graph `cliqueGraph q`) and `k ≥ 1`,
the optimal correlation k-clustering cost satisfies `Cost(OPT) ≥ s(I) a(I) / 2`; moreover the
greedy clustering has cost at most `s(I) a(I) ≤ 2 Cost(OPT)` (a 2-approximation); precisely
`s(I) a(I) / 2 ≤ Cost(OPT_k) ≤ s(I) a(I)`.  (The upper bound is attained by the greedy
clustering of the proof; the polynomial running time of the greedy algorithm and of the PTAS of
Appendix B is not formalized, see `RequestProject/PTAS.lean` for the mathematical content of the
PTAS.) -/
theorem lemma_3_4 (q : V → ι) {k : ℕ} (hk : 0 < k) :
    (sOf q k : ℝ) * aOf q k / 2 ≤ optK (cliqueGraph q) k ∧
      (optK (cliqueGraph q) k : ℝ) ≤ sOf q k * aOf q k := by
  constructor
  · by_cases hV : Nonempty V
    · haveI : Nonempty (V → Fin k) := ⟨fun _ => ⟨0, hk⟩⟩
      obtain ⟨C, hC, hopt⟩ := exists_optimal_cliquePreserving q k
      obtain ⟨D, hD⟩ := exists_factor_cidx q C hC hk
      have hlow := cCost2_lower (cw_sorted q) (fun i hi => cw_pos q hi) hk D
      rw [← disagreeCount_comp_cidx] at hlow
      have hCD : C = fun v => D (cidx q v) := funext hD
      rw [← hopt, hCD]
      have := two_mul_cost (cliqueGraph q) (fun v => D (cidx q v))
      have : (disagreeCount (cliqueGraph q) (fun v => D (cidx q v)) : ℝ) =
          2 * cost (cliqueGraph q) (fun v => D (cidx q v)) := by
        rw [← this]; push_cast; ring
      unfold sOf aOf
      linarith
    · have : IsEmpty V := not_nonempty_iff.1 hV
      have h0 : numCliques q = 0 := by simp [numCliques, cliqueSet]
      have : sOf q k = 0 := by
        unfold sOf sParam; exact tailSum_eq_zero (by rw [h0]; exact Nat.zero_le _)
      rw [this]; simp
  · obtain ⟨D, hD⟩ := cCost2_upper (fun i hi => cw_pos q hi) hk (w := cw q)
      (ℓ := numCliques q)
    rw [← disagreeCount_comp_cidx] at hD
    have h1 := optK_le (cliqueGraph q) (fun v => D (cidx q v))
    have h2 := two_mul_cost (cliqueGraph q) (fun v => D (cidx q v))
    have : (disagreeCount (cliqueGraph q) (fun v => D (cidx q v)) : ℝ) =
        2 * cost (cliqueGraph q) (fun v => D (cidx q v)) := by
      rw [← h2]; push_cast; ring
    have h1' : (optK (cliqueGraph q) k : ℝ) ≤ cost (cliqueGraph q) (fun v => D (cidx q v)) := by
      exact_mod_cast h1
    unfold sOf aOf
    linarith

end CCK
