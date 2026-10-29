module

public import RequestProject.PivotLoad

/-!
# Lemma 7.4 (lower bound on the optimal cost using the broken instance `I_σ`)

We fix an optimal (unconstrained) correlation clustering `Q` of `G`, with clusters
`Q_1, …, Q_ℓ` sorted by size (Definition 7.1; the cluster of `v` has position `cidx Q v` in
the sorted order, and `I_clique = cliqueGraph Q`).  For an arrival order `σ` and each cluster
`Q_j` from which some pivot of PIVOT arrives, `P_j(σ)` is the set of vertices of `Q_j` which are
still uncovered right after the first pivot of `Q_j` arrives (Definition 7.2; `P_j(σ) = ∅` if no
pivot comes from `Q_j`).  The broken instance `I_σ` turns `Q_j \ P_j(σ)` into a clique for the `k`
largest clusters and breaks all other vertices into singletons.

Lemma 7.4 states `E[s(I_σ) a(I_σ)] = O(Cost(OPT_k(I)))`.  The paper's proof uses
`|P_j(σ)| ≤ |Q_j \ P_j(σ)|` without justification; this holds because `Q` is optimal: in an
optimal clustering every vertex is adjacent to at least half of the other vertices of its
cluster (`card_cluster_le_two_mul_adj`), and the first pivot of `Q_j` covers all of its
neighbours.  We also bound the cost on `I_σ` directly in terms of an optimal k-clustering of `I`
rather than through the intermediate instance `I_cs`.
-/

@[expose] public section

open Finset
open scoped Classical

namespace CCK

variable {n : ℕ} (G : SimpleGraph (Fin n)) {ι : Type*} (Q : Fin n → ι)

/-- The cluster `Q_j` of the clustering `Q`, as a set of vertices. -/
noncomputable def qCl (j : ι) : Finset (Fin n) := univ.filter (fun v => Q v = j)

/-- The pivots (of PIVOT with arrival order `σ`) belonging to `Q_j`. -/
noncomputable def qPivots (σ : Equiv.Perm (Fin n)) (j : ι) : Finset (Fin n) :=
  (pivotsUpTo G σ n).filter (fun p => Q p = j)

/-- **Definition 7.2 (the random sets `P_j(σ)`).**  If some pivot arrives from `Q_j`, `P_j(σ)` is
the set of vertices of `Q_j` not covered right after the arrival of the first pivot of `Q_j`
(i.e. not yet arrived and not adjacent to any pivot arrived so far); otherwise `P_j(σ) = ∅`. -/
noncomputable def brokenPart (σ : Equiv.Perm (Fin n)) (j : ι) : Finset (Fin n) :=
  if h : (qPivots G Q σ j).Nonempty then
    qCl Q j ∩ uncovered G σ (((qPivots G Q σ j).image (arrTime σ)).min' (h.image _) + 1)
  else ∅

/-- **Definitions 7.1 and 7.2 (the broken instance `I_σ`).**  `I_σ = cliqueGraph (brokenLabel G Q
k σ)`: the vertices of `Q_j \ P_j(σ)`, for `Q_j` among the `k` largest clusters of `Q`, form a
clique (label `inl j`), and every other vertex is a singleton (label `inr v`).  (The clique
/-- Auxiliary instance for Lemma 7.4 and Definition 7.2 (Section 7.3.1). -/
instance `I_clique` of Definition 7.1 is `cliqueGraph Q`.) -/
noncomputable def brokenLabel (k : ℕ) (σ : Equiv.Perm (Fin n)) : Fin n → ι ⊕ Fin n := fun v =>
  if cidx Q v < k ∧ v ∉ brokenPart G Q σ (Q v) then Sum.inl (Q v) else Sum.inr v

/-! ### Optimal clusterings: every vertex sees at least half of its cluster -/

/-- In an optimal correlation clustering `Q`, every vertex `v` is adjacent to at least half of the
other vertices of its cluster: `|Q(v)| ≤ 2 |N(v) ∩ Q(v)| + 1`. -/
lemma card_cluster_le_two_mul_adj (hQ : cost G Q = optCC G) (v : Fin n) :
    (qCl Q (Q v)).card ≤ 2 * ((qCl Q (Q v)).filter (G.Adj v)).card + 1 := by
  set F := qCl Q (Q v) with hF
  set A := F.filter (G.Adj v) with hA
  set N := (F.erase v).filter (fun u => ¬ G.Adj v u) with hN
  have hvF : v ∈ F := by simp [hF, qCl]
  have hsplit : F.card = 1 + A.card + N.card := by
    have h1 := card_erase_of_mem hvF
    have hAs : A ⊆ F.erase v := by
      intro u hu
      rw [hA, mem_filter] at hu
      exact mem_erase.2 ⟨fun e => G.loopless.irrefl v (e ▸ hu.2), hu.1⟩
    have hNA : N = (F.erase v) \ A := by
      ext u
      simp only [hN, hA, mem_filter, mem_sdiff, mem_erase]
      constructor
      · rintro ⟨h, h'⟩; exact ⟨h, fun h'' => h' h''.2⟩
      · rintro ⟨h, h'⟩; exact ⟨h, fun h'' => h' ⟨h.2, h''⟩⟩
    rw [hNA, card_sdiff_of_subset hAs]
    have := card_le_card hAs
    have := card_pos.2 ⟨v, hvF⟩
    omega
  -- the clustering obtained by moving `v` to a new singleton cluster
  set Q' : Fin n → Option ι := fun u => if u = v then none else some (Q u) with hQ'
  have hopt : cost G Q ≤ cost G Q' := hQ ▸ optCC_le_cost G Q'
  have hD : disagreeCount G Q ≤ disagreeCount G Q' := by
    have e1 := two_mul_cost G Q; have e2 := two_mul_cost G Q'; omega
  set D := univ.filter (fun p : Fin n × Fin n => Disagree G Q p.1 p.2) with hDdef
  set D' := univ.filter (fun p : Fin n × Fin n => Disagree G Q' p.1 p.2) with hD'def
  have hsd : (D \ D').card ≤ (D' \ D).card := by
    have a1 := card_sdiff_add_card_inter D D'
    have a2 := card_sdiff_add_card_inter D' D
    rw [inter_comm] at a2
    unfold disagreeCount at hD
    rw [← hDdef, ← hD'def] at hD
    omega
  have hlow : 2 * N.card ≤ (D \ D').card := by
    have hsub : N.image (fun u => (v, u)) ∪ N.image (fun u => (u, v)) ⊆ D \ D' := by
      intro x hx
      rw [mem_union, mem_image, mem_image] at hx
      have key : ∀ u ∈ N, Disagree G Q v u ∧ ¬ Disagree G Q' v u := by
        intro u hu
        simp only [hN, mem_filter, mem_erase, hF, qCl, mem_univ, true_and] at hu
        obtain ⟨⟨huv, hQu⟩, hadj⟩ := hu
        refine ⟨⟨Ne.symm huv, Or.inr ⟨hadj, hQu.symm⟩⟩, ?_⟩
        rintro ⟨-, h | h⟩
        · exact hadj h.1
        · simp [hQ', huv] at h
      rw [mem_sdiff, hDdef, hD'def, mem_filter, mem_filter]
      rcases hx with ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩
      · exact ⟨⟨mem_univ _, (key u hu).1⟩, fun h => (key u hu).2 h.2⟩
      · exact ⟨⟨mem_univ _, (disagree_symm G Q).1 (key u hu).1⟩,
          fun h => (key u hu).2 ((disagree_symm G Q').1 h.2)⟩
    have hdisj : Disjoint (N.image (fun u => (v, u))) (N.image (fun u => (u, v))) := by
      rw [disjoint_left]
      intro x hx hx'
      obtain ⟨u, hu, rfl⟩ := mem_image.1 hx
      obtain ⟨w, hw, hw'⟩ := mem_image.1 hx'
      simp only [Prod.mk.injEq] at hw'
      have : u ≠ v := (mem_erase.1 (mem_filter.1 hu).1).1
      exact this hw'.2.symm
    have := card_le_card hsub
    rw [card_union_of_disjoint hdisj, card_image_of_injective _ (fun a b h => by simpa using h),
      card_image_of_injective _ (fun a b h => by simpa using h)] at this
    omega
  have hup : (D' \ D).card ≤ 2 * A.card := by
    have hsub : D' \ D ⊆ A.image (fun u => (v, u)) ∪ A.image (fun u => (u, v)) := by
      rintro ⟨x, y⟩ hxy
      rw [mem_sdiff, hDdef, hD'def, mem_filter, mem_filter] at hxy
      obtain ⟨⟨-, h'⟩, hnot⟩ := hxy
      have hnot' : ¬ Disagree G Q x y := fun h => hnot ⟨mem_univ _, h⟩
      have hxy' : x ≠ y := h'.1
      by_cases hx : x = v
      · subst hx
        have hlab : Q' x ≠ Q' y := by simp [hQ', Ne.symm hxy']
        have hadj : G.Adj x y := by
          rcases h'.2 with h | h
          · exact h.1
          · exact absurd h.2 hlab
        have hQy : Q x = Q y := by
          by_contra hq; exact hnot' ⟨hxy', Or.inl ⟨hadj, hq⟩⟩
        refine mem_union_left _ (mem_image.2 ⟨y, ?_, rfl⟩)
        simp [hA, hF, qCl, hQy, hadj]
      · by_cases hy : y = v
        · subst hy
          have hlab : Q' x ≠ Q' y := by simp [hQ', hx]
          have hadj : G.Adj x y := by
            rcases h'.2 with h | h
            · exact h.1
            · exact absurd h.2 hlab
          have hQx : Q x = Q y := by
            by_contra hq; exact hnot' ⟨hxy', Or.inl ⟨hadj, hq⟩⟩
          refine mem_union_right _ (mem_image.2 ⟨x, ?_, rfl⟩)
          simp [hA, hF, qCl, hQx, hadj.symm]
        · exfalso
          apply hnot'
          have hiff : Q' x = Q' y ↔ Q x = Q y := by simp [hQ', hx, hy]
          refine ⟨hxy', ?_⟩
          rcases h'.2 with h | h
          · exact Or.inl ⟨h.1, fun e => h.2 (hiff.2 e)⟩
          · exact Or.inr ⟨h.1, hiff.1 h.2⟩
    exact (card_le_card hsub).trans ((card_union_le _ _).trans (by
      rw [card_image_of_injective _ (fun a b h => by simpa using h),
        card_image_of_injective _ (fun a b h => by simpa using h)]; omega))
  omega

/-- Auxiliary result for Lemma 7.4 and Definition 7.2 (Section 7.3.1). -/
lemma brokenPart_subset (σ : Equiv.Perm (Fin n)) (j : ι) : brokenPart G Q σ j ⊆ qCl Q j := by
  unfold brokenPart
  split_ifs
  · exact inter_subset_left
  · exact empty_subset _

/-- `|P_j(σ)| ≤ |Q_j \ P_j(σ)|` (in fact `2 |P_j(σ)| < |Q_j|`), for an optimal `Q`. -/
lemma two_mul_card_brokenPart_le (hQ : cost G Q = optCC G) (σ : Equiv.Perm (Fin n)) (j : ι) :
    2 * (brokenPart G Q σ j).card ≤ (qCl Q j).card := by
  unfold brokenPart
  split_ifs with h
  swap
  · simp
  set t0 := ((qPivots G Q σ j).image (arrTime σ)).min' (h.image _) with ht0
  obtain ⟨p0, hp0, hp0t⟩ := mem_image.1 (min'_mem ((qPivots G Q σ j).image (arrTime σ))
    (h.image _))
  rw [← ht0] at hp0t
  simp only [qPivots, mem_filter] at hp0
  obtain ⟨hp0piv, hQp0⟩ := hp0
  have hp0P : p0 ∈ pivotsUpTo G σ (t0 + 1) := by
    rw [mem_pivotsUpTo_iff]
    exact ⟨((mem_pivotsUpTo_iff G σ n p0).1 hp0piv).1, by omega⟩
  have hsub : qCl Q j ∩ uncovered G σ (t0 + 1) ⊆
      qCl Q j \ insert p0 ((qCl Q j).filter (G.Adj p0)) := by
    intro u hu
    rw [mem_inter] at hu
    rw [mem_sdiff]
    refine ⟨hu.1, ?_⟩
    simp only [uncovered, mem_filter, mem_univ, true_and] at hu
    rw [mem_insert, mem_filter]
    rintro (rfl | ⟨-, hadj⟩)
    · omega
    · exact hu.2.2 p0 hp0P hadj
  have hins : insert p0 ((qCl Q j).filter (G.Adj p0)) ⊆ qCl Q j := by
    intro u hu
    rw [mem_insert] at hu
    rcases hu with rfl | hu
    · simp [qCl, hQp0]
    · exact (mem_filter.1 hu).1
  have hc1 := card_le_card hsub
  rw [card_sdiff_of_subset hins, card_insert_of_notMem (by simp)] at hc1
  have hhalf := card_cluster_le_two_mul_adj G Q hQ p0
  rw [hQp0] at hhalf
  have : ((qCl Q j).filter (G.Adj p0)).card + 1 ≤ (qCl Q j).card := by
    have := card_le_card hins
    rwa [card_insert_of_notMem (by simp)] at this
  omega

/-! ### The cost of PIVOT and the sets `P_j(σ)` -/

/-- Auxiliary result for Lemma 7.4 and Definition 7.2 (Section 7.3.1). -/
lemma arrTime_pivotOf_lt_of_not_uncovered (σ : Equiv.Perm (Fin n)) {t : ℕ} {u : Fin n}
    (hu : u ∉ uncovered G σ t) : arrTime σ (pivotOf G σ u) < t := by
  simp only [uncovered, mem_filter, mem_univ, true_and, not_and_or, not_le, not_forall,
    not_not] at hu
  rcases hu with h | ⟨p, hp, hadj⟩
  · exact lt_of_le_of_lt (arrTime_pivotOf_le G σ u) h
  · have hp' := (mem_pivotsUpTo_iff G σ t p).1 hp
    by_cases hu : IsPivot G σ u
    · exact absurd hadj (not_adj_of_isPivot G σ hp'.1 hu)
    · exact lt_of_le_of_lt ((pivotOf_spec_of_not_isPivot G σ hu).2.2 p hp'.1 hadj) hp'.2

/-- Auxiliary result for Lemma 7.4 and Definition 7.2 (Section 7.3.1). -/
lemma le_arrTime_pivotOf_of_uncovered (σ : Equiv.Perm (Fin n)) {t : ℕ} {w : Fin n}
    (hw : w ∈ uncovered G σ t) : t ≤ arrTime σ (pivotOf G σ w) := by
  simp only [uncovered, mem_filter, mem_univ, true_and] at hw
  by_cases hwp : IsPivot G σ w
  · rw [pivotOf_of_isPivot G σ hwp]; exact hw.1
  · obtain ⟨hp, hadj, -⟩ := pivotOf_spec_of_not_isPivot G σ hwp
    by_contra h
    push_neg at h
    exact hw.2 _ ((mem_pivotsUpTo_iff G σ t _).2 ⟨hp, h⟩) hadj

/-- Vertices of `Q_j \ P_j(σ)` and of `P_j(σ)` lie in different pivot clusters. -/
lemma pivotOf_ne_of_brokenPart (σ : Equiv.Perm (Fin n)) {j : ι} {u w : Fin n}
    (hu : u ∈ qCl Q j \ brokenPart G Q σ j) (hw : w ∈ brokenPart G Q σ j) :
    pivotOf G σ u ≠ pivotOf G σ w := by
  unfold brokenPart at hu hw
  split_ifs at hu hw with h
  · rw [mem_sdiff, mem_inter] at hu
    have hu' : u ∉ uncovered G σ _ := fun h' => hu.2 ⟨hu.1, h'⟩
    have h1 := arrTime_pivotOf_lt_of_not_uncovered G σ hu'
    have h2 := le_arrTime_pivotOf_of_uncovered G σ (mem_inter.1 hw).2
    intro heq
    rw [heq] at h1
    omega
  · simp at hw

/-- Vertices of `Q_j \ P_j(σ)` and of `P_j(σ)` lie in different pivot clusters, so every such pair
is a disagreement of PIVOT or of `Q`: `∑_j |Q_j \ P_j(σ)| |P_j(σ)| ≤ 2 (Cost(PIVOT_σ) + Cost(Q))`. -/
lemma sum_brokenPart_le (σ : Equiv.Perm (Fin n)) :
    (∑ j ∈ univ.image Q, (((qCl Q j \ brokenPart G Q σ j).card *
      (brokenPart G Q σ j).card : ℕ) : ℝ)) ≤
      2 * ((cost G (pivotOf G σ) : ℝ) + cost G Q) := by
  set Pairs := (univ.image Q).biUnion
    (fun j => (qCl Q j \ brokenPart G Q σ j) ×ˢ brokenPart G Q σ j) with hPairs
  have hcard : Pairs.card = ∑ j ∈ univ.image Q,
      (qCl Q j \ brokenPart G Q σ j).card * (brokenPart G Q σ j).card := by
    rw [hPairs, card_biUnion]
    · exact sum_congr rfl (fun j _ => card_product _ _)
    · intro i _ j _ hij
      rw [Function.onFun, disjoint_left]
      intro x hx hx'
      rw [mem_product, mem_sdiff] at hx hx'
      have h1 := hx.1.1; have h2 := hx'.1.1
      simp only [qCl, mem_filter, mem_univ, true_and] at h1 h2
      exact hij (h1.symm.trans h2)
  have hsub : Pairs ⊆ univ.filter (fun p : Fin n × Fin n => Disagree G (pivotOf G σ) p.1 p.2) ∪
      univ.filter (fun p : Fin n × Fin n => Disagree G Q p.1 p.2) := by
    intro x hx
    rw [hPairs, mem_biUnion] at hx
    obtain ⟨j, -, hx⟩ := hx
    rw [mem_product] at hx
    have hne := pivotOf_ne_of_brokenPart G Q σ hx.1 hx.2
    have huv : x.1 ≠ x.2 := fun h => hne (by rw [h])
    have hQ1 : Q x.1 = j := by
      have := (mem_sdiff.1 hx.1).1; simpa [qCl] using this
    have hQ2 : Q x.2 = j := by
      have := brokenPart_subset G Q σ j hx.2; simpa [qCl] using this
    rw [mem_union, mem_filter, mem_filter]
    by_cases hadj : G.Adj x.1 x.2
    · exact Or.inl ⟨mem_univ _, huv, Or.inl ⟨hadj, hne⟩⟩
    · exact Or.inr ⟨mem_univ _, huv, Or.inr ⟨hadj, hQ1.trans hQ2.symm⟩⟩
  have h1 := (card_le_card hsub).trans (card_union_le _ _)
  have e1 := two_mul_cost G (pivotOf G σ)
  have e2 := two_mul_cost G Q
  unfold disagreeCount at e1 e2
  rw [hcard] at h1
  have : ∑ j ∈ univ.image Q, (qCl Q j \ brokenPart G Q σ j).card * (brokenPart G Q σ j).card
      ≤ 2 * (cost G (pivotOf G σ) + cost G Q) := by omega
  calc _ = ((∑ j ∈ univ.image Q, (qCl Q j \ brokenPart G Q σ j).card *
        (brokenPart G Q σ j).card : ℕ) : ℝ) := by push_cast; rfl
    _ ≤ ((2 * (cost G (pivotOf G σ) + cost G Q) : ℕ) : ℝ) := by exact_mod_cast this
    _ = _ := by push_cast; ring

/-! ### The cost of a k-clustering on `I_σ` -/

/-- The ordered pairs of distinct vertices in a common cluster of `Q` outside the `k` largest
ones number at most `s(I_clique) a(I_clique)` (all such clusters have size below `a(I_clique)`). -/
lemma card_tailPairs_le {k : ℕ} (hk : 0 < k) :
    (((univ : Finset (Fin n × Fin n)).filter (fun p => p.1 ≠ p.2 ∧ Q p.1 = Q p.2 ∧
      k ≤ cidx Q p.1)).card : ℝ) ≤ (sOf Q k : ℝ) * aOf Q k := by
  set ℓ := numCliques Q
  set F : ℕ → Finset (Fin n) := fun i => univ.filter (fun v => cidx Q v = i) with hF
  have hsub : (univ : Finset (Fin n × Fin n)).filter (fun p => p.1 ≠ p.2 ∧ Q p.1 = Q p.2 ∧
      k ≤ cidx Q p.1) ⊆ (Ico k ℓ).biUnion (fun i => F i ×ˢ F i) := by
    intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx
    rw [mem_biUnion]
    refine ⟨cidx Q x.1, mem_Ico.2 ⟨hx.2.2, cidx_lt Q _⟩, ?_⟩
    rw [mem_product]
    simp only [hF, mem_filter, mem_univ, true_and]
    first
      | exact ⟨rfl, ((cidx_eq_iff Q _ _).2 hx.2.1).symm⟩
      | exact ((cidx_eq_iff Q _ _).2 hx.2.1).symm
  have h1 := (card_le_card hsub).trans card_biUnion_le
  have h2 : ∑ i ∈ Ico k ℓ, (F i ×ˢ F i).card = ∑ i ∈ Ico k ℓ, cw Q i * cw Q i := by
    refine sum_congr rfl (fun i hi => ?_)
    rw [card_product, hF, card_cidx_fiber Q (mem_Ico.1 hi).2]
  rw [h2] at h1
  have h3 : ∀ i ∈ Ico k ℓ, (cw Q i : ℝ) ≤ aOf Q k := by
    intro i hi
    have hkℓ : k < ℓ := lt_of_le_of_lt (mem_Ico.1 hi).1 (mem_Ico.1 hi).2
    have hr := rParam_lt (w := cw Q) (fun i hi => cw_pos Q hi) hk hkℓ
    exact (lt_aParam_of_rParam_le (cw_sorted Q) hr (by
      exact le_trans hr.le (mem_Ico.1 hi).1) (mem_Ico.1 hi).2).le
  calc _ ≤ ((∑ i ∈ Ico k ℓ, cw Q i * cw Q i : ℕ) : ℝ) := by exact_mod_cast h1
    _ = ∑ i ∈ Ico k ℓ, (cw Q i : ℝ) * cw Q i := by push_cast; rfl
    _ ≤ ∑ i ∈ Ico k ℓ, (cw Q i : ℝ) * aOf Q k :=
        sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (h3 i hi) (Nat.cast_nonneg _))
    _ = (sOf Q k : ℝ) * aOf Q k := by
        rw [← sum_mul]; congr 1
        simp [sOf, sParam, tailSum, ℓ]

/-- Auxiliary result for Lemma 7.4 and Definition 7.2 (Section 7.3.1). -/
lemma nat_mul_le_two_mul_sub {p m : ℕ} (h : 2 * p ≤ m) : p * m ≤ 2 * ((m - p) * p) := by
  obtain ⟨d, rfl⟩ : ∃ d, m = p + p + d := ⟨m - 2 * p, by omega⟩
  rw [show p + p + d - p = p + d by omega]
  nlinarith

/-- For any clustering `C`, its cost on `I_σ` exceeds its cost on `I` by at most
`Cost(Q) + s(I_clique) a(I_clique) / 2 + 2 ∑_j |Q_j \ P_j(σ)| |P_j(σ)|`. -/
lemma cost_brokenLabel_le (hQ : cost G Q = optCC G) {k : ℕ} (hk : 0 < k)
    (σ : Equiv.Perm (Fin n)) {κ : Type*} (C : Fin n → κ) :
    (cost (cliqueGraph (brokenLabel G Q k σ)) C : ℝ) ≤ cost G C + cost G Q +
      (sOf Q k : ℝ) * aOf Q k / 2 + 2 * ∑ j ∈ univ.image Q,
        (((qCl Q j \ brokenPart G Q σ j).card * (brokenPart G Q σ j).card : ℕ) : ℝ) := by
  set S3 := (univ : Finset (Fin n × Fin n)).filter (fun p => p.1 ≠ p.2 ∧ Q p.1 = Q p.2 ∧
      k ≤ cidx Q p.1) with hS3
  set S4 := (univ.image Q).biUnion (fun j => brokenPart G Q σ j ×ˢ qCl Q j ∪
      qCl Q j ×ˢ brokenPart G Q σ j) with hS4
  have hsub : univ.filter (fun p : Fin n × Fin n =>
      Disagree (cliqueGraph (brokenLabel G Q k σ)) C p.1 p.2) ⊆
      ((univ.filter (fun p : Fin n × Fin n => Disagree G C p.1 p.2) ∪
      univ.filter (fun p : Fin n × Fin n => Disagree G Q p.1 p.2)) ∪ S3) ∪ S4 := by
    rintro ⟨u, w⟩ hx
    simp only [mem_filter, mem_univ, true_and, Disagree, cliqueGraph] at hx
    obtain ⟨huw, hx⟩ := hx
    have hadjσ : ∀ h : brokenLabel G Q k σ u = brokenLabel G Q k σ w, Q u = Q w := by
      intro h
      unfold brokenLabel at h
      split_ifs at h with h1 h2 h2
      · exact Sum.inl_injective h
      · exact absurd (Sum.inr_injective h) huw
    simp only [mem_union, mem_filter, mem_univ, true_and, Disagree, hS3, hS4, mem_biUnion,
      mem_image, mem_product]
    rcases hx with ⟨⟨-, hb⟩, hC⟩ | ⟨hnb, hC⟩
    · by_cases hG : G.Adj u w
      · exact Or.inl (Or.inl (Or.inl ⟨huw, Or.inl ⟨hG, hC⟩⟩))
      · exact Or.inl (Or.inl (Or.inr ⟨huw, Or.inr ⟨hG, hadjσ hb⟩⟩))
    · by_cases hG : G.Adj u w
      · by_cases hQ' : Q u = Q w
        · by_cases hkc : k ≤ cidx Q u
          · exact Or.inl (Or.inr ⟨huw, hQ', hkc⟩)
          · right
            refine ⟨Q u, ⟨u, rfl⟩, ?_⟩
            have hcw : cidx Q w = cidx Q u := (cidx_eq_iff Q _ _).2 hQ'.symm
            have : u ∈ brokenPart G Q σ (Q u) ∨ w ∈ brokenPart G Q σ (Q u) := by
              by_contra hcon
              push_neg at hcon
              apply hnb
              refine ⟨huw, ?_⟩
              unfold brokenLabel
              rw [if_pos ⟨by omega, hcon.1⟩, if_pos ⟨by omega, hQ' ▸ hcon.2⟩, hQ']
            rcases this with h | h
            · exact Or.inl ⟨h, by simp [qCl, hQ']⟩
            · exact Or.inr ⟨by simp [qCl], h⟩
        · exact Or.inl (Or.inl (Or.inr ⟨huw, Or.inl ⟨hG, hQ'⟩⟩))
      · exact Or.inl (Or.inl (Or.inl ⟨huw, Or.inr ⟨hG, hC⟩⟩))
  have h1 := card_le_card hsub
  have u1 := card_union_le ((univ.filter (fun p : Fin n × Fin n => Disagree G C p.1 p.2) ∪
      univ.filter (fun p : Fin n × Fin n => Disagree G Q p.1 p.2)) ∪ S3) S4
  have u2 := card_union_le (univ.filter (fun p : Fin n × Fin n => Disagree G C p.1 p.2) ∪
      univ.filter (fun p : Fin n × Fin n => Disagree G Q p.1 p.2)) S3
  have u3 := card_union_le (univ.filter (fun p : Fin n × Fin n => Disagree G C p.1 p.2))
      (univ.filter (fun p : Fin n × Fin n => Disagree G Q p.1 p.2))
  have hS4c : S4.card ≤ ∑ j ∈ univ.image Q,
      4 * ((qCl Q j \ brokenPart G Q σ j).card * (brokenPart G Q σ j).card) := by
    refine card_biUnion_le.trans (sum_le_sum (fun j _ => ?_))
    refine (card_union_le _ _).trans ?_
    rw [card_product, card_product, card_sdiff_of_subset (brokenPart_subset G Q σ j)]
    have h2 := two_mul_card_brokenPart_le G Q hQ σ j
    have := nat_mul_le_two_mul_sub h2
    rw [mul_comm (qCl Q j).card (brokenPart G Q σ j).card]
    omega
  have hS3c := card_tailPairs_le Q hk
  rw [← hS3] at hS3c
  have e1 := two_mul_cost (cliqueGraph (brokenLabel G Q k σ)) C
  have e2 := two_mul_cost G C
  have e3 := two_mul_cost G Q
  unfold disagreeCount at e1 e2 e3
  have hR : (2 * cost (cliqueGraph (brokenLabel G Q k σ)) C : ℝ) ≤ 2 * cost G C + 2 * cost G Q +
      (S3.card : ℝ) + ((∑ j ∈ univ.image Q,
      4 * ((qCl Q j \ brokenPart G Q σ j).card * (brokenPart G Q σ j).card) : ℕ) : ℝ) := by
    have : 2 * cost (cliqueGraph (brokenLabel G Q k σ)) C ≤ 2 * cost G C + 2 * cost G Q +
        S3.card + ∑ j ∈ univ.image Q,
        4 * ((qCl Q j \ brokenPart G Q σ j).card * (brokenPart G Q σ j).card) := by omega
    exact_mod_cast this
  have hsum : ((∑ j ∈ univ.image Q,
      4 * ((qCl Q j \ brokenPart G Q σ j).card * (brokenPart G Q σ j).card) : ℕ) : ℝ) =
      4 * ∑ j ∈ univ.image Q,
        (((qCl Q j \ brokenPart G Q σ j).card * (brokenPart G Q σ j).card : ℕ) : ℝ) := by
    push_cast; rw [mul_sum]
  rw [hsum] at hR
  linarith

/-- **Lemma 7.4 (lower bound on the optimal cost using `I_σ`).**  Let `Q` be an optimal
unconstrained correlation clustering of `G` and `I_σ` the broken instance of Definition 7.2.
Then `E_σ[s(I_σ) a(I_σ)] ≤ 96 Cost(OPT_k(I))`, i.e. `Ω(E[s(I_σ) a(I_σ)]) ≤ Cost(OPT_k(I))`
(the paper's proof gives `E[s(I_σ) a(I_σ)] / 4 ≤ 24 Cost(OPT_k(I))`).  (Assumes the
3-approximation guarantee of PIVOT [ACN05], as the hypothesis `PivotThreeApprox`.) -/
theorem lemma_7_4 (hPiv : PivotThreeApprox) (hQ : cost G Q = optCC G) {k : ℕ} (hk : 0 < k) :
    expect (fun σ => (sOf (brokenLabel G Q k σ) k : ℝ) * aOf (brokenLabel G Q k σ) k) ≤
      96 * optK G k := by
  haveI : Nonempty (Fin n → Fin k) := ⟨fun _ => ⟨0, hk⟩⟩
  obtain ⟨X, hX⟩ := exists_optK G k
  have hCC : (optCC G : ℝ) ≤ optK G k := by exact_mod_cast optCC_le_optK G k
  have hQR : (cost G Q : ℝ) = optCC G := by exact_mod_cast hQ
  have hcl : (sOf Q k : ℝ) * aOf Q k ≤ 4 * ((optK G k : ℝ) + optCC G) := by
    have h1 := (lemma_3_4 Q hk).1
    have h2 : (optK (cliqueGraph Q) k : ℝ) ≤ optK G k + cost G Q := by
      exact_mod_cast optK_cliqueGraph_le G Q k
    rw [hQR] at h2
    linarith
  set S : Equiv.Perm (Fin n) → ℝ := fun σ => ∑ j ∈ univ.image Q,
    (((qCl Q j \ brokenPart G Q σ j).card * (brokenPart G Q σ j).card : ℕ) : ℝ) with hS
  have hpt : ∀ σ, (sOf (brokenLabel G Q k σ) k : ℝ) * aOf (brokenLabel G Q k σ) k ≤
      (12 * (optK G k : ℝ) + 12 * optCC G + 16 * optCC G) + 16 * (cost G (pivotOf G σ) : ℝ) := by
    intro σ
    have h1 := (lemma_3_4 (brokenLabel G Q k σ) hk).1
    have h2 : (optK (cliqueGraph (brokenLabel G Q k σ)) k : ℝ) ≤
        cost (cliqueGraph (brokenLabel G Q k σ)) X := by
      exact_mod_cast optK_le _ X
    have h3 := cost_brokenLabel_le G Q hQ hk σ X
    have h4 := sum_brokenPart_le G Q σ
    rw [hX, hQR] at h3
    rw [hQR] at h4
    have h5 : 0 ≤ S σ := sum_nonneg (fun j _ => Nat.cast_nonneg _)
    simp only [hS] at h5
    nlinarith
  have hE := expect_mono hpt
  rw [expect_add, expect_const, expect_smul] at hE
  have hP := hPiv n G
  nlinarith

end CCK
