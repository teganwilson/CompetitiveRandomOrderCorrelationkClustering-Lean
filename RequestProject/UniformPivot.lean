module

public import RequestProject.Lemma62

/-!
# The algorithm UNIFORM PIVOT (Section 6)

UNIFORM PIVOT behaves like PIVOT until the time `T₀` at which the `k`-th pivot arrives.  At time
`T₀`, `S` is the set of pivot clusters with load at most `L = c₀ log n`.  Every later pivot is
assigned to a cluster chosen uniformly at random from `S`, and every non-pivot joins the cluster
of its earliest arrived pivot neighbour.

**Modelling the random choices.**  The choices are independent of the arrival order.  We model
them by a uniformly random `ω : Fin n → Fin (n !)`, independent of `σ`: a pivot `p` arriving after
`T₀` picks the element of index `ω p mod |S|` of `S` (listed in increasing order).  Since `|S|`
divides `n !`, this is an exactly uniform choice from `S`, independently for different pivots.
Clusters are labelled by vertices (a cluster is named after its founding pivot); we show that at
most `k` labels are used, so the output is a `k`-clustering.

For a disjoint-cliques instance we prove the bound used in the proof of Theorem 5: conditioned on
`σ`, the expected cost is at most `W · max_{p ∈ S} |K(p)| + F / |S|`, where `W` is the number of
vertices uncovered at time `T₀` and `F` the number of pairs of vertices of distinct uncovered
cliques (`Cost₁` and `Cost₂` in the paper).
-/

@[expose] public section

open Finset
open scoped Classical Nat

namespace CCK

variable {n : ℕ}

/-- Choose the element of index `x mod |S|` from `S` (sorted increasingly); `d` if `S = ∅`. -/
noncomputable def chooseFrom (S : Finset (Fin n)) (x : ℕ) (d : Fin n) : Fin n :=
  if h : 0 < S.card then
    (S.sort (· ≤ ·))[x % S.card]'(by rw [Finset.length_sort]; exact Nat.mod_lt _ h)
  else d

/-- The cluster label of a pivot `p` in UNIFORM PIVOT (Section 6): `p` itself if `p` arrives by
time `T₀` (the arrival of the `k`-th pivot), and otherwise the cluster of `S` picked by the
random choice `ω p`. -/
noncomputable def upLabel (G : SimpleGraph (Fin n)) (k : ℕ) (L : ℝ) (σ : Equiv.Perm (Fin n))
    (ω : Fin n → Fin (n !)) (p : Fin n) : Fin n :=
  if arrTime σ p < kthPivotTime G σ k then p
  else chooseFrom (lightPivots G σ k L) (ω p) p

/-- **Algorithm UNIFORM PIVOT (Section 6).**  The cluster of a vertex `v` is the cluster of its
pivot (`v` itself if `v` is a pivot, otherwise its earliest arrived pivot neighbour). -/
noncomputable def uniformPivot (G : SimpleGraph (Fin n)) (k : ℕ) (L : ℝ) (σ : Equiv.Perm (Fin n))
    (ω : Fin n → Fin (n !)) : Fin n → Fin n :=
  fun v => upLabel G k L σ ω (pivotOf G σ v)

/-- Expectation over the random choices `ω` of UNIFORM PIVOT. -/
noncomputable def expectω (f : (Fin n → Fin (n !)) → ℝ) : ℝ :=
  (∑ ω, f ω) / (Fintype.card (Fin n → Fin (n !)))

/-- The expected cost of UNIFORM PIVOT with threshold `L`, over a uniformly random arrival order
and independent random choices. -/
noncomputable def uniformPivotExpCost (G : SimpleGraph (Fin n)) (k : ℕ) (L : ℝ) : ℝ :=
  expect (fun σ => expectω (fun ω => (cost G (uniformPivot G k L σ ω) : ℝ)))

/-! ### Uniformity of the random choices -/

/-- Auxiliary result for the algorithm UNIFORM PIVOT (Section 6). -/
lemma card_omega_pos : (0 : ℝ) < Fintype.card (Fin n → Fin (n !)) := by
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  have := Nat.factorial_pos n
  positivity

/-- Auxiliary result for the algorithm UNIFORM PIVOT (Section 6). -/
lemma card_mod_eq (M s c : ℕ) (hs : 0 < s) (hsM : s ∣ M) (hc : c < s) :
    (univ.filter (fun x : Fin M => (x : ℕ) % s = c)).card = M / s := by
  have h1 : (univ.filter (fun x : Fin M => (x : ℕ) % s = c)).card =
      ((range M).filter (fun x => x ≡ c [MOD s])).card := by
    rw [← card_map Fin.valEmbedding]
    congr 1
    ext x
    simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply, mem_range,
      Nat.ModEq, Nat.mod_eq_of_lt hc]
    constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨y.2, hy⟩
    · rintro ⟨hx, h⟩; exact ⟨⟨x, hx⟩, h, rfl⟩
  rw [h1, ← Nat.count_eq_card_filter_range, Nat.count_modEq_card _ hs]
  simp [Nat.mod_eq_zero_of_dvd hsM]

/-- For two distinct pivots, the choices agree modulo `s` with probability exactly `1/s`
whenever `s ∣ n !`. -/
lemma expectω_mod_eq {a b : Fin n} (hab : a ≠ b) {s : ℕ} (hs : 0 < s) (hsn : s ∣ n !) :
    expectω (fun ω : Fin n → Fin (n !) =>
      if (ω a : ℕ) % s = (ω b : ℕ) % s then (1 : ℝ) else 0) = 1 / s := by
  unfold expectω
  set M := Nat.factorial n with hMdef
  have hsum : (∑ ω : Fin n → Fin M, if (ω a : ℕ) % s = (ω b : ℕ) % s then (1 : ℝ) else 0) =
      ∑ ρ : {j // j ≠ a} → Fin M, ((M / s : ℕ) : ℝ) := by
    rw [← (Equiv.funSplitAt a (Fin M)).symm.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
    apply sum_congr rfl
    intro ρ _
    simp only [Equiv.funSplitAt_symm_apply, dite_true, dif_neg hab.symm]
    rw [sum_boole]
    congr 1
    exact_mod_cast card_mod_eq M s _ hs hsn (Nat.mod_lt _ hs)
  rw [hsum, sum_const, card_univ, nsmul_eq_mul]
  have hc1 : Fintype.card ({j // j ≠ a} → Fin M) = M ^ (n - 1) := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_subtype_compl, Fintype.card_fin,
      Fintype.card_unique]
  have hc2 : Fintype.card (Fin n → Fin M) = M ^ n := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  have hn : 0 < n := Fin.pos a
  rw [hc1, hc2]
  obtain ⟨m, hm⟩ := hsn
  rw [hm, Nat.mul_div_cancel_left _ hs]
  have : (s * m : ℕ) ^ n = (s * m) ^ (n - 1) * (s * m) := by
    rw [← pow_succ, Nat.sub_add_cancel hn]
  rw [this]
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · have := Nat.factorial_pos n; rw [← hMdef, hm, h] at this; omega
    · exact h
  push_cast
  field_simp

/-! ### PIVOT on a disjoint-cliques graph -/

section cliques

variable {ι : Type*} (q : Fin n → ι) (σ : Equiv.Perm (Fin n))

/-- Auxiliary result for the algorithm UNIFORM PIVOT (Section 6). -/
lemma pivotOf_eq_of_cidx_eq {u v : Fin n} (h : cidx q u = cidx q v) :
    pivotOf (cliqueGraph q) σ u = pivotOf (cliqueGraph q) σ v := by
  by_contra hne
  apply not_adj_of_isPivot (cliqueGraph q) σ (isPivot_pivotOf _ σ u) (isPivot_pivotOf _ σ v)
  show _ ∧ _
  refine ⟨hne, ?_⟩
  rw [← cidx_eq_iff q, cidx_pivotOf_clique, cidx_pivotOf_clique, h]

/-- The vertices uncovered at time `T₀` (the set `U` of Theorem 5): vertices whose clique has no
vertex among the first `T₀` arrivals, i.e. whose pivot arrives after `T₀`. -/
noncomputable def lateSet (k : ℕ) : Finset (Fin n) :=
  univ.filter (fun v => kthPivotTime (cliqueGraph q) σ k ≤
    arrTime σ (pivotOf (cliqueGraph q) σ v))

/-- The maximum size of a (leading) clique of a cluster in `S`. -/
noncomputable def maxLead (k : ℕ) (L : ℝ) : ℕ :=
  (lightPivots (cliqueGraph q) σ k L).sup (fun p => (univ.filter (fun u => cidx q u = cidx q p)).card)

/-- The number of ordered pairs of uncovered vertices in distinct cliques (`2F` in the proof of
Theorem 5). -/
noncomputable def latePairs (k : ℕ) : ℕ :=
  ((lateSet q σ k ×ˢ lateSet q σ k).filter (fun x => cidx q x.1 ≠ cidx q x.2)).card

/-- Auxiliary result for the algorithm UNIFORM PIVOT (Section 6). -/
lemma chooseFrom_mem {S : Finset (Fin n)} (hS : 0 < S.card) (x : ℕ) (d : Fin n) :
    chooseFrom S x d ∈ S := by
  unfold chooseFrom
  rw [dif_pos hS]
  rw [← Finset.mem_sort (· ≤ ·)]
  exact List.getElem_mem _

/-- Auxiliary result for the algorithm UNIFORM PIVOT (Section 6). -/
lemma chooseFrom_eq_iff {S : Finset (Fin n)} (hS : 0 < S.card) (x y : ℕ) (d e : Fin n) :
    chooseFrom S x d = chooseFrom S y e ↔ x % S.card = y % S.card := by
  unfold chooseFrom
  rw [dif_pos hS, dif_pos hS]
  exact (Finset.sort_nodup S (· ≤ ·)).getElem_inj_iff

/-- Auxiliary result for the algorithm UNIFORM PIVOT (Section 6). -/
lemma chooseFrom_of_card_eq_zero {S : Finset (Fin n)} (hS : S.card = 0) (x : ℕ) (d : Fin n) :
    chooseFrom S x d = d := by
  unfold chooseFrom; rw [dif_neg (by omega)]

/-- Auxiliary result for the algorithm UNIFORM PIVOT (Section 6). -/
lemma expectω_mono {f g : (Fin n → Fin (n !)) → ℝ} (h : ∀ ω, f ω ≤ g ω) :
    expectω f ≤ expectω g :=
  div_le_div_of_nonneg_right (sum_le_sum (fun ω _ => h ω)) card_omega_pos.le

/-- Auxiliary result for the algorithm UNIFORM PIVOT (Section 6). -/
lemma expectω_add_const (c : ℝ) (f : (Fin n → Fin (n !)) → ℝ) :
    expectω (fun ω => c + f ω) = c + expectω f := by
  unfold expectω
  rw [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, add_div,
    mul_div_cancel_left₀ _ card_omega_pos.ne']

/-- Auxiliary result for the algorithm UNIFORM PIVOT (Section 6). -/
lemma expectω_sum {κ : Type*} (s : Finset κ) (f : κ → (Fin n → Fin (n !)) → ℝ) :
    expectω (fun ω => ∑ i ∈ s, f i ω) = ∑ i ∈ s, expectω (f i) := by
  unfold expectω; rw [sum_comm, sum_div]

/-- Auxiliary result for the algorithm UNIFORM PIVOT (Section 6). -/
lemma expectω_mul_const (c : ℝ) (f : (Fin n → Fin (n !)) → ℝ) :
    expectω (fun ω => c * f ω) = c * expectω f := by
  unfold expectω; rw [← mul_sum, mul_div_assoc]

/-- The cost decomposition of the proof of Theorem 5, conditioned on the arrival order: the
expected cost over the random choices is at most `W · max_{p ∈ S} |K(p)| + F / |S|`. -/
theorem expectω_cost_le (k : ℕ) (L : ℝ) :
    expectω (fun ω => (cost (cliqueGraph q) (uniformPivot (cliqueGraph q) k L σ ω) : ℝ)) ≤
      (lateSet q σ k).card * maxLead q σ k L +
        (latePairs q σ k : ℝ) / (2 * (lightPivots (cliqueGraph q) σ k L).card) := by
  set G := cliqueGraph q with hG
  set T0 := kthPivotTime G σ k with hT0
  set S := lightPivots G σ k L with hS
  set late := lateSet q σ k with hlate
  set P : Fin n → Fin n := pivotOf G σ with hP
  set LP := (late ×ˢ late).filter (fun x => cidx q x.1 ≠ cidx q x.2) with hLP
  have hPc : ∀ v, cidx q (P v) = cidx q v := cidx_pivotOf_clique q σ
  have hmemlate : ∀ v, v ∈ late ↔ T0 ≤ arrTime σ (P v) := by
    intro v; simp [hlate, lateSet, hT0, hP, hG]
  have hCe : ∀ ω v, v ∉ late → uniformPivot G k L σ ω v = P v := by
    intro ω v hv
    rw [hmemlate] at hv
    simp only [uniformPivot, upLabel, ← hT0, ← hP]
    rw [if_pos (by omega)]
  have hCl : ∀ ω v, v ∈ late → uniformPivot G k L σ ω v = chooseFrom S (ω (P v)) (P v) := by
    intro ω v hv
    rw [hmemlate] at hv
    simp only [uniformPivot, upLabel, ← hT0, ← hP, ← hS]
    rw [if_neg (by omega)]
  have hPne : ∀ u v, cidx q u ≠ cidx q v → P u ≠ P v := by
    intro u v h he; apply h; rw [← hPc u, ← hPc v, he]
  -- the pointwise bound
  have hpt : ∀ ω, (cost G (uniformPivot G k L σ ω) : ℝ) ≤ late.card * maxLead q σ k L +
      (1 / 2 : ℝ) * ∑ x ∈ LP, (if 0 < S.card ∧
        (ω (P x.1) : ℕ) % S.card = (ω (P x.2) : ℕ) % S.card then (1 : ℝ) else 0) := by
    intro ω
    set C := uniformPivot G k L σ ω with hC
    set inner : Fin n → Finset (Fin n) := fun u =>
      univ.filter (fun w => P w ∈ S ∧ P w = chooseFrom S (ω (P u)) (P u)) with hinner
    have hinner_card : ∀ u, (inner u).card ≤ maxLead q σ k L := by
      intro u
      by_cases hc : chooseFrom S (ω (P u)) (P u) ∈ S
      · refine le_trans (card_le_card ?_) (le_sup (f := fun p =>
          (univ.filter (fun w => cidx q w = cidx q p)).card) hc)
        intro w hw
        simp only [hinner, mem_filter, mem_univ, true_and] at hw
        simp only [mem_filter, mem_univ, true_and]
        rw [← hPc w, hw.2]
      · have : inner u = ∅ := by
          ext w; simp only [hinner, mem_filter, mem_univ, true_and, Finset.notMem_empty,
            iff_false, not_and]
          intro h1 h2; exact hc (h2 ▸ h1)
        rw [this]; exact Nat.zero_le _
    set A1 := late.biUnion (fun u => (inner u).map ⟨fun w => (u, w), fun a b h => by
      simpa using h⟩) with hA1
    set A2 := late.biUnion (fun u => (inner u).map ⟨fun w => (w, u), fun a b h => by
      simpa using h⟩) with hA2
    set A3 := LP.filter (fun x => 0 < S.card ∧
        (ω (P x.1) : ℕ) % S.card = (ω (P x.2) : ℕ) % S.card) with hA3
    have hsub : univ.filter (fun x : Fin n × Fin n => Disagree G C x.1 x.2) ⊆ A1 ∪ A2 ∪ A3 := by
      rintro ⟨u, v⟩ hx
      simp only [mem_filter, mem_univ, true_and, hG, disagree_cliqueGraph] at hx
      have hx' : cidx q u ≠ cidx q v ∧ C u = C v := by
        rcases hx with ⟨h1, h2, -⟩ | ⟨h1, h2⟩
        · exfalso; apply h2
          have : P u = P v := pivotOf_eq_of_cidx_eq q σ ((cidx_eq_iff q u v).2 h1)
          simp only [hC, uniformPivot, ← hP, this]
        · exact ⟨fun h => h1 ((cidx_eq_iff q u v).1 h), h2⟩
      obtain ⟨hcid, hCuv⟩ := hx'
      have hPuv := hPne u v hcid
      by_cases hu : u ∈ late <;> by_cases hv : v ∈ late
      · -- both late
        apply mem_union_right
        rw [hC, hCl ω u hu, hCl ω v hv] at hCuv
        by_cases hs : 0 < S.card
        · rw [chooseFrom_eq_iff hs] at hCuv
          simp only [hA3, hLP, mem_filter, mem_product]
          exact ⟨⟨⟨hu, hv⟩, hcid⟩, hs, hCuv⟩
        · rw [chooseFrom_of_card_eq_zero (by omega), chooseFrom_of_card_eq_zero (by omega)]
            at hCuv
          exact absurd hCuv hPuv
      · -- u late, v early
        apply mem_union_left; apply mem_union_left
        rw [hC, hCl ω u hu, hCe ω v hv] at hCuv
        by_cases hs : 0 < S.card
        · simp only [hA1, mem_biUnion, mem_map, Function.Embedding.coeFn_mk, Prod.mk.injEq]
          refine ⟨u, hu, v, ?_, rfl, rfl⟩
          simp only [hinner, mem_filter, mem_univ, true_and]
          exact ⟨hCuv ▸ chooseFrom_mem hs _ _, hCuv.symm⟩
        · rw [chooseFrom_of_card_eq_zero (by omega)] at hCuv
          exact absurd hCuv hPuv
      · -- u early, v late
        apply mem_union_left; apply mem_union_right
        rw [hC, hCe ω u hu, hCl ω v hv] at hCuv
        by_cases hs : 0 < S.card
        · simp only [hA2, mem_biUnion, mem_map, Function.Embedding.coeFn_mk, Prod.mk.injEq]
          refine ⟨v, hv, u, ?_, rfl, rfl⟩
          simp only [hinner, mem_filter, mem_univ, true_and]
          exact ⟨hCuv.symm ▸ chooseFrom_mem hs _ _, hCuv⟩
        · rw [chooseFrom_of_card_eq_zero (by omega)] at hCuv
          exact absurd hCuv hPuv
      · -- both early
        rw [hC, hCe ω u hu, hCe ω v hv] at hCuv
        exact absurd hCuv hPuv
    have hA12 : ∀ A : Finset (Fin n × Fin n), (A = A1 ∨ A = A2) →
        A.card ≤ late.card * maxLead q σ k L := by
      rintro A (rfl | rfl)
      · refine card_biUnion_le.trans ?_
        rw [← smul_eq_mul, ← sum_const]
        exact sum_le_sum (fun u _ => by rw [card_map]; exact hinner_card u)
      · refine card_biUnion_le.trans ?_
        rw [← smul_eq_mul, ← sum_const]
        exact sum_le_sum (fun u _ => by rw [card_map]; exact hinner_card u)
    have hdis : disagreeCount G C ≤ 2 * (late.card * maxLead q σ k L) + A3.card := by
      unfold disagreeCount
      refine (card_le_card hsub).trans ?_
      refine (card_union_le _ _).trans ?_
      have := card_union_le A1 A2
      have h1 := hA12 A1 (Or.inl rfl)
      have h2 := hA12 A2 (Or.inr rfl)
      omega
    have h2c := two_mul_cost G C
    have hA3sum : (A3.card : ℝ) = ∑ x ∈ LP, (if 0 < S.card ∧
        (ω (P x.1) : ℕ) % S.card = (ω (P x.2) : ℕ) % S.card then (1 : ℝ) else 0) := by
      rw [sum_boole]
    have : (2 * cost G C : ℝ) ≤ 2 * (late.card * maxLead q σ k L) + A3.card := by
      exact_mod_cast h2c ▸ hdis
    rw [← hA3sum]
    linarith
  refine (expectω_mono hpt).trans ?_
  rw [expectω_add_const, expectω_mul_const, expectω_sum]
  apply add_le_add le_rfl
  by_cases hs : 0 < S.card
  · have hterm : ∀ x ∈ LP, expectω (fun ω : Fin n → Fin (n !) => if 0 < S.card ∧
        (ω (P x.1) : ℕ) % S.card = (ω (P x.2) : ℕ) % S.card then (1 : ℝ) else 0) =
        1 / S.card := by
      intro x hx
      have hx' := (mem_filter.1 hx).2
      have hsn : S.card ∣ n ! := Nat.dvd_factorial hs (by simpa using card_le_univ S)
      rw [← expectω_mod_eq (hPne _ _ hx') hs hsn]
      congr 1; funext ω; simp only [hs, true_and]
    rw [sum_congr rfl hterm, sum_const, nsmul_eq_mul]
    simp only [latePairs, ← hlate, ← hLP]
    apply le_of_eq
    field_simp
  · have hS0 : S.card = 0 := by omega
    have hterm : ∀ x ∈ LP, expectω (fun ω : Fin n → Fin (n !) => if 0 < S.card ∧
        (ω (P x.1) : ℕ) % S.card = (ω (P x.2) : ℕ) % S.card then (1 : ℝ) else 0) = 0 := by
      intro x _
      unfold expectω; simp [hS0]
    rw [sum_congr rfl hterm, sum_const_zero, hS0]
    simp

end cliques

/-! ### UNIFORM PIVOT outputs a `k`-clustering -/

/-- Auxiliary result for the algorithm UNIFORM PIVOT (Section 6): at most `k` pivots arrive
before the time `T₀` at which the `k`-th pivot arrives. -/
lemma card_pivotsUpTo_kthPivotTime_le (G : SimpleGraph (Fin n)) (σ : Equiv.Perm (Fin n))
    (k : ℕ) : (pivotsUpTo G σ (kthPivotTime G σ k)).card ≤ k := by
  have hstep : ∀ t, (pivotsUpTo G σ (t + 1)).card ≤ (pivotsUpTo G σ t).card + 1 := by
    intro t
    simp only [pivotsUpTo]
    split_ifs
    · exact card_insert_le _ _
    · omega
    · omega
  unfold kthPivotTime
  split_ifs with h
  · rcases Nat.eq_zero_or_pos (Nat.find h) with h0 | h0
    · rw [h0]; simp [pivotsUpTo]
    · obtain ⟨m, hm⟩ : ∃ m, Nat.find h = m + 1 := ⟨Nat.find h - 1, by omega⟩
      have hlt : ¬ k ≤ (pivotsUpTo G σ m).card := Nat.find_min h (by omega)
      rw [hm]
      have := hstep m
      omega
  · push_neg at h
    exact (h n).le

/-- The set `S` is non-empty once the `k`-th pivot exists and `L ≥ 1`: the pivot arriving at
time `T₀` (the `k`-th one) has a cluster consisting of itself only, so its load at time `T₀` is
`1 ≤ L`. -/
lemma lightPivots_nonempty (G : SimpleGraph (Fin n)) (σ : Equiv.Perm (Fin n)) {k : ℕ}
    (hk : 0 < k) {L : ℝ} (hL : 1 ≤ L) (hex : ∃ t, k ≤ (pivotsUpTo G σ t).card) :
    (lightPivots G σ k L).Nonempty := by
  have hT : kthPivotTime G σ k = Nat.find hex := by unfold kthPivotTime; rw [dif_pos hex]
  have hk' : k ≤ (pivotsUpTo G σ (Nat.find hex)).card := Nat.find_spec hex
  have h0 : 0 < Nat.find hex := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
    · rw [h] at hk'; simp [pivotsUpTo] at hk'; omega
    · exact h
  obtain ⟨m, hm⟩ : ∃ m, Nat.find hex = m + 1 := ⟨Nat.find hex - 1, by omega⟩
  have hlt : ¬ k ≤ (pivotsUpTo G σ m).card := Nat.find_min hex (by omega)
  have hsub := pivotsUpTo_mono G σ (Nat.le_succ m)
  obtain ⟨q, hq1, hq2⟩ : ∃ q ∈ pivotsUpTo G σ (m + 1), q ∉ pivotsUpTo G σ m := by
    by_contra hc
    push_neg at hc
    have := card_le_card (show pivotsUpTo G σ (m + 1) ⊆ pivotsUpTo G σ m from hc)
    rw [hm] at hk'
    omega
  have hq := (mem_pivotsUpTo_iff G σ _ q).1 hq1
  have hq' : ¬ (IsPivot G σ q ∧ arrTime σ q < m) := fun h => hq2 ((mem_pivotsUpTo_iff G σ _ q).2 h)
  have hqm : arrTime σ q = m := by
    have := hq.2; by_contra hne; exact hq' ⟨hq.1, by omega⟩
  refine ⟨q, mem_filter.2 ⟨by rw [hT, hm]; exact hq1, ?_⟩⟩
  have hone : pclAt G σ q (kthPivotTime G σ k) ≤ 1 := by
    unfold pclAt
    rw [card_le_one]
    intro u hu w hw
    simp only [mem_inter, mem_filter, mem_univ, true_and, firstSet] at hu hw
    have hu1 := arrTime_pivotOf_le G σ u
    have hw1 := arrTime_pivotOf_le G σ w
    rw [hu.2] at hu1
    rw [hw.2] at hw1
    rw [hT, hm] at hu hw
    exact σ.symm.injective (Fin.ext (by unfold arrTime at *; omega))
  have : (pclAt G σ q (kthPivotTime G σ k) : ℝ) ≤ 1 := by exact_mod_cast hone
  linarith

/-- **UNIFORM PIVOT produces a `k`-clustering.**  For `k ≥ 1` and a threshold `L ≥ 1`, the output
of UNIFORM PIVOT uses at most `k` distinct cluster labels, for every arrival order `σ` and every
outcome `ω` of the random choices.  (The set `S` of light pivot clusters at time `T₀` is never
empty: it contains the `k`-th pivot, whose cluster has load `1` at time `T₀`.) -/
theorem uniformPivot_card_le (G : SimpleGraph (Fin n)) {k : ℕ} (hk : 0 < k) {L : ℝ}
    (hL : 1 ≤ L) (σ : Equiv.Perm (Fin n)) (ω : Fin n → Fin (n !)) :
    (univ.image (uniformPivot G k L σ ω)).card ≤ k := by
  refine le_trans (card_le_card (t := pivotsUpTo G σ (kthPivotTime G σ k)) ?_)
    (card_pivotsUpTo_kthPivotTime_le G σ k)
  intro x hx
  obtain ⟨v, -, rfl⟩ := mem_image.1 hx
  unfold uniformPivot upLabel
  set p := pivotOf G σ v
  have hp : IsPivot G σ p := isPivot_pivotOf G σ v
  split_ifs with h
  · exact (mem_pivotsUpTo_iff G σ _ p).2 ⟨hp, h⟩
  · have hex : ∃ t, k ≤ (pivotsUpTo G σ t).card := by
      by_contra hno
      have hT : kthPivotTime G σ k = n := by unfold kthPivotTime; rw [dif_neg hno]
      exact h (by rw [hT]; exact (σ.symm p).isLt)
    have hS := lightPivots_nonempty G σ hk hL hex
    have hmem := chooseFrom_mem (S := lightPivots G σ k L) (card_pos.2 hS) (ω p) p
    exact (mem_filter.1 hmem).1

end CCK
