module

public import RequestProject.BalancedPivot

/-!
# Structure of BALANCED PIVOT and decomposition of its cost (proof of Theorem 4)

* `Tk G σ k`: the time `T` of the proof of Theorem 4 — the number of arrivals before the
  `(k+1)`-th pivot (`n` if there are at most `k` pivots).  The pivots arriving before `T` are the
  *early* pivots, the others the *late* pivots.
* The cost of BALANCED PIVOT is at most the cost of PIVOT plus the merging cost
  `∑_{p pivot} p_n(p) · L_proj(t_p, cluster of p)` (cost of type (iii) in the proof of Theorem 4,
  charged to the later of two co-clustered pivot clusters), and early pivots do not contribute.
-/

@[expose] public section

open Finset
open scoped Classical

namespace CCK

variable {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) (σ : Equiv.Perm (Fin n))

/-- The time `T` of the proof of Theorem 4: the number of arrivals before the `(k+1)`-th pivot
arrives (`n` if there are at most `k` pivots). -/
noncomputable def Tk : ℕ :=
  if h : ∃ t, k < (pivotsUpTo G σ (t + 1)).card then Nat.find h else n

/-- The merging cost (cost of type (iii) in the proof of Theorem 4): every pair of co-clustered
pivot clusters is charged to the later one, at most `|X| ·` (projected load of its destination
cluster when its pivot arrives). -/
noncomputable def mergeCost : ℕ :=
  ∑ p ∈ pivotsUpTo G σ n, pclSize G σ p * projLoad G k σ (arrTime σ p) (bpLabel G k σ p)

section structure_

/-- Auxiliary result for the proof of Theorem 4 (Section 7.3.4: decomposition of the cost of BALANCED PIVOT). -/
lemma card_pivotsUpTo_succ_le (t : ℕ) :
    (pivotsUpTo G σ (t + 1)).card ≤ (pivotsUpTo G σ t).card + 1 := by
  simp only [pivotsUpTo]
  split_ifs
  · exact card_insert_le _ _
  · omega
  · omega

/-- Auxiliary result for the proof of Theorem 4 (Section 7.3.4: decomposition of the cost of BALANCED PIVOT). -/
lemma card_pivotsUpTo_mono {s t : ℕ} (h : s ≤ t) :
    (pivotsUpTo G σ s).card ≤ (pivotsUpTo G σ t).card :=
  card_le_card (pivotsUpTo_mono G σ h)

/-- Auxiliary result for the proof of Theorem 4 (Section 7.3.4: decomposition of the cost of BALANCED PIVOT). -/
lemma pivotsUpTo_n_eq (t : ℕ) (ht : n ≤ t) : pivotsUpTo G σ t = pivotsUpTo G σ n :=
  pivotsUpTo_eq_of_ge G σ ht

/-- Auxiliary result for the proof of Theorem 4 (Section 7.3.4: decomposition of the cost of BALANCED PIVOT). -/
lemma isPivot_iff_mem (p : Fin n) : IsPivot G σ p ↔ p ∈ pivotsUpTo G σ n := Iff.rfl

/-- Properties of `T` when there are more than `k` pivots. -/
lemma Tk_spec (h : ∃ t, k < (pivotsUpTo G σ (t + 1)).card) :
    Tk G k σ < n ∧ (pivotsUpTo G σ (Tk G k σ)).card = k ∧
      (pivotsUpTo G σ (Tk G k σ + 1)).card = k + 1 := by
  have hT : Tk G k σ = Nat.find h := by unfold Tk; rw [dif_pos h]
  have hs := Nat.find_spec h
  rw [← hT] at hs
  have hle : (pivotsUpTo G σ (Tk G k σ)).card ≤ k := by
    rcases Nat.eq_zero_or_pos (Tk G k σ) with h0 | hpos
    · rw [h0]; simp [pivotsUpTo]
    · have := Nat.find_min h (show Tk G k σ - 1 < Nat.find h by omega)
      push_neg at this
      rwa [show Tk G k σ - 1 + 1 = Tk G k σ by omega] at this
  have hsucc := card_pivotsUpTo_succ_le G σ (Tk G k σ)
  refine ⟨?_, by omega, by omega⟩
  by_contra hn
  push_neg at hn
  rw [pivotsUpTo_succ_of_ge G σ hn] at hs
  omega

/-- Auxiliary result for the proof of Theorem 4 (Section 7.3.4: decomposition of the cost of BALANCED PIVOT). -/
lemma card_pivotsUpTo_le_of_not (h : ¬ ∃ t, k < (pivotsUpTo G σ (t + 1)).card) (t : ℕ) :
    (pivotsUpTo G σ t).card ≤ k := by
  push_neg at h
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp [pivotsUpTo]
  · have := h (t - 1); rwa [show t - 1 + 1 = t by omega] at this

/-- Auxiliary result for the proof of Theorem 4 (Section 7.3.4: decomposition of the cost of BALANCED PIVOT). -/
lemma Tk_le : Tk G k σ ≤ n := by
  by_cases h : ∃ t, k < (pivotsUpTo G σ (t + 1)).card
  · exact (Tk_spec G k σ h).1.le
  · unfold Tk; rw [dif_neg h]

/-- Auxiliary result for the proof of Theorem 4 (Section 7.3.4: decomposition of the cost of BALANCED PIVOT). -/
lemma card_pivotsUpTo_Tk_le : (pivotsUpTo G σ (Tk G k σ)).card ≤ k := by
  by_cases h : ∃ t, k < (pivotsUpTo G σ (t + 1)).card
  · exact (Tk_spec G k σ h).2.1.le
  · exact card_pivotsUpTo_le_of_not G k σ h _

/-- A pivot arriving before `T` has fewer than `k` pivots arriving before it. -/
lemma card_lt_of_arrTime_lt_Tk {p : Fin n} (hp : IsPivot G σ p) (h : arrTime σ p < Tk G k σ) :
    (pivotsUpTo G σ (arrTime σ p)).card < k := by
  have h1 : p ∈ pivotsUpTo G σ (arrTime σ p + 1) :=
    (mem_pivotsUpTo_iff G σ _ p).2 ⟨hp, Nat.lt_succ_self _⟩
  have h2 : p ∉ pivotsUpTo G σ (arrTime σ p) := fun h' =>
    absurd ((mem_pivotsUpTo_iff G σ _ p).1 h').2 (lt_irrefl _)
  have h3 : (pivotsUpTo G σ (arrTime σ p)).card < (pivotsUpTo G σ (arrTime σ p + 1)).card :=
    card_lt_card ⟨pivotsUpTo_mono G σ (Nat.le_succ _), fun hs => h2 (hs h1)⟩
  have h4 := card_pivotsUpTo_mono G σ (show arrTime σ p + 1 ≤ Tk G k σ by omega)
  have h5 := card_pivotsUpTo_Tk_le G k σ
  omega

/-- A pivot arriving at or after `T` has (at least) `k` pivots arriving before it. -/
lemma card_ge_of_Tk_le {p : Fin n} (h : Tk G k σ ≤ arrTime σ p) :
    k ≤ (pivotsUpTo G σ (arrTime σ p)).card := by
  by_cases hex : ∃ t, k < (pivotsUpTo G σ (t + 1)).card
  · have := (Tk_spec G k σ hex).2.1
    have := card_pivotsUpTo_mono G σ h
    omega
  · exfalso
    have hT : Tk G k σ = n := by unfold Tk; rw [dif_neg hex]
    have := arrTime_lt σ p
    omega

/-- The vertices whose pivot is late are exactly the vertices uncovered at time `T`. -/
lemma mem_uncovered_iff_late (t : ℕ) (u : Fin n) :
    u ∈ uncovered G σ t ↔ t ≤ arrTime σ (pivotOf G σ u) := by
  constructor
  · intro hu
    simp only [uncovered, mem_filter, mem_univ, true_and] at hu
    obtain ⟨hut, hunc⟩ := hu
    by_contra hlt
    push_neg at hlt
    by_cases hv : IsPivot G σ u
    · rw [pivotOf_of_isPivot G σ hv] at hlt; omega
    · obtain ⟨hp, hadj, -⟩ := pivotOf_spec_of_not_isPivot G σ hv
      exact hunc _ ((mem_pivotsUpTo_iff G σ _ _).2 ⟨hp, hlt⟩) hadj
  · intro h
    simp only [uncovered, mem_filter, mem_univ, true_and]
    refine ⟨h.trans (arrTime_pivotOf_le G σ u), ?_⟩
    intro p hp hadj
    obtain ⟨hpp, hpt⟩ := (mem_pivotsUpTo_iff G σ _ p).1 hp
    by_cases hv : IsPivot G σ u
    · exact not_adj_of_isPivot G σ hpp hv hadj
    · have := (pivotOf_spec_of_not_isPivot G σ hv).2.2 p hpp hadj
      omega

end structure_

/-! ### The cost decomposition -/

section cost

/-- The projected load is the number of vertices whose pivot arrived before `t` and lies in
cluster `j`. -/
lemma projLoad_eq_card (t j : ℕ) :
    projLoad G k σ t j = (univ.filter (fun v => pivotOf G σ v ∈ pivotsUpTo G σ t ∧
      bpLabel G k σ v = j)).card := by
  unfold projLoad pclSize
  rw [card_eq_sum_card_fiberwise (f := pivotOf G σ)
    (t := (pivotsUpTo G σ t).filter (fun q => bpLabel G k σ q = j))]
  · refine sum_congr rfl (fun q hq => ?_)
    congr 1
    ext v
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro rfl
      exact ⟨⟨(mem_filter.1 hq).1, (bpLabel_pivotOf G k σ v).symm.trans (mem_filter.1 hq).2⟩, rfl⟩
    · rintro ⟨-, h⟩; exact h
  · intro v hv
    simp only [mem_univ, true_and, coe_filter, Set.mem_setOf_eq] at hv ⊢
    exact ⟨hv.1, by rw [bpLabel_pivotOf]; exact hv.2⟩

/-- Early pivots are charged nothing. -/
lemma projLoad_eq_zero_of_early (hk : 0 < k) {p : Fin n} (hp : IsPivot G σ p)
    (h : arrTime σ p < Tk G k σ) : projLoad G k σ (arrTime σ p) (bpLabel G k σ p) = 0 := by
  unfold projLoad
  apply sum_eq_zero
  intro q hq
  exfalso
  obtain ⟨hq1, hq2⟩ := mem_filter.1 hq
  exact bpLabel_ne_of_early G k σ hk hp (card_lt_of_arrTime_lt_Tk G k σ hp h)
    ((mem_pivotsUpTo_iff G σ _ q).1 hq1).2 hq2

/-- The merging cost only involves late pivots. -/
lemma mergeCost_eq_late (hk : 0 < k) :
    mergeCost G k σ = ∑ p ∈ (pivotsUpTo G σ n).filter (fun p => Tk G k σ ≤ arrTime σ p),
      pclSize G σ p * projLoad G k σ (arrTime σ p) (bpLabel G k σ p) := by
  unfold mergeCost
  rw [← sum_filter_add_sum_filter_not (pivotsUpTo G σ n) (fun p => Tk G k σ ≤ arrTime σ p)]
  rw [add_eq_left]
  apply sum_eq_zero
  intro p hp
  obtain ⟨hp1, hp2⟩ := mem_filter.1 hp
  push_neg at hp2
  rw [projLoad_eq_zero_of_early G k σ hk hp1 hp2, mul_zero]

/-- The number of ordered pairs of vertices in distinct pivot clusters but in the same cluster of
BALANCED PIVOT is at most twice the merging cost. -/
lemma mergePairs_le :
    (univ.filter (fun x : Fin n × Fin n => pivotOf G σ x.1 ≠ pivotOf G σ x.2 ∧
      bpLabel G k σ x.1 = bpLabel G k σ x.2)).card ≤ 2 * mergeCost G k σ := by
  let P := pivotOf G σ
  let L := bpLabel G k σ
  set A := univ.filter (fun x : Fin n × Fin n => arrTime σ (P x.2) < arrTime σ (P x.1) ∧
    L x.1 = L x.2) with hA
  have hsub : univ.filter (fun x : Fin n × Fin n => P x.1 ≠ P x.2 ∧ L x.1 = L x.2) ⊆
      A ∪ A.image Prod.swap := by
    rintro ⟨u, v⟩ hx
    simp only [mem_filter, mem_univ, true_and] at hx
    obtain ⟨hne, hl⟩ := hx
    have hne' : arrTime σ (P u) ≠ arrTime σ (P v) := fun h => hne (eq_of_arrTime_eq σ h)
    rcases Nat.lt_or_gt_of_ne hne' with h | h
    · apply mem_union_right
      exact mem_image.2 ⟨(v, u), by simp [hA, h, hl.symm], rfl⟩
    · apply mem_union_left
      simp [hA, h, hl]
  have hcardA : A.card = mergeCost G k σ := by
    have h1 : A.card = ∑ u, (univ.filter (fun v => P v ∈ pivotsUpTo G σ (arrTime σ (P u)) ∧
        L v = L (P u))).card := by
      rw [hA, ← univ_product_univ, card_filter, sum_product]
      refine sum_congr rfl (fun u _ => ?_)
      rw [card_filter]
      refine sum_congr rfl (fun v _ => ?_)
      congr 1
      apply propext
      show (arrTime σ (pivotOf G σ v) < arrTime σ (pivotOf G σ u) ∧
          bpLabel G k σ u = bpLabel G k σ v) ↔
        (pivotOf G σ v ∈ pivotsUpTo G σ (arrTime σ (pivotOf G σ u)) ∧
          bpLabel G k σ v = bpLabel G k σ (pivotOf G σ u))
      rw [mem_pivotsUpTo_iff, bpLabel_pivotOf]
      simp only [isPivot_pivotOf, true_and]
      exact and_congr Iff.rfl eq_comm
    rw [h1]
    have h2 : ∀ u, (univ.filter (fun v => P v ∈ pivotsUpTo G σ (arrTime σ (P u)) ∧
        L v = L (P u))).card = projLoad G k σ (arrTime σ (P u)) (L (P u)) :=
      fun u => (projLoad_eq_card G k σ _ _).symm
    rw [sum_congr rfl (fun u _ => h2 u)]
    unfold mergeCost
    rw [← sum_fiberwise_of_maps_to (g := P) (t := pivotsUpTo G σ n)
      (fun u _ => isPivot_pivotOf G σ u)]
    refine sum_congr rfl (fun p hp => ?_)
    have : ∀ u ∈ univ.filter (fun u => P u = p),
        projLoad G k σ (arrTime σ (P u)) (L (P u)) =
          projLoad G k σ (arrTime σ p) (bpLabel G k σ p) := by
      intro u hu; rw [(mem_filter.1 hu).2]
    rw [sum_congr rfl this, sum_const, smul_eq_mul]
    rfl
  calc _ ≤ (A ∪ A.image Prod.swap).card := card_le_card hsub
    _ ≤ A.card + (A.image Prod.swap).card := card_union_le _ _
    _ ≤ A.card + A.card := by have := card_image_le (s := A) (f := Prod.swap); omega
    _ = 2 * mergeCost G k σ := by rw [hcardA]; ring

/-- **Cost decomposition (proof of Theorem 4).**  The cost of BALANCED PIVOT is at most the cost
of the underlying PIVOT clustering (costs of types (i) and (ii)) plus the merging cost (type (iii)).
-/
theorem cost_bp_le :
    cost G (bpLabel G k σ) ≤ cost G (pivotOf G σ) + mergeCost G k σ := by
  have hsub : univ.filter (fun x : Fin n × Fin n => Disagree G (bpLabel G k σ) x.1 x.2) ⊆
      univ.filter (fun x : Fin n × Fin n => Disagree G (pivotOf G σ) x.1 x.2) ∪
      univ.filter (fun x : Fin n × Fin n => pivotOf G σ x.1 ≠ pivotOf G σ x.2 ∧
        bpLabel G k σ x.1 = bpLabel G k σ x.2) := by
    rintro ⟨u, v⟩ hx
    simp only [mem_filter, mem_univ, true_and, Disagree, mem_union] at hx ⊢
    obtain ⟨hne, (⟨hadj, hl⟩ | ⟨hnadj, hl⟩)⟩ := hx
    · left
      refine ⟨hne, Or.inl ⟨hadj, fun h => hl ?_⟩⟩
      rw [← bpLabel_pivotOf G k σ u, ← bpLabel_pivotOf G k σ v, h]
    · by_cases hp : pivotOf G σ u = pivotOf G σ v
      · exact Or.inl ⟨hne, Or.inr ⟨hnadj, hp⟩⟩
      · exact Or.inr ⟨hp, hl⟩
  have h1 := (card_le_card hsub).trans (card_union_le _ _)
  have h2 := mergePairs_le G k σ
  have e1 := two_mul_cost G (bpLabel G k σ)
  have e2 := two_mul_cost G (pivotOf G σ)
  unfold disagreeCount at e1 e2
  omega

end cost

end CCK
