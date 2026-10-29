module

public import RequestProject.Thm4Case1
public import RequestProject.Theorem5Expect

/-!
# Theorem 4, Case 2: decomposition of the uncovered vertices

Fix a partition `Q` of the vertices (in the proof, an optimal unconstrained correlation
clustering `Q₁, …, Q_ℓ`, ordered by non-increasing size).  We define the missing-edge
certificates `M_H` and `J_H`, the number `Z_T` of top-`k` groups without a pivot by time `T`, and
prove the deterministic bounds (32), (33), (34) of the proof of Theorem 4.
-/

@[expose] public section

open Finset
open scoped Classical

namespace CCK

variable {n : ℕ} (G : SimpleGraph (Fin n)) {ι : Type*} (Q : Fin n → ι) (k : ℕ)

/-- Ordered pairs of distinct non-adjacent vertices in the same group of `Q` (missing edges within
groups, each counted twice; `|missPairs| = 2 e_m`). -/
noncomputable def missPairs : Finset (Fin n × Fin n) :=
  univ.filter (fun x => x.1 ≠ x.2 ∧ Q x.1 = Q x.2 ∧ ¬ G.Adj x.1 x.2)

/-- `M_t = ∑_{v ∈ V_{≤t}} d⁻(v)` (proof of Theorem 4). -/
noncomputable def Mcnt (t : ℕ) (σ : Equiv.Perm (Fin n)) : ℕ :=
  ((missPairs G Q).filter (fun x => arrTime σ x.1 < t)).card

/-- Number of (ordered) missing-edge pairs within groups with both endpoints among the first `t`
arrivals; it bounds the number `J_t` of non-first pivots (proof of Theorem 4, (28)). -/
noncomputable def Jcnt (t : ℕ) (σ : Equiv.Perm (Fin n)) : ℕ :=
  ((missPairs G Q).filter (fun x => arrTime σ x.1 < t ∧ arrTime σ x.2 < t)).card

/-- `Z_T`: the number of top-`k` groups of `Q` without a pivot by time `T`. -/
noncomputable def Zcnt (σ : Equiv.Perm (Fin n)) : ℕ :=
  ((range (min k (numCliques Q))).filter
    (fun j => ∀ p ∈ earlyPiv G k σ, cidx Q p ≠ j)).card

/-- The good event `G^groups` (29) of the proof of Theorem 4 (from Lemma 7.12 with constant `6`),
for all windows simultaneously. -/
def GoodGroups (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ i ≤ Nat.log 2 n, ∀ j ∈ range n, (∀ p ∈ pivotsUpTo G σ (2 ^ i), p ∉ fib Q j) →
    ((uncovered G σ (2 ^ i) ∩ fib Q j).card : ℝ) < 6 * n * Real.log n / 2 ^ i

/-- Auxiliary result for the proof of Theorem 4 (Section 7.3.4, Small-U case). -/
lemma prob_not_goodGroups :
    prob (fun σ => ¬ GoodGroups G Q σ) ≤ ((Nat.log 2 n + 1) * n : ℕ) * (n : ℝ) ^ (-(6 : ℝ)) := by
  have hsub : ∀ σ, ¬ GoodGroups G Q σ → ∃ i ∈ range (Nat.log 2 n + 1), ∃ j ∈ range n,
      (∀ p ∈ pivotsUpTo G σ (2 ^ i), p ∉ fib Q j) ∧
        6 * n * Real.log n / 2 ^ i ≤ ((uncovered G σ (2 ^ i) ∩ fib Q j).card : ℝ) := by
    intro σ h
    unfold GoodGroups at h
    push_neg at h
    obtain ⟨i, hi, j, hj, h1, h2⟩ := h
    exact ⟨i, mem_range.2 (by omega), j, hj, h1, h2⟩
  refine (prob_mono hsub).trans ?_
  refine le_trans (le_of_eq (prob_congr fun σ => Iff.rfl)) ((prob_exists_le _ _).trans ?_)
  have hper : ∀ i ∈ range (Nat.log 2 n + 1), prob (fun σ => ∃ j ∈ range n,
      (∀ p ∈ pivotsUpTo G σ (2 ^ i), p ∉ fib Q j) ∧
        6 * n * Real.log n / 2 ^ i ≤ ((uncovered G σ (2 ^ i) ∩ fib Q j).card : ℝ)) ≤
      n * (n : ℝ) ^ (-(6 : ℝ)) := by
    intro i hi
    refine le_trans (le_of_eq (prob_congr fun σ => Iff.rfl)) ((prob_exists_le _ _).trans ?_)
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    have h2i : 2 ^ i ≤ n :=
      (Nat.pow_le_pow_right (by norm_num) (Nat.lt_succ_iff.1 (mem_range.1 hi))).trans
        (Nat.pow_log_le_self 2 (by omega))
    refine (sum_le_sum (fun j _ => (le_of_eq (prob_congr fun σ => Iff.rfl)).trans
      (lemma_7_12 G (fib Q j) 6 h2i))).trans (le_of_eq ?_)
    simp
  refine le_trans (sum_le_sum fun i hi => (le_of_eq (prob_congr fun σ => Iff.rfl)).trans
    (hper i hi)) (le_of_eq ?_)
  simp [sum_const, card_range, nsmul_eq_mul, mul_assoc]

variable (σ : Equiv.Perm (Fin n))

/-- Auxiliary result for the proof of Theorem 4 (Section 7.3.4, Small-U case). -/
lemma Mcnt_mono {s t : ℕ} (h : s ≤ t) : Mcnt G Q s σ ≤ Mcnt G Q t σ :=
  card_le_card (monotone_filter_right _ (fun _ _ hx => lt_of_lt_of_le hx h))

/-- Auxiliary result for the proof of Theorem 4 (Section 7.3.4, Small-U case). -/
lemma Jcnt_mono {s t : ℕ} (h : s ≤ t) : Jcnt G Q s σ ≤ Jcnt G Q t σ :=
  card_le_card (monotone_filter_right _ (fun _ _ hx =>
    ⟨lt_of_lt_of_le hx.1 h, lt_of_lt_of_le hx.2 h⟩))

/-- Pivots among the first `t` arrivals whose group has index `< j₀`: all but at most `J_t` of them
are first pivots in distinct groups. -/
lemma card_pivots_grp_lt (t j₀ : ℕ) :
    ((pivotsUpTo G σ t).filter (fun p => cidx Q p < j₀)).card ≤
      (((pivotsUpTo G σ t).filter (fun p => cidx Q p < j₀)).image (cidx Q)).card +
        Jcnt G Q t σ := by
  set F := (pivotsUpTo G σ t).filter (fun p => cidx Q p < j₀)
  set NF := F.filter (fun v => ∃ w ∈ pivotsUpTo G σ t, w ≠ v ∧ Q w = Q v ∧
    arrTime σ w < arrTime σ v)
  have h1 : (F \ NF).card ≤ (F.image (cidx Q)).card := by
    rw [← card_image_of_injOn (f := cidx Q) (s := F \ NF)]
    · exact card_le_card (image_subset_image sdiff_subset)
    · intro v hv v' hv' he
      rw [mem_coe, mem_sdiff] at hv hv'
      have hQ : Q v = Q v' := (cidx_eq_iff Q v v').1 he
      by_contra hne
      have hpv : v ∈ pivotsUpTo G σ t := (mem_filter.1 hv.1).1
      have hpv' : v' ∈ pivotsUpTo G σ t := (mem_filter.1 hv'.1).1
      rcases lt_or_gt_of_ne (fun h => hne (eq_of_arrTime_eq σ h)) with hlt | hlt
      · exact hv'.2 (mem_filter.2 ⟨hv'.1, v, hpv, hne, hQ, hlt⟩)
      · exact hv.2 (mem_filter.2 ⟨hv.1, v', hpv', Ne.symm hne, hQ.symm, hlt⟩)
  have h2 : NF.card ≤ Jcnt G Q t σ := by
    have hex : ∀ v ∈ NF, ∃ w, w ∈ pivotsUpTo G σ t ∧ w ≠ v ∧ Q w = Q v ∧
        arrTime σ w < arrTime σ v := fun v hv => by
      obtain ⟨w, hw, h⟩ := (mem_filter.1 hv).2; exact ⟨w, hw, h⟩
    choose! f hf using hex
    unfold Jcnt
    refine card_le_card_of_injOn (fun v => (f v, v)) ?_ ?_
    · intro v hv
      obtain ⟨hw, hne, hQ, hlt⟩ := hf v hv
      have hvF := (mem_filter.1 hv).1
      have hvP := (mem_filter.1 hvF).1
      obtain ⟨hpw, hwt⟩ := (mem_pivotsUpTo_iff G σ _ _).1 hw
      obtain ⟨hpv, hvt⟩ := (mem_pivotsUpTo_iff G σ _ _).1 hvP
      simp only [coe_filter, Set.mem_setOf_eq, missPairs, mem_filter, mem_univ, true_and]
      exact ⟨⟨hne, hQ, not_adj_of_isPivot G σ hpw hpv⟩, hwt, hvt⟩
    · intro v _ v' _ h
      simp only [Prod.mk.injEq] at h
      exact h.2
  have h3 := card_sdiff_add_card_eq_card (show NF ⊆ F from filter_subset _ _)
  omega

/-- **Inequality (33)** (proof of Theorem 4): `Z_T ≤ X + J` where `X` counts the vertices of
`D₀ = ⋃_{j>k} Q_j` among the first `t ≥ T` arrivals and `J = J_t`. -/
lemma Zcnt_le (h : ∃ t, k < (pivotsUpTo G σ (t + 1)).card) {t : ℕ} (ht : Tk G k σ ≤ t) :
    Zcnt G Q k σ ≤ (firstSet σ t ∩ tailVerts Q k).card + Jcnt G Q t σ := by
  have hE : (pivotsUpTo G σ (Tk G k σ)).card = k := card_earlyPiv G k σ h
  have hsplit := card_filter_add_card_filter_not (s := pivotsUpTo G σ (Tk G k σ))
    (fun p => cidx Q p < k)
  have hA := card_pivots_grp_lt G Q σ (Tk G k σ) k
  have hB : ((pivotsUpTo G σ (Tk G k σ)).filter (fun p => ¬ cidx Q p < k)).card ≤
      (firstSet σ (Tk G k σ) ∩ tailVerts Q k).card := by
    apply card_le_card
    intro p hp
    obtain ⟨hp1, hp2⟩ := mem_filter.1 hp
    refine mem_inter.2 ⟨pivotsUpTo_subset_firstSet G σ _ hp1, ?_⟩
    simp only [tailVerts, mem_filter, mem_univ, true_and]; omega
  have hZI : Zcnt G Q k σ +
      (((pivotsUpTo G σ (Tk G k σ)).filter (fun p => cidx Q p < k)).image (cidx Q)).card ≤ k := by
    have hdisj : Disjoint ((range (min k (numCliques Q))).filter
        (fun j => ∀ p ∈ earlyPiv G k σ, cidx Q p ≠ j))
        (((pivotsUpTo G σ (Tk G k σ)).filter (fun p => cidx Q p < k)).image (cidx Q)) := by
      rw [disjoint_left]
      intro j hj hjI
      obtain ⟨p, hp, rfl⟩ := mem_image.1 hjI
      exact (mem_filter.1 hj).2 p (mem_filter.1 hp).1 rfl
    have hsub : ((range (min k (numCliques Q))).filter
        (fun j => ∀ p ∈ earlyPiv G k σ, cidx Q p ≠ j)) ∪
        (((pivotsUpTo G σ (Tk G k σ)).filter (fun p => cidx Q p < k)).image (cidx Q)) ⊆
          range (min k (numCliques Q)) := by
      intro j hj
      rcases mem_union.1 hj with hj | hj
      · exact (mem_filter.1 hj).1
      · obtain ⟨p, hp, rfl⟩ := mem_image.1 hj
        exact mem_range.2 (lt_min (mem_filter.1 hp).2 (cidx_lt Q p))
    have h1 := card_le_card hsub
    rw [card_union_of_disjoint hdisj, card_range] at h1
    have h2 := min_le_left k (numCliques Q)
    unfold Zcnt
    omega
  have hX := card_le_card (inter_subset_inter_right (u := tailVerts Q k) (firstSet_mono σ ht))
  have hJ := Jcnt_mono G Q σ ht
  omega

/-- **Inequality (34)** (proof of Theorem 4): if `r₀ < k` and `T < t`, then `N + J ≥ k - r₀ + 1`,
where `N` counts the vertices of `D = ⋃_{j > r₀} Q_j` among the first `t` arrivals. -/
lemma N_add_J_ge (h : ∃ t, k < (pivotsUpTo G σ (t + 1)).card) {t : ℕ} (ht : Tk G k σ < t) :
    k + 1 ≤ (firstSet σ t ∩ aVerts Q k).card + Jcnt G Q t σ + rOf Q k := by
  have h2 := (Tk_spec G k σ h).2.2
  have hmono := card_le_card (pivotsUpTo_mono G σ (show Tk G k σ + 1 ≤ t by omega))
  have hsplit := card_filter_add_card_filter_not (s := pivotsUpTo G σ t)
    (fun p => cidx Q p < rOf Q k)
  have hA := card_pivots_grp_lt G Q σ t (rOf Q k)
  have hI : (((pivotsUpTo G σ t).filter (fun p => cidx Q p < rOf Q k)).image (cidx Q)).card ≤
      rOf Q k := by
    have : ((pivotsUpTo G σ t).filter (fun p => cidx Q p < rOf Q k)).image (cidx Q) ⊆
        range (rOf Q k) := by
      intro j hj
      obtain ⟨p, hp, rfl⟩ := mem_image.1 hj
      exact mem_range.2 (mem_filter.1 hp).2
    simpa using card_le_card this
  have hB : ((pivotsUpTo G σ t).filter (fun p => ¬ cidx Q p < rOf Q k)).card ≤
      (firstSet σ t ∩ aVerts Q k).card := by
    apply card_le_card
    intro p hp
    obtain ⟨hp1, hp2⟩ := mem_filter.1 hp
    refine mem_inter.2 ⟨pivotsUpTo_subset_firstSet G σ _ hp1, ?_⟩
    simp only [aVerts, mem_filter, mem_univ, true_and]; omega
  omega

/-- **Inequality (32)** (proof of Theorem 4): on `G^groups`, if `2^i ≤ T < t` with
`i ≤ ⌊log₂ n⌋`, then `|U| ≤ s₀ + M_t + κ_i Z_T` with `κ_i = 6 n ln n / 2^i` (decomposition (31)). -/
lemma card_U_le (hGG : GoodGroups G Q σ) {i t : ℕ} (hi : i ≤ Nat.log 2 n)
    (hiT : 2 ^ i ≤ Tk G k σ) (hTt : Tk G k σ < t) :
    ((uncovered G σ (Tk G k σ)).card : ℝ) ≤
      sOf Q k + Mcnt G Q t σ + Zcnt G Q k σ * (6 * n * Real.log n / 2 ^ i) := by
  set U := uncovered G σ (Tk G k σ)
  set E := earlyPiv G k σ
  set U1 := U.filter (fun v => k ≤ cidx Q v)
  set U2 := U.filter (fun v => cidx Q v < k ∧ ∃ p ∈ E, Q p = Q v)
  set U3 := U.filter (fun v => cidx Q v < k ∧ ∀ p ∈ E, Q p ≠ Q v)
  have hcov : U ⊆ U1 ∪ U2 ∪ U3 := by
    intro v hv
    simp only [U1, U2, U3, mem_union, mem_filter]
    by_cases h1 : k ≤ cidx Q v
    · exact Or.inl (Or.inl ⟨hv, h1⟩)
    · by_cases h2 : ∃ p ∈ E, Q p = Q v
      · exact Or.inl (Or.inr ⟨hv, by omega, h2⟩)
      · push_neg at h2; exact Or.inr ⟨hv, by omega, h2⟩
  have hc1 : U1.card ≤ sOf Q k := by
    rw [← card_tailVerts]
    apply card_le_card
    intro v hv
    simp only [U1, mem_filter] at hv
    simp only [tailVerts, mem_filter, mem_univ, true_and]; exact hv.2
  have hc2 : U2.card ≤ Mcnt G Q t σ := by
    have hex : ∀ v ∈ U2, ∃ p, p ∈ E ∧ Q p = Q v := fun v hv => by
      obtain ⟨p, hp, h⟩ := (mem_filter.1 hv).2.2; exact ⟨p, hp, h⟩
    choose! f hf using hex
    unfold Mcnt
    refine card_le_card_of_injOn (fun v => (f v, v)) ?_ ?_
    · intro v hv
      obtain ⟨hpE, hQ⟩ := hf v hv
      have hvU : v ∈ U := (mem_filter.1 hv).1
      obtain ⟨hpp, hpT⟩ := (mem_earlyPiv G k σ).1 hpE
      have hvU' := hvU
      simp only [U, uncovered, mem_filter, mem_univ, true_and] at hvU'
      simp only [coe_filter, Set.mem_setOf_eq, missPairs, mem_filter, mem_univ, true_and]
      refine ⟨⟨?_, hQ, hvU'.2 _ hpE⟩, by omega⟩
      intro he
      have : arrTime σ (f v) = arrTime σ v := by rw [he]
      omega
    · intro v _ v' _ h
      simp only [Prod.mk.injEq] at h
      exact h.2
  set Zs := (range (min k (numCliques Q))).filter (fun j => ∀ p ∈ E, cidx Q p ≠ j)
  have hκ : ∀ j ∈ Zs, ((uncovered G σ (2 ^ i) ∩ fib Q j).card : ℝ) ≤
      6 * n * Real.log n / 2 ^ i := by
    intro j hj
    obtain ⟨hj1, hj2⟩ := mem_filter.1 hj
    have hjl : j < numCliques Q := lt_of_lt_of_le (mem_range.1 hj1) (min_le_right _ _)
    have hjn : j ∈ range n := mem_range.2 (lt_of_lt_of_le hjl (numCliques_le Q))
    refine (hGG i hi j hjn ?_).le
    intro p hp hpf
    have hpE : p ∈ E := pivotsUpTo_mono G σ hiT hp
    exact hj2 p hpE (by simpa [fib] using hpf)
  have hc3 : (U3.card : ℝ) ≤ Zs.card * (6 * n * Real.log n / 2 ^ i) := by
    have hsub : U3 ⊆ Zs.biUnion (fun j => uncovered G σ (2 ^ i) ∩ fib Q j) := by
      intro v hv
      obtain ⟨hvU, hvk, hvE⟩ := mem_filter.1 hv
      rw [mem_biUnion]
      refine ⟨cidx Q v, mem_filter.2 ⟨mem_range.2 (lt_min hvk (cidx_lt Q v)), ?_⟩, ?_⟩
      · intro p hp he
        exact hvE p hp ((cidx_eq_iff Q p v).1 he)
      · exact mem_inter.2 ⟨uncovered_antitone G σ hiT hvU, by simp [fib]⟩
    have h1 := (card_le_card hsub).trans card_biUnion_le
    calc (U3.card : ℝ) ≤ ((∑ j ∈ Zs, (uncovered G σ (2 ^ i) ∩ fib Q j).card : ℕ) : ℝ) := by
          exact_mod_cast h1
      _ = ∑ j ∈ Zs, ((uncovered G σ (2 ^ i) ∩ fib Q j).card : ℝ) := by push_cast; rfl
      _ ≤ ∑ j ∈ Zs, (6 * n * Real.log n / 2 ^ i) := sum_le_sum hκ
      _ = Zs.card * (6 * n * Real.log n / 2 ^ i) := by rw [sum_const, nsmul_eq_mul]
  have hU := (card_le_card hcov).trans ((card_union_le _ _).trans
    (Nat.add_le_add_right (card_union_le _ _) _))
  have hZ : Zs.card = Zcnt G Q k σ := rfl
  rw [← hZ]
  have : (U.card : ℝ) ≤ U1.card + U2.card + U3.card := by exact_mod_cast hU
  have e1 : (U1.card : ℝ) ≤ sOf Q k := by exact_mod_cast hc1
  have e2 : (U2.card : ℝ) ≤ Mcnt G Q t σ := by exact_mod_cast hc2
  linarith

end CCK


/-!
# Theorem 4, Case 2: expectation estimates

For each window `i` (`2^i ≤ T < H_i = min(2^{i+1}, n)`), we bound the expectation of `|U|` on the
window and the good event `G^groups` by `p_i (4 + 48 ln n) (s₀ a₀ + 2 e_m)`, following
sub-cases 1 and 2 of the proof of Theorem 4 (inequalities (27), (28), (35)–(43)).
-/

@[expose] public section

open Finset
open scoped Classical

namespace CCK

variable {n : ℕ} (G : SimpleGraph (Fin n)) {ι : Type*} (Q : Fin n → ι) (k : ℕ)

/-- The window event `{L_i ≤ T < H_i}` (with `T < n`). -/
def InWin (i : ℕ) (σ : Equiv.Perm (Fin n)) : Prop :=
  2 ^ i ≤ Tk G k σ ∧ Tk G k σ < tWin n i ∧ Tk G k σ < n

/-- Auxiliary result for the proof of Theorem 4 (Section 7.3.4, Small-U case). -/
lemma exists_of_Tk_lt {σ : Equiv.Perm (Fin n)} (hT : Tk G k σ < n) :
    ∃ t, k < (pivotsUpTo G σ (t + 1)).card := by
  by_contra h
  have : Tk G k σ = n := by unfold Tk; rw [dif_neg h]
  omega

/-! ### Expectations of the missing-edge certificates -/

/-- **(27)**: `E[M_H] = p · 2 e_m`. -/
lemma expect_Mcnt (i : ℕ) :
    expect (fun σ => (Mcnt G Q (tWin n i) σ : ℝ)) = (missPairs G Q).card * rhoW n i := by
  have hrw : (fun σ => (Mcnt G Q (tWin n i) σ : ℝ)) = fun σ => ∑ x ∈ missPairs G Q,
      (if x.1 ∈ firstSet σ (tWin n i) then (1 : ℝ) else 0) := by
    funext σ
    rw [sum_boole, Mcnt]
    congr 2
    ext x; simp [firstSet]
  rw [hrw, expect_sum]
  have : ∀ x ∈ missPairs G Q, expect (fun σ => if x.1 ∈ firstSet σ (tWin n i) then (1 : ℝ) else 0)
      = rhoW n i := by
    intro x _
    rw [expect_indicator, prob_mem_firstSet (tWin_le i)]; rfl
  rw [sum_congr rfl this, sum_const, nsmul_eq_mul]

/-- **(28)**: `E[J_H] ≤ p² · 2 e_m`. -/
lemma expect_Jcnt_le (i : ℕ) :
    expect (fun σ => (Jcnt G Q (tWin n i) σ : ℝ)) ≤ (missPairs G Q).card * rhoW n i ^ 2 := by
  have hrw : (fun σ => (Jcnt G Q (tWin n i) σ : ℝ)) = fun σ => ∑ x ∈ missPairs G Q,
      (if x.1 ∈ firstSet σ (tWin n i) ∧ x.2 ∈ firstSet σ (tWin n i) then (1 : ℝ) else 0) := by
    funext σ
    rw [sum_boole, Jcnt]
    congr 2
    ext x; simp [firstSet]
  rw [hrw, expect_sum]
  have : ∀ x ∈ missPairs G Q, expect (fun σ =>
      if x.1 ∈ firstSet σ (tWin n i) ∧ x.2 ∈ firstSet σ (tWin n i) then (1 : ℝ) else 0)
      ≤ rhoW n i ^ 2 := by
    intro x hx
    have hne : x.1 ≠ x.2 := (mem_filter.1 hx).2.1
    rw [expect_indicator, prob_pair_firstSet (tWin_le i) _ _ hne]
    exact pair_ratio_le_rho i
  refine (sum_le_sum this).trans (le_of_eq ?_)
  rw [sum_const, nsmul_eq_mul]

/-! ### Pointwise bounds on the window -/

variable (σ : Equiv.Perm (Fin n))

/-- Auxiliary result for the proof of Theorem 4 (Section 7.3.4, Small-U case). -/
lemma log_le_of_InWin {i : ℕ} (hW : InWin G k i σ) : i ≤ Nat.log 2 n :=
  Nat.le_log_of_pow_le (by norm_num) (hW.1.trans hW.2.2.le)

/-- On the window and `G^groups`, (32), (33) and (34) hold with `t = H_i`. -/
lemma window_bounds {i : ℕ} (hW : InWin G k i σ) (hGG : GoodGroups G Q σ) :
    ((uncovered G σ (Tk G k σ)).card : ℝ) ≤
        sOf Q k + Mcnt G Q (tWin n i) σ + Zcnt G Q k σ * (6 * n * Real.log n / 2 ^ i) ∧
      Zcnt G Q k σ ≤ Ycnt Q k i σ + Jcnt G Q (tWin n i) σ ∧
      k + 1 ≤ Ncnt Q k i σ + Jcnt G Q (tWin n i) σ + rOf Q k := by
  have h := exists_of_Tk_lt G k hW.2.2
  exact ⟨card_U_le G Q k σ hGG (log_le_of_InWin G k σ hW) hW.1 hW.2.1,
    Zcnt_le G Q k σ h hW.2.1.le, N_add_J_ge G Q k σ h hW.2.1⟩

/-- **Counting inequalities (39) and (40)** of the proof of Theorem 4. -/
lemma counting_39_40 {X N J Z d : ℕ} (hd : 1 ≤ d) (hZ : Z ≤ X + J) (hXN : X ≤ N)
    (hNJ : d + 1 ≤ N + J) :
    (Z : ℝ) ≤ 2 * J + 2 / d * (X * ((N : ℝ) - 1)) ∧
      (1 : ℝ) ≤ 2 * J / d + 4 / (d : ℝ) ^ 2 * (N * ((N : ℝ) - 1)) := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hZR : (Z : ℝ) ≤ X + J := by exact_mod_cast hZ
  have hXNR : (X : ℝ) ≤ N := by exact_mod_cast hXN
  have hX0 : (0 : ℝ) ≤ X := Nat.cast_nonneg _
  have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg _
  by_cases hcase : 2 * N ≤ d + 1
  · have hJN : N ≤ J := by omega
    have hJd : d + 1 ≤ 2 * J := by omega
    have hJNR : (N : ℝ) ≤ J := by exact_mod_cast hJN
    have hJdR : (d : ℝ) + 1 ≤ 2 * J := by exact_mod_cast hJd
    have hXN1 : 0 ≤ (X : ℝ) * ((N : ℝ) - 1) := by
      rcases Nat.eq_zero_or_pos X with h0 | h0
      · rw [h0]; simp
      · have : (1 : ℝ) ≤ N := by exact_mod_cast (h0.trans_le hXN)
        nlinarith
    have hNN : 0 ≤ (N : ℝ) * ((N : ℝ) - 1) := card_mul_card_sub_one_nonneg N
    refine ⟨?_, ?_⟩
    · have : 0 ≤ 2 / (d : ℝ) * (X * ((N : ℝ) - 1)) := by positivity
      linarith
    · have h1 : 1 ≤ 2 * (J : ℝ) / d := by rw [le_div_iff₀ hd0]; linarith
      have : 0 ≤ 4 / (d : ℝ) ^ 2 * (N * ((N : ℝ) - 1)) := by positivity
      linarith
  · have hN : d + 2 ≤ 2 * N := by omega
    have hNR : (d : ℝ) + 2 ≤ 2 * N := by exact_mod_cast hN
    refine ⟨?_, ?_⟩
    · have h1 : (X : ℝ) ≤ 2 / d * (X * ((N : ℝ) - 1)) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hd0]
        nlinarith
      linarith
    · have h1 : 1 ≤ 4 / (d : ℝ) ^ 2 * (N * ((N : ℝ) - 1)) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        nlinarith
      have : 0 ≤ 2 * (J : ℝ) / d := by positivity
      linarith

/-! ### The window estimates -/

/-- The contribution `|U| 1_{window i} 1_{G^groups}`. -/
noncomputable def fWin (i : ℕ) (σ : Equiv.Perm (Fin n)) : ℝ :=
  if InWin G k i σ ∧ GoodGroups G Q σ then ((uncovered G σ (Tk G k σ)).card : ℝ) else 0

/-- Auxiliary result for the proof of Theorem 4 (Section 7.3.4, Small-U case). -/
lemma fWin_nonneg (i : ℕ) : 0 ≤ fWin G Q k i σ := by
  unfold fWin; split_ifs <;> positivity

/-- Auxiliary result for the proof of Theorem 4 (Section 7.3.4, Small-U case). -/
lemma kappa_mul_rho (hn : 2 ≤ n) (i : ℕ) :
    6 * n * Real.log n / 2 ^ i * rhoW n i ≤ 12 * Real.log n := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hl : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  unfold rhoW
  have ht : (tWin n i : ℝ) ≤ 2 ^ (i + 1) := by
    have : tWin n i ≤ 2 ^ (i + 1) := min_le_left _ _
    exact_mod_cast this
  have e : 6 * n * Real.log n / 2 ^ i * ((tWin n i : ℝ) / n) =
      6 * Real.log n * ((tWin n i : ℝ) / 2 ^ i) := by
    field_simp
  rw [e]
  have : (tWin n i : ℝ) / 2 ^ i ≤ 2 := by
    rw [div_le_iff₀ (by positivity)]; rw [pow_succ] at ht; linarith
  nlinarith

variable {G Q k}

/-- **Sub-case 1 (`p a₀ ≥ 1/4`, or `s₀ = 0`, which includes the case `ℓ ≤ k`)**, inequalities (38)
and (44): `E[|U| 1_{B_i ∩ G^groups}] ≤ p (4 + 48 ln n)(s₀ a₀ + 2 e_m)`. -/
theorem expect_fWin_sub1 (hn : 2 ≤ n) (i : ℕ)
    (hA : sOf Q k = 0 ∨ 1 / 4 ≤ rhoW n i * aOf Q k) :
    expect (fWin G Q k i) ≤ rhoW n i * (4 + 48 * Real.log n) *
      (sOf Q k * aOf Q k + (missPairs G Q).card) := by
  set κ := 6 * n * Real.log n / 2 ^ i
  set p := rhoW n i
  set s0 := (sOf Q k : ℝ)
  set mp := ((missPairs G Q).card : ℝ)
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hl : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  have hκ0 : 0 ≤ κ := by positivity
  have hp0 : 0 ≤ p := rhoW_nonneg i
  have hpt : ∀ σ, fWin G Q k i σ ≤ s0 + (Mcnt G Q (tWin n i) σ : ℝ) +
      κ * ((Ycnt Q k i σ : ℝ) + Jcnt G Q (tWin n i) σ) := by
    intro σ
    unfold fWin
    split_ifs with h
    · obtain ⟨h1, h2, -⟩ := window_bounds G Q k σ h.1 h.2
      have h2R : (Zcnt G Q k σ : ℝ) ≤ Ycnt Q k i σ + Jcnt G Q (tWin n i) σ := by
        exact_mod_cast h2
      have : (Zcnt G Q k σ : ℝ) * κ ≤ κ * ((Ycnt Q k i σ : ℝ) + Jcnt G Q (tWin n i) σ) := by
        rw [mul_comm]; exact mul_le_mul_of_nonneg_left h2R hκ0
      linarith
    · positivity
  have hE := expect_mono hpt
  have hlin : expect (fun σ => s0 + (Mcnt G Q (tWin n i) σ : ℝ) +
      κ * ((Ycnt Q k i σ : ℝ) + Jcnt G Q (tWin n i) σ)) =
      s0 + expect (fun σ => (Mcnt G Q (tWin n i) σ : ℝ)) +
        κ * (expect (fun σ => (Ycnt Q k i σ : ℝ)) +
          expect (fun σ => (Jcnt G Q (tWin n i) σ : ℝ))) := by
    rw [expect_add, expect_add, expect_const, expect_smul, expect_add]
  rw [hlin, expect_Mcnt, expect_Ycnt] at hE
  have hJ := expect_Jcnt_le G Q i
  have hκp := kappa_mul_rho hn i
  have hs0 : s0 ≤ 4 * p * (s0 * aOf Q k) := by
    rcases hA with h0 | h0
    · simp [s0, h0]
    · have : 0 ≤ s0 := Nat.cast_nonneg _
      nlinarith
  have hsa : 0 ≤ s0 * aOf Q k := by
    have := hs0; have : 0 ≤ s0 := Nat.cast_nonneg _
    rcases hA with h0 | h0
    · simp [s0, h0]
    · have ha : 0 ≤ aOf Q k := by
        by_contra hneg; push_neg at hneg
        have : p * aOf Q k ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hp0 hneg.le
        linarith
      positivity
  have hmp : 0 ≤ mp := Nat.cast_nonneg _
  have t1 : κ * (s0 * p) ≤ 12 * Real.log n * s0 := by
    have : κ * (s0 * p) = (κ * p) * s0 := by ring
    rw [this]; exact mul_le_mul_of_nonneg_right hκp (Nat.cast_nonneg _)
  have t2 : κ * (mp * p ^ 2) ≤ 12 * Real.log n * (p * mp) := by
    have : κ * (mp * p ^ 2) = (κ * p) * (p * mp) := by ring
    rw [this]; exact mul_le_mul_of_nonneg_right hκp (by positivity)
  have t3 : 12 * Real.log n * s0 ≤ 12 * Real.log n * (4 * p * (s0 * aOf Q k)) :=
    mul_le_mul_of_nonneg_left hs0 (by positivity)
  have hJ' : κ * expect (fun σ => (Jcnt G Q (tWin n i) σ : ℝ)) ≤ κ * (mp * p ^ 2) :=
    mul_le_mul_of_nonneg_left hJ hκ0
  have : 0 ≤ p * (s0 * aOf Q k) := by positivity
  have : 0 ≤ Real.log n * (p * mp) := by positivity
  nlinarith

/-- Auxiliary result for the proof of Theorem 4 (Section 7.3.4, Small-U case). -/
lemma lt_numCliques_of_sOf_pos (hs : 0 < sOf Q k) : k < numCliques Q := by
  by_contra h
  push_neg at h
  have : sOf Q k = 0 := tailSum_eq_zero h
  omega

/-- **Sub-case 2 (`p a₀ < 1/4`, `s₀ > 0`)**, inequalities (39)–(43):
`E[|U| 1_{B_i ∩ G^groups}] ≤ p (4 + 48 ln n)(s₀ a₀ + 2 e_m)`. -/
theorem expect_fWin_sub2 (hk0 : 0 < k) (hn : 2 ≤ n) (i : ℕ) (hs : 0 < sOf Q k)
    (hpa : rhoW n i * aOf Q k < 1 / 4) :
    expect (fWin G Q k i) ≤ rhoW n i * (4 + 48 * Real.log n) *
      (sOf Q k * aOf Q k + (missPairs G Q).card) := by
  have hk := lt_numCliques_of_sOf_pos hs
  have hrk := rOf_lt hk0 hk
  set κ := 6 * n * Real.log n / 2 ^ i
  set p := rhoW n i
  set s0 := (sOf Q k : ℝ)
  set a0 := aOf Q k
  set mp := ((missPairs G Q).card : ℝ)
  set d : ℕ := k - rOf Q k with hd
  have hd1 : 1 ≤ d := by omega
  have hdR : (d : ℝ) = (k : ℝ) - rOf Q k := by rw [hd]; push_cast [hrk.le]; ring
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd1
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hl : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  have hκ0 : 0 ≤ κ := by positivity
  have hp0 : 0 ≤ p := rhoW_nonneg i
  have ha0 : 0 ≤ a0 := aOf_nonneg hk0 hk
  have hs0 : 0 ≤ s0 := Nat.cast_nonneg _
  have hmp : 0 ≤ mp := Nat.cast_nonneg _
  set g : Equiv.Perm (Fin n) → ℝ := fun σ =>
    (s0 * (2 / d) + 2 * κ) * (Jcnt G Q (tWin n i) σ : ℝ) +
      s0 * (4 / (d : ℝ) ^ 2) * ((Ncnt Q k i σ : ℝ) * ((Ncnt Q k i σ : ℝ) - 1)) +
      (Mcnt G Q (tWin n i) σ : ℝ) +
      κ * (2 / d) * ((Ycnt Q k i σ : ℝ) * ((Ncnt Q k i σ : ℝ) - 1)) with hg
  have hpt : ∀ σ, fWin G Q k i σ ≤ g σ := by
    intro σ
    have hNN := card_mul_card_sub_one_nonneg (Ncnt Q k i σ)
    have hXN := Y_mul_N_sub_one_nonneg hk0 hk i σ
    unfold fWin
    split_ifs with h
    · obtain ⟨h1, h2, h3⟩ := window_bounds G Q k σ h.1 h.2
      obtain ⟨c1, c2⟩ := counting_39_40 hd1 h2 (Ycnt_le_Ncnt hk0 hk i σ) (by omega)
      have e1 : (Zcnt G Q k σ : ℝ) * κ ≤ κ * (2 * (Jcnt G Q (tWin n i) σ : ℝ) +
          2 / d * ((Ycnt Q k i σ : ℝ) * ((Ncnt Q k i σ : ℝ) - 1))) := by
        rw [mul_comm]; exact mul_le_mul_of_nonneg_left c1 hκ0
      have e2 : s0 ≤ s0 * (2 * (Jcnt G Q (tWin n i) σ : ℝ) / d +
          4 / (d : ℝ) ^ 2 * ((Ncnt Q k i σ : ℝ) * ((Ncnt Q k i σ : ℝ) - 1))) := by
        nlinarith
      have e3 : g σ = s0 * (2 * (Jcnt G Q (tWin n i) σ : ℝ) / d +
          4 / (d : ℝ) ^ 2 * ((Ncnt Q k i σ : ℝ) * ((Ncnt Q k i σ : ℝ) - 1))) +
          (Mcnt G Q (tWin n i) σ : ℝ) + κ * (2 * (Jcnt G Q (tWin n i) σ : ℝ) +
          2 / d * ((Ycnt Q k i σ : ℝ) * ((Ncnt Q k i σ : ℝ) - 1))) := by
        simp only [hg]; ring
      rw [e3]; linarith
    · simp only [hg]; positivity
  have hE := expect_mono hpt
  have hlin : expect g = (s0 * (2 / d) + 2 * κ) * expect (fun σ => (Jcnt G Q (tWin n i) σ : ℝ)) +
      s0 * (4 / (d : ℝ) ^ 2) *
        expect (fun σ => (Ncnt Q k i σ : ℝ) * ((Ncnt Q k i σ : ℝ) - 1)) +
      expect (fun σ => (Mcnt G Q (tWin n i) σ : ℝ)) +
      κ * (2 / d) * expect (fun σ => (Ycnt Q k i σ : ℝ) * ((Ncnt Q k i σ : ℝ) - 1)) := by
    simp only [hg]
    rw [expect_add, expect_add, expect_add, expect_smul, expect_smul, expect_smul]
  rw [hlin, expect_Mcnt] at hE
  have hJ := expect_Jcnt_le G Q i
  have hNN : expect (fun σ => (Ncnt Q k i σ : ℝ) * ((Ncnt Q k i σ : ℝ) - 1)) ≤
      ((d : ℝ) * a0) ^ 2 * p ^ 2 := by
    have := expect_pair_count_le (tWin_le (n := n) i) (aVerts Q k)
    rw [card_aVerts_real hk0 hk, ← hdR] at this
    have hp2 : (tWin n i : ℝ) ^ 2 / (n : ℝ) ^ 2 = p ^ 2 := by
      simp only [p, rhoW]; rw [div_pow]
    rw [hp2] at this
    exact this
  have hXN := expect_YN (q := Q) hk0 hk i
  rw [← hdR] at hXN
  have hκp := kappa_mul_rho hn i
  have hsd : s0 / d ≤ a0 := by
    rw [div_le_iff₀ hdpos]; have := s_le_ka hk0 hk; rw [← hdR] at this; linarith
  -- assemble
  have b1 : (s0 * (2 / d) + 2 * κ) * expect (fun σ => (Jcnt G Q (tWin n i) σ : ℝ)) ≤
      (s0 * (2 / d) + 2 * κ) * (mp * p ^ 2) :=
    mul_le_mul_of_nonneg_left hJ (by positivity)
  have b2 : s0 * (4 / (d : ℝ) ^ 2) *
      expect (fun σ => (Ncnt Q k i σ : ℝ) * ((Ncnt Q k i σ : ℝ) - 1)) ≤
      s0 * (4 / (d : ℝ) ^ 2) * (((d : ℝ) * a0) ^ 2 * p ^ 2) :=
    mul_le_mul_of_nonneg_left hNN (by positivity)
  have b3 : κ * (2 / d) * expect (fun σ => (Ycnt Q k i σ : ℝ) * ((Ncnt Q k i σ : ℝ) - 1)) ≤
      κ * (2 / d) * (s0 * ((d : ℝ) * a0) * p ^ 2) :=
    mul_le_mul_of_nonneg_left hXN (by positivity)
  have q1 : (s0 * (2 / d)) * (mp * p ^ 2) ≤ p * mp / 2 := by
    have : (s0 * (2 / d)) * (mp * p ^ 2) = 2 * (s0 / d) * p * (p * mp) := by ring
    rw [this]
    have h1 : 2 * (s0 / d) * p ≤ 1 / 2 := by
      have := mul_le_mul_of_nonneg_right hsd hp0; linarith
    have h2 : 0 ≤ p * mp := by positivity
    have := mul_le_mul_of_nonneg_right h1 h2
    linarith
  have q2 : s0 * (4 / (d : ℝ) ^ 2) * (((d : ℝ) * a0) ^ 2 * p ^ 2) ≤ p * (s0 * a0) := by
    have : s0 * (4 / (d : ℝ) ^ 2) * (((d : ℝ) * a0) ^ 2 * p ^ 2) =
        4 * (p * a0) * (p * (s0 * a0)) := by field_simp
    rw [this]
    have h0 : 0 ≤ p * (s0 * a0) := by positivity
    have := mul_le_mul_of_nonneg_right (show 4 * (p * a0) ≤ 1 by linarith) h0
    linarith
  have q3 : 2 * κ * (mp * p ^ 2) ≤ 24 * Real.log n * (p * mp) := by
    have : 2 * κ * (mp * p ^ 2) = 2 * (κ * p) * (p * mp) := by ring
    rw [this]
    have h0 : 0 ≤ p * mp := by positivity
    have := mul_le_mul_of_nonneg_right (show 2 * (κ * p) ≤ 24 * Real.log n by linarith) h0
    linarith
  have q4 : κ * (2 / d) * (s0 * ((d : ℝ) * a0) * p ^ 2) ≤ 24 * Real.log n * (p * (s0 * a0)) := by
    have : κ * (2 / d) * (s0 * ((d : ℝ) * a0) * p ^ 2) = 2 * (κ * p) * (p * (s0 * a0)) := by
      field_simp
    rw [this]
    have h0 : 0 ≤ p * (s0 * a0) := by positivity
    have := mul_le_mul_of_nonneg_right (show 2 * (κ * p) ≤ 24 * Real.log n by linarith) h0
    linarith
  have : 0 ≤ p * (s0 * a0) := by positivity
  have : 0 ≤ Real.log n * (p * mp) := by positivity
  have : 0 ≤ Real.log n * (p * (s0 * a0)) := by positivity
  have hR : p * (4 + 48 * Real.log n) * (s0 * a0 + mp) = 4 * (p * (s0 * a0)) +
      48 * (Real.log n * (p * (s0 * a0))) + 4 * (p * mp) + 48 * (Real.log n * (p * mp)) := by ring
  have hb1 : (s0 * (2 / d) + 2 * κ) * (mp * p ^ 2) =
      (s0 * (2 / d)) * (mp * p ^ 2) + 2 * κ * (mp * p ^ 2) := by ring
  have hM : ((missPairs G Q).card : ℝ) * rhoW n i = p * mp := mul_comm _ _
  rw [hM] at hE
  rw [hR]
  clear hpt hlin hg hJ hNN hXN hM
  clear_value g κ p s0 a0 mp
  have hsum := add_le_add (add_le_add (add_le_add b1 b2) (le_refl (p * mp))) b3
  rw [hb1] at hsum
  have hfin : s0 * (2 / ↑d) * (mp * p ^ 2) + 2 * κ * (mp * p ^ 2) +
      s0 * (4 / (d : ℝ) ^ 2) * (((d : ℝ) * a0) ^ 2 * p ^ 2) + p * mp +
      κ * (2 / d) * (s0 * ((d : ℝ) * a0) * p ^ 2) ≤
      4 * (p * (s0 * a0)) + 48 * (Real.log n * (p * (s0 * a0))) + 4 * (p * mp) +
        48 * (Real.log n * (p * mp)) := by
    have hmp' : 0 ≤ p * mp := by positivity
    linarith
  exact hE.trans (hsum.trans hfin)

/-- **Window estimate for Case 2** (combining sub-cases 1 and 2 of the proof of Theorem 4):
`E[|U| 1_{L_i ≤ T < H_i} 1_{G^groups}] ≤ p_i (4 + 48 ln n)(s₀ a₀ + 2 e_m)`. -/
theorem expect_fWin_le (hk0 : 0 < k) (hn : 2 ≤ n) (i : ℕ) :
    expect (fWin G Q k i) ≤ rhoW n i * (4 + 48 * Real.log n) *
      (sOf Q k * aOf Q k + (missPairs G Q).card) := by
  by_cases h : sOf Q k = 0 ∨ 1 / 4 ≤ rhoW n i * aOf Q k
  · exact expect_fWin_sub1 hn i h
  · push_neg at h
    exact expect_fWin_sub2 hk0 hn i (Nat.pos_of_ne_zero h.1) h.2

end CCK
