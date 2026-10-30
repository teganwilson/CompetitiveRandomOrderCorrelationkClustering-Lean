module

public import Mathlib

/-!
# Random arrival orders

The random-order model: the vertices `Fin n` arrive in a uniformly random order.  An arrival
order is a permutation `σ : Equiv.Perm (Fin n)`, where `σ t` is the vertex arriving at time
`t` (times are `0, …, n-1`; "arrives by time `t`" means arrival time `< t`, i.e. among the first
`t` arrivals).  Probabilities and expectations are taken with respect to the uniform
distribution on the `n!` orders.

We also prove Fact 2.3 and the basic hypergeometric counting used throughout the paper.
-/

@[expose] public section

open Finset
open scoped Classical

namespace CCK

variable {n : ℕ}

/-- Probability of an event under a uniformly random arrival order. -/
noncomputable def prob (P : Equiv.Perm (Fin n) → Prop) [DecidablePred P] : ℝ :=
  ((univ.filter P).card : ℝ) / (Fintype.card (Equiv.Perm (Fin n)))

/-- Expectation of a random variable under a uniformly random arrival order. -/
noncomputable def expect (f : Equiv.Perm (Fin n) → ℝ) : ℝ :=
  (∑ σ, f σ) / (Fintype.card (Equiv.Perm (Fin n)))

/-- Arrival time of vertex `v` under the order `σ`. -/
def arrTime (σ : Equiv.Perm (Fin n)) (v : Fin n) : ℕ := (σ.symm v : ℕ)

/-- The set of the first `t` arrivals. -/
noncomputable def firstSet (σ : Equiv.Perm (Fin n)) (t : ℕ) : Finset (Fin n) :=
  univ.filter (fun v => arrTime σ v < t)

/-- Auxiliary result for random arrival orders and Fact 2.3 (Section 2). -/
lemma card_perm_pos : (0 : ℝ) < Fintype.card (Equiv.Perm (Fin n)) := by
  exact_mod_cast Fintype.card_pos

/-- Auxiliary result for random arrival orders and Fact 2.3 (Section 2). -/
lemma prob_nonneg (P : Equiv.Perm (Fin n) → Prop) [DecidablePred P] : 0 ≤ prob P :=
  div_nonneg (Nat.cast_nonneg _) card_perm_pos.le

/-- Auxiliary result for random arrival orders and Fact 2.3 (Section 2). -/
lemma prob_le_one (P : Equiv.Perm (Fin n) → Prop) [DecidablePred P] : prob P ≤ 1 := by
  unfold prob
  rw [div_le_one card_perm_pos]
  exact_mod_cast card_le_univ _

/-- Auxiliary result for random arrival orders and Fact 2.3 (Section 2). -/
lemma prob_mono {P Q : Equiv.Perm (Fin n) → Prop} [DecidablePred P] [DecidablePred Q] (h : ∀ σ, P σ → Q σ) : prob P ≤ prob Q := by
  unfold prob
  apply div_le_div_of_nonneg_right _ card_perm_pos.le
  exact_mod_cast card_le_card (fun σ => by simpa using h σ)

/-- Auxiliary result for random arrival orders and Fact 2.3 (Section 2). -/
lemma prob_compl (P : Equiv.Perm (Fin n) → Prop) [DecidablePred P] : prob (fun σ => ¬ P σ) = 1 - prob P := by
  unfold prob
  rw [eq_sub_iff_add_eq, ← add_div, div_eq_one_iff_eq card_perm_pos.ne']
  have h := card_filter_add_card_filter_not (s := (univ : Finset (Equiv.Perm (Fin n)))) P
  rw [card_univ] at h
  have h2 : (univ.filter (fun σ => ¬ P σ)).card + (univ.filter P).card =
      Fintype.card (Equiv.Perm (Fin n)) := by
    rw [add_comm]; exact h
  exact_mod_cast h2

/-- `P(A ∩ B) ≥ P(A) - P(Bᶜ)`. -/
lemma prob_and_ge (P Q : Equiv.Perm (Fin n) → Prop) [DecidablePred P] [DecidablePred Q] :
    prob P - prob (fun σ => ¬ Q σ) ≤ prob (fun σ => P σ ∧ Q σ) := by
  unfold prob
  rw [← sub_div]
  apply div_le_div_of_nonneg_right _ card_perm_pos.le
  have h1 : univ.filter P ⊆ univ.filter (fun σ => P σ ∧ Q σ) ∪ univ.filter (fun σ => ¬ Q σ) := by
    intro σ; simp only [mem_filter, mem_univ, true_and, mem_union]; tauto
  have := (card_le_card h1).trans (card_union_le _ _)
  rw [sub_le_iff_le_add]
  exact_mod_cast this

/-- Auxiliary result for random arrival orders and Fact 2.3 (Section 2). -/
lemma expect_mono {f g : Equiv.Perm (Fin n) → ℝ} (h : ∀ σ, f σ ≤ g σ) : expect f ≤ expect g :=
  div_le_div_of_nonneg_right (sum_le_sum (fun σ _ => h σ)) card_perm_pos.le

/-- Markov-type bound used for lower bounds: if `f ≥ a` on the event `P` and `f ≥ 0`, then
`E[f] ≥ a P(P)`. -/
lemma expect_ge_of_event (f : Equiv.Perm (Fin n) → ℝ) (P : Equiv.Perm (Fin n) → Prop) [DecidablePred P]
    (a : ℝ) (hf0 : ∀ σ, 0 ≤ f σ) (hfa : ∀ σ, P σ → a ≤ f σ) :
    a * prob P ≤ expect f := by
  unfold prob expect
  rw [mul_div_assoc']
  apply div_le_div_of_nonneg_right _ card_perm_pos.le
  calc a * ((univ.filter P).card : ℝ) = ∑ σ ∈ univ.filter P, a := by
        rw [sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ σ ∈ univ.filter P, f σ := sum_le_sum (fun σ hσ => hfa σ (mem_filter.1 hσ).2)
    _ ≤ ∑ σ, f σ := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun σ _ _ => hf0 σ)

/-- Auxiliary result for random arrival orders and Fact 2.3 (Section 2). -/
lemma card_firstSet (σ : Equiv.Perm (Fin n)) {t : ℕ} (ht : t ≤ n) :
    (firstSet σ t).card = t := by
  unfold firstSet arrTime
  have : univ.filter (fun v : Fin n => (σ.symm v : ℕ) < t) =
      (univ.filter (fun i : Fin n => (i : ℕ) < t)).map σ.toEmbedding := by
    ext v
    simp only [mem_filter, mem_univ, true_and, mem_map, Equiv.coe_toEmbedding]
    constructor
    · intro h; exact ⟨σ.symm v, h, by simp⟩
    · rintro ⟨i, hi, rfl⟩; simpa using hi
  rw [this, card_map, Fin.card_filter_val_lt, min_eq_right ht]

/-- A permutation mapping a given set onto another set of the same size. -/
lemma exists_perm_image (S S' : Finset (Fin n)) (h : S.card = S'.card) :
    ∃ π : Equiv.Perm (Fin n), S.image π = S' := by
  have e1 : {x // x ∈ S} ≃ {x // x ∈ S'} := Fintype.equivOfCardEq (by simpa using h)
  have e2 : {x // x ∉ S} ≃ {x // x ∉ S'} := Fintype.equivOfCardEq (by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl]
    simp [h])
  refine ⟨Equiv.subtypeCongr e1 e2, ?_⟩
  ext y
  simp only [mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simp only [Equiv.subtypeCongr, Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_pos hx,
      Equiv.sumCongr_apply, Sum.map_inl, Equiv.sumCompl_apply_inl]
    exact (e1 ⟨x, hx⟩).2
  · intro hy
    refine ⟨e1.symm ⟨y, hy⟩, (e1.symm ⟨y, hy⟩).2, ?_⟩
    simp only [Equiv.subtypeCongr, Equiv.trans_apply,
      Equiv.sumCompl_symm_apply_of_pos (e1.symm ⟨y, hy⟩).2, Equiv.sumCongr_apply, Sum.map_inl,
      Equiv.sumCompl_apply_inl]
    simp

/-- All fibres of `σ ↦ firstSet σ t` over `t`-subsets have the same size. -/
lemma card_fiber_firstSet_eq {t : ℕ} (S S' : Finset (Fin n)) (h : S.card = S'.card) :
    (univ.filter (fun σ : Equiv.Perm (Fin n) => firstSet σ t = S)).card =
      (univ.filter (fun σ : Equiv.Perm (Fin n) => firstSet σ t = S')).card := by
  obtain ⟨π, hπ⟩ := exists_perm_image S S' h
  have key : ∀ σ : Equiv.Perm (Fin n), firstSet (σ.trans π) t = (firstSet σ t).image π := by
    intro σ
    ext v
    simp only [firstSet, arrTime, mem_filter, mem_univ, true_and, mem_image]
    constructor
    · intro hv; exact ⟨π.symm v, by simpa [Equiv.symm_trans_apply] using hv, by simp⟩
    · rintro ⟨u, hu, rfl⟩; simpa [Equiv.symm_trans_apply] using hu
  apply card_bij (fun σ _ => σ.trans π)
  · intro σ hσ
    simp only [mem_filter, mem_univ, true_and] at hσ ⊢
    rw [key, hσ, hπ]
  · intro σ₁ _ σ₂ _ h
    exact Equiv.ext (fun x => π.injective (by simpa using congrArg (fun f => f x) h))
  · intro τ hτ
    refine ⟨τ.trans π.symm, ?_, by ext; simp⟩
    simp only [mem_filter, mem_univ, true_and] at hτ ⊢
    have : (τ.trans π.symm).trans π = τ := by ext; simp
    have h2 := key (τ.trans π.symm)
    rw [this, hτ, ← hπ] at h2
    exact (image_injective π.injective h2).symm

/-- The set of the first `t` arrivals is a uniformly random `t`-subset: each fibre has size
`n! / C(n, t)`. -/
lemma card_fiber_firstSet {t : ℕ} (ht : t ≤ n) (S : Finset (Fin n)) (hS : S.card = t) :
    ((univ.filter (fun σ : Equiv.Perm (Fin n) => firstSet σ t = S)).card : ℝ) *
      (n.choose t) = Fintype.card (Equiv.Perm (Fin n)) := by
  have hsum : ∑ S' ∈ powersetCard t (univ : Finset (Fin n)),
      (univ.filter (fun σ : Equiv.Perm (Fin n) => firstSet σ t = S')).card =
      Fintype.card (Equiv.Perm (Fin n)) := by
    rw [← card_univ, card_eq_sum_card_fiberwise (f := fun σ => firstSet σ t)
      (t := powersetCard t univ)]
    intro σ _
    simp [mem_powersetCard, card_firstSet σ ht]
  rw [sum_congr rfl (fun S' hS' => card_fiber_firstSet_eq (t := t) S' S
    (by rw [(mem_powersetCard.1 hS').2, hS])), sum_const, card_powersetCard, card_univ,
    Fintype.card_fin, smul_eq_mul] at hsum
  rw [mul_comm]; exact_mod_cast hsum

/-- Probability of an event that only depends on the set of the first `t` arrivals:
it equals the fraction of `t`-subsets satisfying it. -/
lemma prob_firstSet {t : ℕ} (ht : t ≤ n) (P : Finset (Fin n) → Prop) [DecidablePred P] :
    prob (fun σ => P (firstSet σ t)) =
      ((powersetCard t (univ : Finset (Fin n))).filter P).card / (n.choose t) := by
  unfold prob
  have hc : (0 : ℝ) < n.choose t := by exact_mod_cast Nat.choose_pos ht
  rw [div_eq_div_iff card_perm_pos.ne' hc.ne']
  rw [card_eq_sum_card_fiberwise (f := fun σ => firstSet σ t)
    (t := (powersetCard t univ).filter P)]
  · push_cast
    rw [sum_mul]
    have : ∀ S ∈ (powersetCard t (univ : Finset (Fin n))).filter P,
        (((univ.filter (fun σ => P (firstSet σ t))).filter
          (fun σ => firstSet σ t = S)).card : ℝ) * (n.choose t) =
          Fintype.card (Equiv.Perm (Fin n)) := by
      intro S hS
      simp only [mem_filter, mem_powersetCard] at hS
      rw [← card_fiber_firstSet ht S hS.1.2, filter_filter]
      congr 2
      apply congrArg
      apply filter_congr
      intro σ _
      constructor
      · rintro ⟨-, h⟩; exact h
      · intro h; exact ⟨h ▸ hS.2, h⟩
    rw [sum_congr rfl this, sum_const, nsmul_eq_mul]
  · intro σ hσ
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq, mem_powersetCard,
      subset_univ] at hσ ⊢
    exact ⟨card_firstSet σ ht, hσ⟩

/-- **Fact 2.3.** For non-negative integers `n, a, b` with `a ≤ n` and `b ≤ n - a`,
`(1 - a/(n-b+1))^b ≤ C(n-a, b)/C(n, b) ≤ (1 - a/n)^b ≤ e^{-ab/n}`. -/
theorem fact_2_3 (n a b : ℕ) (ha : a ≤ n) (hb : b ≤ n - a) (hn : 0 < n) :
    (1 - (a : ℝ) / (n - b + 1)) ^ b ≤ ((n - a).choose b : ℝ) / (n.choose b) ∧
    ((n - a).choose b : ℝ) / (n.choose b) ≤ (1 - (a : ℝ) / n) ^ b ∧
    (1 - (a : ℝ) / n) ^ b ≤ Real.exp (-(a * b : ℝ) / n) := by
  -- product formula `C(n-a,b)/C(n,b) = ∏_{i<b} (n-a-i)/(n-i)`
  have hprod : ∀ b', b' ≤ n - a → ((n - a).choose b' : ℝ) / (n.choose b') =
      ∏ i ∈ range b', ((n : ℝ) - a - i) / (n - i) := by
    intro b' hb'
    induction b' with
    | zero => simp
    | succ b' ih =>
      have hb'' : b' ≤ n - a := by omega
      rw [prod_range_succ, ← ih hb'']
      have h1 := Nat.choose_succ_right_eq (n - a) b'
      have h2 := Nat.choose_succ_right_eq n b'
      have hc1 : (0 : ℝ) < (n.choose b') := by exact_mod_cast Nat.choose_pos (by omega)
      have hc2 : (0 : ℝ) < (n.choose (b' + 1)) := by exact_mod_cast Nat.choose_pos (by omega)
      have hnb : (0 : ℝ) < n - b' := by
        have : (b' : ℝ) < n := by exact_mod_cast (by omega : b' < n)
        linarith
      have h1' : ((n - a).choose (b' + 1) : ℝ) * (b' + 1) = ((n - a).choose b') * ((n : ℝ) - a - b') := by
        have := congrArg (fun x : ℕ => (x : ℝ)) h1
        push_cast [Nat.cast_sub ha, Nat.cast_sub (by omega : b' ≤ n - a)] at this
        linarith
      have h2' : (n.choose (b' + 1) : ℝ) * (b' + 1) = (n.choose b') * ((n : ℝ) - b') := by
        have := congrArg (fun x : ℕ => (x : ℝ)) h2
        push_cast [Nat.cast_sub (by omega : b' ≤ n)] at this
        linarith
      field_simp
      nlinarith [h1', h2']
  rw [hprod b hb]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  refine ⟨?_, ?_, ?_⟩
  · rw [show (1 - (a : ℝ) / (n - b + 1)) ^ b = ∏ _i ∈ range b, (1 - (a : ℝ) / (n - b + 1)) by
      rw [prod_const, card_range]]
    apply prod_le_prod
    · intro i hi
      have hi : i < b := mem_range.1 hi
      have : (a + b : ℝ) ≤ n := by exact_mod_cast (by omega : a + b ≤ n)
      have : (0 : ℝ) ≤ a := Nat.cast_nonneg _
      rw [sub_nonneg, div_le_one (by linarith)]; linarith
    · intro i hi
      have hi : i < b := mem_range.1 hi
      have hni : (0 : ℝ) < n - i := by
        have : (i : ℝ) < n := by exact_mod_cast (by omega : i < n)
        linarith
      have hib : (i : ℝ) + 1 ≤ b := by exact_mod_cast hi
      rw [show ((n : ℝ) - a - i) / (n - i) = 1 - a / (n - i) by field_simp; ring]
      have : (a : ℝ) / (n - i) ≤ a / (n - b + 1) := by
        apply div_le_div_of_nonneg_left (Nat.cast_nonneg _)
        · have : (b : ℝ) ≤ n := by exact_mod_cast (by omega : b ≤ n)
          linarith
        · linarith
      linarith
  · rw [show (1 - (a : ℝ) / n) ^ b = ∏ _i ∈ range b, (1 - (a : ℝ) / n) by
      rw [prod_const, card_range]]
    apply prod_le_prod
    · intro i hi
      have hi : i < b := mem_range.1 hi
      have hni : (0 : ℝ) < n - i := by
        have : (i : ℝ) < n := by exact_mod_cast (by omega : i < n)
        linarith
      apply div_nonneg _ hni.le
      have : (a + i : ℝ) ≤ n := by exact_mod_cast (by omega : a + i ≤ n)
      linarith
    · intro i hi
      have hi : i < b := mem_range.1 hi
      have hni : (0 : ℝ) < n - i := by
        have : (i : ℝ) < n := by exact_mod_cast (by omega : i < n)
        linarith
      rw [div_le_iff₀ hni]
      have : (0 : ℝ) ≤ i := Nat.cast_nonneg _
      have : (0 : ℝ) ≤ a := Nat.cast_nonneg _
      have : (1 - (a : ℝ) / n) * (n - i) = n - a - i + a * i / n := by field_simp; ring
      rw [this]
      have : 0 ≤ (a : ℝ) * i / n := by positivity
      linarith
  · have h1 : 1 - (a : ℝ) / n ≤ Real.exp (-(a : ℝ) / n) := by
      have := Real.add_one_le_exp (-(a : ℝ) / n)
      rw [neg_div] at this ⊢; linarith
    have h0 : 0 ≤ 1 - (a : ℝ) / n := by
      rw [sub_nonneg, div_le_one hn']; exact_mod_cast ha
    calc (1 - (a : ℝ) / n) ^ b ≤ Real.exp (-(a : ℝ) / n) ^ b := pow_le_pow_left₀ h0 h1 b
      _ = Real.exp (-(a * b : ℝ) / n) := by
          rw [← Real.exp_nat_mul]; congr 1; ring

/-- Hypergeometric probability that a fixed set `A` of `a` vertices has no vertex among the
first `t` arrivals: `C(n-a, t) / C(n, t)`. -/
lemma prob_disjoint_firstSet {t : ℕ} (ht : t ≤ n) (A : Finset (Fin n)) :
    prob (fun σ => Disjoint (firstSet σ t) A) = ((n - A.card).choose t : ℝ) / (n.choose t) := by
  rw [prob_firstSet ht (fun S => Disjoint S A)]
  congr 2
  have : (powersetCard t (univ : Finset (Fin n))).filter (fun S => Disjoint S A) =
      powersetCard t (univ \ A) := by
    ext S
    simp only [mem_filter, mem_powersetCard, subset_univ, true_and, subset_sdiff]
    tauto
  rw [this, card_powersetCard, card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin]

/-- Probability that two fixed distinct vertices are both among the first `t` arrivals:
`t(t-1) / (n(n-1))` (used in Lemma 5.1 and Lemma 7.10). -/
lemma prob_pair_firstSet {t : ℕ} (ht : t ≤ n) (u v : Fin n) (huv : u ≠ v) :
    prob (fun σ => u ∈ firstSet σ t ∧ v ∈ firstSet σ t) =
      ((t : ℝ) * (t - 1)) / (n * (n - 1)) := by
  rw [prob_firstSet ht (fun S => u ∈ S ∧ v ∈ S)]
  have hn2 : 2 ≤ n := by
    have := Fintype.card_le_of_injective (fun b : Bool => if b then u else v) (by
      intro b1 b2 h; cases b1 <;> cases b2 <;> simp_all [eq_comm])
    simpa using this
  rcases Nat.lt_or_ge t 2 with ht2 | ht2
  · have : (powersetCard t (univ : Finset (Fin n))).filter (fun S => u ∈ S ∧ v ∈ S) = ∅ := by
      apply filter_false_of_mem
      intro S hS ⟨hu, hv⟩
      have := (mem_powersetCard.1 hS).2
      have : ({u, v} : Finset (Fin n)).card ≤ S.card := card_le_card (by
        intro x hx; simp only [mem_insert, mem_singleton] at hx; rcases hx with rfl | rfl <;>
          assumption)
      rw [card_pair huv] at this; omega
    rw [this]
    interval_cases t <;> simp
  · have hbij : ((powersetCard t (univ : Finset (Fin n))).filter (fun S => u ∈ S ∧ v ∈ S)).card =
        (powersetCard (t - 2) (univ \ {u, v})).card := by
      symm
      apply card_bij (fun S _ => S ∪ {u, v})
      · intro S hS
        simp only [mem_powersetCard, subset_sdiff] at hS
        simp only [mem_filter, mem_powersetCard, subset_univ, true_and, mem_union,
          mem_insert, mem_singleton, or_true, true_or, and_true]
        rw [card_union_of_disjoint hS.1.2, card_pair huv, hS.2]; omega
      · intro S₁ h₁ S₂ h₂ h
        simp only [mem_powersetCard, subset_sdiff] at h₁ h₂
        have := congrArg (fun X => X \ {u, v}) h
        simp only [union_sdiff_right] at this
        rwa [sdiff_eq_self_of_disjoint h₁.1.2, sdiff_eq_self_of_disjoint h₂.1.2] at this
      · intro S hS
        simp only [mem_filter, mem_powersetCard, subset_univ, true_and] at hS
        refine ⟨S \ {u, v}, ?_, ?_⟩
        · simp only [mem_powersetCard, subset_sdiff, subset_univ, true_and]
          refine ⟨disjoint_sdiff_self_left, ?_⟩
          rw [card_sdiff_of_subset (by
            intro x hx; simp only [mem_insert, mem_singleton] at hx
            rcases hx with rfl | rfl
            · exact hS.2.1
            · exact hS.2.2), card_pair huv, hS.1]
        · ext x; simp only [mem_union, mem_sdiff, mem_insert, mem_singleton]
          constructor
          · rintro (⟨h, -⟩ | rfl | rfl)
            · exact h
            · exact hS.2.1
            · exact hS.2.2
          · intro h; by_cases h' : x = u ∨ x = v
            · right; exact h'
            · left; exact ⟨h, h'⟩
    rw [hbij, card_powersetCard, card_sdiff_of_subset (subset_univ _), card_pair huv, card_univ,
      Fintype.card_fin]
    have hc : (0 : ℝ) < n.choose t := by exact_mod_cast Nat.choose_pos ht
    have hn : (0 : ℝ) < n * (n - 1) := by
      have : (2 : ℝ) ≤ n := by exact_mod_cast hn2
      nlinarith
    rw [div_eq_div_iff hc.ne' hn.ne']
    -- `C(n-2, t-2) * n (n-1) = C(n, t) * t (t-1)`
    have key : (n - 2).choose (t - 2) * (n * (n - 1)) = n.choose t * (t * (t - 1)) := by
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 2 := ⟨n - 2, by omega⟩
      obtain ⟨t', rfl⟩ : ∃ t', t = t' + 2 := ⟨t - 2, by omega⟩
      simp only [Nat.add_sub_cancel]
      have e1 := Nat.add_one_mul_choose_eq (n' + 1) (t' + 1)
      have e2 := Nat.add_one_mul_choose_eq n' t'
      have : n' + 2 - 1 = n' + 1 := by omega
      rw [this, show t' + 2 - 1 = t' + 1 by omega]
      nlinarith [e1, e2]
    have key' := congrArg (fun x : ℕ => (x : ℝ)) key
    push_cast [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_sub (by omega : 1 ≤ t)] at key'
    linarith

end CCK
