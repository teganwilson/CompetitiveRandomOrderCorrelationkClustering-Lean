module

public import RequestProject.Prob

/-!
# Exchangeability of arrival orders

Combinatorial tools used in the proofs of Theorem 2 and Theorem 3 (Section 5 of the paper):
when the vertices occupying a set `I` of arrival positions are indistinguishable for an online
algorithm, re-shuffling them among these positions produces equally likely arrival orders on
which the algorithm behaves in exactly the same way.  The *indistinguishability* argument of the
paper ("the algorithm has no way of distinguishing which vertices are true singletons") is made
rigorous through `exchange_count` and `card_fixOutside_pair`.
-/

@[expose] public section

open Finset
open scoped Classical

namespace CCK

variable {n : ℕ}

/-- Permutations of positions which only move positions inside `I`. -/
noncomputable def fixOutside (I : Finset (Fin n)) : Finset (Equiv.Perm (Fin n)) :=
  univ.filter (fun ρ => ∀ p, p ∉ I → ρ p = p)

/-- Auxiliary result for the exchangeability of random arrival orders (Section 2). -/
lemma one_mem_fixOutside (I : Finset (Fin n)) : (1 : Equiv.Perm (Fin n)) ∈ fixOutside I := by
  simp [fixOutside]

/-- Auxiliary result for the exchangeability of random arrival orders (Section 2). -/
lemma fixOutside_card_pos (I : Finset (Fin n)) : 0 < (fixOutside I).card :=
  card_pos.2 ⟨1, one_mem_fixOutside I⟩

/-- Auxiliary result for the exchangeability of random arrival orders (Section 2). -/
lemma fixOutside_mem_iff {I : Finset (Fin n)} {ρ : Equiv.Perm (Fin n)} :
    ρ ∈ fixOutside I ↔ ∀ p, p ∉ I → ρ p = p := by
  simp [fixOutside]

/-- Auxiliary result for the exchangeability of random arrival orders (Section 2). -/
lemma fixOutside_apply_mem {I : Finset (Fin n)} {ρ : Equiv.Perm (Fin n)} (hρ : ρ ∈ fixOutside I)
    {p : Fin n} (hp : p ∈ I) : ρ p ∈ I := by
  by_contra h
  have := (fixOutside_mem_iff.1 hρ) _ h
  rw [ρ.injective this] at h
  exact h hp

/-- Auxiliary result for the exchangeability of random arrival orders (Section 2). -/
lemma fixOutside_inv_mem {I : Finset (Fin n)} {ρ : Equiv.Perm (Fin n)} (hρ : ρ ∈ fixOutside I) :
    ρ⁻¹ ∈ fixOutside I := by
  rw [fixOutside_mem_iff] at hρ ⊢
  intro p hp
  conv_lhs => rw [← hρ p hp]
  simp

/-- Auxiliary result for the exchangeability of random arrival orders (Section 2). -/
lemma fixOutside_symm_apply_mem {I : Finset (Fin n)} {ρ : Equiv.Perm (Fin n)}
    (hρ : ρ ∈ fixOutside I) {p : Fin n} (hp : p ∈ I) : ρ.symm p ∈ I :=
  fixOutside_apply_mem (fixOutside_inv_mem hρ) hp

/-- Auxiliary result for the exchangeability of random arrival orders (Section 2). -/
lemma fixOutside_mul_mem {I : Finset (Fin n)} {ρ τ : Equiv.Perm (Fin n)}
    (hρ : ρ ∈ fixOutside I) (hτ : τ ∈ fixOutside I) : ρ * τ ∈ fixOutside I := by
  rw [fixOutside_mem_iff] at hρ hτ ⊢
  intro p hp
  rw [Equiv.Perm.mul_apply, hτ p hp, hρ p hp]

/-- Auxiliary result for the exchangeability of random arrival orders (Section 2). -/
lemma swap_mem_fixOutside {I : Finset (Fin n)} {p q : Fin n} (hp : p ∈ I) (hq : q ∈ I) :
    Equiv.swap p q ∈ fixOutside I := by
  rw [fixOutside_mem_iff]
  intro r hr
  exact Equiv.swap_apply_of_ne_of_ne (fun h => hr (h ▸ hp)) (fun h => hr (h ▸ hq))

/-- **Exchangeability lemma.**  Let `S` be an event and `I σ` a set of positions such that
re-shuffling the vertices at the positions `I σ` keeps the order inside `S` and does not change
`I`.  If, for each `σ ∈ S`, at least a `c` fraction of the re-shufflings of `σ` are bad, then
at least a `c` fraction of `S` is bad. -/
theorem exchange_count (S : Finset (Equiv.Perm (Fin n))) (I : Equiv.Perm (Fin n) → Finset (Fin n))
    (Bad : Equiv.Perm (Fin n) → Prop) [DecidablePred Bad] (c : ℝ)
    (hinv : ∀ σ ∈ S, ∀ ρ ∈ fixOutside (I σ), σ * ρ ∈ S ∧ I (σ * ρ) = I σ)
    (hbad : ∀ σ ∈ S, c * (fixOutside (I σ)).card ≤
      ((fixOutside (I σ)).filter (fun ρ => Bad (σ * ρ))).card) :
    c * S.card ≤ (S.filter Bad).card := by
  set P := (S ×ˢ (univ : Finset (Equiv.Perm (Fin n)))).filter
    (fun x => x.2 ∈ fixOutside (I x.1)) with hP
  set w : Equiv.Perm (Fin n) × Equiv.Perm (Fin n) → ℝ :=
    fun x => (if Bad (x.1 * x.2) then 1 else 0) / ((fixOutside (I x.1)).card : ℝ) with hw
  have hsplit : ∀ g : Equiv.Perm (Fin n) × Equiv.Perm (Fin n) → ℝ,
      ∑ x ∈ P, g x = ∑ σ ∈ S, ∑ ρ ∈ fixOutside (I σ), g (σ, ρ) := by
    intro g
    rw [hP, sum_filter, sum_product]
    refine sum_congr rfl (fun σ _ => ?_)
    rw [← sum_filter]
    congr 1
    ext ρ; simp
  -- first evaluation
  have h1 : c * S.card ≤ ∑ x ∈ P, w x := by
    rw [hsplit]
    rw [mul_comm, ← nsmul_eq_mul, ← sum_const]
    apply sum_le_sum
    intro σ hσ
    have hpos : (0 : ℝ) < (fixOutside (I σ)).card := by exact_mod_cast fixOutside_card_pos _
    simp only [hw]
    rw [← sum_div, le_div_iff₀ hpos]
    rw [sum_boole]
    simpa using hbad σ hσ
  -- second evaluation via the involution `(σ, ρ) ↦ (σ ρ, ρ⁻¹)`
  have h2 : ∑ x ∈ P, w x = (S.filter Bad).card := by
    have hmem : ∀ x ∈ P, (x.1 * x.2, x.2⁻¹) ∈ P := by
      intro x hx
      simp only [hP, mem_filter, mem_product, mem_univ, and_true] at hx ⊢
      obtain ⟨h1, h2⟩ := hinv x.1 hx.1 x.2 hx.2
      exact ⟨h1, h2 ▸ fixOutside_inv_mem hx.2⟩
    rw [sum_nbij' (fun x => (x.1 * x.2, x.2⁻¹)) (fun x => (x.1 * x.2, x.2⁻¹)) hmem hmem
      (fun x _ => by simp) (fun x _ => by simp) (g := fun x =>
        (if Bad x.1 then 1 else 0) / ((fixOutside (I x.1)).card : ℝ))]
    · rw [hsplit]
      rw [card_eq_sum_ones, Nat.cast_sum, sum_filter]
      refine sum_congr rfl (fun σ _ => ?_)
      have hpos : (0 : ℝ) < (fixOutside (I σ)).card := by exact_mod_cast fixOutside_card_pos _
      show ∑ ρ ∈ fixOutside (I σ), (if Bad σ then (1:ℝ) else 0) /
        ((fixOutside (I σ)).card : ℝ) = _
      rw [sum_const, nsmul_eq_mul]
      split_ifs <;> simp [hpos.ne']
    · intro x hx
      simp only [hP, mem_filter, mem_product, mem_univ, and_true] at hx
      simp only [hw, (hinv x.1 hx.1 x.2 hx.2).2]
  linarith

/-- Constructing a re-shuffling of `I` mapping one ordered pair of distinct positions to
another. -/
lemma exists_fixOutside_pair {I : Finset (Fin n)} {p q p' q' : Fin n} (hp : p ∈ I) (hq : q ∈ I)
    (hp' : p' ∈ I) (hq' : q' ∈ I) (hpq : p ≠ q) (hpq' : p' ≠ q') :
    ∃ τ ∈ fixOutside I, τ p' = p ∧ τ q' = q := by
  set τ1 := Equiv.swap p p'
  have hτ1q : τ1 q' ∈ I := fixOutside_apply_mem (swap_mem_fixOutside hp hp') hq'
  refine ⟨Equiv.swap q (τ1 q') * τ1,
    fixOutside_mul_mem (swap_mem_fixOutside hq hτ1q) (swap_mem_fixOutside hp hp'), ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right]
    apply Equiv.swap_apply_of_ne_of_ne hpq
    intro h
    apply hpq'
    have : τ1 q' = τ1 p' := by rw [← h, Equiv.swap_apply_right]
    exact (τ1.injective this).symm
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right]

/-- Under a uniformly random re-shuffling of the positions `I`, the pair of new positions of
two fixed vertices (at positions `a ≠ b` of `I`) is a uniformly random ordered pair of distinct
positions of `I`. -/
theorem card_fixOutside_pair (I : Finset (Fin n)) {a b : Fin n} (ha : a ∈ I) (hb : b ∈ I)
    (hab : a ≠ b) (B : Finset (Fin n × Fin n)) (hB : B ⊆ I.offDiag) :
    ((fixOutside I).filter (fun ρ => (ρ.symm a, ρ.symm b) ∈ B)).card * I.offDiag.card =
      B.card * (fixOutside I).card := by
  set N : Fin n × Fin n → ℕ := fun x =>
    ((fixOutside I).filter (fun ρ => (ρ.symm a, ρ.symm b) = x)).card with hN
  -- all fibres over `I.offDiag` have the same size
  have hconst : ∀ x ∈ I.offDiag, N x = N (a, b) := by
    rintro ⟨p, q⟩ hx
    simp only [mem_offDiag] at hx
    obtain ⟨τ, hτ, hτp, hτq⟩ := exists_fixOutside_pair ha hb hx.1 hx.2.1 hab hx.2.2
    simp only [hN]
    apply card_nbij' (fun ρ => ρ * τ⁻¹) (fun ρ => ρ * τ)
    · intro ρ hρ
      simp only [coe_filter, Set.mem_setOf_eq, Prod.mk.injEq] at hρ ⊢
      refine ⟨fixOutside_mul_mem hρ.1 (fixOutside_inv_mem hτ), ?_, ?_⟩
      · simp [Equiv.Perm.mul_def, Equiv.Perm.inv_def, hρ.2.1, hτp]
      · simp [Equiv.Perm.mul_def, Equiv.Perm.inv_def, hρ.2.2, hτq]
    · intro ρ hρ
      simp only [coe_filter, Set.mem_setOf_eq, Prod.mk.injEq] at hρ ⊢
      refine ⟨fixOutside_mul_mem hρ.1 hτ, ?_, ?_⟩
      · rw [Equiv.Perm.mul_def, Equiv.symm_trans_apply, hρ.2.1]
        rw [← hτp]; simp
      · rw [Equiv.Perm.mul_def, Equiv.symm_trans_apply, hρ.2.2]
        rw [← hτq]; simp
    · intro ρ _; simp
    · intro ρ _; simp
  have hmaps : ∀ ρ ∈ fixOutside I, (ρ.symm a, ρ.symm b) ∈ I.offDiag := by
    intro ρ hρ
    simp only [mem_offDiag]
    exact ⟨fixOutside_symm_apply_mem hρ ha, fixOutside_symm_apply_mem hρ hb,
      fun h => hab (ρ.symm.injective h)⟩
  have htot : (fixOutside I).card = ∑ x ∈ I.offDiag, N x :=
    card_eq_sum_card_fiberwise hmaps
  have hpart : ((fixOutside I).filter (fun ρ => (ρ.symm a, ρ.symm b) ∈ B)).card =
      ∑ x ∈ B, N x := by
    have := card_eq_sum_card_fiberwise
      (s := (fixOutside I).filter (fun ρ => (ρ.symm a, ρ.symm b) ∈ B))
      (f := fun ρ : Equiv.Perm (Fin n) => (ρ.symm a, ρ.symm b))
      (t := B) (fun ρ hρ => (mem_filter.1 hρ).2)
    rw [this]
    refine sum_congr rfl (fun x hx => ?_)
    simp only [hN, filter_filter]
    congr 1
    apply filter_congr
    intro ρ _
    constructor
    · rintro ⟨-, h⟩; exact h
    · intro h; exact ⟨h ▸ hx, h⟩
  rw [hpart, htot, sum_congr rfl (fun x hx => hconst x (hB hx)),
    sum_congr rfl hconst, sum_const, sum_const, smul_eq_mul, smul_eq_mul]
  ring

/-- Under a uniformly random re-shuffling of the positions `I`, a fixed position `p₀ ∈ I`
receives the vertex of a uniformly random position of `I`. -/
theorem card_fixOutside_point (I : Finset (Fin n)) {p₀ : Fin n} (hp₀ : p₀ ∈ I)
    (Q : Finset (Fin n)) (hQ : Q ⊆ I) :
    ((fixOutside I).filter (fun ρ => ρ p₀ ∈ Q)).card * I.card = Q.card * (fixOutside I).card := by
  set N : Fin n → ℕ := fun x => ((fixOutside I).filter (fun ρ => ρ p₀ = x)).card with hN
  have hconst : ∀ x ∈ I, N x = N p₀ := by
    intro x hx
    simp only [hN]
    have hs := swap_mem_fixOutside hx hp₀
    apply card_nbij' (fun ρ => Equiv.swap x p₀ * ρ) (fun ρ => Equiv.swap x p₀ * ρ)
    · intro ρ hρ
      simp only [coe_filter, Set.mem_setOf_eq] at hρ ⊢
      refine ⟨fixOutside_mul_mem hs hρ.1, ?_⟩
      rw [Equiv.Perm.mul_apply, hρ.2, Equiv.swap_apply_left]
    · intro ρ hρ
      simp only [coe_filter, Set.mem_setOf_eq] at hρ ⊢
      refine ⟨fixOutside_mul_mem hs hρ.1, ?_⟩
      rw [Equiv.Perm.mul_apply, hρ.2, Equiv.swap_apply_right]
    · intro ρ _; simp [← mul_assoc]
    · intro ρ _; simp [← mul_assoc]
  have hmaps : ∀ ρ ∈ fixOutside I, ρ p₀ ∈ I := fun ρ hρ => fixOutside_apply_mem hρ hp₀
  have htot : (fixOutside I).card = ∑ x ∈ I, N x := card_eq_sum_card_fiberwise hmaps
  have hpart : ((fixOutside I).filter (fun ρ => ρ p₀ ∈ Q)).card = ∑ x ∈ Q, N x := by
    have := card_eq_sum_card_fiberwise
      (s := (fixOutside I).filter (fun ρ => ρ p₀ ∈ Q))
      (f := fun ρ : Equiv.Perm (Fin n) => ρ p₀) (t := Q) (fun ρ hρ => (mem_filter.1 hρ).2)
    rw [this]
    refine sum_congr rfl (fun x hx => ?_)
    simp only [hN, filter_filter]
    congr 1
    apply filter_congr
    intro ρ _
    constructor
    · rintro ⟨-, h⟩; exact h
    · intro h; exact ⟨h ▸ hx, h⟩
  rw [hpart, htot, sum_congr rfl (fun x hx => hconst x (hQ hx)), sum_congr rfl hconst,
    sum_const, sum_const, smul_eq_mul, smul_eq_mul]
  ring

end CCK
