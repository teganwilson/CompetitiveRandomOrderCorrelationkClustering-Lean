module

public import RequestProject.CliqueInstance

/-!
# Appendix A: NP-hardness of offline k-CC on disjoint cliques (Theorem 6)

We formalize the reduction from 3-PARTITION used to prove Theorem 6 and prove its correctness:
a 3-PARTITION instance is a YES-instance iff the associated disjoint-cliques instance admits a
k-clustering (with `k = m`) of cost at most `T = (m B^2 - ∑ a_i^2) / 2`.

The strong NP-completeness of 3-PARTITION [GJ79] is an external result and is not formalized;
neither is the polynomial running time of the reduction.
-/

@[expose] public section

open Finset
open scoped Classical

namespace CCK

/-- The vertex set of the disjoint-cliques instance built from sizes `a`: clique `K_i` has
`a i` vertices. -/
abbrev CliquesVtx {n : ℕ} (a : Fin n → ℕ) := Σ i : Fin n, Fin (a i)

/-- Auxiliary result for Theorem 6 (Appendix A). -/
lemma card_sigma_fiber {n : ℕ} (a : Fin n → ℕ) (i : Fin n) :
    (univ.filter (fun v : CliquesVtx a => v.1 = i)).card = a i := by
  rw [show (univ.filter (fun v : CliquesVtx a => v.1 = i)) =
      (univ : Finset (Fin (a i))).map ⟨Sigma.mk i, sigma_mk_injective⟩ by
    ext ⟨j, x⟩; simp only [mem_filter, mem_univ, true_and, mem_map, Function.Embedding.coeFn_mk]
    constructor
    · rintro rfl; exact ⟨x, rfl⟩
    · rintro ⟨y, h⟩; exact (congrArg Sigma.fst h).symm]
  simp

/-- Equation (47): for a clique-preserving clustering `v ↦ f (clique of v)`,
`2 Cost + ∑ n_i^2 = ∑_j c_j^2`. -/
lemma two_cost_sigma {n m : ℕ} (a : Fin n → ℕ) (f : Fin n → Fin m) :
    2 * cost (cliqueGraph (fun v : CliquesVtx a => v.1)) (fun v => f v.1) + ∑ i, a i ^ 2 =
      ∑ j, (∑ i ∈ univ.filter (fun i => f i = j), a i) ^ 2 := by
  have hpres : CliquePreserving (fun v : CliquesVtx a => v.1) (fun v => f v.1) := by
    intro u v h; simp only [h]
  have h := disagreeCount_cliquePreserving (fun v : CliquesVtx a => v.1) _ hpres
  rw [two_mul_cost]
  have h1 : samePairs (fun v : CliquesVtx a => v.1) = ∑ i, a i ^ 2 := by
    rw [samePairs_eq_sum_sq _ univ (fun _ => mem_univ _)]
    apply sum_congr rfl; intro i _
    congr 1; convert card_sigma_fiber a i
  have h2 : samePairs (fun v : CliquesVtx a => f v.1) =
      ∑ j, (∑ i ∈ univ.filter (fun i => f i = j), a i) ^ 2 := by
    rw [samePairs_eq_sum_sq _ univ (fun _ => mem_univ _)]
    apply sum_congr rfl; intro j _
    congr 1
    rw [card_eq_sum_card_fiberwise (f := fun v : CliquesVtx a => v.1)
      (t := univ.filter (fun i => f i = j)) (by
        intro v hv
        simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hv ⊢
        exact hv)]
    apply sum_congr rfl; intro i hi
    simp only [mem_filter, mem_univ, true_and] at hi
    rw [← card_sigma_fiber a i]
    congr 1; ext v; simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨-, h⟩; exact h
    · intro h; exact ⟨by rw [h, hi], h⟩
  rw [← h1, ← h2, h]

/-- **Theorem 6 (correctness of the reduction from 3-PARTITION).**  Let `a_1, …, a_{3m}` be a
3-PARTITION instance with `B/4 < a_i < B/2` and `∑ a_i = m B`.  Form the disjoint-cliques
/-- Auxiliary instance for Theorem 6 (Appendix A). -/
instance with cliques of sizes `a_i` and `k = m` clusters, and threshold
`T = (m B^2 - ∑ a_i^2) / 2`.  Then the 3-PARTITION instance is a YES-instance (there is a
partition of `[3m]` into `m` triples each summing to `B`) iff some k-clustering has cost at most
`T` (stated as `2 Cost + ∑ a_i^2 ≤ m B^2`).  Together with the strong NP-completeness of
3-PARTITION [GJ79] this shows that k-CC on disjoint cliques is strongly NP-hard. -/
theorem theorem_6 (m B : ℕ) (a : Fin (3 * m) → ℕ) (hlo : ∀ i, B < 4 * a i)
    (hhi : ∀ i, 2 * a i < B) (hsum : ∑ i, a i = m * B) :
    (∃ f : Fin (3 * m) → Fin m, ∀ j, (univ.filter (fun i => f i = j)).card = 3 ∧
        ∑ i ∈ univ.filter (fun i => f i = j), a i = B) ↔
    (∃ C : CliquesVtx a → Fin m,
        2 * cost (cliqueGraph (fun v : CliquesVtx a => v.1)) C + ∑ i, a i ^ 2 ≤ m * B ^ 2) := by
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨fun v => f v.1, ?_⟩
    rw [two_cost_sigma]
    simp [fun j => (hf j).2]
  · rintro ⟨C, hC⟩
    obtain ⟨C', hC'p, hC'c⟩ := exists_cliquePreserving_le (fun v : CliquesVtx a => v.1) C
    have hapos : ∀ i, 0 < a i := fun i => by have := hlo i; omega
    let f : Fin (3 * m) → Fin m := fun i => C' ⟨i, ⟨0, hapos i⟩⟩
    have hCf : C' = fun v => f v.1 := by
      funext v; exact hC'p _ _ rfl
    have hle : ∑ j, (∑ i ∈ univ.filter (fun i => f i = j), a i) ^ 2 ≤ m * B ^ 2 := by
      rw [← two_cost_sigma, ← hCf]; omega
    set c : Fin m → ℕ := fun j => ∑ i ∈ univ.filter (fun i => f i = j), a i
    have hcsum : ∑ j, c j = m * B := by
      rw [← hsum]; exact sum_fiberwise univ f a
    -- all clusters have size exactly `B`
    have hcB : ∀ j, c j = B := by
      have hz : ∑ j, ((c j : ℤ) - B) ^ 2 = 0 := by
        apply le_antisymm _ (sum_nonneg (fun _ _ => sq_nonneg _))
        have h1 : (∑ j, (c j : ℤ) ^ 2) ≤ m * B ^ 2 := by exact_mod_cast hle
        have h2 : (∑ j, (c j : ℤ)) = m * B := by exact_mod_cast hcsum
        have : ∑ j, ((c j : ℤ) - B) ^ 2 =
            ∑ j, (c j : ℤ) ^ 2 - 2 * B * ∑ j, (c j : ℤ) + m * B ^ 2 := by
          simp only [sub_sq, sum_add_distrib, sum_sub_distrib, mul_sum, sum_const, card_univ,
            Fintype.card_fin, nsmul_eq_mul]
          congr 2
          apply sum_congr rfl; intro x _; ring
        rw [this, h2]; nlinarith
      intro j
      have := (sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg ((c j : ℤ) - B))).1 hz j
        (mem_univ _)
      have : (c j : ℤ) = B := by nlinarith [sq_eq_zero_iff.1 this]
      exact_mod_cast this
    refine ⟨f, fun j => ⟨?_, hcB j⟩⟩
    set S := univ.filter (fun i => f i = j)
    have hSsum : ∑ i ∈ S, a i = B := hcB j
    have hBpos : 0 < B := by
      have : 0 < 3 * m := by have := j.2; omega
      have := hhi ⟨0, this⟩; omega
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · rcases Nat.eq_zero_or_pos S.card with h0 | h0
      · rw [card_eq_zero.1 h0] at hSsum; simp at hSsum; omega
      · have : ∑ i ∈ S, 2 * a i < ∑ i ∈ S, B :=
          sum_lt_sum_of_nonempty (card_pos.1 h0) (fun i _ => hhi i)
        rw [← mul_sum, sum_const, smul_eq_mul] at this
        have : S.card * B ≤ 2 * B := Nat.mul_le_mul_right _ (by omega)
        omega
    · have hne' : S.Nonempty := card_pos.1 (by omega)
      have : ∑ i ∈ S, B < ∑ i ∈ S, 4 * a i := sum_lt_sum_of_nonempty hne' (fun i _ => hlo i)
      rw [← mul_sum, sum_const, smul_eq_mul] at this
      have : 4 * B ≤ S.card * B := Nat.mul_le_mul_right _ (by omega)
      omega

end CCK
