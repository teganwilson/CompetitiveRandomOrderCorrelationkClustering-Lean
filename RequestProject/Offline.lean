module

public import RequestProject.Cliques

/-!
# Constant-factor approximation for offline correlation k-clustering (Section 4)

Given a clustering `C` of a graph `G` (an approximate solution for unconstrained correlation
clustering), let `I' = cliqueGraph C` be the instance obtained by turning each cluster ("group")
of `C` into a clique and deleting all edges between groups.  We prove Lemma 4.1 and the
approximation guarantee behind Theorem 1.
-/

@[expose] public section

open Finset
open scoped Classical

namespace CCK

variable {V : Type*} [Fintype V] {ι : Type*}

/-- Changing the instance from `G` to `I' = cliqueGraph C` changes the cost of any clustering
`X` by at most `Cost(C, G)` (pairwise: a pair on which the two instances differ is a disagreement
of `C` on `G`). -/
lemma disagreeCount_le_change (G : SimpleGraph V) (C : V → ι) {κ : Type*} (X : V → κ) :
    disagreeCount G X ≤ disagreeCount (cliqueGraph C) X + disagreeCount G C ∧
    disagreeCount (cliqueGraph C) X ≤ disagreeCount G X + disagreeCount G C := by
  have key : ∀ (H₁ H₂ : SimpleGraph V), (∀ u v, u ≠ v → (H₁.Adj u v ↔ H₂.Adj u v) ∨
      Disagree G C u v) → disagreeCount H₁ X ≤ disagreeCount H₂ X + disagreeCount G C := by
    intro H₁ H₂ h
    unfold disagreeCount
    calc (univ.filter (fun p : V × V => Disagree H₁ X p.1 p.2)).card
        ≤ (univ.filter (fun p : V × V => Disagree H₂ X p.1 p.2) ∪
            univ.filter (fun p : V × V => Disagree G C p.1 p.2)).card := by
          apply card_le_card
          intro p hp
          simp only [mem_filter, mem_univ, true_and, mem_union] at hp ⊢
          rcases h p.1 p.2 hp.1 with h' | h'
          · left; unfold Disagree at hp ⊢; rw [← h']; exact hp
          · right; exact h'
      _ ≤ _ := card_union_le _ _
  have hdiff : ∀ u v, u ≠ v → (G.Adj u v ↔ (cliqueGraph C).Adj u v) ∨ Disagree G C u v := by
    intro u v huv
    by_cases hA : G.Adj u v <;> by_cases hC : C u = C v
    · left; simp [cliqueGraph, hA, hC, huv]
    · right; exact ⟨huv, Or.inl ⟨hA, hC⟩⟩
    · right; exact ⟨huv, Or.inr ⟨hA, hC⟩⟩
    · left; simp [cliqueGraph, hA, hC, huv]
  exact ⟨key _ _ hdiff, key _ _ (fun u v huv => (hdiff u v huv).imp Iff.symm id)⟩

/-- Auxiliary result for Section 4 (Lemma 4.1 and Theorem 1). -/
lemma cost_le_change (G : SimpleGraph V) (C : V → ι) {κ : Type*} (X : V → κ) :
    cost G X ≤ cost (cliqueGraph C) X + cost G C ∧
    cost (cliqueGraph C) X ≤ cost G X + cost G C := by
  have h := disagreeCount_le_change G C X
  have e1 := two_mul_cost G X
  have e2 := two_mul_cost (cliqueGraph C) X
  have e3 := two_mul_cost G C
  omega

/-- `Cost(OPT_k, I') ≤ Cost(OPT_k, I) + Cost(C, I)` (proof of Lemma 4.1). -/
lemma optK_cliqueGraph_le (G : SimpleGraph V) (C : V → ι) (k : ℕ) [Nonempty (V → Fin k)] :
    optK (cliqueGraph C) k ≤ optK G k + cost G C := by
  obtain ⟨X, hX⟩ := exists_optK G k
  rw [← hX]
  exact (optK_le _ X).trans (cost_le_change G C X).2

/-- **Lemma 4.1.** Given an `α`-approximate correlation clustering solution `C` for a graph
/-- Auxiliary instance for Section 4 (Lemma 4.1 and Theorem 1). -/
instance `G`, there exists a `(1 + 2α)`-approximate solution to the correlation k-clustering
problem which does not split any cluster of `C`. -/
theorem lemma_4_1 (G : SimpleGraph V) (C : V → ι) {α : ℝ} (hα : 0 ≤ α)
    (hC : (cost G C : ℝ) ≤ α * optCC G) {k : ℕ} (hk : 0 < k) :
    ∃ X : V → Fin k, CliquePreserving C X ∧ (cost G X : ℝ) ≤ (1 + 2 * α) * optK G k := by
  haveI : Nonempty (V → Fin k) := ⟨fun _ => ⟨0, hk⟩⟩
  obtain ⟨X₀, hX₀⟩ := exists_optK G k
  obtain ⟨X, hXp, hXc⟩ := exists_cliquePreserving_le C X₀
  refine ⟨X, hXp, ?_⟩
  have h1 := (cost_le_change G C X).1
  have h2 := (cost_le_change G C X₀).2
  have h3 : (optCC G : ℝ) ≤ optK G k := by exact_mod_cast optCC_le_optK G k
  have h4 : (cost G X : ℝ) ≤ optK G k + 2 * cost G C := by
    have : cost G X ≤ optK G k + 2 * cost G C := by omega
    exact_mod_cast this
  nlinarith

/-- **Theorem 1 (approximation guarantee).** Let `C` be an `α`-approximate solution for
(unconstrained) correlation clustering on `G` (as returned by the algorithm `A`), let
`I' = cliqueGraph C` be the disjoint-cliques instance obtained by turning the clusters of `C`
into cliques, and let `X` be any `(1 + ε)`-approximate correlation k-clustering of `I'` (as
returned by the PTAS of Lemma 3.4 / Appendix B).  Then `X` is a
`(1 + 2α + ε(1 + α))`-approximate, i.e. `(1 + 2α + O(ε))`-approximate, correlation k-clustering
of `G`.  (The polynomial running time of the resulting algorithm `A_k` is not formalized.) -/
theorem theorem_1 (G : SimpleGraph V) (C : V → ι) {α ε : ℝ} (hα : 0 ≤ α) (hε : 0 ≤ ε)
    (hC : (cost G C : ℝ) ≤ α * optCC G) {k : ℕ} (hk : 0 < k) (X : V → Fin k)
    (hX : (cost (cliqueGraph C) X : ℝ) ≤ (1 + ε) * optK (cliqueGraph C) k) :
    (cost G X : ℝ) ≤ (1 + 2 * α + ε * (1 + α)) * optK G k := by
  haveI : Nonempty (V → Fin k) := ⟨fun _ => ⟨0, hk⟩⟩
  have h1 : (cost G X : ℝ) ≤ cost (cliqueGraph C) X + cost G C := by
    exact_mod_cast (cost_le_change G C X).1
  have h2 : (optK (cliqueGraph C) k : ℝ) ≤ optK G k + cost G C := by
    exact_mod_cast optK_cliqueGraph_le G C k
  have h3 : (optCC G : ℝ) ≤ optK G k := by exact_mod_cast optCC_le_optK G k
  have hc0 : (0 : ℝ) ≤ cost G C := Nat.cast_nonneg _
  have hcC : (cost G C : ℝ) ≤ α * optK G k := hC.trans (mul_le_mul_of_nonneg_left h3 hα)
  calc (cost G X : ℝ) ≤ (1 + ε) * (optK G k + cost G C) + cost G C := by nlinarith
    _ = (1 + ε) * optK G k + (2 + ε) * cost G C := by ring
    _ ≤ (1 + ε) * optK G k + (2 + ε) * (α * optK G k) := by nlinarith
    _ = (1 + 2 * α + ε * (1 + α)) * optK G k := by ring

end CCK
