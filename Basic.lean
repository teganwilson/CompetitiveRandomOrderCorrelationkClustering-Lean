module

public import Mathlib

/-!
# Correlation (k-)clustering: basic definitions

This file sets up the basic objects of the paper
*Competitive Random-Order Correlation k-Clustering* (Derakhshan, Ghasemi, Rajaraman, Wasim, Wilson):

* the disagreement cost of a clustering of a graph (Section 1, "Given a set of n items, the
  correlation-clustering problem ...");
* the optimal correlation clustering cost `optCC` (problem CC) and the optimal correlation
  k-clustering cost `optK` (problem k-CC);
* disjoint-cliques instances (Section 3) and clique-preserving clusterings;
* Lemma 3.1 (an optimal k-clustering of a disjoint-cliques instance never splits a clique).

Graphs are `SimpleGraph V` on a finite vertex type `V`; an edge is a `+` pair and a non-edge is
a `-` pair.  A clustering is any map `C : V → ι` (two vertices are in the same cluster iff they
have the same label).  A *k-clustering* is a map `V → Fin k`.
-/

@[expose] public section

open Finset
open scoped Classical

namespace CCK

variable {V : Type*} [Fintype V]

/-- Two distinct vertices `u, v` *disagree* under the clustering `C` if they are adjacent but in
different clusters, or non-adjacent but in the same cluster (Section 1 of the paper). -/
def Disagree (G : SimpleGraph V) {ι : Type*} (C : V → ι) (u v : V) : Prop :=
  u ≠ v ∧ ((G.Adj u v ∧ C u ≠ C v) ∨ (¬ G.Adj u v ∧ C u = C v))

/-- The number of *ordered* pairs of vertices which disagree under `C`.  This is twice the
disagreement cost. -/
noncomputable def disagreeCount (G : SimpleGraph V) {ι : Type*} (C : V → ι) : ℕ :=
  (univ.filter (fun p : V × V => Disagree G C p.1 p.2)).card

/-- The disagreement cost `Cost(C)` of a clustering `C` of the graph `G` (Section 1 of the
paper): the number of unordered pairs of vertices that are inter-cluster edges or intra-cluster
non-edges. -/
noncomputable def cost (G : SimpleGraph V) {ι : Type*} (C : V → ι) : ℕ :=
  disagreeCount G C / 2

/-- The optimal cost of correlation k-clustering, `Cost(OPT_k)` in the paper (problem k-CC):
the minimum cost over all clusterings with at most `k` clusters. -/
noncomputable def optK (G : SimpleGraph V) (k : ℕ) : ℕ :=
  ⨅ C : V → Fin k, cost G C

/-- The optimal cost of (unconstrained) correlation clustering, `Cost(OPT_CC)` in the paper
(problem CC).  Every partition of `V` has at most `|V|` parts, so it suffices to use labels in
`V`. -/
noncomputable def optCC (G : SimpleGraph V) : ℕ :=
  ⨅ C : V → V, cost G C

/-- The disjoint-cliques graph whose cliques are the fibres of `q` (Section 3 of the paper:
an `ℓ` disjoint cliques instance). -/
def cliqueGraph {ι : Type*} (q : V → ι) : SimpleGraph V where
  Adj u v := u ≠ v ∧ q u = q v
  symm := fun _ _ ⟨h1, h2⟩ => ⟨h1.symm, h2.symm⟩
  loopless := ⟨fun _ ⟨h1, _⟩ => h1 rfl⟩

/-- A clustering `C` is *clique-preserving* for the clique structure `q` if it never splits a
clique, i.e. every clique is entirely contained within a single cluster (Lemma 3.1). -/
def CliquePreserving {ι κ : Type*} (q : V → ι) (C : V → κ) : Prop :=
  ∀ u v, q u = q v → C u = C v

/-! ### Basic API -/

omit [Fintype V] in
/-- Auxiliary result for the basic definitions of correlation (k-)clustering (Section 1). -/
lemma disagree_symm (G : SimpleGraph V) {ι : Type*} (C : V → ι) {u v : V} :
    Disagree G C u v ↔ Disagree G C v u := by
  unfold Disagree
  constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨Ne.symm h1, ?_⟩ <;>
    rcases h2 with ⟨a, b⟩ | ⟨a, b⟩
  · exact Or.inl ⟨a.symm, Ne.symm b⟩
  · exact Or.inr ⟨fun h => a h.symm, b.symm⟩
  · exact Or.inl ⟨a.symm, Ne.symm b⟩
  · exact Or.inr ⟨fun h => a h.symm, b.symm⟩

/-- The number of ordered disagreeing pairs is even. -/
lemma even_disagreeCount (G : SimpleGraph V) {ι : Type*} (C : V → ι) :
    Even (disagreeCount G C) := by
  letI : LinearOrder V := LinearOrder.lift' (Fintype.equivFin V) (Fintype.equivFin V).injective
  set S := univ.filter (fun p : V × V => Disagree G C p.1 p.2)
  have hsplit : S = S.filter (fun p => p.1 < p.2) ∪ S.filter (fun p => ¬ p.1 < p.2) :=
    (filter_union_filter_not_eq _ _).symm
  have hdisj : Disjoint (S.filter (fun p => p.1 < p.2)) (S.filter (fun p => ¬ p.1 < p.2)) :=
    disjoint_filter_filter_not _ _ _
  have himg : S.filter (fun p => ¬ p.1 < p.2) = (S.filter (fun p => p.1 < p.2)).image Prod.swap := by
    ext ⟨a, b⟩
    simp only [S, mem_filter, mem_univ, true_and, mem_image, Prod.exists, Prod.swap_prod_mk,
      Prod.mk.injEq]
    constructor
    · rintro ⟨h, hlt⟩
      refine ⟨b, a, ⟨(disagree_symm G C).1 h, ?_⟩, rfl, rfl⟩
      have : a ≠ b := h.1
      exact lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm this)
    · rintro ⟨x, y, ⟨h, hlt⟩, rfl, rfl⟩
      exact ⟨(disagree_symm G C).1 h, not_lt.2 hlt.le⟩
  have hcard : (S.filter (fun p => ¬ p.1 < p.2)).card = (S.filter (fun p => p.1 < p.2)).card := by
    rw [himg, card_image_of_injective _ Prod.swap_injective]
  unfold disagreeCount
  change Even S.card
  rw [hsplit, card_union_of_disjoint hdisj, hcard]
  exact ⟨_, rfl⟩

/-- Auxiliary result for the basic definitions of correlation (k-)clustering (Section 1). -/
lemma two_mul_cost (G : SimpleGraph V) {ι : Type*} (C : V → ι) :
    2 * cost G C = disagreeCount G C := by
  obtain ⟨m, hm⟩ := even_disagreeCount G C
  unfold cost; omega

/-- The cost only depends on which pairs of vertices share a cluster. -/
lemma cost_congr (G : SimpleGraph V) {ι κ : Type*} (C : V → ι) (D : V → κ)
    (h : ∀ u v, C u = C v ↔ D u = D v) : cost G C = cost G D := by
  have : disagreeCount G C = disagreeCount G D := by
    unfold disagreeCount Disagree
    congr 1
    ext p
    simp only [mem_filter, mem_univ, true_and]
    have := h p.1 p.2
    tauto
  unfold cost; rw [this]

/-- Auxiliary result for the basic definitions of correlation (k-)clustering (Section 1). -/
lemma optK_le (G : SimpleGraph V) {k : ℕ} (C : V → Fin k) : optK G k ≤ cost G C :=
  ciInf_le (OrderBot.bddBelow _) C

/-- Auxiliary result for the basic definitions of correlation (k-)clustering (Section 1). -/
lemma exists_optK (G : SimpleGraph V) (k : ℕ) [Nonempty (V → Fin k)] :
    ∃ C : V → Fin k, cost G C = optK G k := by
  unfold optK
  obtain ⟨C, hC⟩ := ciInf_mem (fun C : V → Fin k => cost G C)
  exact ⟨C, hC⟩

/-- Auxiliary result for the basic definitions of correlation (k-)clustering (Section 1). -/
lemma le_optK (G : SimpleGraph V) {k : ℕ} [Nonempty (V → Fin k)] {m : ℕ}
    (h : ∀ C : V → Fin k, m ≤ cost G C) : m ≤ optK G k := by
  obtain ⟨C, hC⟩ := exists_optK G k
  rw [← hC]; exact h C

/-- Auxiliary result for the basic definitions of correlation (k-)clustering (Section 1). -/
lemma optCC_le_cost (G : SimpleGraph V) {ι : Type*} (C : V → ι) : optCC G ≤ cost G C := by
  -- reindex the clusters of `C` by representatives in `V`
  let D : V → V := fun v => Classical.choose (⟨v, rfl⟩ : ∃ u, C u = C v)
  have hD : ∀ v, C (D v) = C v := fun v => Classical.choose_spec (⟨v, rfl⟩ : ∃ u, C u = C v)
  have hcongr : ∀ u v, C u = C v ↔ D u = D v := by
    intro u v
    constructor
    · intro h
      show Classical.choose (⟨u, rfl⟩ : ∃ w, C w = C u) =
        Classical.choose (⟨v, rfl⟩ : ∃ w, C w = C v)
      congr 1
      funext w; rw [h]
    · intro h
      rw [← hD u, ← hD v, h]
  rw [cost_congr G C D hcongr]
  exact ciInf_le (OrderBot.bddBelow _) D

/-- Auxiliary result for the basic definitions of correlation (k-)clustering (Section 1). -/
lemma exists_optCC (G : SimpleGraph V) : ∃ C : V → V, cost G C = optCC G := by
  by_cases hV : Nonempty V
  · unfold optCC
    obtain ⟨C, hC⟩ := ciInf_mem (fun C : V → V => cost G C)
    exact ⟨C, hC⟩
  · have : IsEmpty V := not_nonempty_iff.1 hV
    refine ⟨fun v => v, ?_⟩
    unfold optCC
    have hc : ∀ C : V → V, cost G C = 0 := by
      intro C; unfold cost disagreeCount
      simp
    simp [hc]

/-- `OPT_CC ≤ OPT_k`: the unconstrained optimum is at most the constrained one. -/
lemma optCC_le_optK (G : SimpleGraph V) (k : ℕ) [Nonempty (V → Fin k)] :
    optCC G ≤ optK G k := by
  obtain ⟨C, hC⟩ := exists_optK G k
  rw [← hC]; exact optCC_le_cost G C

/-- `disagreeCount` as a double sum of indicators. -/
lemma disagreeCount_eq_sum (G : SimpleGraph V) {ι : Type*} (C : V → ι) :
    disagreeCount G C = ∑ u, ∑ v, if Disagree G C u v then 1 else 0 := by
  unfold disagreeCount
  rw [card_filter, ← univ_product_univ, sum_product]

end CCK
