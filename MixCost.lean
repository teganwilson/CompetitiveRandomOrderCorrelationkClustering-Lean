module

public import RequestProject.Cliques

/-!
# Cost of mixing two cliques

Elementary cost lower bounds for disjoint-cliques instances used in Section 5 of the paper
(Figure 5): if a cluster contains vertices of two different cliques, then the cost is at least
the size of one of them; if moreover cliques are never split, the cost is at least the product
of their sizes.
-/

@[expose] public section

open Finset
open scoped Classical

namespace CCK

variable {V : Type*} [Fintype V] {ι : Type*} [DecidableEq ι]

/-- (Figure 5(a)) If two vertices `u, v` of different cliques share a cluster, then the number of
disagreeing ordered pairs is at least twice the size of the clique of `u`. -/
theorem two_mul_card_le_disagreeCount (q : V → ι) {κ : Type*} (f : V → κ) {u v : V}
    (hf : f u = f v) (hq : q u ≠ q v) :
    2 * (univ.filter (fun w => q w = q u)).card ≤ disagreeCount (cliqueGraph q) f := by
  set Cl := univ.filter (fun w => q w = q u) with hCl
  set A := Cl.filter (fun w => f w = f u) with hA
  set D1 := (A ×ˢ ({v} : Finset V)) ∪ (A ×ˢ (Cl \ A)) with hD1
  have hdisj1 : Disjoint (A ×ˢ ({v} : Finset V)) (A ×ˢ (Cl \ A)) := by
    rw [disjoint_product]; right
    rw [disjoint_singleton_left]
    intro hv
    have := (mem_filter.1 (mem_sdiff.1 hv).1).2
    exact hq this.symm
  have hcardD1 : D1.card = A.card + A.card * (Cl.card - A.card) := by
    rw [hD1, card_union_of_disjoint hdisj1, card_product, card_product, card_singleton,
      card_sdiff_of_subset (filter_subset _ _)]
    ring
  have hdisj2 : Disjoint D1 (D1.image Prod.swap) := by
    rw [disjoint_left]
    intro x hx hx'
    obtain ⟨y, hy, rfl⟩ := mem_image.1 hx'
    simp only [hD1, mem_union, mem_product, mem_singleton, mem_sdiff] at hx hy
    simp only [Prod.fst_swap, Prod.snd_swap] at hx
    rcases hy with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hx with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · rw [h2] at h3
      exact hq ((mem_filter.1 (mem_filter.1 h3).1).2).symm
    · rw [h2] at h3
      exact hq ((mem_filter.1 (mem_filter.1 h3).1).2).symm
    · exact h2.2 h3
    · exact h2.2 h3
  have hsub : D1 ∪ D1.image Prod.swap ⊆
      univ.filter (fun p : V × V => Disagree (cliqueGraph q) f p.1 p.2) := by
    have hD1sub : ∀ x ∈ D1, Disagree (cliqueGraph q) f x.1 x.2 := by
      intro x hx
      rw [disagree_cliqueGraph]
      simp only [hD1, mem_union, mem_product, mem_singleton, mem_sdiff, hA, hCl,
        mem_filter, mem_univ, true_and] at hx
      rcases hx with ⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3, h4⟩
      · right; rw [h1, h3]; exact ⟨hq, h2.trans hf⟩
      · left
        refine ⟨h1.trans h3.symm, fun h => h4 ⟨h3, h.symm.trans h2⟩, ?_⟩
        rintro h; rw [h] at h2; exact h4 ⟨h3, h2⟩
    intro x hx
    rw [mem_filter]
    refine ⟨mem_univ _, ?_⟩
    rcases mem_union.1 hx with hx | hx
    · exact hD1sub x hx
    · obtain ⟨y, hy, rfl⟩ := mem_image.1 hx
      exact (disagree_symm _ _).1 (hD1sub y hy)
  have hcard := card_le_card hsub
  rw [card_union_of_disjoint hdisj2, card_image_of_injective _ Prod.swap_injective,
    hcardD1] at hcard
  have hu : u ∈ A := by simp [hA, hCl]
  have h1 : 1 ≤ A.card := card_pos.2 ⟨u, hu⟩
  have h2 : A.card ≤ Cl.card := card_le_card (filter_subset _ _)
  unfold disagreeCount
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le h2
  rw [hd, Nat.add_sub_cancel_left] at hcard
  rw [hd]
  nlinarith

/-- (Figure 5(a)) If two vertices of different cliques share a cluster, the cost is at least the
size of the clique of the first one. -/
theorem card_le_cost_of_mix (q : V → ι) {κ : Type*} (f : V → κ) {u v : V}
    (hf : f u = f v) (hq : q u ≠ q v) :
    (univ.filter (fun w => q w = q u)).card ≤ cost (cliqueGraph q) f := by
  have := two_mul_card_le_disagreeCount q f hf hq
  unfold cost
  omega

/-- (Figure 5(b)) If a clique-preserving clustering puts two different cliques in the same
cluster, the cost is at least the product of their sizes. -/
theorem card_mul_card_le_cost_of_mix (q : V → ι) {κ : Type*} (f : V → κ)
    (hpres : CliquePreserving q f) {u v : V} (hf : f u = f v) (hq : q u ≠ q v) :
    (univ.filter (fun w => q w = q u)).card * (univ.filter (fun w => q w = q v)).card ≤
      cost (cliqueGraph q) f := by
  set Cu := univ.filter (fun w => q w = q u)
  set Cv := univ.filter (fun w => q w = q v)
  have hdisj : Disjoint (Cu ×ˢ Cv) ((Cu ×ˢ Cv).image Prod.swap) := by
    rw [disjoint_left]
    intro x hx hx'
    obtain ⟨y, hy, rfl⟩ := mem_image.1 hx'
    simp only [Cu, Cv, mem_product, mem_filter, mem_univ, true_and, Prod.fst_swap,
      Prod.snd_swap] at hx hy
    exact hq (hy.1.symm.trans hx.2)
  have hD : ∀ x ∈ Cu ×ˢ Cv, Disagree (cliqueGraph q) f x.1 x.2 := by
    intro x hx
    simp only [Cu, Cv, mem_product, mem_filter, mem_univ, true_and] at hx
    rw [disagree_cliqueGraph]
    right
    refine ⟨fun h => hq (hx.1.symm.trans (h.trans hx.2)), ?_⟩
    rw [hpres _ _ hx.1, hpres _ _ hx.2, hf]
  have hsub : (Cu ×ˢ Cv) ∪ (Cu ×ˢ Cv).image Prod.swap ⊆
      univ.filter (fun p : V × V => Disagree (cliqueGraph q) f p.1 p.2) := by
    intro x hx
    rw [mem_filter]
    refine ⟨mem_univ _, ?_⟩
    rcases mem_union.1 hx with hx | hx
    · exact hD x hx
    · obtain ⟨y, hy, rfl⟩ := mem_image.1 hx
      exact (disagree_symm _ _).1 (hD y hy)
  have hcard := card_le_card hsub
  rw [card_union_of_disjoint hdisj, card_image_of_injective _ Prod.swap_injective,
    card_product] at hcard
  unfold cost disagreeCount
  omega

end CCK
