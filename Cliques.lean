module

public import RequestProject.Basic

/-!
# Disjoint-cliques instances: Lemma 3.1

We show that for a disjoint-cliques instance, splitting a clique never helps: every k-clustering
can be turned into a clique-preserving k-clustering of no larger cost (Lemma 3.1 of the paper).
We also give the cost formula for clique-preserving clusterings (equation (47), Appendix A).
-/

@[expose] public section

open Finset
open scoped Classical

namespace CCK

variable {V : Type*} [Fintype V] {ι : Type*}

omit [Fintype V] in
/-- Auxiliary result for Lemma 3.1 (Section 3). -/
lemma disagree_cliqueGraph (q : V → ι) {κ : Type*} (C : V → κ) (u v : V) :
    Disagree (cliqueGraph q) C u v ↔
      ((q u = q v ∧ C u ≠ C v ∧ u ≠ v) ∨ (q u ≠ q v ∧ C u = C v)) := by
  unfold Disagree cliqueGraph
  simp only
  constructor
  · rintro ⟨huv, ⟨⟨-, h1⟩, h2⟩ | ⟨h1, h2⟩⟩
    · exact Or.inl ⟨h1, h2, huv⟩
    · exact Or.inr ⟨fun h => h1 ⟨huv, h⟩, h2⟩
  · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2⟩)
    · exact ⟨h3, Or.inl ⟨⟨h3, h1⟩, h2⟩⟩
    · exact ⟨fun h => h1 (h ▸ rfl), Or.inr ⟨fun h => h1 h.2, h2⟩⟩

/-- Number of ordered pairs of vertices sharing a label. -/
noncomputable def samePairs {κ : Type*} (C : V → κ) : ℕ :=
  (univ.filter (fun p : V × V => C p.1 = C p.2)).card

/-- Cost formula for clique-preserving clusterings of a disjoint-cliques instance (cf. equation
(47) in Appendix A): twice the cost equals the number of ordered pairs in a common cluster minus
the number of ordered pairs in a common clique. -/
lemma disagreeCount_cliquePreserving (q : V → ι) {κ : Type*} (C : V → κ)
    (hC : CliquePreserving q C) :
    disagreeCount (cliqueGraph q) C + samePairs q = samePairs C := by
  unfold disagreeCount samePairs
  have hsub : univ.filter (fun p : V × V => q p.1 = q p.2) ⊆
      univ.filter (fun p : V × V => C p.1 = C p.2) := by
    intro p; simp only [mem_filter, mem_univ, true_and]; exact hC _ _
  have heq : univ.filter (fun p : V × V => Disagree (cliqueGraph q) C p.1 p.2) =
      univ.filter (fun p : V × V => C p.1 = C p.2) \
        univ.filter (fun p : V × V => q p.1 = q p.2) := by
    ext p
    simp only [mem_filter, mem_univ, true_and, mem_sdiff, disagree_cliqueGraph]
    constructor
    · rintro (⟨h1, h2, -⟩ | ⟨h1, h2⟩)
      · exact absurd (hC _ _ h1) h2
      · exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩; exact Or.inr ⟨h2, h1⟩
  rw [heq, card_sdiff_of_subset hsub, Nat.sub_add_cancel (card_le_card hsub)]

/-- Moving a whole clique to a single cluster: the cost bookkeeping used in the proof of
Lemma 3.1. -/
lemma disagreeCount_move (q : V → ι) {k : ℕ} (C : V → Fin k) (i : ι) (j : Fin k) :
    disagreeCount (cliqueGraph q) (fun v => if q v = i then j else C v) +
      2 * ∑ u ∈ univ.filter (fun u => q u = i),
        (univ.filter (fun v => q v ≠ i ∧ C v = C u)).card ≤
    disagreeCount (cliqueGraph q) C +
      2 * ((univ.filter (fun u => q u = i)).card *
        (univ.filter (fun v => q v ≠ i ∧ C v = j)).card) := by
  set C' : V → Fin k := fun v => if q v = i then j else C v with hC'
  set K := univ.filter (fun u : V => q u = i)
  rw [disagreeCount_eq_sum, disagreeCount_eq_sum]
  -- split each double sum into four blocks
  have split : ∀ D : V → Fin k, (∑ u, ∑ v, if Disagree (cliqueGraph q) D u v then 1 else 0) =
      (∑ u ∈ K, ∑ v ∈ K, if Disagree (cliqueGraph q) D u v then 1 else 0) +
      (∑ u ∈ K, ∑ v ∈ univ.filter (fun v => ¬ q v = i),
        if Disagree (cliqueGraph q) D u v then 1 else 0) +
      (∑ u ∈ univ.filter (fun u => ¬ q u = i), ∑ v ∈ K,
        if Disagree (cliqueGraph q) D u v then 1 else 0) +
      (∑ u ∈ univ.filter (fun u => ¬ q u = i), ∑ v ∈ univ.filter (fun v => ¬ q v = i),
        if Disagree (cliqueGraph q) D u v then 1 else 0) := by
    intro D
    rw [← sum_filter_add_sum_filter_not univ (fun u => q u = i)]
    simp_rw [← sum_filter_add_sum_filter_not univ (fun v => q v = i)]
    rw [sum_add_distrib, sum_add_distrib]
    ring
  rw [split C', split C]
  -- block in/in
  have hII : (∑ u ∈ K, ∑ v ∈ K, if Disagree (cliqueGraph q) C' u v then 1 else 0) = 0 := by
    apply sum_eq_zero; intro u hu; apply sum_eq_zero; intro v hv
    simp only [K, mem_filter, mem_univ, true_and] at hu hv
    rw [if_neg]
    rw [disagree_cliqueGraph]
    simp [hC', hu, hv]
  -- block in/out
  have hIO : (∑ u ∈ K, ∑ v ∈ univ.filter (fun v => ¬ q v = i),
      if Disagree (cliqueGraph q) C' u v then 1 else 0) =
      K.card * (univ.filter (fun v => q v ≠ i ∧ C v = j)).card := by
    rw [← smul_eq_mul, ← sum_const]
    apply sum_congr rfl; intro u hu
    simp only [K, mem_filter, mem_univ, true_and] at hu
    rw [← card_filter, filter_filter]
    congr 1; apply filter_congr; intro v _
    rw [disagree_cliqueGraph]
    simp only [hC', hu]
    constructor
    · rintro ⟨hv, (⟨h1, -⟩ | ⟨-, h2⟩)⟩
      · exact absurd h1.symm hv
      · simp only [hv, if_false] at h2; exact ⟨hv, h2.symm⟩
    · rintro ⟨hv, h⟩
      refine ⟨hv, Or.inr ⟨fun h' => hv h'.symm, ?_⟩⟩
      simp [hv, h]
  have hOI : (∑ u ∈ univ.filter (fun u => ¬ q u = i), ∑ v ∈ K,
      if Disagree (cliqueGraph q) C' u v then 1 else 0) =
      K.card * (univ.filter (fun v => q v ≠ i ∧ C v = j)).card := by
    rw [sum_comm, ← hIO]
    apply sum_congr rfl; intro u _; apply sum_congr rfl; intro v _
    congr 1; exact propext (disagree_symm _ _)
  have hOO : (∑ u ∈ univ.filter (fun u => ¬ q u = i), ∑ v ∈ univ.filter (fun v => ¬ q v = i),
      if Disagree (cliqueGraph q) C' u v then 1 else 0) =
      (∑ u ∈ univ.filter (fun u => ¬ q u = i), ∑ v ∈ univ.filter (fun v => ¬ q v = i),
      if Disagree (cliqueGraph q) C u v then 1 else 0) := by
    apply sum_congr rfl; intro u hu; apply sum_congr rfl; intro v hv
    simp only [mem_filter, mem_univ, true_and] at hu hv
    simp [disagree_cliqueGraph, hC', hu, hv]
  -- blocks for `C`
  have hIO' : (∑ u ∈ K, ∑ v ∈ univ.filter (fun v => ¬ q v = i),
      if Disagree (cliqueGraph q) C u v then 1 else 0) =
      ∑ u ∈ K, (univ.filter (fun v => q v ≠ i ∧ C v = C u)).card := by
    apply sum_congr rfl; intro u hu
    simp only [K, mem_filter, mem_univ, true_and] at hu
    rw [← card_filter, filter_filter]
    congr 1; apply filter_congr; intro v _
    rw [disagree_cliqueGraph]
    constructor
    · rintro ⟨hv, (⟨h1, -⟩ | ⟨-, h2⟩)⟩
      · exact absurd (hu ▸ h1).symm hv
      · exact ⟨hv, h2.symm⟩
    · rintro ⟨hv, h⟩
      exact ⟨hv, Or.inr ⟨fun h' => hv (hu ▸ h'.symm), h.symm⟩⟩
  have hOI' : (∑ u ∈ univ.filter (fun u => ¬ q u = i), ∑ v ∈ K,
      if Disagree (cliqueGraph q) C u v then 1 else 0) =
      ∑ u ∈ K, (univ.filter (fun v => q v ≠ i ∧ C v = C u)).card := by
    rw [sum_comm, ← hIO']
    apply sum_congr rfl; intro u _; apply sum_congr rfl; intro v _
    congr 1; exact propext (disagree_symm _ _)
  rw [hII, hIO, hOI, hOO, hIO', hOI']
  omega

/-- The set of cliques that are split by a clustering. -/
noncomputable def splitCliques (q : V → ι) {κ : Type*} (C : V → κ) : Finset ι :=
  (univ.image q).filter (fun i => ∃ u v, q u = i ∧ q v = i ∧ C u ≠ C v)

/-- **Lemma 3.1.** In correlation k-clustering of a disjoint-cliques instance, every k-clustering
can be modified into one in which each clique is entirely contained within a single cluster,
without increasing the cost. -/
theorem exists_cliquePreserving_le (q : V → ι) {k : ℕ} (C : V → Fin k) :
    ∃ C' : V → Fin k, CliquePreserving q C' ∧
      cost (cliqueGraph q) C' ≤ cost (cliqueGraph q) C := by
  suffices H : ∀ m : ℕ, ∀ C : V → Fin k, (splitCliques q C).card = m →
      ∃ C' : V → Fin k, CliquePreserving q C' ∧
        disagreeCount (cliqueGraph q) C' ≤ disagreeCount (cliqueGraph q) C by
    obtain ⟨C', h1, h2⟩ := H _ C rfl
    refine ⟨C', h1, ?_⟩
    unfold cost; exact Nat.div_le_div_right h2
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro C hm
  by_cases hsplit : (splitCliques q C).Nonempty
  · obtain ⟨i, hi⟩ := hsplit
    have hi' := hi
    simp only [splitCliques, mem_filter, mem_image, mem_univ, true_and] at hi'
    obtain ⟨-, u0, v0, hu0, hv0, -⟩ := hi'
    set K := univ.filter (fun u : V => q u = i)
    let X : Fin k → ℕ := fun j => (univ.filter (fun v => q v ≠ i ∧ C v = j)).card
    obtain ⟨j, -, hj⟩ := exists_min_image (univ : Finset (Fin k)) X ⟨C u0, mem_univ _⟩
    set C' : V → Fin k := fun v => if q v = i then j else C v with hC'
    have hmove := disagreeCount_move q C i j
    have hle : K.card * X j ≤ ∑ u ∈ K, X (C u) := by
      rw [← smul_eq_mul, ← sum_const]
      exact sum_le_sum (fun u _ => hj _ (mem_univ _))
    have hcost : disagreeCount (cliqueGraph q) C' ≤ disagreeCount (cliqueGraph q) C := by
      have : disagreeCount (cliqueGraph q) C' + 2 * ∑ u ∈ K, X (C u) ≤
          disagreeCount (cliqueGraph q) C + 2 * (K.card * X j) := hmove
      omega
    -- the number of split cliques decreases
    have hsub : splitCliques q C' ⊆ (splitCliques q C).erase i := by
      intro i' hi''
      simp only [splitCliques, mem_filter, mem_image, mem_univ, true_and, mem_erase] at hi'' ⊢
      obtain ⟨hex, u, v, hu, hv, hne⟩ := hi''
      have hii : i' ≠ i := by
        rintro rfl
        simp [hC', hu, hv] at hne
      refine ⟨hii, hex, u, v, hu, hv, ?_⟩
      simpa [hC', hu, hv, hii] using hne
    have hlt : (splitCliques q C').card < m := by
      rw [← hm]
      calc (splitCliques q C').card ≤ ((splitCliques q C).erase i).card := card_le_card hsub
        _ < (splitCliques q C).card := card_erase_lt_of_mem hi
    obtain ⟨C'', h1, h2⟩ := ih _ hlt C' rfl
    exact ⟨C'', h1, h2.trans hcost⟩
  · refine ⟨C, ?_, le_rfl⟩
    intro u v huv
    by_contra hne
    apply hsplit
    refine ⟨q u, ?_⟩
    simp only [splitCliques, mem_filter, mem_image, mem_univ, true_and]
    exact ⟨⟨u, rfl⟩, u, v, rfl, huv.symm, hne⟩

/-- **Lemma 3.1 (optimal form).** For a disjoint-cliques instance there exists an optimal
k-clustering in which each clique is entirely contained within a single cluster. -/
theorem exists_optimal_cliquePreserving (q : V → ι) (k : ℕ) [Nonempty (V → Fin k)] :
    ∃ C : V → Fin k, CliquePreserving q C ∧ cost (cliqueGraph q) C = optK (cliqueGraph q) k := by
  obtain ⟨C, hC⟩ := exists_optK (cliqueGraph q) k
  obtain ⟨C', h1, h2⟩ := exists_cliquePreserving_le q C
  exact ⟨C', h1, le_antisymm (hC ▸ h2) (optK_le _ _)⟩

end CCK
