module

public import RequestProject.Online
public import RequestProject.MixCost

/-!
# The lower-bound instance of Section 5

The instance of Section 5 (Figure 4a): `c = k - 1` disjoint cliques of size `m` (in the paper
`m = 2 ln k`) and two singletons, on `n = c m + 2` vertices.  Vertex `v < c m` belongs to clique
`v / m`; the vertices `c m` and `c m + 1` are the two singletons.  Its optimal `k`-clustering
cost is `1` (Figure 4b).
-/

@[expose] public section

open Finset
open scoped Classical

namespace CCK

variable {c m : ℕ}

/-- Component label of a vertex of the lower-bound instance: `v / m` for the clique vertices
`v < c m`, and `c`, `c + 1` for the two singletons. -/
def lbComp (c m : ℕ) (v : Fin (c * m + 2)) : ℕ :=
  if (v : ℕ) < c * m then (v : ℕ) / m else c + ((v : ℕ) - c * m)

/-- The lower-bound instance of Section 5 (Figure 4a): `c` cliques of size `m` and two
singletons. -/
def lbGraph (c m : ℕ) : SimpleGraph (Fin (c * m + 2)) := cliqueGraph (lbComp c m)

/-- The first singleton. -/
def lbS1 (c m : ℕ) : Fin (c * m + 2) := ⟨c * m, by omega⟩

/-- The second singleton. -/
def lbS2 (c m : ℕ) : Fin (c * m + 2) := ⟨c * m + 1, by omega⟩

/-- Auxiliary result for the lower-bound instance of Section 5 (proof of Theorem 2). -/
lemma lbComp_s1 : lbComp c m (lbS1 c m) = c := by simp [lbComp, lbS1]

/-- Auxiliary result for the lower-bound instance of Section 5 (proof of Theorem 2). -/
lemma lbComp_s2 : lbComp c m (lbS2 c m) = c + 1 := by simp [lbComp, lbS2]

/-- Auxiliary result for the lower-bound instance of Section 5 (proof of Theorem 2). -/
lemma lbS1_ne_lbS2 : lbS1 c m ≠ lbS2 c m := by
  simp [lbS1, lbS2, Fin.ext_iff]

/-- Auxiliary result for the lower-bound instance of Section 5 (proof of Theorem 2). -/
lemma lbComp_lt (hm : 1 ≤ m) (v : Fin (c * m + 2)) : lbComp c m v < c + 2 := by
  unfold lbComp
  split_ifs with h
  · have : (v : ℕ) / m < c := (Nat.div_lt_iff_lt_mul (by omega)).2 (by linarith)
    omega
  · omega

/-- Auxiliary result for the lower-bound instance of Section 5 (proof of Theorem 2). -/
lemma lbComp_of_lt (hm : 1 ≤ m) {v : Fin (c * m + 2)} (hv : (v : ℕ) < c * m) :
    lbComp c m v < c := by
  unfold lbComp
  rw [if_pos hv]
  exact (Nat.div_lt_iff_lt_mul (by omega)).2 (by linarith)

/-- A vertex whose label is at least `c` is one of the two singletons. -/
lemma eq_s1_or_s2 (hm : 1 ≤ m) {v : Fin (c * m + 2)} (hv : c ≤ lbComp c m v) :
    v = lbS1 c m ∨ v = lbS2 c m := by
  by_cases h : (v : ℕ) < c * m
  · have := lbComp_of_lt hm h; omega
  · have := v.2
    simp only [lbS1, lbS2, Fin.ext_iff]
    omega

/-- Auxiliary result for the lower-bound instance of Section 5 (proof of Theorem 2). -/
lemma lbComp_eq_s1 (hm : 1 ≤ m) {v : Fin (c * m + 2)} (hv : lbComp c m v = c) :
    v = lbS1 c m := by
  rcases eq_s1_or_s2 hm hv.ge with h | h
  · exact h
  · rw [h, lbComp_s2] at hv; omega

/-- Auxiliary result for the lower-bound instance of Section 5 (proof of Theorem 2). -/
lemma lbComp_eq_s2 (hm : 1 ≤ m) {v : Fin (c * m + 2)} (hv : lbComp c m v = c + 1) :
    v = lbS2 c m := by
  rcases eq_s1_or_s2 hm (by omega : c ≤ lbComp c m v) with h | h
  · rw [h, lbComp_s1] at hv; omega
  · exact h

/-- A representative of each component `j < c + 2`. -/
def lbRep (c m : ℕ) (j : ℕ) : Fin (c * m + 2) :=
  if h : j < c then ⟨j * m, by nlinarith⟩ else if j = c then lbS1 c m else lbS2 c m

/-- Auxiliary result for the lower-bound instance of Section 5 (proof of Theorem 2). -/
lemma lbComp_rep (hm : 1 ≤ m) {j : ℕ} (hj : j < c + 2) : lbComp c m (lbRep c m j) = j := by
  unfold lbRep
  split_ifs with h1 h2
  · have : j * m < c * m := Nat.mul_lt_mul_of_pos_right h1 (by omega)
    simp only [lbComp, this, if_true]
    exact Nat.mul_div_cancel j (by omega)
  · rw [lbComp_s1]; omega
  · rw [lbComp_s2]; omega

/-- Every clique has at least `m` vertices. -/
lemma le_card_comp (hm : 1 ≤ m) {u : Fin (c * m + 2)} (hu : (u : ℕ) < c * m) :
    m ≤ (univ.filter (fun w => lbComp c m w = lbComp c m u)).card := by
  set j := (u : ℕ) / m
  have hj : j < c := (Nat.div_lt_iff_lt_mul (by omega)).2 (by linarith)
  have hjm : j * m + m ≤ c * m := by nlinarith
  have := card_le_card_of_injOn (s := range m)
    (t := univ.filter (fun w => lbComp c m w = lbComp c m u))
    (fun i => (⟨j * m + i % m, by
      have := Nat.mod_lt i (show 0 < m by omega); omega⟩ : Fin (c * m + 2)))
    (by
      intro i hi
      simp only [coe_filter, Set.mem_setOf_eq, mem_univ, true_and]
      have hi' := mem_range.1 hi
      have him : i % m = i := Nat.mod_eq_of_lt hi'
      simp only [lbComp, him]
      rw [if_pos (by omega), if_pos hu]
      rw [show j * m + i = i + m * j by ring, Nat.add_mul_div_left _ _ (by omega),
        Nat.div_eq_of_lt hi', zero_add])
    (by
      intro i hi i' hi' h
      simp only [mem_coe, mem_range] at hi hi'
      simp only [Fin.mk.injEq, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hi'] at h
      omega)
  simpa using this

/-- In a clustering of cost less than `m`, two vertices from different components share a
cluster only if they are the two singletons. -/
lemma singletons_of_cost_lt (hm : 1 ≤ m) {κ : Type*} (f : Fin (c * m + 2) → κ)
    (hf : cost (lbGraph c m) f < m) {u v : Fin (c * m + 2)} (huv : f u = f v)
    (hcomp : lbComp c m u ≠ lbComp c m v) :
    c ≤ lbComp c m u ∧ c ≤ lbComp c m v := by
  have key : ∀ x y : Fin (c * m + 2), f x = f y → lbComp c m x ≠ lbComp c m y →
      c ≤ lbComp c m x := by
    intro x y hxy hc
    by_contra hlt
    push_neg at hlt
    have hx : (x : ℕ) < c * m := by
      by_contra h
      simp only [lbComp, h, if_false] at hlt
      omega
    have h1 := card_le_cost_of_mix (lbComp c m) f hxy hc
    have h2 := le_card_comp hm hx
    unfold lbGraph at hf
    omega
  exact ⟨key u v huv hcomp, key v u huv.symm (Ne.symm hcomp)⟩

/-- The optimal `k`-clustering of the instance, `k = c + 1` (Figure 4b), has cost `1`. -/
theorem optK_lbGraph (hm : 1 ≤ m) : optK (lbGraph c m) (c + 1) = 1 := by
  apply le_antisymm
  · -- the clustering `v ↦ min (label v) c`
    set f : Fin (c * m + 2) → Fin (c + 1) := fun v => ⟨min (lbComp c m v) c, by omega⟩
    refine (optK_le _ f).trans (le_of_eq ?_)
    have hset : univ.filter (fun p : Fin (c * m + 2) × Fin (c * m + 2) =>
        Disagree (lbGraph c m) f p.1 p.2) =
        {(lbS1 c m, lbS2 c m), (lbS2 c m, lbS1 c m)} := by
      ext ⟨u, v⟩
      simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton, Prod.mk.injEq]
      unfold lbGraph
      rw [disagree_cliqueGraph]
      simp only [f, ne_eq, Fin.mk.injEq]
      constructor
      · rintro (⟨h1, h2, -⟩ | ⟨h1, h2⟩)
        · exact absurd (by rw [h1]) h2
        · have hu : c ≤ lbComp c m u := by
            by_contra h; push_neg at h
            have : lbComp c m u = min (lbComp c m v) c := by rw [← h2]; omega
            omega
          have hv : c ≤ lbComp c m v := by
            by_contra h; push_neg at h
            have : lbComp c m v = min (lbComp c m u) c := by rw [h2]; omega
            omega
          rcases eq_s1_or_s2 hm hu with rfl | rfl <;> rcases eq_s1_or_s2 hm hv with rfl | rfl
          · exact absurd rfl h1
          · left; exact ⟨rfl, rfl⟩
          · right; exact ⟨rfl, rfl⟩
          · exact absurd rfl h1
      · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · right; rw [lbComp_s1, lbComp_s2]; omega
        · right; rw [lbComp_s1, lbComp_s2]; omega
    unfold cost disagreeCount
    rw [hset, card_pair]
    intro h
    simp only [Prod.mk.injEq] at h
    exact lbS1_ne_lbS2 h.1
  · -- any `(c+1)`-clustering mixes two of the `c + 2` components
    obtain ⟨f, hf⟩ := exists_optK (lbGraph c m) (c + 1)
    rw [← hf]
    obtain ⟨x, hx, y, hy, hxy, hfxy⟩ := exists_ne_map_eq_of_card_lt_of_maps_to
      (s := range (c + 2)) (t := (univ : Finset (Fin (c + 1))))
      (f := fun j => f (lbRep c m j)) (by simp) (fun _ _ => by simp)
    have hx' := mem_range.1 hx
    have hy' := mem_range.1 hy
    have := card_le_cost_of_mix (lbComp c m) f (u := lbRep c m x) (v := lbRep c m y) hfxy
      (by rw [lbComp_rep hm hx', lbComp_rep hm hy']; exact hxy)
    have hpos : 1 ≤ (univ.filter (fun w => lbComp c m w = lbComp c m (lbRep c m x))).card :=
      card_pos.2 ⟨lbRep c m x, by simp⟩
    unfold lbGraph
    omega

end CCK
