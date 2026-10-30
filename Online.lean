module

public import RequestProject.Basic
public import RequestProject.Exchange

/-!
# The online random-order model

Online correlation k-clustering in the random-order model (Section 1 / Section 2 of the paper).
The vertices of a graph `G` on `Fin n` arrive in a uniformly random order
`σ : Equiv.Perm (Fin n)` (`σ p` is the vertex arriving at time `p`).  When the vertex at time
`p` arrives, the algorithm sees the subgraph induced on the arrived vertices (only through their
arrival times: the labels of the vertices carry no information) and must irrevocably assign the
new vertex to one of the `k` clusters.

Since a deterministic online algorithm can recompute all its past decisions from the current
view, a deterministic online algorithm is simply a function from (time, view) to a cluster.  A
randomized online algorithm whose random bits are independent of the arrival order is a finite
mixture of deterministic ones.

We also set up the *indistinguishability* machinery used in Section 5: the time `tstar` at which
the last connected component receives its first vertex, and the set `isoSet` of positions whose
vertex has no arrived neighbour at that time; re-shuffling the vertices at these positions does
not change anything the algorithm sees up to time `tstar` (`view_mul_fixOutside`).
-/

@[expose] public section

open Finset
open scoped Classical

namespace CCK

variable {n k : ℕ}

/-- What an online algorithm sees at time `t` under arrival order `σ`: the adjacency relation
between the arrival times `≤ t`. -/
def view (G : SimpleGraph (Fin n)) (σ : Equiv.Perm (Fin n)) (t : ℕ) (i j : Fin n) : Prop :=
  (i : ℕ) ≤ t ∧ (j : ℕ) ≤ t ∧ G.Adj (σ i) (σ j)

/-- A deterministic online algorithm for k-CC in the random-order model: at time `t` it assigns
the arriving vertex to a cluster, as a function of the current view (which determines all past
decisions as well). -/
structure OnlineAlg (n k : ℕ) where
  /-- the cluster chosen at time `t` for the arriving vertex, given the current view -/
  decide : ℕ → (Fin n → Fin n → Prop) → Fin k

namespace OnlineAlg

/-- The cluster assigned to the vertex arriving at time `p`. -/
noncomputable def dec (A : OnlineAlg n k) (G : SimpleGraph (Fin n)) (σ : Equiv.Perm (Fin n))
    (p : Fin n) : Fin k :=
  A.decide p (view G σ p)

/-- The final clustering produced by `A` on `G` under the arrival order `σ`. -/
noncomputable def run (A : OnlineAlg n k) (G : SimpleGraph (Fin n)) (σ : Equiv.Perm (Fin n)) :
    Fin n → Fin k :=
  fun v => A.dec G σ (σ.symm v)

/-- Expected cost of `A` over a uniformly random arrival order. -/
noncomputable def expCost (A : OnlineAlg n k) (G : SimpleGraph (Fin n)) : ℝ :=
  expect (fun σ => (cost G (A.run G σ) : ℝ))

end OnlineAlg

/-- Expected cost of a randomized online algorithm, i.e. a probability distribution `w` over
(finitely many) deterministic online algorithms `A`, independent of the arrival order. -/
noncomputable def randExpCost {ι : Type*} [Fintype ι] (w : ι → ℝ) (A : ι → OnlineAlg n k)
    (G : SimpleGraph (Fin n)) : ℝ :=
  ∑ i, w i * (A i).expCost G

/-- A lower bound on the expected cost of every deterministic online algorithm transfers to
randomized online algorithms. -/
lemma le_randExpCost {ι : Type*} [Fintype ι] (w : ι → ℝ) (A : ι → OnlineAlg n k)
    (G : SimpleGraph (Fin n)) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (L : ℝ)
    (hL : ∀ i, L ≤ (A i).expCost G) : L ≤ randExpCost w A G := by
  unfold randExpCost
  calc L = ∑ i, w i * L := by rw [← sum_mul, hw1, one_mul]
    _ ≤ ∑ i, w i * (A i).expCost G :=
        sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hL i) (hw i))

/-! ### Leaders, the time `tstar`, and the isolated positions -/

/-- Positions `≤ t` which are the first arrival of their connected component in the view
(for disjoint cliques, one per clique hit so far). -/
noncomputable def leaders (R : Fin n → Fin n → Prop) (t : ℕ) : Finset (Fin n) :=
  univ.filter (fun p => (p : ℕ) ≤ t ∧ ∀ q, q < p → ¬ R q p)

/-- The first time at which the view contains at least `L` leaders. -/
noncomputable def tstar (G : SimpleGraph (Fin n)) (L : ℕ) (σ : Equiv.Perm (Fin n)) : ℕ :=
  sInf {t | L ≤ (leaders (view G σ t) t).card}

/-- The positions (arrived by time `tstar`) whose vertex has no neighbour arrived by `tstar`. -/
noncomputable def isoSet (G : SimpleGraph (Fin n)) (L : ℕ) (σ : Equiv.Perm (Fin n)) :
    Finset (Fin n) :=
  univ.filter (fun p => (p : ℕ) ≤ tstar G L σ ∧ ∀ q, ¬ view G σ (tstar G L σ) p q)

/-- Auxiliary result for the online random-order model (Sections 1 and 2). -/
lemma tstar_spec (G : SimpleGraph (Fin n)) (L : ℕ) (σ : Equiv.Perm (Fin n))
    (h : ∃ t, L ≤ (leaders (view G σ t) t).card) :
    L ≤ (leaders (view G σ (tstar G L σ)) (tstar G L σ)).card :=
  Nat.sInf_mem (s := {t | L ≤ (leaders (view G σ t) t).card}) h

/-- Auxiliary result for the online random-order model (Sections 1 and 2). -/
lemma lt_of_lt_tstar (G : SimpleGraph (Fin n)) (L : ℕ) (σ : Equiv.Perm (Fin n)) {t : ℕ}
    (ht : t < tstar G L σ) : (leaders (view G σ t) t).card < L := by
  by_contra h
  exact Nat.notMem_of_lt_sInf ht (not_lt.1 h)

/-- Re-shuffling the isolated vertices does not change adjacencies between positions arrived by
`tstar`. -/
lemma adj_mul_fixOutside (G : SimpleGraph (Fin n)) (L : ℕ) (σ ρ : Equiv.Perm (Fin n))
    (hρ : ρ ∈ fixOutside (isoSet G L σ)) {i j : Fin n} (hi : (i : ℕ) ≤ tstar G L σ)
    (hj : (j : ℕ) ≤ tstar G L σ) :
    G.Adj ((σ * ρ) i) ((σ * ρ) j) ↔ G.Adj (σ i) (σ j) := by
  set I := isoSet G L σ
  have hle : ∀ x : Fin n, (x : ℕ) ≤ tstar G L σ → ((ρ x : Fin n) : ℕ) ≤ tstar G L σ := by
    intro x hx
    by_cases hxI : x ∈ I
    · exact (mem_filter.1 (fixOutside_apply_mem hρ hxI)).2.1
    · rw [(fixOutside_mem_iff.1 hρ) x hxI]; exact hx
  have hiso : ∀ x y : Fin n, x ∈ I → (y : ℕ) ≤ tstar G L σ → ¬ G.Adj (σ x) (σ y) := by
    intro x y hx hy hadj
    have hx' := mem_filter.1 hx
    exact hx'.2.2 y ⟨hx'.2.1, hy, hadj⟩
  simp only [Equiv.Perm.mul_apply]
  by_cases hiI : i ∈ I
  · have h1 := hiso _ _ (fixOutside_apply_mem hρ hiI) (hle j hj)
    have h2 := hiso _ _ hiI hj
    tauto
  by_cases hjI : j ∈ I
  · have h1 := hiso _ _ (fixOutside_apply_mem hρ hjI) (hle i hi)
    have h2 := hiso _ _ hjI hi
    constructor
    · intro h; exact absurd h.symm h1
    · intro h; exact absurd h.symm h2
  rw [(fixOutside_mem_iff.1 hρ) i hiI, (fixOutside_mem_iff.1 hρ) j hjI]

/-- Up to time `tstar`, re-shuffling the isolated vertices does not change the view. -/
lemma view_mul_fixOutside (G : SimpleGraph (Fin n)) (L : ℕ) (σ ρ : Equiv.Perm (Fin n))
    (hρ : ρ ∈ fixOutside (isoSet G L σ)) {t : ℕ} (ht : t ≤ tstar G L σ) :
    view G (σ * ρ) t = view G σ t := by
  funext i j
  apply propext
  unfold view
  constructor
  · rintro ⟨hi, hj, h⟩
    exact ⟨hi, hj, (adj_mul_fixOutside G L σ ρ hρ (hi.trans ht) (hj.trans ht)).1 h⟩
  · rintro ⟨hi, hj, h⟩
    exact ⟨hi, hj, (adj_mul_fixOutside G L σ ρ hρ (hi.trans ht) (hj.trans ht)).2 h⟩

/-- Auxiliary result for the online random-order model (Sections 1 and 2). -/
lemma tstar_mul_fixOutside (G : SimpleGraph (Fin n)) (L : ℕ) (σ ρ : Equiv.Perm (Fin n))
    (hρ : ρ ∈ fixOutside (isoSet G L σ)) (h : ∃ t, L ≤ (leaders (view G σ t) t).card) :
    tstar G L (σ * ρ) = tstar G L σ := by
  apply le_antisymm
  · apply Nat.sInf_le
    show L ≤ (leaders (view G (σ * ρ) (tstar G L σ)) (tstar G L σ)).card
    rw [view_mul_fixOutside G L σ ρ hρ le_rfl]
    exact tstar_spec G L σ h
  · apply le_csInf
    · refine ⟨tstar G L σ, ?_⟩
      show L ≤ (leaders (view G (σ * ρ) (tstar G L σ)) (tstar G L σ)).card
      rw [view_mul_fixOutside G L σ ρ hρ le_rfl]
      exact tstar_spec G L σ h
    · intro t ht
      by_contra hlt
      push_neg at hlt
      have := lt_of_lt_tstar G L σ hlt
      simp only [Set.mem_setOf_eq] at ht
      rw [view_mul_fixOutside G L σ ρ hρ hlt.le] at ht
      omega

/-- Auxiliary result for the online random-order model (Sections 1 and 2). -/
lemma exists_leaders_mul_fixOutside (G : SimpleGraph (Fin n)) (L : ℕ) (σ ρ : Equiv.Perm (Fin n))
    (hρ : ρ ∈ fixOutside (isoSet G L σ)) (h : ∃ t, L ≤ (leaders (view G σ t) t).card) :
    ∃ t, L ≤ (leaders (view G (σ * ρ) t) t).card := by
  refine ⟨tstar G L σ, ?_⟩
  rw [view_mul_fixOutside G L σ ρ hρ le_rfl]
  exact tstar_spec G L σ h

/-- Auxiliary result for the online random-order model (Sections 1 and 2). -/
lemma isoSet_mul_fixOutside (G : SimpleGraph (Fin n)) (L : ℕ) (σ ρ : Equiv.Perm (Fin n))
    (hρ : ρ ∈ fixOutside (isoSet G L σ)) (h : ∃ t, L ≤ (leaders (view G σ t) t).card) :
    isoSet G L (σ * ρ) = isoSet G L σ := by
  unfold isoSet
  rw [tstar_mul_fixOutside G L σ ρ hρ h, view_mul_fixOutside G L σ ρ hρ le_rfl]

/-- Up to time `tstar`, the decisions of any online algorithm are unchanged when the isolated
vertices are re-shuffled. -/
lemma dec_mul_fixOutside (A : OnlineAlg n k) (G : SimpleGraph (Fin n)) (L : ℕ)
    (σ ρ : Equiv.Perm (Fin n)) (hρ : ρ ∈ fixOutside (isoSet G L σ)) {p : Fin n}
    (hp : (p : ℕ) ≤ tstar G L σ) : A.dec G (σ * ρ) p = A.dec G σ p := by
  unfold OnlineAlg.dec
  rw [view_mul_fixOutside G L σ ρ hρ hp]

end CCK
