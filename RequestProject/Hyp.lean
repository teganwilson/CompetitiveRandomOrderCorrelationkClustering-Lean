module

public import RequestProject.Prob

/-!
# External probabilistic facts (taken as hypotheses)

The paper uses a few standard facts from the literature, which we do **not** prove; following
the instructions, they are stated here as `Prop`s and are assumed as explicit hypotheses by the
results that use them:

* `ChernoffBound` — Fact 2.1 (Chernoff bounds for negatively associated `{0,1}` variables);
* `PermNegAssoc` — Lemma 5.3 (permutation distributions are negatively associated, [JDP83]);
* `NegAssocClosure` — Lemma 5.4 (closure of negative association under monotone functions of
  disjoint sets of variables, [JDP83]).

All random variables live on the probability space of uniformly random arrival orders
`Equiv.Perm (Fin n)` (the only randomness used in the paper apart from the internal randomness
of the algorithms).  We then *derive* Fact 2.2 (Chernoff bounds for hypergeometric variables)
and Lemma 5.2 from these hypotheses.
-/

@[expose] public section

open Finset
open scoped Classical

namespace CCK

variable {n : ℕ}

/-- Auxiliary result for the external probabilistic facts of Section 2. -/
lemma expect_add (f g : Equiv.Perm (Fin n) → ℝ) :
    expect (fun σ => f σ + g σ) = expect f + expect g := by
  unfold expect; rw [sum_add_distrib, add_div]

/-- Auxiliary result for the external probabilistic facts of Section 2. -/
lemma expect_sum {ι : Type*} (s : Finset ι) (f : ι → Equiv.Perm (Fin n) → ℝ) :
    expect (fun σ => ∑ i ∈ s, f i σ) = ∑ i ∈ s, expect (f i) := by
  unfold expect; rw [sum_comm, sum_div]

/-- Auxiliary result for the external probabilistic facts of Section 2. -/
lemma expect_indicator (P : Equiv.Perm (Fin n) → Prop) [DecidablePred P] :
    expect (fun σ => if P σ then (1 : ℝ) else 0) = prob P := by
  unfold expect prob; rw [sum_boole]

/-- Negative association of a family of random variables on uniformly random arrival orders
(Section 2.5 of the paper, following [JDP83]): for disjoint index sets `A, B` and nondecreasing
functions `f, g` depending only on the coordinates in `A`, resp. `B`,
`E[f(X) g(X)] ≤ E[f(X)] E[g(X)]`. -/
def NegAssoc {ι : Type*} (X : ι → Equiv.Perm (Fin n) → ℝ) : Prop :=
  ∀ (A B : Finset ι), Disjoint A B → ∀ f g : (ι → ℝ) → ℝ, Monotone f → Monotone g →
    (∀ x y : ι → ℝ, (∀ i ∈ A, x i = y i) → f x = f y) →
    (∀ x y : ι → ℝ, (∀ i ∈ B, x i = y i) → g x = g y) →
    expect (fun σ => f (fun i => X i σ) * g (fun i => X i σ)) ≤
      expect (fun σ => f (fun i => X i σ)) * expect (fun σ => g (fun i => X i σ))

/-- **Fact 2.1 (Chernoff bound)**, assumed as a hypothesis.  For `X = ∑ X_i` with `X_i ∈ {0,1}`
negatively associated and `μ = E[X]`: (1) `P[X ≥ (1+δ)μ] ≤ exp(-δ²μ/(2+δ))` for `δ > 0`;
(2) `P[X ≤ (1-δ)μ] ≤ exp(-δ²μ/2)` for `δ ∈ (0,1)`; and `P[X ≥ a] ≤ 2^{-a}` for `a ≥ 2eμ`.
(Only the negatively associated version is used in the paper.) -/
def ChernoffBound : Prop :=
  ∀ (n : ℕ) (ι : Type) [Fintype ι] (X : ι → Equiv.Perm (Fin n) → ℝ),
    (∀ i σ, X i σ = 0 ∨ X i σ = 1) → NegAssoc X →
    (∀ δ : ℝ, 0 < δ → prob (fun σ => (1 + δ) * expect (fun τ => ∑ i, X i τ) ≤ ∑ i, X i σ) ≤
        Real.exp (-(δ ^ 2 * expect (fun τ => ∑ i, X i τ)) / (2 + δ))) ∧
    (∀ δ : ℝ, 0 < δ → δ < 1 →
        prob (fun σ => ∑ i, X i σ ≤ (1 - δ) * expect (fun τ => ∑ i, X i τ)) ≤
        Real.exp (-(δ ^ 2 * expect (fun τ => ∑ i, X i τ)) / 2)) ∧
    (∀ a : ℝ, 2 * Real.exp 1 * expect (fun τ => ∑ i, X i τ) ≤ a →
        prob (fun σ => a ≤ ∑ i, X i σ) ≤ (2 : ℝ) ^ (-a))

/-- **Lemma 5.3 (permutation distributions are negatively associated, [JDP83])**, assumed as a
hypothesis: if values `x_0, …, x_{n-1}` are assigned to the vertices in uniformly random order
(vertex `v` receives the value attached to its arrival time), the resulting variables are
negatively associated. -/
def PermNegAssoc : Prop :=
  ∀ (n : ℕ) (x : Fin n → ℝ), NegAssoc (fun (v : Fin n) (σ : Equiv.Perm (Fin n)) => x (σ.symm v))

/-- **Lemma 5.4 (closure of negative association, [JDP83])**, assumed as a hypothesis: functions
which are all nondecreasing (or all nonincreasing), each depending on a different one of
pairwise disjoint sets of negatively associated variables, are negatively associated. -/
def NegAssocClosure : Prop :=
  ∀ (n : ℕ) (ι κ : Type) (Y : ι → Equiv.Perm (Fin n) → ℝ), NegAssoc Y →
    ∀ (S : κ → Finset ι), (∀ j j', j ≠ j' → Disjoint (S j) (S j')) →
    ∀ F : κ → (ι → ℝ) → ℝ, ((∀ j, Monotone (F j)) ∨ (∀ j, Antitone (F j))) →
    (∀ j (x y : ι → ℝ), (∀ i ∈ S j, x i = y i) → F j x = F j y) →
    NegAssoc (fun j σ => F j (fun i => Y i σ))

/-- A subfamily of a negatively associated family is negatively associated. -/
lemma NegAssoc.comp_subtype {ι : Type*} {X : ι → Equiv.Perm (Fin n) → ℝ} (hX : NegAssoc X)
    (p : ι → Prop) : NegAssoc (fun (i : Subtype p) => X i) := by
  intro A B hAB f g hf hg hfA hgB
  let ext : (ι → ℝ) → (Subtype p → ℝ) := fun y i => y i
  have hext : Monotone ext := fun y y' h i => h i
  have := hX (A.map (Function.Embedding.subtype p)) (B.map (Function.Embedding.subtype p))
    (by
      rw [disjoint_left]
      intro i hiA hiB
      obtain ⟨a, ha, rfl⟩ := mem_map.1 hiA
      obtain ⟨b, hb, hab⟩ := mem_map.1 hiB
      have : b = a := Subtype.ext hab
      subst this
      exact disjoint_left.1 hAB ha hb)
    (f ∘ ext) (g ∘ ext) (hf.comp hext) (hg.comp hext)
    (by
      intro x y hxy
      apply hfA
      intro i hi
      exact hxy i (mem_map.2 ⟨i, hi, rfl⟩))
    (by
      intro x y hxy
      apply hgB
      intro i hi
      exact hxy i (mem_map.2 ⟨i, hi, rfl⟩))
  simpa [ext] using this

/-- `P(v arrives among the first t) = t / n`. -/
lemma prob_mem_firstSet {t : ℕ} (ht : t ≤ n) (v : Fin n) :
    prob (fun σ => v ∈ firstSet σ t) = (t : ℝ) / n := by
  have hn : 0 < n := Nat.lt_of_lt_of_le (Fin.pos v) le_rfl
  have h := prob_disjoint_firstSet ht {v}
  rw [card_singleton] at h
  have hc : prob (fun σ => v ∈ firstSet σ t) = 1 - prob (fun σ => Disjoint (firstSet σ t) {v}) := by
    rw [← prob_compl]
    congr 1
    funext σ
    simp [disjoint_singleton_right]
  rw [hc, h]
  have hchoose : (n - 1).choose t * n = n.choose t * (n - t) := by
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    simpa using Nat.choose_mul_succ_eq n' t
  have hcpos : (0 : ℝ) < n.choose t := by exact_mod_cast Nat.choose_pos ht
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h' : ((n - 1).choose t : ℝ) * n = n.choose t * (n - t) := by
    have := congrArg (fun x : ℕ => (x : ℝ)) hchoose
    push_cast [Nat.cast_sub ht] at this
    exact this
  field_simp
  linarith

/-- **Fact 2.2 (hypergeometric distributions are negatively associated; Chernoff bounds for
them).**  Let `M` be a set of `K` marked vertices and `X` the number of marked vertices among the
first `t` arrivals (`X ∼ Hypergeometric(n, K, t)`).  Then `E[X] = K t / n` and the Chernoff
bounds of Fact 2.1 hold for `X`.  Derived here from Fact 2.1 and Lemma 5.3. -/
theorem fact_2_2 (hCh : ChernoffBound) (hPNA : PermNegAssoc) (M : Finset (Fin n)) {t : ℕ}
    (ht : t ≤ n) :
    expect (fun σ => ((firstSet σ t ∩ M).card : ℝ)) = (M.card : ℝ) * t / n ∧
    (∀ δ : ℝ, 0 < δ → prob (fun σ => (1 + δ) * ((M.card : ℝ) * t / n) ≤
        (firstSet σ t ∩ M).card) ≤ Real.exp (-(δ ^ 2 * ((M.card : ℝ) * t / n)) / (2 + δ))) ∧
    (∀ δ : ℝ, 0 < δ → δ < 1 →
        prob (fun σ => ((firstSet σ t ∩ M).card : ℝ) ≤ (1 - δ) * ((M.card : ℝ) * t / n)) ≤
        Real.exp (-(δ ^ 2 * ((M.card : ℝ) * t / n)) / 2)) ∧
    (∀ a : ℝ, 2 * Real.exp 1 * ((M.card : ℝ) * t / n) ≤ a →
        prob (fun σ => a ≤ (firstSet σ t ∩ M).card) ≤ (2 : ℝ) ^ (-a)) := by
  -- indicator variables of the marked vertices
  set x : Fin n → ℝ := fun i => if (i : ℕ) < t then 1 else 0
  set Y : {v // v ∈ M} → Equiv.Perm (Fin n) → ℝ := fun v σ => x (σ.symm v)
  have hNA : NegAssoc Y := (hPNA n x).comp_subtype (fun v => v ∈ M)
  have h01 : ∀ v σ, Y v σ = 0 ∨ Y v σ = 1 := by
    intro v σ; simp only [Y, x]; split_ifs <;> simp
  have hsum : ∀ σ, ∑ v, Y v σ = ((firstSet σ t ∩ M).card : ℝ) := by
    intro σ
    simp only [Y, x]
    rw [sum_boole]
    congr 1
    rw [← card_map (Function.Embedding.subtype (· ∈ M))]
    congr 1
    ext w
    simp only [mem_map, mem_filter, mem_univ, true_and, Function.Embedding.coe_subtype,
      firstSet, arrTime, mem_inter]
    constructor
    · rintro ⟨v, hv, rfl⟩; exact ⟨hv, v.2⟩
    · rintro ⟨hw, hwM⟩; exact ⟨⟨w, hwM⟩, hw, rfl⟩
  have hexp : expect (fun σ => ∑ v, Y v σ) = (M.card : ℝ) * t / n := by
    rw [expect_sum]
    have : ∀ v : {v // v ∈ M}, expect (Y v) = (t : ℝ) / n := by
      intro v
      rw [← prob_mem_firstSet ht v.1, ← expect_indicator]
      congr 1
      funext σ
      simp [Y, x, firstSet, arrTime]
    rw [sum_congr rfl (fun v _ => this v), sum_const, card_univ, Fintype.card_coe,
      nsmul_eq_mul]
    ring
  have hexp' : expect (fun σ => ((firstSet σ t ∩ M).card : ℝ)) = (M.card : ℝ) * t / n := by
    rw [← hexp]; congr 1; funext σ; rw [hsum]
  obtain ⟨h1, h2, h3⟩ := hCh n {v // v ∈ M} Y h01 hNA
  simp only [hsum] at h1 h2 h3
  rw [hexp'] at h1 h2 h3
  exact ⟨hexp', h1, h2, h3⟩

end CCK
