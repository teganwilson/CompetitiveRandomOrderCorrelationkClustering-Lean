module

public import RequestProject.Lemma76

/-!
# Conditional hypergeometric Chernoff bounds

The proofs of Lemmas 7.5, 7.7 and 7.9 condition on the arrival sequence up to some time `j`
and then use that the remaining vertices arrive in a uniformly random order, so that the number
of vertices of a (conditionally fixed) set arriving between times `j` and `t` is hypergeometric,
and apply the Chernoff bounds of Fact 2.2 to it.

Fact 2.2 is an external result which we do not prove; it is stated here, for a uniformly random
re-arrangement of an arbitrary set `I` of positions, as the hypothesis `HypergeomChernoff`.  We
then transfer it to the conditional statements used in the paper.
-/

@[expose] public section

open Finset
open scoped Classical

namespace CCK

variable {n : ℕ}

/-- **Fact 2.2 (Chernoff bounds for hypergeometric distributions)**, in the form used in the
proofs of Lemmas 7.5, 7.7 and 7.9, assumed as a hypothesis.  Let `I` be a set of positions,
`J ⊆ I` and `Q ⊆ I`, and let `ρ` be a uniformly random permutation of the positions in `I`
(fixing all other positions).  Then `X = |{p ∈ J : ρ p ∈ Q}| ∼ Hypergeometric(|I|, |Q|, |J|)`
has mean `μ = |Q| |J| / |I|` and satisfies the Chernoff bounds
`P[X ≥ (1+δ)μ] ≤ exp(-δ²μ/(2+δ))` for `δ > 0` and `P[X ≤ (1-δ)μ] ≤ exp(-δ²μ/2)` for
`δ ∈ (0,1)`.  (Probabilities are written as counts of permutations.) -/
def HypergeomChernoff : Prop :=
  ∀ (n : ℕ) (I J Q : Finset (Fin n)), J ⊆ I → Q ⊆ I →
    (∀ δ : ℝ, 0 < δ →
      (((fixOutside I).filter (fun ρ => (1 + δ) * ((Q.card : ℝ) * J.card / I.card) ≤
          ((J.filter (fun p => ρ p ∈ Q)).card : ℝ))).card : ℝ) ≤
        Real.exp (-(δ ^ 2 * ((Q.card : ℝ) * J.card / I.card)) / (2 + δ)) *
          (fixOutside I).card) ∧
    (∀ δ : ℝ, 0 < δ → δ < 1 →
      (((fixOutside I).filter (fun ρ => ((J.filter (fun p => ρ p ∈ Q)).card : ℝ) ≤
          (1 - δ) * ((Q.card : ℝ) * J.card / I.card))).card : ℝ) ≤
        Real.exp (-(δ ^ 2 * ((Q.card : ℝ) * J.card / I.card)) / 2) * (fixOutside I).card)

/-- Probabilities of equivalent events (with arbitrary decidability instances) agree. -/
lemma prob_congr {P Q : Equiv.Perm (Fin n) → Prop} {_ : DecidablePred P} {_ : DecidablePred Q}
    (h : ∀ σ, P σ ↔ Q σ) : prob P = prob Q := by
  unfold prob
  rw [filter_congr (fun σ _ => h σ)]

/-- If, for every outcome of an event `A` which is invariant under re-shuffling the positions `I`,
at most a `c` fraction of the re-shufflings are bad, then `P[A ∧ Bad] ≤ c P[A]`. -/
lemma prob_and_le_of_orbit (I : Finset (Fin n)) (A : Equiv.Perm (Fin n) → Prop)
    (hA : ∀ σ ρ, ρ ∈ fixOutside I → A σ → A (σ * ρ))
    (Bad : Equiv.Perm (Fin n) → Prop) (c : ℝ)
    (hc : ∀ σ, A σ → (((fixOutside I).filter (fun ρ => Bad (σ * ρ))).card : ℝ) ≤
      c * (fixOutside I).card) :
    prob (fun σ => A σ ∧ Bad σ) ≤ c * prob A := by
  set S := univ.filter A with hS
  have key := exchange_count S (fun _ => I) (fun σ => ¬ Bad σ) (1 - c)
    (by
      intro σ hσ ρ hρ
      refine ⟨?_, rfl⟩
      simp only [hS, mem_filter, mem_univ, true_and] at hσ ⊢
      exact hA σ ρ hρ hσ)
    (by
      intro σ hσ
      have hσ' : A σ := by simpa [hS] using hσ
      have h1 := hc σ hσ'
      have h2 := card_filter_add_card_filter_not (s := fixOutside I) (fun ρ => Bad (σ * ρ))
      have h2' : (((fixOutside I).filter (fun ρ => Bad (σ * ρ))).card : ℝ) +
          (((fixOutside I).filter (fun ρ => ¬ Bad (σ * ρ))).card : ℝ) =
          (fixOutside I).card := by exact_mod_cast h2
      linarith)
  have h3 := card_filter_add_card_filter_not (s := S) Bad
  have h3' : ((S.filter Bad).card : ℝ) + ((S.filter (fun σ => ¬ Bad σ)).card : ℝ) = S.card := by
    exact_mod_cast h3
  have hSB : S.filter Bad = univ.filter (fun σ => A σ ∧ Bad σ) := by
    ext σ; simp [hS]
  unfold prob
  rw [← hSB, mul_div_assoc', ← hS]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  linarith

/-- The positions `≥ j`. -/
noncomputable def posGe (j : ℕ) : Finset (Fin n) := univ.filter (fun p : Fin n => j ≤ (p : ℕ))

/-- The positions in `[j, t)`. -/
noncomputable def posIco (j t : ℕ) : Finset (Fin n) :=
  univ.filter (fun p : Fin n => j ≤ (p : ℕ) ∧ (p : ℕ) < t)

/-- Auxiliary result for the conditional use of Fact 2.2 (Section 2). -/
lemma card_posIco (j t : ℕ) (ht : t ≤ n) : (posIco (n := n) j t).card = t - j := by
  have : (posIco (n := n) j t).map Fin.valEmbedding = Ico j t := by
    ext x; simp only [posIco, mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply,
      mem_Ico]
    constructor
    · rintro ⟨p, hp, rfl⟩; exact hp
    · intro hx; exact ⟨⟨x, by omega⟩, hx, rfl⟩
  rw [← card_map, this, Nat.card_Ico]

/-- Auxiliary result for the conditional use of Fact 2.2 (Section 2). -/
lemma posGe_eq_posIco (j : ℕ) : posGe (n := n) j = posIco j n := by
  ext p; simp [posGe, posIco]

/-- Auxiliary result for the conditional use of Fact 2.2 (Section 2). -/
lemma card_posGe (j : ℕ) : (posGe (n := n) j).card = n - j := by
  rw [posGe_eq_posIco, card_posIco j n le_rfl]

/-- Re-shuffling the positions `≥ j`: the number of vertices of a set `R` (all arriving at
time `≥ j`) among the first `t` arrivals of `σ ρ` is the number of positions `p ∈ [j, t)` with
`ρ p ∈ σ⁻¹(R)`. -/
lemma card_firstSet_mul_inter {j t : ℕ} (σ ρ : Equiv.Perm (Fin n))
    (hρ : ρ ∈ fixOutside (posGe j)) (R : Finset (Fin n)) (hR : ∀ u ∈ R, j ≤ arrTime σ u) :
    (firstSet (σ * ρ) t ∩ R).card =
      ((posIco j t).filter (fun p => ρ p ∈ R.image σ.symm)).card := by
  symm
  apply card_nbij' (fun p => σ (ρ p)) (fun u => ρ.symm (σ.symm u))
  · intro p hp
    simp only [coe_filter, posIco, mem_filter, mem_univ, true_and, Set.mem_setOf_eq,
      mem_image] at hp
    obtain ⟨⟨hjp, hpt⟩, u, hu, hu'⟩ := hp
    simp only [coe_inter, Set.mem_inter_iff, mem_coe, firstSet, mem_filter, mem_univ, true_and,
      arrTime]
    refine ⟨?_, ?_⟩
    · rw [mul_symm_apply]; simpa using hpt
    · rw [← hu']; simpa using hu
  · intro u hu
    simp only [coe_inter, Set.mem_inter_iff, mem_coe, firstSet, mem_filter, mem_univ, true_and,
      arrTime] at hu
    obtain ⟨hut, huR⟩ := hu
    simp only [coe_filter, posIco, mem_filter, mem_univ, true_and, Set.mem_setOf_eq,
      mem_image, Equiv.apply_symm_apply]
    refine ⟨⟨?_, ?_⟩, u, huR, rfl⟩
    · have h1 : σ.symm u ∈ posGe j := by simpa [posGe, arrTime] using hR u huR
      have := fixOutside_symm_apply_mem hρ h1
      simpa [posGe] using this
    · rw [mul_symm_apply] at hut; exact hut
  · intro p _; simp
  · intro u _; simp

/-- **Conditional upper tail.**  Condition on an event `A` determined by the first `j` arrivals,
and let `R σ` be a set of vertices determined by the first `j` arrivals, all arriving at time
`≥ j` on `A`.  Then the number of vertices of `R σ` among the first `t` arrivals exceeds any
threshold `θ σ ≥ (1+δ) μ` with conditional probability at most `exp(-δ²μ/(2+δ))`, where
`μ = |R σ| (t - j) / (n - j)`. -/
lemma prob_cond_upper (hH : HypergeomChernoff) {j t : ℕ} (hjt : j ≤ t) (ht : t ≤ n)
    (A : Equiv.Perm (Fin n) → Prop)
    (hA : ∀ σ ρ, ρ ∈ fixOutside (posGe j) → A σ → A (σ * ρ))
    (R : Equiv.Perm (Fin n) → Finset (Fin n))
    (hR : ∀ σ ρ, ρ ∈ fixOutside (posGe j) → A σ → R (σ * ρ) = R σ)
    (hRj : ∀ σ, A σ → ∀ u ∈ R σ, j ≤ arrTime σ u)
    (θ : Equiv.Perm (Fin n) → ℝ)
    (hθ : ∀ σ ρ, ρ ∈ fixOutside (posGe j) → A σ → θ (σ * ρ) = θ σ)
    (c : ℝ) (hc0 : 0 ≤ c)
    (hc : ∀ σ, A σ → (∃ δ : ℝ, 0 < δ ∧
      (1 + δ) * ((R σ).card * (t - j : ℝ) / (n - j)) ≤ θ σ ∧
      Real.exp (-(δ ^ 2 * ((R σ).card * (t - j : ℝ) / (n - j))) / (2 + δ)) ≤ c) ∨
      ((R σ).card * (t - j : ℝ) / (n - j) = 0 ∧ 0 < θ σ)) :
    prob (fun σ => A σ ∧ θ σ ≤ ((firstSet σ t ∩ R σ).card : ℝ)) ≤ c * prob A := by
  apply prob_and_le_of_orbit (posGe j) A hA
  intro σ hσ
  rcases hc σ hσ with ⟨δ, hδ, hθδ, hexp⟩ | ⟨hμ0, hθ0⟩
  swap
  · -- degenerate case: no vertex of `R σ` can arrive in `[j, t)`
    have hempty : (fixOutside (posGe j)).filter (fun ρ => θ (σ * ρ) ≤
        ((firstSet (σ * ρ) t ∩ R (σ * ρ)).card : ℝ)) = ∅ := by
      rw [filter_eq_empty_iff]
      intro ρ hρ h2
      rw [hθ σ ρ hρ hσ, hR σ ρ hρ hσ,
        card_firstSet_mul_inter σ ρ hρ (R σ) (hRj σ hσ)] at h2
      have hor : (R σ).card = 0 ∨ t = j := by
        rcases div_eq_zero_iff.1 hμ0 with h | h
        · rcases mul_eq_zero.1 h with h | h
          · left; exact_mod_cast h
          · right
            have : (t : ℝ) = j := by linarith
            exact_mod_cast this
        · right
          have : (n : ℝ) = j := by linarith
          have : n = j := by exact_mod_cast this
          omega
      have hzero : ((posIco j t).filter (fun p => ρ p ∈ (R σ).image σ.symm)).card = 0 := by
        rcases hor with h | h
        · have : R σ = ∅ := card_eq_zero.1 h
          simp [this]
        · subst h
          rw [card_eq_zero, filter_eq_empty_iff]
          intro p hp; simp [posIco] at hp; omega
      rw [hzero] at h2; simp at h2; linarith
    rw [hempty]; simp; positivity
  set Q := (R σ).image σ.symm with hQ
  have hQI : Q ⊆ posGe j := by
    intro p hp
    obtain ⟨u, hu, rfl⟩ := mem_image.1 hp
    simpa [posGe, arrTime] using hRj σ hσ u hu
  have hJI : posIco (n := n) j t ⊆ posGe j := by
    intro p hp; simp only [posIco, posGe, mem_filter, mem_univ, true_and] at hp ⊢; exact hp.1
  have hμ : (Q.card : ℝ) * (posIco (n := n) j t).card / (posGe (n := n) j).card =
      (R σ).card * (t - j : ℝ) / (n - j) := by
    rw [hQ, card_image_of_injective _ σ.symm.injective, card_posIco j t ht, card_posGe,
      Nat.cast_sub hjt, Nat.cast_sub (hjt.trans ht)]
  have hsub : (fixOutside (posGe j)).filter (fun ρ => θ (σ * ρ) ≤
      ((firstSet (σ * ρ) t ∩ R (σ * ρ)).card : ℝ)) ⊆
      (fixOutside (posGe j)).filter (fun ρ => (1 + δ) * ((Q.card : ℝ) *
        (posIco (n := n) j t).card / (posGe (n := n) j).card) ≤
        (((posIco j t).filter (fun p => ρ p ∈ Q)).card : ℝ)) := by
    intro ρ hρ
    rw [mem_filter] at hρ ⊢
    refine ⟨hρ.1, ?_⟩
    have h2 := hρ.2
    rw [hθ σ ρ hρ.1 hσ, hR σ ρ hρ.1 hσ,
      card_firstSet_mul_inter σ ρ hρ.1 (R σ) (hRj σ hσ)] at h2
    rw [hμ]; linarith
  have hch := (hH n (posGe j) (posIco j t) Q hJI hQI).1 δ hδ
  calc _ ≤ (((fixOutside (posGe j)).filter (fun ρ => (1 + δ) * ((Q.card : ℝ) *
        (posIco (n := n) j t).card / (posGe (n := n) j).card) ≤
        (((posIco j t).filter (fun p => ρ p ∈ Q)).card : ℝ))).card : ℝ) := by
          exact_mod_cast card_le_card hsub
    _ ≤ _ := hch
    _ ≤ c * (fixOutside (posGe j)).card := by rw [hμ]; gcongr

/-- **Conditional lower tail**, the analogue of `prob_cond_upper` for the lower tail. -/
lemma prob_cond_lower (hH : HypergeomChernoff) {j t : ℕ} (hjt : j ≤ t) (ht : t ≤ n)
    (A : Equiv.Perm (Fin n) → Prop)
    (hA : ∀ σ ρ, ρ ∈ fixOutside (posGe j) → A σ → A (σ * ρ))
    (R : Equiv.Perm (Fin n) → Finset (Fin n))
    (hR : ∀ σ ρ, ρ ∈ fixOutside (posGe j) → A σ → R (σ * ρ) = R σ)
    (hRj : ∀ σ, A σ → ∀ u ∈ R σ, j ≤ arrTime σ u)
    (θ : Equiv.Perm (Fin n) → ℝ)
    (hθ : ∀ σ ρ, ρ ∈ fixOutside (posGe j) → A σ → θ (σ * ρ) = θ σ)
    (c : ℝ)
    (hc : ∀ σ, A σ → ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      θ σ ≤ (1 - δ) * ((R σ).card * (t - j : ℝ) / (n - j)) ∧
      Real.exp (-(δ ^ 2 * ((R σ).card * (t - j : ℝ) / (n - j))) / 2) ≤ c) :
    prob (fun σ => A σ ∧ ((firstSet σ t ∩ R σ).card : ℝ) ≤ θ σ) ≤ c * prob A := by
  apply prob_and_le_of_orbit (posGe j) A hA
  intro σ hσ
  obtain ⟨δ, hδ, hδ1, hθδ, hexp⟩ := hc σ hσ
  set Q := (R σ).image σ.symm with hQ
  have hQI : Q ⊆ posGe j := by
    intro p hp
    obtain ⟨u, hu, rfl⟩ := mem_image.1 hp
    simpa [posGe, arrTime] using hRj σ hσ u hu
  have hJI : posIco (n := n) j t ⊆ posGe j := by
    intro p hp; simp only [posIco, posGe, mem_filter, mem_univ, true_and] at hp ⊢; exact hp.1
  have hμ : (Q.card : ℝ) * (posIco (n := n) j t).card / (posGe (n := n) j).card =
      (R σ).card * (t - j : ℝ) / (n - j) := by
    rw [hQ, card_image_of_injective _ σ.symm.injective, card_posIco j t ht, card_posGe,
      Nat.cast_sub hjt, Nat.cast_sub (hjt.trans ht)]
  have hsub : (fixOutside (posGe j)).filter (fun ρ =>
      ((firstSet (σ * ρ) t ∩ R (σ * ρ)).card : ℝ) ≤ θ (σ * ρ)) ⊆
      (fixOutside (posGe j)).filter (fun ρ =>
        (((posIco j t).filter (fun p => ρ p ∈ Q)).card : ℝ) ≤ (1 - δ) * ((Q.card : ℝ) *
        (posIco (n := n) j t).card / (posGe (n := n) j).card)) := by
    intro ρ hρ
    rw [mem_filter] at hρ ⊢
    refine ⟨hρ.1, ?_⟩
    have h2 := hρ.2
    rw [hθ σ ρ hρ.1 hσ, hR σ ρ hρ.1 hσ,
      card_firstSet_mul_inter σ ρ hρ.1 (R σ) (hRj σ hσ)] at h2
    rw [hμ]; linarith
  have hch := (hH n (posGe j) (posIco j t) Q hJI hQI).2 δ hδ hδ1
  calc _ ≤ (((fixOutside (posGe j)).filter (fun ρ =>
        (((posIco j t).filter (fun p => ρ p ∈ Q)).card : ℝ) ≤ (1 - δ) * ((Q.card : ℝ) *
        (posIco (n := n) j t).card / (posGe (n := n) j).card))).card : ℝ) := by
          exact_mod_cast card_le_card hsub
    _ ≤ _ := hch
    _ ≤ c * (fixOutside (posGe j)).card := by rw [hμ]; gcongr

end CCK
