module

public import RequestProject.Exchange
public import RequestProject.ProbTools

/-!
# Sequential arrival arguments

The proofs of Lemma 7.6 and Lemma 7.11 bound the probability of an event `B_t` along the arrival
process by chaining the one-step estimates `Pr[B_{t+1}] ≤ (1 - κ/(n-t)) Pr[B_t]`: conditioned on
the first `t` arrivals (and possibly on the positions of some fixed later arrivals), the next
arrival is a uniformly random one among the remaining vertices.  This file makes this rigorous
via the exchangeability lemma `exchange_count`.
-/

@[expose] public section

open Finset
open scoped Classical

namespace CCK

variable {n : ℕ}

/-- The positions `≥ t` outside the set `E` of excluded positions. -/
noncomputable def Ipos (t : ℕ) (E : Finset (Fin n)) : Finset (Fin n) :=
  univ.filter (fun p : Fin n => t ≤ (p : ℕ) ∧ p ∉ E)

/-- Auxiliary result for the sequential random-arrival arguments of Sections 6 and 7. -/
lemma card_Ipos_le (t : ℕ) (E : Finset (Fin n)) : (Ipos t E).card ≤ n - t := by
  have h : ∀ p ∈ Ipos t E, (p : ℕ) ∈ Ico t n := by
    intro p hp
    have hp' := mem_filter.1 hp
    exact mem_Ico.2 ⟨hp'.2.1, p.2⟩
  have := card_le_card_of_injOn (fun p : Fin n => (p : ℕ)) (s := Ipos t E) (t := Ico t n)
    (fun p hp => mem_coe.2 (h p (mem_coe.1 hp))) (fun p _ q _ h => Fin.ext h)
  simpa using this

/-- **One step of the arrival process.**  Let `A` be an event and `Bad σ` a set of vertices, both
invariant under re-shuffling the positions `Ipos t E` (i.e. determined by the first `t` arrivals
and the arrivals at the excluded positions `E`), such that on `A` the vertices of `Bad σ` occupy
positions in `Ipos t E` and `x |Ipos t E| ≤ |Bad σ|`.  Then the probability that `A` holds and the
vertex arriving at time `t` is not bad is at most `exp(-x) Pr[A]`. -/
lemma prob_step {t : ℕ} (ht : t < n) (E : Finset (Fin n)) (htE : (⟨t, ht⟩ : Fin n) ∉ E)
    (A : Equiv.Perm (Fin n) → Prop)
    (hA : ∀ σ ρ, ρ ∈ fixOutside (Ipos t E) → A σ → A (σ * ρ))
    (Bad : Equiv.Perm (Fin n) → Finset (Fin n))
    (hBad : ∀ σ ρ, ρ ∈ fixOutside (Ipos t E) → A σ → Bad (σ * ρ) = Bad σ)
    (hBadI : ∀ σ, A σ → ∀ v ∈ Bad σ, σ.symm v ∈ Ipos t E)
    (x : ℝ) (hx : ∀ σ, A σ → x * (Ipos t E).card ≤ (Bad σ).card) :
    prob (fun σ => A σ ∧ σ ⟨t, ht⟩ ∉ Bad σ) ≤ Real.exp (-x) * prob A := by
  set I := Ipos t E with hI
  have hp₀ : (⟨t, ht⟩ : Fin n) ∈ I := by simp [hI, Ipos, htE]
  have hIpos : (0 : ℝ) < I.card := by exact_mod_cast card_pos.2 ⟨_, hp₀⟩
  set S := univ.filter A with hS
  have key := exchange_count S (fun _ => I) (fun σ => σ ⟨t, ht⟩ ∈ Bad σ) x
    (by
      intro σ hσ ρ hρ
      exact ⟨by simp only [hS, mem_filter, mem_univ, true_and] at hσ ⊢; exact hA σ ρ hρ hσ, rfl⟩)
    (by
      intro σ hσ
      have hσ' : A σ := by simpa [hS] using hσ
      set Q := (Bad σ).image σ.symm with hQ
      have hQI : Q ⊆ I := by
        intro p hp
        obtain ⟨v, hv, rfl⟩ := mem_image.1 hp
        exact hBadI σ hσ' v hv
      have hcount := card_fixOutside_point I hp₀ Q hQI
      have hfilt : (fixOutside I).filter (fun ρ => (σ * ρ) ⟨t, ht⟩ ∈ Bad (σ * ρ)) =
          (fixOutside I).filter (fun ρ => ρ ⟨t, ht⟩ ∈ Q) := by
        apply filter_congr
        intro ρ hρ
        rw [hBad σ ρ hρ hσ', Equiv.Perm.mul_apply, hQ, mem_image]
        constructor
        · intro h; exact ⟨_, h, by simp⟩
        · rintro ⟨v, hv, hvρ⟩; rw [← hvρ]; simpa using hv
      rw [hfilt]
      have hQcard : Q.card = (Bad σ).card := card_image_of_injective _ σ.symm.injective
      have hc : (((fixOutside I).filter (fun ρ => ρ ⟨t, ht⟩ ∈ Q)).card : ℝ) * I.card =
          Q.card * (fixOutside I).card := by exact_mod_cast hcount
      rw [hQcard] at hc
      have hxI := hx σ hσ'
      have hF : (0 : ℝ) ≤ (fixOutside I).card := by positivity
      have : x * (fixOutside I).card * I.card ≤
          (((fixOutside I).filter (fun ρ => ρ ⟨t, ht⟩ ∈ Q)).card : ℝ) * I.card := by
        rw [hc]; nlinarith
      exact le_of_mul_le_mul_right this hIpos)
  -- conclude
  have hsplit : (S.filter (fun σ => ¬ σ ⟨t, ht⟩ ∈ Bad σ)).card =
      S.card - (S.filter (fun σ => σ ⟨t, ht⟩ ∈ Bad σ)).card := by
    rw [← card_filter_add_card_filter_not (s := S) (fun σ => σ ⟨t, ht⟩ ∈ Bad σ)]
    omega
  have hle : (S.filter (fun σ => σ ⟨t, ht⟩ ∈ Bad σ)).card ≤ S.card := card_filter_le _ _
  have hprob : prob (fun σ => A σ ∧ σ ⟨t, ht⟩ ∉ Bad σ) =
      ((S.filter (fun σ => ¬ σ ⟨t, ht⟩ ∈ Bad σ)).card : ℝ) /
        Fintype.card (Equiv.Perm (Fin n)) := by
    unfold prob; rw [hS, filter_filter]
  have hA' : prob A = (S.card : ℝ) / Fintype.card (Equiv.Perm (Fin n)) := rfl
  rw [hprob, hA', hsplit, Nat.cast_sub hle, ← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ card_perm_pos.le
  have h1 : (S.card : ℝ) - (S.filter (fun σ => σ ⟨t, ht⟩ ∈ Bad σ)).card ≤ (1 - x) * S.card := by
    linarith
  have h2 : 1 - x ≤ Real.exp (-x) := by linarith [Real.add_one_le_exp (-x)]
  nlinarith [(Nat.cast_nonneg S.card : (0 : ℝ) ≤ S.card)]

end CCK
