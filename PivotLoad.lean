module

public import RequestProject.CondChernoff

/-!
# Pivot cluster sizes along the arrival process (Section 7.3.2)

For a pivot `v` we write `p_t(v)` for the number of vertices of its pivot cluster among the first
`t` arrivals (`pclAt`) and `p_n(v)` for its final size (`pclSize`).  Conditioned on the arrival
sequence up to the arrival of `v`, the pivot cluster of `v` is `{v} ∪ R_{t_v - 1}(v)` and the
remaining vertices arrive in uniformly random order; this is the structure used in the proofs of
Lemmas 7.5, 7.6 and 7.9.
-/

@[expose] public section

open Finset
open scoped Classical

namespace CCK

variable {n : ℕ} (G : SimpleGraph (Fin n))

/-- The size `p_t(v)` of the pivot cluster of `v` at time `t` (Section 7.3.2): the number of
vertices among the first `t` arrivals whose pivot is `v`. -/
noncomputable def pclAt (σ : Equiv.Perm (Fin n)) (v : Fin n) (t : ℕ) : ℕ :=
  (firstSet σ t ∩ univ.filter (fun u => pivotOf G σ u = v)).card

/-- The set `R_{t_v - 1}(v)` of neighbours of `v` uncovered when `v` arrives (in our
`0`-indexed convention, uncovered at time `arrTime σ v`). -/
noncomputable def uncNbrs (σ : Equiv.Perm (Fin n)) (v : Fin n) : Finset (Fin n) :=
  uncovered G σ (arrTime σ v) ∩ G.neighborFinset v

/-- For a pivot `v`, its pivot cluster without `v` is exactly `R_{t_v - 1}(v)`
(proof of Lemma 7.6: `p_n(v) = 1 + |R_{t_v-1}(v)|`). -/
lemma pivotCluster_erase_eq (σ : Equiv.Perm (Fin n)) {v : Fin n} (hv : IsPivot G σ v) :
    (univ.filter (fun u => pivotOf G σ u = v)).erase v = uncNbrs G σ v := by
  apply Subset.antisymm (pivotCluster_erase_subset G σ hv)
  intro u hu
  simp only [mem_inter, uncovered, mem_filter, mem_univ, true_and,
    SimpleGraph.mem_neighborFinset] at hu
  obtain ⟨⟨hge, hunc⟩, hadj⟩ := hu
  have hne : u ≠ v := fun h => G.loopless.irrefl _ (h ▸ hadj)
  have hlt : arrTime σ v < arrTime σ u := by
    rcases lt_or_eq_of_le hge with h | h
    · exact h
    · exact absurd (σ.symm.injective (Fin.ext h)).symm hne
  have hnp : ¬ IsPivot G σ u := by
    rw [isPivot_iff]
    push_neg
    exact ⟨v, (mem_pivotsUpTo_iff G σ _ v).2 ⟨hv, hlt⟩, hadj⟩
  obtain ⟨hp, hpadj, hmin⟩ := pivotOf_spec_of_not_isPivot G σ hnp
  have h1 := hmin v hv hadj
  have h2 : arrTime σ v ≤ arrTime σ (pivotOf G σ u) := by
    by_contra h
    push_neg at h
    exact hunc _ ((mem_pivotsUpTo_iff G σ _ _).2 ⟨hp, h⟩) hpadj
  have heq : arrTime σ (pivotOf G σ u) = arrTime σ v := le_antisymm h1 h2
  have : pivotOf G σ u = v := σ.symm.injective (Fin.ext heq)
  simp [hne, this]

/-- Auxiliary result for the pivot cluster size estimates of Section 7.3.2. -/
lemma mem_pivotCluster_self (σ : Equiv.Perm (Fin n)) {v : Fin n} (hv : IsPivot G σ v) :
    v ∈ univ.filter (fun u => pivotOf G σ u = v) := by
  simp [pivotOf_of_isPivot G σ hv]

/-- `p_n(v) = 1 + |R_{t_v-1}(v)|` for a pivot `v`. -/
lemma pclSize_eq (σ : Equiv.Perm (Fin n)) {v : Fin n} (hv : IsPivot G σ v) :
    pclSize G σ v = 1 + (uncNbrs G σ v).card := by
  rw [← pivotCluster_erase_eq G σ hv, card_erase_of_mem (mem_pivotCluster_self G σ hv), pclSize]
  have := card_pos.2 ⟨v, mem_pivotCluster_self G σ hv⟩
  omega

/-- `p_t(v) = 1 + |R_{t_v-1}(v) ∩ (first t arrivals)|` for a pivot `v` arrived before `t`. -/
lemma pclAt_eq (σ : Equiv.Perm (Fin n)) {v : Fin n} (hv : IsPivot G σ v) {t : ℕ}
    (ht : arrTime σ v < t) :
    pclAt G σ v t = 1 + (firstSet σ t ∩ uncNbrs G σ v).card := by
  rw [← pivotCluster_erase_eq G σ hv, pclAt]
  have hvm : v ∈ firstSet σ t ∩ univ.filter (fun u => pivotOf G σ u = v) :=
    mem_inter.2 ⟨by simpa [firstSet] using ht, mem_pivotCluster_self G σ hv⟩
  rw [inter_erase, card_erase_of_mem hvm]
  have := card_pos.2 ⟨v, hvm⟩
  omega

/-- Auxiliary result for the pivot cluster size estimates of Section 7.3.2. -/
lemma pclAt_le_pclSize (σ : Equiv.Perm (Fin n)) (v : Fin n) (t : ℕ) :
    pclAt G σ v t ≤ pclSize G σ v :=
  card_le_card inter_subset_right

/-- The vertices of `R_{t_v-1}(v)` arrive after `v`. -/
lemma lt_arrTime_of_mem_uncNbrs (σ : Equiv.Perm (Fin n)) {v u : Fin n}
    (hu : u ∈ uncNbrs G σ v) : arrTime σ v < arrTime σ u := by
  simp only [uncNbrs, mem_inter, uncovered, mem_filter, mem_univ, true_and,
    SimpleGraph.mem_neighborFinset] at hu
  obtain ⟨⟨hge, -⟩, hadj⟩ := hu
  have hne : u ≠ v := fun h => G.loopless.irrefl _ (h ▸ hadj)
  rcases lt_or_eq_of_le hge with h | h
  · exact h
  · exact absurd (σ.symm.injective (Fin.ext h)).symm hne

section invariance

variable {G}

/-- Auxiliary result for the pivot cluster size estimates of Section 7.3.2. -/
lemma fixOutside_posGe_lt {j : ℕ} {ρ : Equiv.Perm (Fin n)} (hρ : ρ ∈ fixOutside (posGe j)) :
    ∀ p : Fin n, (p : ℕ) < j → ρ p = p := by
  intro p hp
  apply fixOutside_mem_iff.1 hρ
  simp [posGe]; omega

/-- The arrival time of a vertex arriving among the first `j` is unchanged by re-shuffling the
positions `≥ j`. -/
lemma arrTime_mul_of_lt {j : ℕ} {σ ρ : Equiv.Perm (Fin n)} (hρ : ρ ∈ fixOutside (posGe j))
    {v : Fin n} (hv : arrTime σ v < j) : arrTime (σ * ρ) v = arrTime σ v := by
  unfold arrTime at *
  rw [mul_symm_apply]
  have := fixOutside_posGe_lt hρ (σ.symm v) hv
  rw [(Equiv.symm_apply_eq ρ).2 this.symm]

/-- The event "`v` arrives at time `j` and is a pivot" only depends on the first `j + 1`
arrivals. -/
lemma pivotEvent_mul {j : ℕ} {σ ρ : Equiv.Perm (Fin n)} (hρ : ρ ∈ fixOutside (posGe (j + 1)))
    {v : Fin n} (h : arrTime σ v = j ∧ IsPivot G σ v) :
    arrTime (σ * ρ) v = j ∧ IsPivot G (σ * ρ) v := by
  have ha : arrTime (σ * ρ) v = j := by
    rw [arrTime_mul_of_lt hρ (by omega)]; exact h.1
  refine ⟨ha, ?_⟩
  rw [isPivot_iff, ha, pivotsUpTo_mul (fun p hp => fixOutside_posGe_lt hρ p (by omega)),
    ← h.1, ← isPivot_iff]
  exact h.2

/-- On the event "`v` arrives at time `j` and is a pivot", `R_{t_v-1}(v)` only depends on the
first `j + 1` arrivals. -/
lemma uncNbrs_mul {j : ℕ} {σ ρ : Equiv.Perm (Fin n)} (hρ : ρ ∈ fixOutside (posGe (j + 1)))
    {v : Fin n} (h : arrTime σ v = j) : uncNbrs G (σ * ρ) v = uncNbrs G σ v := by
  have ha : arrTime (σ * ρ) v = j := by
    rw [arrTime_mul_of_lt hρ (by omega)]; exact h
  simp only [uncNbrs, ha, h]
  rw [uncovered_mul (fun p hp => fixOutside_posGe_lt hρ p (by omega))]

/-- Auxiliary result for the pivot cluster size estimates of Section 7.3.2. -/
lemma pclSize_mul {j : ℕ} {σ ρ : Equiv.Perm (Fin n)} (hρ : ρ ∈ fixOutside (posGe (j + 1)))
    {v : Fin n} (h : arrTime σ v = j ∧ IsPivot G σ v) : pclSize G (σ * ρ) v = pclSize G σ v := by
  rw [pclSize_eq G _ (pivotEvent_mul hρ h).2, pclSize_eq G _ h.2, uncNbrs_mul hρ h.1]

end invariance

end CCK
