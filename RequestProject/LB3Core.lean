module

public import RequestProject.LBInstance
public import RequestProject.LBFail


/-!
# Combinatorial core of Theorem 3 (algorithms which never split cliques)

If at time `tstar` at least four positions are isolated (the two singletons and at least two
first vertices of cliques), then any online algorithm which never splits the cliques of the
/-- Auxiliary instance for the proof of Theorem 3. -/
instance puts two different cliques into a common cluster with probability at least `1/6`
(proof of Theorem 3 in the paper), paying at least `m²`.
-/

@[expose] public section

open Finset
open scoped Classical

namespace CCK

variable {c m : ℕ}

/-- The event `E''`: both singletons are isolated at `tstar` and there are at least four isolated
positions. -/
def lbEvent'' (c m : ℕ) (σ : Equiv.Perm (Fin (c * m + 2))) : Prop :=
  σ.symm (lbS1 c m) ∈ isoSet (lbGraph c m) (c + 2) σ ∧
    σ.symm (lbS2 c m) ∈ isoSet (lbGraph c m) (c + 2) σ ∧
    4 ≤ (isoSet (lbGraph c m) (c + 2) σ).card

/-- Auxiliary result for the proof of Theorem 3. -/
lemma lt_of_lbComp_lt {v : Fin (c * m + 2)} (hv : lbComp c m v < c) : (v : ℕ) < c * m := by
  by_contra h
  simp only [lbComp, h, if_false] at hv
  omega

/-- For each order in `E''`, at least a sixth of the re-shufflings of the isolated vertices make a
clique-preserving algorithm pay at least `m²`. -/
lemma sixth_bad (hm : 1 ≤ m) (A : OnlineAlg (c * m + 2) (c + 1))
    (hpres : ∀ τ, CliquePreserving (lbComp c m) (A.run (lbGraph c m) τ))
    (σ : Equiv.Perm (Fin (c * m + 2))) (hE : lbEvent'' c m σ) :
    (1 / 6 : ℝ) * (fixOutside (isoSet (lbGraph c m) (c + 2) σ)).card ≤
      ((fixOutside (isoSet (lbGraph c m) (c + 2) σ)).filter
        (fun ρ => m * m ≤ cost (lbGraph c m) (A.run (lbGraph c m) (σ * ρ)))).card := by
  set G := lbGraph c m
  set I := isoSet G (c + 2) σ
  set H := fixOutside I
  set a := σ.symm (lbS1 c m)
  set b := σ.symm (lbS2 c m)
  have hab : a ≠ b := fun h => lbS1_ne_lbS2 (σ.symm.injective h)
  obtain ⟨p, q, hpq, hp, hq, hcomp, hdpq⟩ := exists_collision hm A σ
  set B := (I \ {p, q}).offDiag
  have hBsub : B ⊆ I.offDiag := offDiag_mono sdiff_subset
  have hpair := card_fixOutside_pair I hE.1 hE.2.1 hab B hBsub
  have hsub : H.filter (fun ρ => (ρ.symm a, ρ.symm b) ∈ B) ⊆
      H.filter (fun ρ => m * m ≤ cost G (A.run G (σ * ρ))) := by
    intro ρ hρ
    simp only [mem_filter] at hρ ⊢
    obtain ⟨hρH, hxy⟩ := hρ
    refine ⟨hρH, ?_⟩
    set τ := σ * ρ
    simp only [B, mem_offDiag, mem_sdiff, mem_insert, mem_singleton, not_or] at hxy
    have hts : tstar G (c + 2) τ = tstar G (c + 2) σ :=
      tstar_mul_fixOutside G (c + 2) σ ρ hρH (exists_leaders_lb hm σ)
    have hIτ : isoSet G (c + 2) τ = I :=
      isoSet_mul_fixOutside G (c + 2) σ ρ hρH (exists_leaders_lb hm σ)
    -- the collision persists in `τ`
    have hdτ : A.run G τ (τ p) = A.run G τ (τ q) := by
      show A.dec G τ (τ.symm (τ p)) = A.dec G τ (τ.symm (τ q))
      rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply,
        dec_mul_fixOutside A G (c + 2) σ ρ hρH hp, dec_mul_fixOutside A G (c + 2) σ ρ hρH hq]
      exact hdpq
    have hcτ : lbComp c m (τ p) ≠ lbComp c m (τ q) := by
      by_cases hpI : p ∈ I
      · rw [← hIτ, mem_isoSet_iff] at hpI
        exact fun h => hpI.2 q (hts ▸ hq) (Ne.symm hpq) h.symm
      by_cases hqI : q ∈ I
      · rw [← hIτ, mem_isoSet_iff] at hqI
        exact fun h => hqI.2 p (hts ▸ hp) hpq h
      · have e1 : τ p = σ p := by
          show σ (ρ p) = σ p; rw [(fixOutside_mem_iff.1 hρH) p hpI]
        have e2 : τ q = σ q := by
          show σ (ρ q) = σ q; rw [(fixOutside_mem_iff.1 hρH) q hqI]
        rw [e1, e2]; exact hcomp
    -- neither `τ p` nor `τ q` is a singleton
    have hτx : τ.symm (lbS1 c m) = ρ.symm a := symm_mul_apply σ ρ _
    have hτy : τ.symm (lbS2 c m) = ρ.symm b := symm_mul_apply σ ρ _
    have hclique : ∀ r : Fin (c * m + 2), r ≠ ρ.symm a → r ≠ ρ.symm b →
        ((τ r : Fin (c * m + 2)) : ℕ) < c * m := by
      intro r hra hrb
      apply lt_of_lbComp_lt
      by_contra hc
      push_neg at hc
      rcases eq_s1_or_s2 hm hc with h | h
      · apply hra; rw [← hτx, ← h, Equiv.symm_apply_apply]
      · apply hrb; rw [← hτy, ← h, Equiv.symm_apply_apply]
    have hpc := hclique p (fun h => hxy.1.2.1 (h ▸ rfl)) (fun h => hxy.2.1.2.1 (h ▸ rfl))
    have hqc := hclique q (fun h => hxy.1.2.2 (h ▸ rfl)) (fun h => hxy.2.1.2.2 (h ▸ rfl))
    have h1 := card_mul_card_le_cost_of_mix (lbComp c m) (A.run G τ) (hpres τ) hdτ hcτ
    have h2 := le_card_comp hm hpc
    have h3 := le_card_comp hm hqc
    calc m * m ≤ _ := Nat.mul_le_mul h2 h3
      _ ≤ _ := h1
  -- counting
  have hj := hE.2.2
  set j := I.card
  set s := (I \ {p, q}).card
  have hs1 : j - 2 ≤ s := by
    have := le_card_sdiff {p, q} I
    have h2 : ({p, q} : Finset (Fin (c * m + 2))).card ≤ 2 := card_le_two
    omega
  have hs2 : s ≤ j := card_le_card sdiff_subset
  have hBc : B.card = s * s - s := offDiag_card _
  have hOc : I.offDiag.card = j * j - j := offDiag_card I
  have hFc := card_le_card hsub
  have hO : (I.offDiag.card : ℝ) = (j : ℝ) * j - j := by
    rw [hOc, Nat.cast_sub (Nat.le_mul_self j)]; push_cast; ring
  have hB : (B.card : ℝ) = (s : ℝ) * s - s := by
    rw [hBc, Nat.cast_sub (Nat.le_mul_self s)]; push_cast; ring
  have hpair' : ((H.filter (fun ρ => (ρ.symm a, ρ.symm b) ∈ B)).card : ℝ) *
      I.offDiag.card = B.card * H.card := by exact_mod_cast hpair
  have hj' : (4 : ℝ) ≤ j := by exact_mod_cast hj
  have hs1' : (j : ℝ) - 2 ≤ s := by
    have : ((j - 2 : ℕ) : ℝ) ≤ s := by exact_mod_cast hs1
    rw [Nat.cast_sub (by omega)] at this; exact_mod_cast this
  have hF' : ((H.filter (fun ρ => (ρ.symm a, ρ.symm b) ∈ B)).card : ℝ) ≤
      (H.filter (fun ρ => m * m ≤ cost G (A.run G (σ * ρ)))).card := by exact_mod_cast hFc
  have hHpos : (0 : ℝ) ≤ H.card := Nat.cast_nonneg _
  have hOpos : (0 : ℝ) < I.offDiag.card := by rw [hO]; nlinarith
  have hBO : (1 / 6 : ℝ) * I.offDiag.card ≤ B.card := by
    rw [hO, hB]
    have h1 : ((j : ℝ) - 2) * ((j : ℝ) - 3) ≤ (s : ℝ) * s - s := by nlinarith
    nlinarith
  have key : (1 / 6 : ℝ) * H.card * I.offDiag.card ≤
      ((H.filter (fun ρ => (ρ.symm a, ρ.symm b) ∈ B)).card : ℝ) * I.offDiag.card := by
    rw [hpair']; nlinarith
  have := le_of_mul_le_mul_right key hOpos
  linarith

/-- **Combinatorial core of Theorem 3.**  For every deterministic online algorithm which never
splits the cliques of the instance, the expected cost is at least `m² · P(E'') / 6`. -/
theorem lb3_expCost (hm : 1 ≤ m) (A : OnlineAlg (c * m + 2) (c + 1))
    (hpres : ∀ τ, CliquePreserving (lbComp c m) (A.run (lbGraph c m) τ)) :
    ((m : ℝ) * m) * prob (lbEvent'' c m) / 6 ≤ A.expCost (lbGraph c m) := by
  set G := lbGraph c m
  set S := (univ : Finset (Equiv.Perm (Fin (c * m + 2)))).filter (lbEvent'' c m)
  have hex := exchange_count S (isoSet G (c + 2))
    (fun τ => m * m ≤ cost G (A.run G τ)) (1 / 6)
    (by
      intro σ hσ ρ hρ
      have hE := (mem_filter.1 hσ).2
      have hI := isoSet_mul_fixOutside G (c + 2) σ ρ hρ (exists_leaders_lb hm σ)
      refine ⟨?_, hI⟩
      simp only [S, mem_filter, mem_univ, true_and, lbEvent'', symm_mul_apply]
      rw [show isoSet (lbGraph c m) (c + 2) (σ * ρ) = isoSet (lbGraph c m) (c + 2) σ from hI]
      exact ⟨fixOutside_symm_apply_mem hρ hE.1, fixOutside_symm_apply_mem hρ hE.2.1, hE.2.2⟩)
    (fun σ hσ => sixth_bad hm A hpres σ (mem_filter.1 hσ).2)
  have hcardpos := card_perm_pos (n := c * m + 2)
  have h2 : ((S.filter (fun τ => m * m ≤ cost G (A.run G τ))).card : ℝ) ≤
      ((univ.filter (fun τ => m * m ≤ cost G (A.run G τ))).card : ℝ) := by
    exact_mod_cast card_le_card (filter_subset_filter _ (subset_univ _))
  have h3 := expect_ge_of_event (fun σ => (cost G (A.run G σ) : ℝ))
    (fun τ => m * m ≤ cost G (A.run G τ)) ((m : ℝ) * m) (fun σ => Nat.cast_nonneg _)
    (fun σ hσ => by simp only at hσ ⊢; exact_mod_cast hσ)
  unfold OnlineAlg.expCost
  unfold prob at h3
  have hm0 : (0 : ℝ) ≤ (m : ℝ) * m := by positivity
  have : prob (lbEvent'' c m) / 6 ≤
      ((univ.filter (fun τ => m * m ≤ cost G (A.run G τ))).card : ℝ) /
        Fintype.card (Equiv.Perm (Fin (c * m + 2))) := by
    unfold prob
    rw [div_div, div_le_div_iff₀ (by positivity) hcardpos]
    have : (S.card : ℝ) = ((univ.filter (lbEvent'' c m)).card : ℝ) := rfl
    nlinarith
  calc ((m : ℝ) * m) * prob (lbEvent'' c m) / 6 = (m * m) * (prob (lbEvent'' c m) / 6) := by
        ring
    _ ≤ _ := mul_le_mul_of_nonneg_left this hm0
    _ ≤ _ := h3

end CCK
