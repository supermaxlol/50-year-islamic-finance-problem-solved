import Mathlib

/-!
Stage 246 (draft): Second Welfare Theorem from PREFERENCES (econ-wrapper for ③).

Builds the aggregate strictly-preferred set `B = {∑ x_h | ∀h, U_h(x_h) > U_h(c*_h)}` from
continuous convex preferences, shows it is convex, open, nonempty with the efficient
aggregate `Ω = ∑ c*_h ∉ B` (Pareto efficiency), and applies the separating-price core
(`separating_price`, stage 244 — re-proved locally here to keep the file self-contained) to
obtain supporting prices. Closes the SWT at the level of primitives.
-/

noncomputable section
open scoped BigOperators

namespace SecondWelfareWrapper

/-- Stage-244 `exists_price_repr`, local copy. -/
theorem exists_price_repr {S : Type*} [Fintype S] (f : (S → ℝ) →L[ℝ] ℝ) :
    ∃ p : S → ℝ, ∀ x : S → ℝ, f x = ∑ s, p s * x s := by
  classical
  refine ⟨fun s => f (Pi.single s 1), fun x => ?_⟩
  have hx : x = ∑ s, x s • Pi.single s (1 : ℝ) := by
    funext j; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hx]
  rw [map_sum]
  exact Finset.sum_congr rfl (fun s _ => by rw [map_smul, smul_eq_mul]; ring)

/-- Stage-244 `separating_price`, local copy. -/
theorem separating_price {S : Type*} [Fintype S] (B : Set (S → ℝ)) (hBconv : Convex ℝ B)
    (hBopen : IsOpen B) (hBne : B.Nonempty) (Ω : S → ℝ) (hΩ : Ω ∉ B) :
    ∃ p : S → ℝ, (∃ s, p s ≠ 0) ∧ ∀ b ∈ B, ∑ s, p s * Ω s ≤ ∑ s, p s * b s := by
  classical
  obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hBconv hBopen hΩ
  obtain ⟨p0, hp0⟩ := exists_price_repr f
  have hpx : ∀ x : S → ℝ, ∑ s, (- p0 s) * x s = - f x := by
    intro x; rw [hp0 x, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun s _ => by ring)
  refine ⟨fun s => - p0 s, ?_, ?_⟩
  · by_contra hall
    push Not at hall
    obtain ⟨a, ha⟩ := hBne
    have hfa : f a = 0 := by
      have h0 : ∑ s, (- p0 s) * a s = 0 :=
        Finset.sum_eq_zero (fun s _ => by rw [hall s, zero_mul])
      rw [hpx a] at h0; linarith
    have hfΩ : f Ω = 0 := by
      have h0 : ∑ s, (- p0 s) * Ω s = 0 :=
        Finset.sum_eq_zero (fun s _ => by rw [hall s, zero_mul])
      rw [hpx Ω] at h0; linarith
    have := hf a ha; rw [hfa, hfΩ] at this; exact lt_irrefl 0 this
  · intro b hb
    rw [hpx Ω, hpx b]; have := hf b hb; linarith

variable {H S : Type*} [Fintype H] [Fintype S] [Nonempty H]

/-- **Second Welfare Theorem (from preferences).** For continuous, convex preferences and a
Pareto-efficient allocation `c` (no profile strictly preferred by all with the same aggregate),
with local non-satiation, there is a nonzero price `p` under which the efficient aggregate
`∑ c_h` is cost-minimal over every strictly-preferred aggregate `∑ x_h`. -/
theorem second_welfare_from_preferences
    (U : H → (S → ℝ) → ℝ) (hUcont : ∀ h, Continuous (U h))
    (c : H → S → ℝ)
    (hPconv : ∀ h, Convex ℝ {x : S → ℝ | U h (c h) < U h x})
    (hLNS : ∀ h, ∃ y, U h (c h) < U h y)
    (heff : ¬ ∃ x : H → S → ℝ, (∀ h, U h (c h) < U h (x h)) ∧ ∑ h, x h = ∑ h, c h) :
    ∃ p : S → ℝ, (∃ s, p s ≠ 0) ∧
      ∀ x : H → S → ℝ, (∀ h, U h (c h) < U h (x h)) →
        ∑ s, p s * (∑ h, c h s) ≤ ∑ s, p s * (∑ h, x h s) := by
  classical
  set P : H → Set (S → ℝ) := fun h => {x | U h (c h) < U h x} with hP
  set B : Set (S → ℝ) := {b | ∃ x : H → (S → ℝ), (∀ h, x h ∈ P h) ∧ ∑ h, x h = b} with hB
  have hPopen : ∀ h, IsOpen (P h) := fun h => isOpen_lt continuous_const (hUcont h)
  -- B convex (convex preferences)
  have hBconv : Convex ℝ B := by
    rintro b1 ⟨x1, hx1, rfl⟩ b2 ⟨x2, hx2, rfl⟩ α β hα hβ hαβ
    refine ⟨fun h => α • x1 h + β • x2 h, fun h => hPconv h (hx1 h) (hx2 h) hα hβ hαβ, ?_⟩
    rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
  -- B open (perturb one household's bundle)
  have hBopen : IsOpen B := by
    rw [isOpen_iff_forall_mem_open]
    intro b hb
    obtain ⟨x, hxP, hxsum⟩ := hb
    obtain ⟨h0⟩ := (inferInstance : Nonempty H)
    have hcont : Continuous (fun b' : S → ℝ => x h0 + (b' - b)) :=
      continuous_const.add (continuous_id.sub continuous_const)
    refine ⟨(fun b' => x h0 + (b' - b)) ⁻¹' P h0, ?_, (hPopen h0).preimage hcont, ?_⟩
    · intro b' hb'
      refine ⟨Function.update x h0 (x h0 + (b' - b)), fun h => ?_, ?_⟩
      · rcases eq_or_ne h h0 with rfl | hne
        · rw [Function.update_self]; exact hb'
        · rw [Function.update_of_ne hne]; exact hxP h
      · rw [Finset.sum_update_of_mem (Finset.mem_univ h0),
            Finset.sum_sdiff_eq_sub (Finset.subset_univ {h0}),
            Finset.sum_singleton, hxsum]
        abel
    · show x h0 + (b - b) ∈ P h0
      rw [sub_self, add_zero]; exact hxP h0
  -- B nonempty (local non-satiation)
  have hBne : B.Nonempty := by
    choose y hy using hLNS
    exact ⟨∑ h, y h, y, fun h => hy h, rfl⟩
  -- efficiency ⟹ Ω ∉ B
  have hΩB : (∑ h, c h) ∉ B := by
    rintro ⟨x, hxP, hxsum⟩
    exact heff ⟨x, fun h => hxP h, hxsum⟩
  -- separate
  obtain ⟨p, hp0, hpsep⟩ :=
    separating_price B hBconv hBopen hBne (∑ h, c h) hΩB
  refine ⟨p, hp0, fun x hx => ?_⟩
  have hmem : (∑ h, x h) ∈ B := ⟨x, fun h => hx h, rfl⟩
  have hsep := hpsep (∑ h, x h) hmem
  simpa only [Finset.sum_apply] using hsep

end SecondWelfareWrapper

#print axioms SecondWelfareWrapper.second_welfare_from_preferences
