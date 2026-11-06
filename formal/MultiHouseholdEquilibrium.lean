import GEOverlap

/-!
Stage 234 (draft): fully micro-founded multi-household competitive equilibrium.

`general_preferences_equilibrium` is single representative agent. This generalizes to
finitely many heterogeneous households, each with its own continuous strictly-concave
utility and positive endowment: every household's demand is DERIVED by utility
maximization (the accepted Berge demand-continuity engine), and a clearing price exists
at which all households simultaneously optimize within budget. Demand is constructed from
preferences, not assumed — the complete micro-foundation of competitive equilibrium.
-/

noncomputable section
open scoped BigOperators
open GEOverlap
open Set

namespace MultiHousehold

variable {S : Type*} [Fintype S] [Nonempty S]

/-- Per-household Berge demand: continuous, budget-feasible, utility-maximal at each price.
(The construction of `general_preferences_equilibrium`, packaged as a reusable demand.) -/
theorem utility_demand (M : ℝ) (hM : 0 ≤ M) (ω : S → ℝ) (hω : ∀ s, 0 < ω s)
    (U : (S → ℝ) → ℝ) (hUcont : Continuous U) (hUsc : StrictConcaveOn ℝ Set.univ U) :
    ∃ d : priceSimplex S → (S → ℝ), Continuous d ∧
      (∀ p : priceSimplex S, (∀ s, d p s ∈ Set.Icc (0:ℝ) M) ∧
        ∑ s, (p : S → ℝ) s * d p s ≤ ∑ s, (p : S → ℝ) s * ω s) ∧
      (∀ (p : priceSimplex S) (y : S → ℝ), (∀ s, y s ∈ Set.Icc (0:ℝ) M) →
        ∑ s, (p : S → ℝ) s * y s ≤ ∑ s, (p : S → ℝ) s * ω s → U y ≤ U (d p)) := by
  classical
  set box : Set (S → ℝ) := {c | ∀ s, c s ∈ Set.Icc (0:ℝ) M} with hbox_def
  set D : priceSimplex S → Set (S → ℝ) :=
    fun p => {c | (∀ s, c s ∈ Set.Icc (0:ℝ) M) ∧ ∑ s, (p : S → ℝ) s * c s ≤ ∑ s, (p : S → ℝ) s * ω s}
    with hD_def
  have hbox_compact : IsCompact box := by
    have hbx : IsCompact (Set.univ.pi fun _ : S => Set.Icc (0:ℝ) M) :=
      isCompact_univ_pi fun _ => isCompact_Icc
    apply hbx.of_isClosed_subset
    · have : box = ⋂ s, {c : S → ℝ | c s ∈ Set.Icc (0:ℝ) M} := by
        ext c; simp only [hbox_def, Set.mem_iInter, Set.mem_ofPred_eq]
      rw [this]; exact isClosed_iInter fun s => isClosed_Icc.preimage (continuous_apply s)
    · intro c hc; rw [Set.mem_univ_pi]; exact hc
  have hvalc : ∀ v : S → ℝ, Continuous (fun c : S → ℝ => ∑ s, v s * c s) :=
    fun v => continuous_finsetSum _ (fun s _ => continuous_const.mul (continuous_apply s))
  have hwpos : ∀ p : priceSimplex S, 0 < ∑ s, (p : S → ℝ) s * ω s := by
    intro p
    have hex : ∃ s₀, 0 < (p : S → ℝ) s₀ := by
      by_contra h; rw [not_exists] at h
      have hle : ∑ s, (p : S → ℝ) s ≤ 0 := Finset.sum_nonpos (fun s _ => not_lt.mp (h s))
      have : ∑ s, (p : S → ℝ) s = 1 := p.2.2
      linarith
    obtain ⟨s₀, hs₀⟩ := hex
    exact Finset.sum_pos' (fun s _ => mul_nonneg (p.2.1 s) (hω s).le)
      ⟨s₀, Finset.mem_univ s₀, mul_pos hs₀ (hω s₀)⟩
  have hDsub : ∀ p, D p ⊆ box := fun p c hc => hc.1
  have hDconvex : ∀ p : priceSimplex S, Convex ℝ (D p) := by
    intro p x hx y hy a b ha hb hab
    refine ⟨fun s => ?_, ?_⟩
    · rw [Set.mem_Icc]
      have hx' := Set.mem_Icc.mp (hx.1 s)
      have hy' := Set.mem_Icc.mp (hy.1 s)
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      refine ⟨by nlinarith [mul_nonneg ha hx'.1, mul_nonneg hb hy'.1], ?_⟩
      have h1 : a * x s ≤ a * M := mul_le_mul_of_nonneg_left hx'.2 ha
      have h2 : b * y s ≤ b * M := mul_le_mul_of_nonneg_left hy'.2 hb
      have h3 : a * M + b * M = M := by rw [← add_mul, hab, one_mul]
      linarith
    · have hcombo : ∑ s, (p : S → ℝ) s * (a • x + b • y) s
          = a * (∑ s, (p : S → ℝ) s * x s) + b * (∑ s, (p : S → ℝ) s * y s) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun s _ => ?_)
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
      rw [hcombo]
      have h1 := mul_le_mul_of_nonneg_left hx.2 ha
      have h2 := mul_le_mul_of_nonneg_left hy.2 hb
      have h3 : a * (∑ s, (p : S → ℝ) s * ω s) + b * (∑ s, (p : S → ℝ) s * ω s)
          = ∑ s, (p : S → ℝ) s * ω s := by rw [← add_mul, hab, one_mul]
      linarith
  have hexists : ∀ p : priceSimplex S, ∃ c, c ∈ D p ∧ ∀ y ∈ D p, U y ≤ U c := by
    intro p
    have hDcompact : IsCompact (D p) := by
      apply hbox_compact.of_isClosed_subset _ (hDsub p)
      have hbud : IsClosed {c : S → ℝ | ∑ s, (p : S → ℝ) s * c s ≤ ∑ s, (p : S → ℝ) s * ω s} :=
        isClosed_le (hvalc _) continuous_const
      have hset : D p = box ∩ {c | ∑ s, (p : S → ℝ) s * c s ≤ ∑ s, (p : S → ℝ) s * ω s} := by
        ext c; simp only [hD_def, hbox_def, Set.mem_inter_iff, Set.mem_ofPred_eq]
      rw [hset]; exact hbox_compact.isClosed.inter hbud
    have hDne : (D p).Nonempty := by
      refine ⟨0, ⟨fun s => ?_, ?_⟩⟩
      · rw [Set.mem_Icc]; exact ⟨le_refl 0, hM⟩
      · simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero]; exact (hwpos p).le
    obtain ⟨c, hc, hcmax⟩ := hDcompact.exists_isMaxOn hDne hUcont.continuousOn
    exact ⟨c, hc, fun y hy => hcmax hy⟩
  choose dem hdmem hdmax using hexists
  have hdcont : Continuous dem := by
    refine continuous_of_unique_maximizer_subset box hbox_compact D hDsub
      (fun _ c => U c) (hUcont.comp continuous_snd) dem hdmem
      (fun p y hy => hdmax p y hy) ?_ ?_ ?_
    · intro p x hx hxmax
      exact unique_max_of_strictConcaveOn
        (hUsc.subset (Set.subset_univ _) (hDconvex p))
        hx (hdmem p) hxmax (hdmax p)
    · have hbud : IsClosed {pc : priceSimplex S × (S → ℝ) |
          ∑ s, ((pc.1 : S → ℝ)) s * pc.2 s ≤ ∑ s, ((pc.1 : S → ℝ)) s * ω s} := by
        apply isClosed_le
        · exact continuous_finsetSum _ (fun s _ =>
            (((continuous_apply s).comp (continuous_subtype_val.comp continuous_fst)).mul
              ((continuous_apply s).comp continuous_snd)))
        · exact continuous_finsetSum _ (fun s _ =>
            ((continuous_apply s).comp (continuous_subtype_val.comp continuous_fst)).mul
              continuous_const)
      have hbx : IsClosed {pc : priceSimplex S × (S → ℝ) | pc.2 ∈ box} :=
        hbox_compact.isClosed.preimage continuous_snd
      have hset : {pc : priceSimplex S × (S → ℝ) | pc.2 ∈ D pc.1}
          = {pc | pc.2 ∈ box} ∩ {pc | ∑ s, ((pc.1 : S → ℝ)) s * pc.2 s
              ≤ ∑ s, ((pc.1 : S → ℝ)) s * ω s} := by
        ext pc; simp only [hD_def, hbox_def, Set.mem_inter_iff, Set.mem_ofPred_eq]
      rw [hset]; exact hbx.inter hbud
    · intro p pn hpn y hy
      exact budget_lower_hemicontinuous M ω (fun s => (hω s).le) p pn hpn (hwpos p) y hy.1 hy.2
  exact ⟨dem, hdcont, hdmem, fun p y hy hby => hdmax p y ⟨hy, hby⟩⟩

/-- **Fully micro-founded multi-household competitive equilibrium.** For finitely many
households, each with a continuous strictly-concave utility and a strictly positive
endowment, there is a clearing price at which every household's choice is its own
utility-maximizing, budget-feasible demand, and aggregate demand does not exceed aggregate
endowment in any good. Demand is derived from preferences via the Berge engine. -/
theorem multi_household_equilibrium {H : Type*} [Fintype H]
    (M : ℝ) (hM : 0 ≤ M) (ω : H → S → ℝ) (hω : ∀ h s, 0 < ω h s)
    (U : H → (S → ℝ) → ℝ) (hUcont : ∀ h, Continuous (U h))
    (hUsc : ∀ h, StrictConcaveOn ℝ Set.univ (U h)) :
    ∃ (p : priceSimplex S) (c : H → S → ℝ),
      (∀ h s, c h s ∈ Set.Icc (0:ℝ) M) ∧
      (∀ h, ∑ s, (p : S → ℝ) s * c h s ≤ ∑ s, (p : S → ℝ) s * ω h s) ∧
      (∀ h (y : S → ℝ), (∀ s, y s ∈ Set.Icc (0:ℝ) M) →
        ∑ s, (p : S → ℝ) s * y s ≤ ∑ s, (p : S → ℝ) s * ω h s → U h y ≤ U h (c h)) ∧
      (∀ s, (∑ h, c h s) ≤ ∑ h, ω h s) := by
  choose d hdcont hdfeas hdmax using
    fun h => utility_demand M hM (ω h) (hω h) (U h) (hUcont h) (hUsc h)
  set z : priceSimplex S → (S → ℝ) := fun p => fun s => (∑ h, d h p s) - (∑ h, ω h s) with hz_def
  have hzcont : Continuous z := by
    refine continuous_pi (fun s => ?_)
    exact (continuous_finsetSum _ (fun h _ => (continuous_apply s).comp (hdcont h))).sub
      continuous_const
  have hzwal : ∀ p : priceSimplex S, ∑ s, (p : S → ℝ) s * z p s ≤ 0 := by
    intro p
    have hrw : ∑ s, (p : S → ℝ) s * z p s
        = ∑ h, ((∑ s, (p : S → ℝ) s * d h p s) - (∑ s, (p : S → ℝ) s * ω h s)) := by
      simp only [hz_def]
      calc ∑ s, (p : S → ℝ) s * ((∑ h, d h p s) - (∑ h, ω h s))
          = ∑ s, ∑ h, ((p : S → ℝ) s * d h p s - (p : S → ℝ) s * ω h s) := by
            apply Finset.sum_congr rfl; intro s _
            rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
        _ = ∑ h, ∑ s, ((p : S → ℝ) s * d h p s - (p : S → ℝ) s * ω h s) := Finset.sum_comm
        _ = ∑ h, ((∑ s, (p : S → ℝ) s * d h p s) - (∑ s, (p : S → ℝ) s * ω h s)) := by
            apply Finset.sum_congr rfl; intro h _; rw [Finset.sum_sub_distrib]
    rw [hrw]
    exact Finset.sum_nonpos (fun h _ => by have := (hdfeas h p).2; linarith)
  obtain ⟨p, hp⟩ := gale_nikaido_debreu_weak z hzcont hzwal
  refine ⟨p, fun h => d h p, fun h s => (hdfeas h p).1 s, fun h => (hdfeas h p).2,
    fun h y hy hby => hdmax h p y hy hby, fun s => ?_⟩
  have hps := hp s
  simp only [hz_def] at hps
  linarith

/-- **Capstone: micro-founded competitive equilibrium WITH production/ownership.** A
production activity `y ≥ 0` (net output) is distributed to households by ownership shares
`θ` summing to one. With utility-maximizing demand (the Berge engine), a clearing price
exists at which every household optimizes over its **dividend-augmented** budget
`p·c_h ≤ p·(ω_h + θ_h·y)`, and aggregate demand does not exceed aggregate endowment **plus
production** in any good (`∑ c_h ≤ ∑ ω_h + y`). Fully from primitives: preferences,
endowments, a production activity, and ownership shares — demand derived, nothing assumed.
Boundary: `y` is a given owned activity; endogenizing it as a profit-maximizing choice
inside this fixed point (vs. the separate GND-level profit fixed point, stage 230) needs
budget l.h.c. at profit-augmented wealth — the next step. -/
theorem production_ownership_equilibrium {H : Type*} [Fintype H]
    (M : ℝ) (hM : 0 ≤ M) (ω : H → S → ℝ) (y : S → ℝ) (θ : H → ℝ)
    (hω : ∀ h s, 0 < ω h s) (hy : ∀ s, 0 ≤ y s) (hθ : ∀ h, 0 ≤ θ h) (hθsum : ∑ h, θ h = 1)
    (U : H → (S → ℝ) → ℝ) (hUcont : ∀ h, Continuous (U h))
    (hUsc : ∀ h, StrictConcaveOn ℝ Set.univ (U h)) :
    ∃ (p : priceSimplex S) (c : H → S → ℝ),
      (∀ h s, c h s ∈ Set.Icc (0:ℝ) M) ∧
      (∀ h, ∑ s, (p : S → ℝ) s * c h s ≤ ∑ s, (p : S → ℝ) s * (ω h s + θ h * y s)) ∧
      (∀ h (x : S → ℝ), (∀ s, x s ∈ Set.Icc (0:ℝ) M) →
        ∑ s, (p : S → ℝ) s * x s ≤ ∑ s, (p : S → ℝ) s * (ω h s + θ h * y s) →
        U h x ≤ U h (c h)) ∧
      (∀ s, (∑ h, c h s) ≤ (∑ h, ω h s) + y s) := by
  obtain ⟨p, c, hbox, hbud, hmax, hclear⟩ :=
    multi_household_equilibrium M hM (fun h s => ω h s + θ h * y s)
      (fun h s => by have h1 := hω h s; have h2 := mul_nonneg (hθ h) (hy s); linarith)
      U hUcont hUsc
  refine ⟨p, c, hbox, hbud, hmax, fun s => ?_⟩
  have hcl := hclear s
  have hrw : ∑ h, (ω h s + θ h * y s) = (∑ h, ω h s) + y s := by
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, hθsum, one_mul]
  rw [hrw] at hcl
  exact hcl

end MultiHousehold

#print axioms MultiHousehold.utility_demand
#print axioms MultiHousehold.multi_household_equilibrium
#print axioms MultiHousehold.production_ownership_equilibrium
