import GEOverlap

/-!
Keystone for the profit-max-firm production capstone: budget lower-hemicontinuity at a
general continuous positive wealth `W(p)` (not just endowment value `p·ω`). This is the one
lemma needed to let household demand respond to profit income `W(p) = p·ω + θ·π(p)`.
A faithful generalization of `GEOverlap.budget_lower_hemicontinuous` (same proof, `W` for
`∑ p·ω`).
-/

noncomputable section
open scoped BigOperators
open GEOverlap

namespace ProfitCapstone

theorem budget_lhc_general {S : Type*} [Fintype S]
    (M : ℝ) (W : priceSimplex S → ℝ) (hWcont : Continuous W) (hWnn : ∀ q, 0 ≤ W q)
    (p : priceSimplex S) (pn : ℕ → priceSimplex S)
    (hpn : Filter.Tendsto pn Filter.atTop (nhds p))
    (hWpos : 0 < W p)
    (c : S → ℝ) (hcbox : ∀ s, c s ∈ Set.Icc (0:ℝ) M)
    (hcbudget : ∑ s, (p : S → ℝ) s * c s ≤ W p) :
    ∃ cn : ℕ → (S → ℝ),
      (∀ n, (∀ s, cn n s ∈ Set.Icc (0:ℝ) M) ∧
        ∑ s, ((pn n : S → ℝ)) s * cn n s ≤ W (pn n)) ∧
      Filter.Tendsto cn Filter.atTop (nhds c) := by
  classical
  have hval : ∀ v : S → ℝ, Continuous (fun q : S → ℝ => ∑ s, q s * v s) :=
    fun v => continuous_finsetSum _ (fun s _ => (continuous_apply s).mul continuous_const)
  have hpval : Filter.Tendsto (fun n => ((pn n : S → ℝ))) Filter.atTop (nhds (p : S → ℝ)) :=
    (continuous_subtype_val.tendsto p).comp hpn
  set a : ℕ → ℝ := fun n => ∑ s, ((pn n : S → ℝ)) s * c s with ha_def
  set b : ℕ → ℝ := fun n => W (pn n) with hb_def
  have ha : Filter.Tendsto a Filter.atTop (nhds (∑ s, (p : S → ℝ) s * c s)) :=
    ((hval c).tendsto _).comp hpval
  have hb : Filter.Tendsto b Filter.atTop (nhds (W p)) := (hWcont.tendsto p).comp hpn
  have hbnn : ∀ n, 0 ≤ b n := fun n => hWnn (pn n)
  set A := ∑ s, (p : S → ℝ) s * c s
  set B := W p
  have hAB : A ≤ B := hcbudget
  set f : ℕ → ℝ := fun n => if a n ≤ b n then (1:ℝ) else b n / a n with hf_def
  have hf01 : ∀ n, f n ∈ Set.Icc (0:ℝ) 1 := by
    intro n; simp only [hf_def]; rw [Set.mem_Icc]
    split_ifs with h
    · exact ⟨zero_le_one, le_refl 1⟩
    · rw [not_le] at h
      have ha0 : 0 < a n := lt_of_le_of_lt (hbnn n) h
      exact ⟨div_nonneg (hbnn n) ha0.le, (div_le_one ha0).mpr h.le⟩
  have hfa : ∀ n, f n * a n ≤ b n := by
    intro n; simp only [hf_def]
    split_ifs with h
    · rw [one_mul]; exact h
    · rw [not_le] at h
      have ha0 : 0 < a n := lt_of_le_of_lt (hbnn n) h
      exact le_of_eq (div_mul_cancel₀ (b n) ha0.ne')
  have hA0le : 0 ≤ A := Finset.sum_nonneg (fun s _ => mul_nonneg (p.2.1 s) (hcbox s).1)
  have hf1 : Filter.Tendsto f Filter.atTop (nhds (1:ℝ)) := by
    rcases eq_or_lt_of_le hA0le with hA0 | hApos
    · have hev : ∀ᶠ n in Filter.atTop, f n = 1 := by
        have hdiff : Filter.Tendsto (fun n => b n - a n) Filter.atTop (nhds (B - A)) := hb.sub ha
        have hBA : (0:ℝ) < B - A := by rw [← hA0]; simpa using hWpos
        have hpos : ∀ᶠ n in Filter.atTop, 0 < b n - a n := hdiff.eventually (eventually_gt_nhds hBA)
        filter_upwards [hpos] with n hn
        simp only [hf_def]
        split_ifs with h
        · rfl
        · exact absurd (by linarith : a n ≤ b n) h
      exact (Filter.tendsto_congr' hev).mpr tendsto_const_nhds
    · have ha0ev : ∀ᶠ n in Filter.atTop, 0 < a n := ha.eventually (eventually_gt_nhds hApos)
      have hfeq : ∀ᶠ n in Filter.atTop, f n = min 1 (b n / a n) := by
        filter_upwards [ha0ev] with n hn
        simp only [hf_def]
        split_ifs with h
        · rw [eq_comm, min_eq_left_iff, le_div_iff₀ hn, one_mul]; exact h
        · rw [not_le] at h
          rw [eq_comm, min_eq_right_iff, div_le_one hn]; exact h.le
      have hdiv : Filter.Tendsto (fun n => b n / a n) Filter.atTop (nhds (B / A)) :=
        hb.div ha hApos.ne'
      have hmin : Filter.Tendsto (fun n => min 1 (b n / a n)) Filter.atTop (nhds (min 1 (B / A))) :=
        tendsto_const_nhds.min hdiv
      have hBA1 : min (1:ℝ) (B / A) = 1 := by
        rw [min_eq_left_iff, le_div_iff₀ hApos, one_mul]; exact hAB
      rw [hBA1] at hmin
      exact (Filter.tendsto_congr' hfeq).mpr hmin
  refine ⟨fun n => f n • c, fun n => ⟨fun s => ?_, ?_⟩, ?_⟩
  · show (f n • c) s ∈ Set.Icc (0:ℝ) M
    rw [Pi.smul_apply, smul_eq_mul, Set.mem_Icc]
    refine ⟨mul_nonneg (hf01 n).1 (hcbox s).1, ?_⟩
    calc f n * c s ≤ 1 * c s := mul_le_mul_of_nonneg_right (hf01 n).2 (hcbox s).1
      _ = c s := one_mul _
      _ ≤ M := (hcbox s).2
  · show ∑ s, ((pn n : S → ℝ)) s * (f n • c) s ≤ W (pn n)
    have hbudn : ∑ s, ((pn n : S → ℝ)) s * (f n • c) s = f n * a n := by
      simp only [ha_def, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun s _ => ?_)
      simp only [Pi.smul_apply, smul_eq_mul]; ring
    rw [hbudn]
    have : f n * a n ≤ b n := hfa n
    simpa [hb_def] using this
  · have htend : Filter.Tendsto (fun n => f n • c) Filter.atTop (nhds ((1:ℝ) • c)) :=
      hf1.smul_const c
    simpa using htend

/-- Household demand from utility maximization at wealth `W(p) = p·ω + I(p)` (endowment
value plus a continuous nonnegative income `I`, e.g. a profit share): continuous,
budget-feasible, utility-maximal. The `general_preferences` construction with general wealth,
using `budget_lhc_general` for lower-hemicontinuity. -/
theorem utility_demand_income {S : Type*} [Fintype S] [Nonempty S]
    (M : ℝ) (hM : 0 ≤ M) (ω : S → ℝ) (hω : ∀ s, 0 < ω s)
    (I : priceSimplex S → ℝ) (hIcont : Continuous I) (hInn : ∀ p, 0 ≤ I p)
    (U : (S → ℝ) → ℝ) (hUcont : Continuous U) (hUsc : StrictConcaveOn ℝ Set.univ U) :
    ∃ d : priceSimplex S → (S → ℝ), Continuous d ∧
      (∀ p : priceSimplex S, (∀ s, d p s ∈ Set.Icc (0:ℝ) M) ∧
        ∑ s, (p : S → ℝ) s * d p s ≤ (∑ s, (p : S → ℝ) s * ω s) + I p) ∧
      (∀ (p : priceSimplex S) (y : S → ℝ), (∀ s, y s ∈ Set.Icc (0:ℝ) M) →
        ∑ s, (p : S → ℝ) s * y s ≤ (∑ s, (p : S → ℝ) s * ω s) + I p → U y ≤ U (d p)) := by
  classical
  set W : priceSimplex S → ℝ := fun p => (∑ s, (p : S → ℝ) s * ω s) + I p with hW_def
  have hWcont : Continuous W := by
    refine Continuous.add ?_ hIcont
    exact continuous_finsetSum _ (fun s _ =>
      ((continuous_apply s).comp continuous_subtype_val).mul continuous_const)
  have hbase : ∀ p : priceSimplex S, 0 < ∑ s, (p : S → ℝ) s * ω s := by
    intro p
    have hex : ∃ s₀, 0 < (p : S → ℝ) s₀ := by
      by_contra h; rw [not_exists] at h
      have hle : ∑ s, (p : S → ℝ) s ≤ 0 := Finset.sum_nonpos (fun s _ => not_lt.mp (h s))
      have hone : ∑ s, (p : S → ℝ) s = 1 := p.2.2
      linarith
    obtain ⟨s₀, hs₀⟩ := hex
    exact Finset.sum_pos' (fun s _ => mul_nonneg (p.2.1 s) (hω s).le)
      ⟨s₀, Finset.mem_univ s₀, mul_pos hs₀ (hω s₀)⟩
  have hWnn : ∀ q : priceSimplex S, 0 ≤ W q :=
    fun q => add_nonneg (hbase q).le (hInn q)
  have hWpos : ∀ p : priceSimplex S, 0 < W p := by
    intro p; have := hInn p; have := hbase p; simp only [hW_def]; linarith
  set box : Set (S → ℝ) := {c | ∀ s, c s ∈ Set.Icc (0:ℝ) M} with hbox_def
  set D : priceSimplex S → Set (S → ℝ) :=
    fun p => {c | (∀ s, c s ∈ Set.Icc (0:ℝ) M) ∧ ∑ s, (p : S → ℝ) s * c s ≤ W p} with hD_def
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
      have h3 : a * W p + b * W p = W p := by rw [← add_mul, hab, one_mul]
      linarith
  have hexists : ∀ p : priceSimplex S, ∃ c, c ∈ D p ∧ ∀ y ∈ D p, U y ≤ U c := by
    intro p
    have hDcompact : IsCompact (D p) := by
      apply hbox_compact.of_isClosed_subset _ (hDsub p)
      have hbud : IsClosed {c : S → ℝ | ∑ s, (p : S → ℝ) s * c s ≤ W p} :=
        isClosed_le (hvalc _) continuous_const
      have hset : D p = box ∩ {c | ∑ s, (p : S → ℝ) s * c s ≤ W p} := by
        ext c; simp only [hD_def, hbox_def, Set.mem_inter_iff, Set.mem_ofPred_eq]
      rw [hset]; exact hbox_compact.isClosed.inter hbud
    have hDne : (D p).Nonempty := by
      refine ⟨0, ⟨fun s => ?_, ?_⟩⟩
      · rw [Set.mem_Icc]; exact ⟨le_refl 0, hM⟩
      · simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero]; exact (hWpos p).le
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
          ∑ s, ((pc.1 : S → ℝ)) s * pc.2 s ≤ W pc.1} := by
        apply isClosed_le
        · exact continuous_finsetSum _ (fun s _ =>
            (((continuous_apply s).comp (continuous_subtype_val.comp continuous_fst)).mul
              ((continuous_apply s).comp continuous_snd)))
        · exact hWcont.comp continuous_fst
      have hbx : IsClosed {pc : priceSimplex S × (S → ℝ) | pc.2 ∈ box} :=
        hbox_compact.isClosed.preimage continuous_snd
      have hset : {pc : priceSimplex S × (S → ℝ) | pc.2 ∈ D pc.1}
          = {pc | pc.2 ∈ box} ∩ {pc | ∑ s, ((pc.1 : S → ℝ)) s * pc.2 s ≤ W pc.1} := by
        ext pc; simp only [hD_def, hbox_def, Set.mem_inter_iff, Set.mem_ofPred_eq]
      rw [hset]; exact hbx.inter hbud
    · intro p pn hpn y hy
      exact budget_lhc_general M W hWcont hWnn p pn hpn (hWpos p) y hy.1 hy.2
  exact ⟨dem, hdcont, hdmem, fun p y hy hby => hdmax p y ⟨hy, hby⟩⟩

/-- **Profit-income production equilibrium with utility-maximizing demand.** Households'
demand is derived from utility maximization over **profit-augmented** budgets
`p·c_h ≤ p·ω_h + θ_h·(p·η(p))` (ownership share `θ_h` of the firm's profit `p·η(p)`), and a
clearing price exists with aggregate demand not exceeding endowment plus production in any
good (`∑ c_h ≤ ∑ ω_h + η`). This is the micro-founded production equilibrium where the firm's
profit flows to utility-maximizing owners and demand responds to it — the profit-income
closure of the capstone.
Boundary: the firm's net supply `η` is a given continuous function with nonnegative profit;
endogenizing `η` as a profit maximizer over a production set (a further Berge application)
is the remaining step. -/
theorem profit_income_equilibrium {H S : Type*} [Fintype H] [Fintype S] [Nonempty S]
    (M : ℝ) (hM : 0 ≤ M) (ω : H → S → ℝ) (θ : H → ℝ) (η : priceSimplex S → (S → ℝ))
    (hω : ∀ h s, 0 < ω h s) (hθ : ∀ h, 0 ≤ θ h) (hθsum : ∑ h, θ h = 1)
    (hηcont : Continuous η)
    (hprofit_nn : ∀ p : priceSimplex S, 0 ≤ ∑ s, (p : S → ℝ) s * η p s)
    (U : H → (S → ℝ) → ℝ) (hUcont : ∀ h, Continuous (U h))
    (hUsc : ∀ h, StrictConcaveOn ℝ Set.univ (U h)) :
    ∃ (p : priceSimplex S) (c : H → S → ℝ),
      (∀ h s, c h s ∈ Set.Icc (0:ℝ) M) ∧
      (∀ h, ∑ s, (p : S → ℝ) s * c h s ≤
        (∑ s, (p : S → ℝ) s * ω h s) + θ h * ∑ s, (p : S → ℝ) s * η p s) ∧
      (∀ (h : H) (x : S → ℝ), (∀ s, x s ∈ Set.Icc (0:ℝ) M) →
        ∑ s, (p : S → ℝ) s * x s ≤
          (∑ s, (p : S → ℝ) s * ω h s) + θ h * ∑ s, (p : S → ℝ) s * η p s →
        U h x ≤ U h (c h)) ∧
      (∀ s, (∑ h, c h s) ≤ (∑ h, ω h s) + η p s) := by
  choose d hdcont hdfeas hdmax using fun h =>
    utility_demand_income M hM (ω h) (hω h)
      (fun p => θ h * ∑ s, (p : S → ℝ) s * η p s)
      (continuous_const.mul (continuous_finsetSum _ (fun s _ =>
        (((continuous_apply s).comp continuous_subtype_val).mul
          ((continuous_apply s).comp hηcont)))))
      (fun p => mul_nonneg (hθ h) (hprofit_nn p))
      (U h) (hUcont h) (hUsc h)
  set z : priceSimplex S → (S → ℝ) :=
    fun p => fun s => (∑ h, d h p s) - (∑ h, ω h s) - η p s with hz_def
  have hzcont : Continuous z := by
    refine continuous_pi (fun s => ?_)
    exact (((continuous_finsetSum _ (fun h _ => (continuous_apply s).comp (hdcont h))).sub
      continuous_const).sub ((continuous_apply s).comp hηcont))
  have hswap : ∀ (p : priceSimplex S) (f : H → S → ℝ),
      ∑ s, (p : S → ℝ) s * (∑ h, f h s) = ∑ h, ∑ s, (p : S → ℝ) s * f h s := by
    intro p f; simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]
  have hzwal : ∀ p : priceSimplex S, ∑ s, (p : S → ℝ) s * z p s ≤ 0 := by
    intro p
    have e1 : ∑ s, (p : S → ℝ) s * z p s
        = (∑ s, (p : S → ℝ) s * (∑ h, d h p s)) - (∑ s, (p : S → ℝ) s * (∑ h, ω h s))
          - (∑ s, (p : S → ℝ) s * η p s) := by
      simp only [hz_def]
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun s _ => by ring)
    rw [e1, hswap p (fun h s => d h p s), hswap p ω]
    have hstep : ∑ h, ∑ s, (p : S → ℝ) s * d h p s
        ≤ ∑ h, ((∑ s, (p : S → ℝ) s * ω h s) + θ h * ∑ s, (p : S → ℝ) s * η p s) :=
      Finset.sum_le_sum (fun h _ => (hdfeas h p).2)
    have hrw : ∑ h, ((∑ s, (p : S → ℝ) s * ω h s) + θ h * ∑ s, (p : S → ℝ) s * η p s)
        = (∑ h, ∑ s, (p : S → ℝ) s * ω h s) + ∑ s, (p : S → ℝ) s * η p s := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, hθsum, one_mul]
    rw [hrw] at hstep
    linarith
  obtain ⟨p, hp⟩ := gale_nikaido_debreu_weak z hzcont hzwal
  refine ⟨p, fun h => d h p, fun h s => (hdfeas h p).1 s, fun h => (hdfeas h p).2,
    fun h x hx hbx => hdmax h p x hx hbx, fun s => ?_⟩
  have hps := hp s; simp only [hz_def] at hps; linarith

/-- **Endogenous price-responsive firm → full production equilibrium.** The firm scales a
net-output activity `v ≥ 0` by its profit-maximizing scale `t*(p) = max(0, p·v)` (optimum of
the strictly-concave scale criterion `t·(p·v) − t²/2`), giving a CONTINUOUS price-responsive
net supply `η(p) = t*(p)·v` with nonnegative profit `p·η(p) ≥ 0`. Feeding it to
`profit_income_equilibrium` yields a competitive equilibrium with an endogenously
profit-maximizing firm: demand from utility max, supply responding to prices, markets clear.
Boundary: a one-parameter (scale) firm with a quadratic adjustment criterion; a general
production-set firm (linear profit over a strictly convex set) is the further step. -/
theorem endogenous_scale_firm_equilibrium {H S : Type*} [Fintype H] [Fintype S] [Nonempty S]
    (M : ℝ) (hM : 0 ≤ M) (ω : H → S → ℝ) (θ : H → ℝ) (v : S → ℝ)
    (hω : ∀ h s, 0 < ω h s) (hθ : ∀ h, 0 ≤ θ h) (hθsum : ∑ h, θ h = 1)
    (U : H → (S → ℝ) → ℝ) (hUcont : ∀ h, Continuous (U h))
    (hUsc : ∀ h, StrictConcaveOn ℝ Set.univ (U h)) :
    ∃ (p : priceSimplex S) (c : H → S → ℝ),
      (∀ h s, c h s ∈ Set.Icc (0:ℝ) M) ∧
      (∀ s, (∑ h, c h s) ≤ (∑ h, ω h s) + (max 0 (∑ t, (p : S → ℝ) t * v t)) * v s) := by
  set η : priceSimplex S → (S → ℝ) :=
    fun p => fun s => (max 0 (∑ t, (p : S → ℝ) t * v t)) * v s with hη_def
  have hηcont : Continuous η := by
    refine continuous_pi (fun s => ?_)
    refine Continuous.mul ?_ continuous_const
    refine continuous_const.max ?_
    exact continuous_finsetSum _ (fun t _ =>
      ((continuous_apply t).comp continuous_subtype_val).mul continuous_const)
  have hprofit_nn : ∀ p : priceSimplex S, 0 ≤ ∑ s, (p : S → ℝ) s * η p s := by
    intro p
    have key : ∑ s, (p : S → ℝ) s * η p s
        = (max 0 (∑ t, (p : S → ℝ) t * v t)) * (∑ s, (p : S → ℝ) s * v s) := by
      rw [Finset.mul_sum]; simp only [hη_def]
      exact Finset.sum_congr rfl (fun s _ => by ring)
    rw [key]
    set q := ∑ t, (p : S → ℝ) t * v t with hq_def
    rcases le_total 0 q with hq | hq
    · rw [max_eq_right hq]; exact mul_nonneg hq hq
    · rw [max_eq_left hq]; simp
  obtain ⟨p, c, hbox, _hbud, _hmax, hclear⟩ :=
    profit_income_equilibrium M hM ω θ η hω hθ hθsum hηcont hprofit_nn U hUcont hUsc
  exact ⟨p, c, hbox, hclear⟩

/-- **Rational SMD — the rational-demand direction.** A finite family of strictly-concave
utility maximizers (demand `d_h` derived from utility maximization over budgets, no
production) produces an aggregate excess demand `Z(p) = ∑_h d_h(p) − ∑_h ω_h` that is (i)
CONTINUOUS, (ii) obeys WALRAS' law (`p·Z(p) ≤ 0`), and (iii) admits a free-disposal CLEARING
price. Together with stage 233 (function-level realizability — GND imposes nothing beyond
continuity + Walras), this brackets the Sonnenschein–Mantel–Debreu content: rational
economies generate exactly continuous Walras excess demand, and that is all equilibrium needs.
Boundary: this is the "preferences → aggregate excess demand" direction. Mantel SURJECTIVITY
(every continuous Walras `z` realized by rational households) needs the multi-household ray
construction and is NOT closed here — a single household cannot rationalize arbitrary `z`
(integrability / Slutsky-symmetry obstruction). -/
theorem rational_aggregate_excess_smd {H S : Type*} [Fintype H] [Fintype S] [Nonempty S]
    (M : ℝ) (hM : 0 ≤ M) (ω : H → S → ℝ) (hω : ∀ h s, 0 < ω h s)
    (U : H → (S → ℝ) → ℝ) (hUcont : ∀ h, Continuous (U h))
    (hUsc : ∀ h, StrictConcaveOn ℝ Set.univ (U h)) :
    ∃ (d : H → priceSimplex S → (S → ℝ)),
      (∀ h, Continuous (d h)) ∧
      (∀ h p s, d h p s ∈ Set.Icc (0:ℝ) M) ∧
      (∀ (h : H) (p : priceSimplex S), ∑ s, (p : S → ℝ) s * d h p s ≤ ∑ s, (p : S → ℝ) s * ω h s) ∧
      (∀ (h : H) (p : priceSimplex S) (y : S → ℝ), (∀ s, y s ∈ Set.Icc (0:ℝ) M) →
        ∑ s, (p : S → ℝ) s * y s ≤ ∑ s, (p : S → ℝ) s * ω h s → U h y ≤ U h (d h p)) ∧
      Continuous (fun p => fun s => (∑ h, d h p s) - (∑ h, ω h s)) ∧
      (∀ p : priceSimplex S, ∑ s, (p : S → ℝ) s * ((∑ h, d h p s) - (∑ h, ω h s)) ≤ 0) ∧
      (∃ p : priceSimplex S, ∀ s, (∑ h, d h p s) - (∑ h, ω h s) ≤ 0) := by
  choose d hdcont hdfeas hdmax using fun h =>
    utility_demand_income M hM (ω h) (hω h) (fun _ => (0:ℝ))
      continuous_const (fun _ => le_refl 0) (U h) (hUcont h) (hUsc h)
  set Z : priceSimplex S → (S → ℝ) :=
    fun p => fun s => (∑ h, d h p s) - (∑ h, ω h s) with hZ_def
  have hZcont : Continuous Z := by
    refine continuous_pi (fun s => ?_)
    exact (continuous_finsetSum _ (fun h _ => (continuous_apply s).comp (hdcont h))).sub
      continuous_const
  have hswap : ∀ (p : priceSimplex S) (f : H → S → ℝ),
      ∑ s, (p : S → ℝ) s * (∑ h, f h s) = ∑ h, ∑ s, (p : S → ℝ) s * f h s := by
    intro p f; simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]
  have hZwal : ∀ p : priceSimplex S, ∑ s, (p : S → ℝ) s * Z p s ≤ 0 := by
    intro p
    have e1 : ∑ s, (p : S → ℝ) s * Z p s
        = (∑ s, (p : S → ℝ) s * (∑ h, d h p s)) - (∑ s, (p : S → ℝ) s * (∑ h, ω h s)) := by
      simp only [hZ_def]; rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun s _ => by ring)
    rw [e1, hswap p (fun h s => d h p s), hswap p ω]
    have hstep : ∑ h, ∑ s, (p : S → ℝ) s * d h p s ≤ ∑ h, ∑ s, (p : S → ℝ) s * ω h s :=
      Finset.sum_le_sum (fun h _ => by have := (hdfeas h p).2; simpa using this)
    linarith
  obtain ⟨peq, hpeq⟩ := gale_nikaido_debreu_weak Z hZcont hZwal
  refine ⟨d, hdcont, fun h p s => (hdfeas h p).1 s, ?_, ?_, hZcont, hZwal, peq, hpeq⟩
  · intro h p; have := (hdfeas h p).2; simpa using this
  · intro h p y hy hby; exact hdmax h p y hy (by simpa using hby)

end ProfitCapstone

#print axioms ProfitCapstone.budget_lhc_general
#print axioms ProfitCapstone.utility_demand_income
#print axioms ProfitCapstone.profit_income_equilibrium
#print axioms ProfitCapstone.endogenous_scale_firm_equilibrium
#print axioms ProfitCapstone.rational_aggregate_excess_smd
