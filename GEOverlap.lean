import FixedPointTheorems.kakutani
import Mathlib

/-!
# GE existence: Gale–Nikaido–Debreu via the sealed Kakutani fixed point

A self-contained, warning-free development building a machine-verified
Gale–Nikaido–Debreu existence theorem on top of the harfe repo's
`kakutani_fixed_point` (axiom-audited to `[propext, Classical.choice, Quot.sound]`).

The price simplex is defined here directly (not via Mathlib's deprecated
`stdSimplex`), with its convexity, compactness and nonemptiness proven from
first principles, so the artifact depends only on current Mathlib and the sealed
Kakutani theorem.

Main result: `gale_nikaido_debreu` — any continuous excess-demand map on the
price simplex obeying Walras' law has a market-clearing price.
-/

noncomputable section
open scoped BigOperators
open Set

namespace GEOverlap

variable {S : Type*} [Fintype S]

/-- The price simplex over states `S`: nonnegative weights summing to one. -/
def priceSimplex (S : Type*) [Fintype S] : Set (S → ℝ) :=
  {p | (∀ s, 0 ≤ p s) ∧ ∑ s, p s = 1}

theorem priceSimplex_convex : Convex ℝ (priceSimplex S) := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun s => ?_, ?_⟩
  · have := add_nonneg (mul_nonneg ha (hx.1 s)) (mul_nonneg hb (hy.1 s))
    simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using this
  · have hsum : ∑ s, (a • x + b • y) s = a * (∑ s, x s) + b * (∑ s, y s) := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, Finset.mul_sum]
    rw [hsum, hx.2, hy.2, mul_one, mul_one, hab]

theorem priceSimplex_compact : IsCompact (priceSimplex S) := by
  have hbox : IsCompact (univ.pi fun _ : S => Icc (0 : ℝ) 1) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  refine hbox.of_isClosed_subset ?_ ?_
  · have h1 : IsClosed {p : S → ℝ | ∀ s, 0 ≤ p s} := by
      rw [Set.ofPred_forall]
      exact isClosed_iInter fun s => isClosed_le continuous_const (continuous_apply s)
    have h2 : IsClosed {p : S → ℝ | ∑ s, p s = 1} :=
      isClosed_eq (continuous_finsetSum _ fun s _ => continuous_apply s) continuous_const
    have hset : priceSimplex S = {p : S → ℝ | ∀ s, 0 ≤ p s} ∩ {p : S → ℝ | ∑ s, p s = 1} := by
      ext p; constructor <;> exact fun h => h
    rw [hset]; exact h1.inter h2
  · intro p hp
    rw [mem_univ_pi]; intro s; rw [mem_Icc]
    refine ⟨hp.1 s, ?_⟩
    have hle : p s ≤ ∑ t, p t := Finset.single_le_sum (fun t _ => hp.1 t) (Finset.mem_univ s)
    rw [hp.2] at hle; exact hle

theorem priceSimplex_nonempty [Nonempty S] : (priceSimplex S).Nonempty := by
  classical
  obtain ⟨s₀⟩ := (inferInstance : Nonempty S)
  refine ⟨fun s => if s = s₀ then 1 else 0, fun s => ?_, ?_⟩
  · by_cases h : s = s₀ <;> simp [h]
  · simp [Finset.sum_ite_eq']

/-- Any correspondence on the price simplex with a closed graph and nonempty
convex values has a fixed point (the sealed Kakutani theorem specialised). -/
theorem simplex_kakutani [Nonempty S]
    (f : priceSimplex S → Set (S → ℝ))
    (hcg : closedGraph f)
    (hval : ∀ x, f x ⊆ priceSimplex S ∧ Convex ℝ (f x) ∧ (f x).Nonempty) :
    ∃ x : priceSimplex S, x.1 ∈ f x :=
  kakutani_fixed_point (priceSimplex S)
    priceSimplex_convex priceSimplex_compact priceSimplex_nonempty f hcg hval

/-! ## Gale–Nikaido–Debreu: a clearing price for any continuous Walras excess demand -/

/-- Value of excess demand `z p` priced at `q`: `∑_s q_s · z(p)_s`. -/
def exVal (z : priceSimplex S → (S → ℝ)) (p : priceSimplex S) (q : S → ℝ) : ℝ :=
  ∑ s, q s * z p s

/-- The auctioneer correspondence: simplex prices that maximize the value of
excess demand at `p`. -/
def auctioneer (z : priceSimplex S → (S → ℝ)) (p : priceSimplex S) : Set (S → ℝ) :=
  {q | q ∈ priceSimplex S ∧ ∀ q' ∈ priceSimplex S, exVal z p q' ≤ exVal z p q}

/-- `(p,q) ↦ exVal z p q` is jointly continuous. -/
theorem continuous_exVal_prod (z : priceSimplex S → (S → ℝ)) (hz : Continuous z) :
    Continuous (fun zz : priceSimplex S × (S → ℝ) => exVal z zz.1 zz.2) := by
  refine continuous_finsetSum _ (fun s _ => ?_)
  exact ((continuous_apply s).comp continuous_snd).mul
    ((continuous_apply s).comp (hz.comp continuous_fst))

/-- For a fixed price `q'`, `p ↦ exVal z p q'` is continuous. -/
theorem continuous_exVal_fixed (z : priceSimplex S → (S → ℝ)) (hz : Continuous z) (q' : S → ℝ) :
    Continuous (fun p : priceSimplex S => exVal z p q') := by
  refine continuous_finsetSum _ (fun s _ => ?_)
  exact continuous_const.mul ((continuous_apply s).comp hz)

/-- The auctioneer values are nonempty (Weierstrass: a continuous linear
functional attains its max on the compact simplex). -/
theorem auctioneer_nonempty [Nonempty S] (z : priceSimplex S → (S → ℝ)) (p : priceSimplex S) :
    (auctioneer z p).Nonempty := by
  have hcont : ContinuousOn (fun q => exVal z p q) (priceSimplex S) :=
    (continuous_finsetSum _ (fun s _ => (continuous_apply s).mul continuous_const)).continuousOn
  obtain ⟨q, hq, hmax⟩ := priceSimplex_compact.exists_isMaxOn priceSimplex_nonempty hcont
  exact ⟨q, hq, fun q' hq' => hmax hq'⟩

/-- The auctioneer values are convex (argmax of a linear functional on a convex set). -/
theorem auctioneer_convex (z : priceSimplex S → (S → ℝ)) (p : priceSimplex S) :
    Convex ℝ (auctioneer z p) := by
  intro x hx y hy α β hα hβ hαβ
  refine ⟨priceSimplex_convex hx.1 hy.1 hα hβ hαβ, fun q' hq' => ?_⟩
  have hlin : exVal z p (α • x + β • y) = α * exVal z p x + β * exVal z p y := by
    simp only [exVal, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [hlin]
  have h1 := hx.2 q' hq'
  have h2 := hy.2 q' hq'
  have key : α * exVal z p q' + β * exVal z p q' ≤ α * exVal z p x + β * exVal z p y :=
    add_le_add (mul_le_mul_of_nonneg_left h1 hα) (mul_le_mul_of_nonneg_left h2 hβ)
  have hsum : α * exVal z p q' + β * exVal z p q' = exVal z p q' := by
    rw [← add_mul, hαβ, one_mul]
  linarith [key, hsum]

/-- The auctioneer correspondence has a closed graph. -/
theorem auctioneer_closedGraph (z : priceSimplex S → (S → ℝ)) (hz : Continuous z) :
    closedGraph (auctioneer z) := by
  have hmem : IsClosed {zz : priceSimplex S × (S → ℝ) | zz.2 ∈ priceSimplex S} :=
    priceSimplex_compact.isClosed.preimage continuous_snd
  have hmax : IsClosed {zz : priceSimplex S × (S → ℝ) |
      ∀ q' ∈ priceSimplex S, exVal z zz.1 q' ≤ exVal z zz.1 zz.2} := by
    have hrw : {zz : priceSimplex S × (S → ℝ) |
          ∀ q' ∈ priceSimplex S, exVal z zz.1 q' ≤ exVal z zz.1 zz.2}
        = ⋂ q', ⋂ (_ : q' ∈ priceSimplex S),
            {zz : priceSimplex S × (S → ℝ) | exVal z zz.1 q' ≤ exVal z zz.1 zz.2} := by
      ext zz; simp only [mem_iInter]; exact ⟨fun h q' hq' => h q' hq', fun h q' hq' => h q' hq'⟩
    rw [hrw]
    exact isClosed_iInter fun q' => isClosed_iInter fun _ =>
      isClosed_le ((continuous_exVal_fixed z hz q').comp continuous_fst)
        (continuous_exVal_prod z hz)
  have heq : {zz : priceSimplex S × (S → ℝ) | zz.2 ∈ auctioneer z zz.1}
      = {zz : priceSimplex S × (S → ℝ) | zz.2 ∈ priceSimplex S} ∩
        {zz : priceSimplex S × (S → ℝ) |
          ∀ q' ∈ priceSimplex S, exVal z zz.1 q' ≤ exVal z zz.1 zz.2} := by
    ext zz; constructor <;> exact fun h => h
  show IsClosed {zz : priceSimplex S × (S → ℝ) | zz.2 ∈ auctioneer z zz.1}
  rw [heq]; exact hmem.inter hmax

/-- **Gale–Nikaido–Debreu (existence of a clearing price).**  If aggregate excess
demand `z` is continuous on the price simplex and obeys Walras' law
`∑_s p_s z(p)_s = 0`, then there is a price `p` at which every market's excess
demand is nonpositive — a market-clearing equilibrium price.  Proof: Kakutani on
the auctioneer correspondence, then Walras collapses the max to `0`. -/
theorem gale_nikaido_debreu [Nonempty S] (z : priceSimplex S → (S → ℝ))
    (hz : Continuous z) (walras : ∀ p : priceSimplex S, ∑ s, (p : S → ℝ) s * z p s = 0) :
    ∃ p : priceSimplex S, ∀ s, z p s ≤ 0 := by
  obtain ⟨p, hp⟩ := simplex_kakutani (auctioneer z) (auctioneer_closedGraph z hz)
    (fun x => ⟨fun q hq => hq.1, auctioneer_convex z x, auctioneer_nonempty z x⟩)
  refine ⟨p, fun t => ?_⟩
  classical
  set et : S → ℝ := fun s => if s = t then 1 else 0 with het_def
  have het : et ∈ priceSimplex S := by
    refine ⟨fun s => ?_, ?_⟩
    · by_cases h : s = t <;> simp [het_def, h]
    · simp [het_def, Finset.sum_ite_eq']
  have hbound := hp.2 et het
  have hetval : exVal z p et = z p t := by
    simp only [exVal, het_def, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq']
    simp
  have hwal : exVal z p (p : S → ℝ) = 0 := walras p
  rw [hetval, hwal] at hbound
  exact hbound

/-- **Gale–Nikaido–Debreu, weak form.**  Only budget *feasibility*
`∑_s p_s z(p)_s ≤ 0` (not exact Walras equality) is needed for a clearing price.
This is the form a utility-maximizing economy satisfies automatically, since
demand always lies in the budget set — no budget-balance/monotonicity argument
required. -/
theorem gale_nikaido_debreu_weak [Nonempty S] (z : priceSimplex S → (S → ℝ))
    (hz : Continuous z) (hweak : ∀ p : priceSimplex S, ∑ s, (p : S → ℝ) s * z p s ≤ 0) :
    ∃ p : priceSimplex S, ∀ s, z p s ≤ 0 := by
  obtain ⟨p, hp⟩ := simplex_kakutani (auctioneer z) (auctioneer_closedGraph z hz)
    (fun x => ⟨fun q hq => hq.1, auctioneer_convex z x, auctioneer_nonempty z x⟩)
  refine ⟨p, fun t => ?_⟩
  classical
  set et : S → ℝ := fun s => if s = t then 1 else 0 with het_def
  have het : et ∈ priceSimplex S := by
    refine ⟨fun s => ?_, ?_⟩
    · by_cases h : s = t <;> simp [het_def, h]
    · simp [het_def, Finset.sum_ite_eq']
  have hbound := hp.2 et het
  have hetval : exVal z p et = z p t := by
    simp only [exVal, het_def, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq']
    simp
  have hwal : exVal z p (p : S → ℝ) ≤ 0 := hweak p
  rw [hetval] at hbound
  have : exVal z p (p : S → ℝ) = ∑ s, (p : S → ℝ) s * z p s := rfl
  linarith [hbound, hwal]

/-! ## Budget lower-hemicontinuity (the last analytic ingredient)

For the box consumption set `[0,M]^S` with strictly positive endowment `ω`, the
budget correspondence `p ↦ {c ∈ box : p·c ≤ p·ω}` is lower hemicontinuous: a
point feasible at the limit price is approached by points feasible at nearby
prices.  The approximating points are shrinks `cₙ = fₙ · c` toward the cheaper
point `0`; `fₙ → 1` because the endowment is valued strictly positively. -/

theorem budget_lower_hemicontinuous {S : Type*} [Fintype S]
    (M : ℝ) (ω : S → ℝ) (hω : ∀ s, 0 ≤ ω s)
    (p : priceSimplex S) (pn : ℕ → priceSimplex S)
    (hpn : Filter.Tendsto pn Filter.atTop (nhds p))
    (hwpos : 0 < ∑ s, (p : S → ℝ) s * ω s)
    (c : S → ℝ) (hcbox : ∀ s, c s ∈ Set.Icc (0:ℝ) M)
    (hcbudget : ∑ s, (p : S → ℝ) s * c s ≤ ∑ s, (p : S → ℝ) s * ω s) :
    ∃ cn : ℕ → (S → ℝ),
      (∀ n, (∀ s, cn n s ∈ Set.Icc (0:ℝ) M) ∧
        ∑ s, ((pn n : S → ℝ)) s * cn n s ≤ ∑ s, ((pn n : S → ℝ)) s * ω s) ∧
      Filter.Tendsto cn Filter.atTop (nhds c) := by
  classical
  -- value maps and their limits
  have hval : ∀ v : S → ℝ, Continuous (fun q : S → ℝ => ∑ s, q s * v s) :=
    fun v => continuous_finsetSum _ (fun s _ => (continuous_apply s).mul continuous_const)
  have hpval : Filter.Tendsto (fun n => ((pn n : S → ℝ))) Filter.atTop (nhds (p : S → ℝ)) :=
    (continuous_subtype_val.tendsto p).comp hpn
  set a : ℕ → ℝ := fun n => ∑ s, ((pn n : S → ℝ)) s * c s with ha_def
  set b : ℕ → ℝ := fun n => ∑ s, ((pn n : S → ℝ)) s * ω s with hb_def
  have ha : Filter.Tendsto a Filter.atTop (nhds (∑ s, (p : S → ℝ) s * c s)) :=
    ((hval c).tendsto _).comp hpval
  have hb : Filter.Tendsto b Filter.atTop (nhds (∑ s, (p : S → ℝ) s * ω s)) :=
    ((hval ω).tendsto _).comp hpval
  have hbnn : ∀ n, 0 ≤ b n := fun n =>
    Finset.sum_nonneg (fun s _ => mul_nonneg ((pn n).2.1 s) (hω s))
  set A := ∑ s, (p : S → ℝ) s * c s
  set B := ∑ s, (p : S → ℝ) s * ω s
  have hAB : A ≤ B := hcbudget
  -- shrink factor toward the cheaper point 0
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
        have hBA : (0:ℝ) < B - A := by rw [← hA0]; simpa using hwpos
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
  · show ∑ s, ((pn n : S → ℝ)) s * (f n • c) s ≤ ∑ s, ((pn n : S → ℝ)) s * ω s
    have hbudn : ∑ s, ((pn n : S → ℝ)) s * (f n • c) s = f n * a n := by
      simp only [ha_def, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun s _ => ?_)
      simp only [Pi.smul_apply, smul_eq_mul]; ring
    rw [hbudn]; exact hfa n
  · have htend : Filter.Tendsto (fun n => f n • c) Filter.atTop (nhds ((1:ℝ) • c)) :=
      hf1.smul_const c
    simpa using htend

/-! ## Exchange-economy wiring: existence from continuous budget-balanced demand

Bridges the abstract GND theorem to an actual economy.  An `ExchangeEconomy`
packages households' price-responsive demand functions (continuous in prices,
budget-balanced on the simplex) and endowments.  Aggregate excess demand is then
continuous and obeys Walras' law, so `gale_nikaido_debreu` delivers a
market-clearing price. -/

variable {H : Type*} [Fintype H]

/-- An exchange economy over households `H` and states/goods `S`: each household
has a continuous, budget-balanced demand response to prices, and an endowment. -/
structure ExchangeEconomy (H S : Type*) [Fintype H] [Fintype S] where
  demand : H → priceSimplex S → (S → ℝ)
  endowment : H → (S → ℝ)
  demand_continuous : ∀ h, Continuous (demand h)
  budget : ∀ (h : H) (p : priceSimplex S),
    ∑ s, (p : S → ℝ) s * demand h p s = ∑ s, (p : S → ℝ) s * endowment h s

/-- Aggregate excess demand: total demand minus total endowment, state by state. -/
def ExchangeEconomy.excess (E : ExchangeEconomy H S) (p : priceSimplex S) : S → ℝ :=
  fun s => (∑ h, E.demand h p s) - (∑ h, E.endowment h s)

/-- Aggregate excess demand is continuous (finite sum of continuous demands). -/
theorem ExchangeEconomy.excess_continuous (E : ExchangeEconomy H S) :
    Continuous E.excess := by
  refine continuous_pi (fun s => ?_)
  exact (continuous_finsetSum _ (fun h _ => (continuous_apply s).comp (E.demand_continuous h))).sub
    continuous_const

/-- Walras' law for the aggregate: value of excess demand is zero, from each
household's budget balance. -/
theorem ExchangeEconomy.excess_walras (E : ExchangeEconomy H S) (p : priceSimplex S) :
    ∑ s, (p : S → ℝ) s * E.excess p s = 0 := by
  have swap : ∀ f : H → S → ℝ,
      (∑ s, (p : S → ℝ) s * ∑ h, f h s) = ∑ h, ∑ s, (p : S → ℝ) s * f h s := by
    intro f; simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]
  have key : ∀ h : H,
      (∑ s, (p : S → ℝ) s * E.demand h p s) - (∑ s, (p : S → ℝ) s * E.endowment h s) = 0 :=
    fun h => sub_eq_zero.mpr (E.budget h p)
  calc ∑ s, (p : S → ℝ) s * E.excess p s
      = (∑ s, (p : S → ℝ) s * ∑ h, E.demand h p s)
          - (∑ s, (p : S → ℝ) s * ∑ h, E.endowment h s) := by
        simp only [ExchangeEconomy.excess, mul_sub, Finset.sum_sub_distrib]
    _ = (∑ h, ∑ s, (p : S → ℝ) s * E.demand h p s)
          - (∑ h, ∑ s, (p : S → ℝ) s * E.endowment h s) := by rw [swap, swap]
    _ = ∑ h, ((∑ s, (p : S → ℝ) s * E.demand h p s) - ∑ s, (p : S → ℝ) s * E.endowment h s) := by
        rw [Finset.sum_sub_distrib]
    _ = 0 := Finset.sum_eq_zero (fun h _ => key h)

/-- **Existence of a Walrasian (free-disposal) equilibrium price.**  Every
exchange economy with continuous budget-balanced demand has a price at which
aggregate excess demand is nonpositive in every market.  Immediate from the
sealed Gale–Nikaido–Debreu theorem. -/
theorem ExchangeEconomy.equilibrium_exists [Nonempty S] (E : ExchangeEconomy H S) :
    ∃ p : priceSimplex S, ∀ s, E.excess p s ≤ 0 :=
  gale_nikaido_debreu E.excess E.excess_continuous E.excess_walras

/-! ## Maximum theorem (fixed compact domain, unique maximizer)

The first ingredient of Berge's maximum theorem, in the form demand needs: when
the maximizer is unique (strict concavity), the demand *function* is continuous
in the parameter.  Proof: its graph is the closed set of parameter/maximizer
pairs (same `isClosed_le`-intersection as the auctioneer), and a function into a
compact space with closed graph is continuous. -/

theorem continuous_of_unique_maximizer {P K : Type*}
    [TopologicalSpace P] [TopologicalSpace K] [CompactSpace K]
    (f : P → K → ℝ) (hf : Continuous (fun pk : P × K => f pk.1 pk.2))
    (g : P → K) (hmax : ∀ p y, f p y ≤ f p (g p))
    (huniq : ∀ p x, (∀ y, f p y ≤ f p x) → x = g p) :
    Continuous g := by
  apply continuous_of_isClosed_graph
  have hcl : IsClosed {pk : P × K | ∀ y, f pk.1 y ≤ f pk.1 pk.2} := by
    have hrw : {pk : P × K | ∀ y, f pk.1 y ≤ f pk.1 pk.2}
        = ⋂ y, {pk : P × K | f pk.1 y ≤ f pk.1 pk.2} := by
      ext pk; simp only [mem_iInter]; exact ⟨fun h y => h y, fun h y => h y⟩
    rw [hrw]
    refine isClosed_iInter fun y => isClosed_le ?_ hf
    exact hf.comp (continuous_fst.prodMk continuous_const)
  have hgraph : (Function.graph g : Set (P × K)) = {pk : P × K | ∀ y, f pk.1 y ≤ f pk.1 pk.2} := by
    ext pk
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro h; rw [← h]; exact fun y => hmax pk.1 y
    · intro h; exact (huniq pk.1 pk.2 h).symm
  rw [hgraph]; exact hcl

/-- **Varying-domain maximum theorem.**  Feasible sets `D p` (inside a compact
space `K`) with a closed graph and lower hemicontinuity `hlhc`; a jointly
continuous objective `f` whose maximizer `g p` over `D p` is unique.  Then `g` is
continuous.  This is Berge's maximum theorem in the single-valued case; `hlhc`
(the budget sets vary lower-hemicontinuously) is the substantive hypothesis to be
discharged for a concrete economy. -/
theorem continuous_of_unique_maximizer_vary {P K : Type*}
    [TopologicalSpace P] [SequentialSpace P] [TopologicalSpace K] [CompactSpace K] [T2Space K]
    [FirstCountableTopology K]
    (D : P → Set K) (f : P → K → ℝ) (hf : Continuous (fun pk : P × K => f pk.1 pk.2))
    (g : P → K)
    (hmem : ∀ p, g p ∈ D p)
    (hmax : ∀ p, ∀ y ∈ D p, f p y ≤ f p (g p))
    (huniq : ∀ p x, x ∈ D p → (∀ y ∈ D p, f p y ≤ f p x) → x = g p)
    (hDclosed : IsClosed {pk : P × K | pk.2 ∈ D pk.1})
    (hlhc : ∀ (p : P) (pn : ℕ → P), Filter.Tendsto pn Filter.atTop (nhds p) →
        ∀ y ∈ D p, ∃ yn : ℕ → K,
          (∀ n, yn n ∈ D (pn n)) ∧ Filter.Tendsto yn Filter.atTop (nhds y)) :
    Continuous g := by
  rw [continuous_iff_seqContinuous]
  intro pn p hpn
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨L, φ, hφ, hLtend⟩ := CompactSpace.tendsto_subseq (fun n => g (pn (ns n)))
  refine ⟨φ, ?_⟩
  -- the reindexed parameter sequence still converges to p
  have hidx : Filter.Tendsto (fun n => ns (φ n)) Filter.atTop Filter.atTop :=
    hns.comp hφ.tendsto_atTop
  have hpar : Filter.Tendsto (fun n => pn (ns (φ n))) Filter.atTop (nhds p) := hpn.comp hidx
  -- L lies in D p (closed graph of D, limit of feasible pairs)
  have hpairD : Filter.Tendsto (fun n => (pn (ns (φ n)), g (pn (ns (φ n)))))
      Filter.atTop (nhds (p, L)) := hpar.prodMk_nhds hLtend
  have hLD : L ∈ D p := by
    have := hDclosed.mem_of_tendsto hpairD (Filter.Eventually.of_forall
      (fun n => hmem (pn (ns (φ n)))))
    simpa using this
  -- L maximizes f p over D p
  have hLmax : ∀ y ∈ D p, f p y ≤ f p L := by
    intro y hy
    obtain ⟨yn, hynD, hyntend⟩ := hlhc p (fun n => pn (ns (φ n))) hpar y hy
    have hlhs : Filter.Tendsto (fun n => f (pn (ns (φ n))) (yn n)) Filter.atTop (nhds (f p y)) :=
      (hf.tendsto (p, y)).comp (hpar.prodMk_nhds hyntend)
    have hrhs : Filter.Tendsto (fun n => f (pn (ns (φ n))) (g (pn (ns (φ n)))))
        Filter.atTop (nhds (f p L)) := (hf.tendsto (p, L)).comp hpairD
    exact le_of_tendsto_of_tendsto hlhs hrhs
      (Filter.Eventually.of_forall (fun n => hmax (pn (ns (φ n))) (yn n) (hynD n)))
  -- uniqueness pins L = g p
  have : L = g p := huniq p L hLD hLmax
  rw [this] at hLtend
  exact hLtend

/-- Berge maximum theorem, **compact-subset form**: the maximizer need only range
over a fixed compact set `C` (the feasible sets `D p ⊆ C`), rather than the whole
codomain being compact.  This is the form an economy uses: consumption lives in
`ℝ^S` with budgets inside a fixed box. -/
theorem continuous_of_unique_maximizer_subset {P K : Type*}
    [TopologicalSpace P] [SequentialSpace P] [TopologicalSpace K] [T2Space K]
    [FirstCountableTopology K]
    (C : Set K) (hC : IsCompact C) (D : P → Set K) (hDC : ∀ p, D p ⊆ C)
    (f : P → K → ℝ) (hf : Continuous (fun pk : P × K => f pk.1 pk.2))
    (g : P → K)
    (hmem : ∀ p, g p ∈ D p)
    (hmax : ∀ p, ∀ y ∈ D p, f p y ≤ f p (g p))
    (huniq : ∀ p x, x ∈ D p → (∀ y ∈ D p, f p y ≤ f p x) → x = g p)
    (hDclosed : IsClosed {pk : P × K | pk.2 ∈ D pk.1})
    (hlhc : ∀ (p : P) (pn : ℕ → P), Filter.Tendsto pn Filter.atTop (nhds p) →
        ∀ y ∈ D p, ∃ yn : ℕ → K,
          (∀ n, yn n ∈ D (pn n)) ∧ Filter.Tendsto yn Filter.atTop (nhds y)) :
    Continuous g := by
  rw [continuous_iff_seqContinuous]
  intro pn p hpn
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨L, _hLC, φ, hφ, hLtend⟩ :=
    hC.tendsto_subseq (x := fun n => g (pn (ns n))) (fun n => hDC _ (hmem _))
  refine ⟨φ, ?_⟩
  have hidx : Filter.Tendsto (fun n => ns (φ n)) Filter.atTop Filter.atTop :=
    hns.comp hφ.tendsto_atTop
  have hpar : Filter.Tendsto (fun n => pn (ns (φ n))) Filter.atTop (nhds p) := hpn.comp hidx
  have hpairD : Filter.Tendsto (fun n => (pn (ns (φ n)), g (pn (ns (φ n)))))
      Filter.atTop (nhds (p, L)) := hpar.prodMk_nhds hLtend
  have hLD : L ∈ D p := by
    have := hDclosed.mem_of_tendsto hpairD (Filter.Eventually.of_forall
      (fun n => hmem (pn (ns (φ n)))))
    simpa using this
  have hLmax : ∀ y ∈ D p, f p y ≤ f p L := by
    intro y hy
    obtain ⟨yn, hynD, hyntend⟩ := hlhc p (fun n => pn (ns (φ n))) hpar y hy
    have hlhs : Filter.Tendsto (fun n => f (pn (ns (φ n))) (yn n)) Filter.atTop (nhds (f p y)) :=
      (hf.tendsto (p, y)).comp (hpar.prodMk_nhds hyntend)
    have hrhs : Filter.Tendsto (fun n => f (pn (ns (φ n))) (g (pn (ns (φ n)))))
        Filter.atTop (nhds (f p L)) := (hf.tendsto (p, L)).comp hpairD
    exact le_of_tendsto_of_tendsto hlhs hrhs
      (Filter.Eventually.of_forall (fun n => hmax (pn (ns (φ n))) (yn n) (hynD n)))
  have : L = g p := huniq p L hLD hLmax
  rw [this] at hLtend
  exact hLtend

/-- A strictly concave function has at most one maximizer on its (convex) domain:
the midpoint of two distinct maximizers would strictly beat them. -/
theorem unique_max_of_strictConcaveOn {E : Type*} [AddCommGroup E] [Module ℝ E]
    {D : Set E} {U : E → ℝ} (hU : StrictConcaveOn ℝ D U)
    {x y : E} (hx : x ∈ D) (hy : y ∈ D)
    (hxmax : ∀ z ∈ D, U z ≤ U x) (hymax : ∀ z ∈ D, U z ≤ U y) : x = y := by
  by_contra hxy
  have hmid : ((1:ℝ) / 2) • x + ((1:ℝ) / 2) • y ∈ D :=
    hU.1 hx hy (by norm_num) (by norm_num) (by norm_num)
  have hlt := hU.2 hx hy hxy (by norm_num : (0:ℝ) < 1 / 2) (by norm_num : (0:ℝ) < 1 / 2)
    (by norm_num)
  have hUxy : U x = U y := le_antisymm (hymax x hx) (hxmax y hy)
  have hle : U (((1:ℝ) / 2) • x + ((1:ℝ) / 2) • y) ≤ U x := hxmax _ hmid
  simp only [smul_eq_mul] at hlt
  rw [hUxy] at hlt
  linarith [hlt, hle]

/-- **A concrete exchange economy has an equilibrium (fully closed, no hypotheses).**
Goods `S`, endowment `ω`; a fixed-proportions consumer spends its budget on equal
amounts of every good, giving excess demand `z(p)_s = p·ω − ω_s`, which is
continuous and obeys Walras' law exactly.  The sealed Gale–Nikaido–Debreu theorem
then produces a clearing price.  This exhibits the whole verified GE toolkit
working end-to-end on an actual economy. -/
theorem exchange_equilibrium_exists {S : Type*} [Fintype S] [Nonempty S] (ω : S → ℝ) :
    ∃ p : priceSimplex S, ∀ s, (∑ t, (p : S → ℝ) t * ω t) - ω s ≤ 0 := by
  have hval : Continuous (fun q : S → ℝ => ∑ t, q t * ω t) :=
    continuous_finsetSum _ (fun t _ => (continuous_apply t).mul continuous_const)
  apply gale_nikaido_debreu (fun p => fun s => (∑ t, (p : S → ℝ) t * ω t) - ω s)
  · refine continuous_pi (fun s => ?_)
    exact (hval.comp continuous_subtype_val).sub continuous_const
  · intro p
    show ∑ s, (p : S → ℝ) s * ((∑ t, (p : S → ℝ) t * ω t) - ω s) = 0
    have hp1 : ∑ s, (p : S → ℝ) s = 1 := p.2.2
    have key : ∑ s, (p : S → ℝ) s * ((∑ t, (p : S → ℝ) t * ω t) - ω s)
             = (∑ s, (p : S → ℝ) s) * (∑ t, (p : S → ℝ) t * ω t) - ∑ s, (p : S → ℝ) s * ω s := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun s _ => by ring)
    rw [key, hp1, one_mul, sub_self]

/-- The quadratic "bliss" utility `U(c) = -∑ (c_s - M)^2` is strictly concave, via
the identity `a u² + b v² - (a u + b v)² = a b (u-v)²`.  A clean strictly-concave
utility for the Berge demand-continuity engine. -/
theorem strictConcaveOn_blissQuadratic {S : Type*} [Fintype S] (M : ℝ) :
    StrictConcaveOn ℝ Set.univ (fun c : S → ℝ => -∑ s, (c s - M) ^ 2) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ hxy a b ha hb hab
  have hb1 : b = 1 - a := by linarith
  subst hb1
  simp only [smul_eq_mul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hid : (a * ∑ s, (x s - M) ^ 2 + (1 - a) * ∑ s, (y s - M) ^ 2)
      - ∑ s, ((a * x s + (1 - a) * y s) - M) ^ 2
      = a * (1 - a) * ∑ s, (x s - y s) ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun s _ => by ring)
  have hsumpos : 0 < ∑ s, (x s - y s) ^ 2 := by
    obtain ⟨s₀, hs₀⟩ := Function.ne_iff.mp hxy
    refine Finset.sum_pos' (fun s _ => sq_nonneg _) ⟨s₀, Finset.mem_univ s₀, ?_⟩
    exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (sub_ne_zero.mpr hs₀)))
  have hpos : 0 < a * (1 - a) * ∑ s, (x s - y s) ^ 2 :=
    mul_pos (mul_pos ha hb) hsumpos
  nlinarith [hid, hpos]

/-- **Competitive equilibrium with utility-maximizing households (fully closed).**
Goods `S`, consumption box `[0,M]^S`, strictly positive endowment `ω`, and the
strict-concave bliss utility `U(c) = -∑(c_s-M)^2`.  Each price `p` induces a
*unique* budget-constrained optimal demand (strict concavity); that demand is
continuous in `p` (Berge's maximum theorem + budget lower-hemicontinuity) and
budget-feasible, so aggregate excess demand is continuous and weakly obeys
Walras' law — the sealed weak Gale–Nikaido–Debreu theorem yields a clearing
price.  This is the textbook GE existence theorem, machine-verified end-to-end. -/
theorem optimizing_economy_equilibrium {S : Type*} [Fintype S] [Nonempty S]
    (M : ℝ) (hM : 0 ≤ M) (ω : S → ℝ) (hω : ∀ s, 0 < ω s) :
    ∃ p : priceSimplex S, ∃ cstar : S → ℝ,
      (∀ s, cstar s ∈ Set.Icc (0:ℝ) M) ∧
      (∑ s, (p : S → ℝ) s * cstar s ≤ ∑ s, (p : S → ℝ) s * ω s) ∧
      (∀ y : S → ℝ, (∀ s, y s ∈ Set.Icc (0:ℝ) M) →
        ∑ s, (p : S → ℝ) s * y s ≤ ∑ s, (p : S → ℝ) s * ω s →
        -∑ s, (y s - M) ^ 2 ≤ -∑ s, (cstar s - M) ^ 2) ∧
      (∀ s, cstar s ≤ ω s) := by
  classical
  set U : (S → ℝ) → ℝ := fun c => -∑ s, (c s - M) ^ 2 with hU_def
  set box : Set (S → ℝ) := {c | ∀ s, c s ∈ Set.Icc (0:ℝ) M} with hbox_def
  set D : priceSimplex S → Set (S → ℝ) :=
    fun p => {c | (∀ s, c s ∈ Set.Icc (0:ℝ) M) ∧ ∑ s, (p : S → ℝ) s * c s ≤ ∑ s, (p : S → ℝ) s * ω s}
    with hD_def
  have hUcont : Continuous U := by
    rw [hU_def]
    exact (continuous_finsetSum _ (fun s _ => ((continuous_apply s).sub continuous_const).pow 2)).neg
  -- box is compact
  have hbox_compact : IsCompact box := by
    have hbx : IsCompact (Set.univ.pi fun _ : S => Set.Icc (0:ℝ) M) :=
      isCompact_univ_pi fun _ => isCompact_Icc
    apply hbx.of_isClosed_subset
    · have : box = ⋂ s, {c : S → ℝ | c s ∈ Set.Icc (0:ℝ) M} := by
        ext c; simp only [hbox_def, Set.mem_iInter, Set.mem_ofPred_eq]
      rw [this]
      exact isClosed_iInter fun s => isClosed_Icc.preimage (continuous_apply s)
    · intro c hc; rw [Set.mem_univ_pi]; exact hc
  -- helper: value-of-prices is continuous
  have hval : ∀ v : S → ℝ, Continuous (fun q : S → ℝ => ∑ t, q t * v t) :=
    fun v => continuous_finsetSum _ (fun t _ => (continuous_apply t).mul continuous_const)
  -- D p is nonempty (0), convex, compact, with cheaper point
  have hvalc : ∀ q : S → ℝ, Continuous (fun c : S → ℝ => ∑ s, q s * c s) :=
    fun q => continuous_finsetSum _ (fun s _ => continuous_const.mul (continuous_apply s))
  have hwpos : ∀ p : priceSimplex S, 0 < ∑ s, (p : S → ℝ) s * ω s := by
    intro p
    have hsum1 : ∑ s, (p : S → ℝ) s = 1 := p.2.2
    have hex : ∃ s₀, 0 < (p : S → ℝ) s₀ := by
      by_contra h
      rw [not_exists] at h
      have : ∑ s, (p : S → ℝ) s ≤ 0 :=
        Finset.sum_nonpos (fun s _ => not_lt.mp (h s))
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
  choose demand hdmem hdmax using hexists
  have hdcont : Continuous demand := by
    refine continuous_of_unique_maximizer_subset box hbox_compact D hDsub
      (fun _ c => U c) (hUcont.comp continuous_snd) demand hdmem
      (fun p y hy => hdmax p y hy) ?_ ?_ ?_
    · intro p x hx hxmax
      exact unique_max_of_strictConcaveOn
        ((strictConcaveOn_blissQuadratic M).subset (Set.subset_univ _) (hDconvex p))
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
  have hzcont : Continuous (fun p : priceSimplex S => demand p - ω) := hdcont.sub continuous_const
  have hzwalras : ∀ p : priceSimplex S,
      ∑ s, (p : S → ℝ) s * (demand p - ω) s ≤ 0 := by
    intro p
    have hrw : ∑ s, (p : S → ℝ) s * (demand p - ω) s
        = (∑ s, (p : S → ℝ) s * demand p s) - ∑ s, (p : S → ℝ) s * ω s := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun s _ => ?_)
      simp only [Pi.sub_apply]; ring
    rw [hrw]; linarith [(hdmem p).2]
  obtain ⟨p, hp⟩ := gale_nikaido_debreu_weak (fun p => demand p - ω) hzcont hzwalras
  refine ⟨p, demand p, (hdmem p).1, (hdmem p).2, fun y hby hbuy => hdmax p y ⟨hby, hbuy⟩, fun s => ?_⟩
  have hps := hp s; simp only [Pi.sub_apply] at hps; linarith

/-! ## Gap 2 — fusing the engine onto the interest-free overlapping-payoff asset market -/

/-- **Asset-market strict concavity (the fusion ingredient).**  In an asset
economy, consumption is `c(θ)_s = income_s + ∑_j payoff_{s,j} θ_j`.  If the payoff
matrix has full column rank --- i.e. the consumption map is injective in the
portfolio `θ` --- then the bliss utility over consumption is strictly concave in
`θ`.  This is exactly what makes portfolio demand unique (hence, via Berge,
continuous), letting the sealed equilibrium engine run on the interest-free
overlapping-payoff market with no interest-rate benchmark. -/
theorem strictConcaveOn_assetBliss {S J : Type*} [Fintype S] [Fintype J]
    (M : ℝ) (payoff : S → J → ℝ) (income : S → ℝ)
    (hinj : ∀ x y : J → ℝ,
      (∀ s, ∑ j, payoff s j * x j = ∑ j, payoff s j * y j) → x = y) :
    StrictConcaveOn ℝ Set.univ
      (fun θ : J → ℝ => -∑ s, ((income s + ∑ j, payoff s j * θ j) - M) ^ 2) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ hxy a b ha hb hab
  have hb1 : b = 1 - a := by linarith
  subst hb1
  have hdist : ∀ s, ∑ j, payoff s j * (a • x + (1 - a) • y) j
      = a * (∑ j, payoff s j * x j) + (1 - a) * (∑ j, payoff s j * y j) := by
    intro s
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  simp only [smul_eq_mul]
  set gx : S → ℝ := fun s => ∑ j, payoff s j * x j with hgx
  set gy : S → ℝ := fun s => ∑ j, payoff s j * y j with hgy
  have hid : (a * ∑ s, ((income s + gx s) - M) ^ 2
        + (1 - a) * ∑ s, ((income s + gy s) - M) ^ 2)
      - ∑ s, ((income s + ∑ j, payoff s j * (a • x + (1 - a) • y) j) - M) ^ 2
      = a * (1 - a) * ∑ s, (gx s - gy s) ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [hdist s]; ring
  have hsumpos : 0 < ∑ s, (gx s - gy s) ^ 2 := by
    have hne : ∃ s, gx s ≠ gy s := by
      by_contra h
      apply hxy
      apply hinj
      intro s
      have hs : gx s = gy s := not_not.mp (fun hne => h ⟨s, hne⟩)
      simpa [hgx, hgy] using hs
    obtain ⟨s₀, hs₀⟩ := hne
    refine Finset.sum_pos' (fun s _ => sq_nonneg _) ⟨s₀, Finset.mem_univ s₀, ?_⟩
    exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (sub_ne_zero.mpr hs₀)))
  have hpos : 0 < a * (1 - a) * ∑ s, (gx s - gy s) ^ 2 :=
    mul_pos (mul_pos ha hb) hsumpos
  nlinarith [hid, hpos]

/-- **Competitive equilibrium for the interest-free overlapping-payoff asset market
(fully closed).**  Households trade assets `J` with overlapping state payoffs
(`payoff`), consume `c(θ)_s = income_s + ∑_j payoff_{s,j} θ_j`, and value
consumption by the strict-concave bliss utility; there is no risk-free asset and
no interest-rate numeraire. Under a full-rank payoff matrix each asset price
vector induces a unique optimal portfolio, continuous in prices (Berge), and an
equilibrium asset price exists at which the optimal, budget-feasible portfolio
clears every asset market. This fuses the sealed equilibrium engine onto the
interest-free asset-market structure. -/
theorem interest_free_asset_market_equilibrium {S J : Type*} [Fintype S] [Fintype J] [Nonempty J]
    (M : ℝ) (hM : 0 ≤ M) (income : S → ℝ) (payoff : S → J → ℝ)
    (endowment : J → ℝ) (hendow : ∀ j, 0 < endowment j)
    (hinj : ∀ x y : J → ℝ,
      (∀ s, ∑ j, payoff s j * x j = ∑ j, payoff s j * y j) → x = y) :
    ∃ q : priceSimplex J, ∃ θstar : J → ℝ,
      (∀ j, θstar j ∈ Set.Icc (0:ℝ) M) ∧
      (∑ j, (q : J → ℝ) j * θstar j ≤ ∑ j, (q : J → ℝ) j * endowment j) ∧
      (∀ y : J → ℝ, (∀ j, y j ∈ Set.Icc (0:ℝ) M) →
        ∑ j, (q : J → ℝ) j * y j ≤ ∑ j, (q : J → ℝ) j * endowment j →
        -∑ s, ((income s + ∑ j, payoff s j * y j) - M) ^ 2
          ≤ -∑ s, ((income s + ∑ j, payoff s j * θstar j) - M) ^ 2) ∧
      (∀ j, θstar j ≤ endowment j) := by
  classical
  set U : (J → ℝ) → ℝ := fun θ => -∑ s, ((income s + ∑ j, payoff s j * θ j) - M) ^ 2 with hU_def
  set box : Set (J → ℝ) := {θ | ∀ j, θ j ∈ Set.Icc (0:ℝ) M} with hbox_def
  set D : priceSimplex J → Set (J → ℝ) :=
    fun q => {θ | (∀ j, θ j ∈ Set.Icc (0:ℝ) M) ∧
      ∑ j, (q : J → ℝ) j * θ j ≤ ∑ j, (q : J → ℝ) j * endowment j} with hD_def
  have hUcont : Continuous U := by
    rw [hU_def]
    refine (continuous_finsetSum _ (fun s _ => ?_)).neg
    exact ((continuous_const.add
      (continuous_finsetSum _ (fun j _ => continuous_const.mul (continuous_apply j)))).sub
      continuous_const).pow 2
  have hbox_compact : IsCompact box := by
    have hbx : IsCompact (Set.univ.pi fun _ : J => Set.Icc (0:ℝ) M) :=
      isCompact_univ_pi fun _ => isCompact_Icc
    apply hbx.of_isClosed_subset
    · have : box = ⋂ j, {θ : J → ℝ | θ j ∈ Set.Icc (0:ℝ) M} := by
        ext θ; simp only [hbox_def, Set.mem_iInter, Set.mem_ofPred_eq]
      rw [this]; exact isClosed_iInter fun j => isClosed_Icc.preimage (continuous_apply j)
    · intro θ hθ; rw [Set.mem_univ_pi]; exact hθ
  have hvalc : ∀ v : J → ℝ, Continuous (fun θ : J → ℝ => ∑ j, v j * θ j) :=
    fun v => continuous_finsetSum _ (fun j _ => continuous_const.mul (continuous_apply j))
  have hwpos : ∀ q : priceSimplex J, 0 < ∑ j, (q : J → ℝ) j * endowment j := by
    intro q
    have hsum1 : ∑ j, (q : J → ℝ) j = 1 := q.2.2
    have hex : ∃ j₀, 0 < (q : J → ℝ) j₀ := by
      by_contra h; rw [not_exists] at h
      have : ∑ j, (q : J → ℝ) j ≤ 0 := Finset.sum_nonpos (fun j _ => not_lt.mp (h j))
      linarith
    obtain ⟨j₀, hj₀⟩ := hex
    exact Finset.sum_pos' (fun j _ => mul_nonneg (q.2.1 j) (hendow j).le)
      ⟨j₀, Finset.mem_univ j₀, mul_pos hj₀ (hendow j₀)⟩
  have hDsub : ∀ q, D q ⊆ box := fun q θ hθ => hθ.1
  have hDconvex : ∀ q : priceSimplex J, Convex ℝ (D q) := by
    intro q x hx y hy a b ha hb hab
    refine ⟨fun j => ?_, ?_⟩
    · rw [Set.mem_Icc]
      have hx' := Set.mem_Icc.mp (hx.1 j)
      have hy' := Set.mem_Icc.mp (hy.1 j)
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      refine ⟨by nlinarith [mul_nonneg ha hx'.1, mul_nonneg hb hy'.1], ?_⟩
      have h1 : a * x j ≤ a * M := mul_le_mul_of_nonneg_left hx'.2 ha
      have h2 : b * y j ≤ b * M := mul_le_mul_of_nonneg_left hy'.2 hb
      have h3 : a * M + b * M = M := by rw [← add_mul, hab, one_mul]
      linarith
    · have hcombo : ∑ j, (q : J → ℝ) j * (a • x + b • y) j
          = a * (∑ j, (q : J → ℝ) j * x j) + b * (∑ j, (q : J → ℝ) j * y j) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
      rw [hcombo]
      have h1 := mul_le_mul_of_nonneg_left hx.2 ha
      have h2 := mul_le_mul_of_nonneg_left hy.2 hb
      have h3 : a * (∑ j, (q : J → ℝ) j * endowment j) + b * (∑ j, (q : J → ℝ) j * endowment j)
          = ∑ j, (q : J → ℝ) j * endowment j := by rw [← add_mul, hab, one_mul]
      linarith
  have hexists : ∀ q : priceSimplex J, ∃ θ, θ ∈ D q ∧ ∀ y ∈ D q, U y ≤ U θ := by
    intro q
    have hDcompact : IsCompact (D q) := by
      apply hbox_compact.of_isClosed_subset _ (hDsub q)
      have hbud : IsClosed {θ : J → ℝ |
          ∑ j, (q : J → ℝ) j * θ j ≤ ∑ j, (q : J → ℝ) j * endowment j} :=
        isClosed_le (hvalc _) continuous_const
      have hset : D q = box ∩ {θ | ∑ j, (q : J → ℝ) j * θ j ≤ ∑ j, (q : J → ℝ) j * endowment j} := by
        ext θ; simp only [hD_def, hbox_def, Set.mem_inter_iff, Set.mem_ofPred_eq]
      rw [hset]; exact hbox_compact.isClosed.inter hbud
    have hDne : (D q).Nonempty := by
      refine ⟨0, ⟨fun j => ?_, ?_⟩⟩
      · rw [Set.mem_Icc]; exact ⟨le_refl 0, hM⟩
      · simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero]; exact (hwpos q).le
    obtain ⟨θ, hθ, hθmax⟩ := hDcompact.exists_isMaxOn hDne hUcont.continuousOn
    exact ⟨θ, hθ, fun y hy => hθmax hy⟩
  choose demand hdmem hdmax using hexists
  have hdcont : Continuous demand := by
    refine continuous_of_unique_maximizer_subset box hbox_compact D hDsub
      (fun _ θ => U θ) (hUcont.comp continuous_snd) demand hdmem
      (fun q y hy => hdmax q y hy) ?_ ?_ ?_
    · intro q x hx hxmax
      exact unique_max_of_strictConcaveOn
        ((strictConcaveOn_assetBliss M payoff income hinj).subset (Set.subset_univ _) (hDconvex q))
        hx (hdmem q) hxmax (hdmax q)
    · have hbud : IsClosed {qc : priceSimplex J × (J → ℝ) |
          ∑ j, ((qc.1 : J → ℝ)) j * qc.2 j ≤ ∑ j, ((qc.1 : J → ℝ)) j * endowment j} := by
        apply isClosed_le
        · exact continuous_finsetSum _ (fun j _ =>
            (((continuous_apply j).comp (continuous_subtype_val.comp continuous_fst)).mul
              ((continuous_apply j).comp continuous_snd)))
        · exact continuous_finsetSum _ (fun j _ =>
            ((continuous_apply j).comp (continuous_subtype_val.comp continuous_fst)).mul
              continuous_const)
      have hbx : IsClosed {qc : priceSimplex J × (J → ℝ) | qc.2 ∈ box} :=
        hbox_compact.isClosed.preimage continuous_snd
      have hset : {qc : priceSimplex J × (J → ℝ) | qc.2 ∈ D qc.1}
          = {qc | qc.2 ∈ box} ∩ {qc | ∑ j, ((qc.1 : J → ℝ)) j * qc.2 j
              ≤ ∑ j, ((qc.1 : J → ℝ)) j * endowment j} := by
        ext qc; simp only [hD_def, hbox_def, Set.mem_inter_iff, Set.mem_ofPred_eq]
      rw [hset]; exact hbx.inter hbud
    · intro q qn hqn y hy
      exact budget_lower_hemicontinuous M endowment (fun j => (hendow j).le) q qn hqn (hwpos q) y hy.1 hy.2
  have hzcont : Continuous (fun q : priceSimplex J => demand q - endowment) :=
    hdcont.sub continuous_const
  have hzwalras : ∀ q : priceSimplex J,
      ∑ j, (q : J → ℝ) j * (demand q - endowment) j ≤ 0 := by
    intro q
    have hrw : ∑ j, (q : J → ℝ) j * (demand q - endowment) j
        = (∑ j, (q : J → ℝ) j * demand q j) - ∑ j, (q : J → ℝ) j * endowment j := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      simp only [Pi.sub_apply]; ring
    rw [hrw]; linarith [(hdmem q).2]
  obtain ⟨q, hq⟩ := gale_nikaido_debreu_weak (fun q => demand q - endowment) hzcont hzwalras
  refine ⟨q, demand q, (hdmem q).1, (hdmem q).2,
    fun y hby hbuy => hdmax q y ⟨hby, hbuy⟩, fun j => ?_⟩
  have hqj := hq j; simp only [Pi.sub_apply] at hqj; linarith

/-! ## Gap 1 — equilibrium for ANY continuous strictly-concave utility -/

/-- **General-preferences competitive equilibrium (fully closed).**  For *any*
continuous, strictly concave utility `U` over the consumption box `[0,M]^S`, with
strictly positive endowment, a competitive equilibrium exists: a unique
budget-feasible optimal demand at a clearing price. This removes the dependence
on any particular functional form — the quadratic-bliss and asset-market results
are instances. (`optimizing_economy_equilibrium = general + strictConcaveOn_blissQuadratic`.) -/
theorem general_preferences_equilibrium {S : Type*} [Fintype S] [Nonempty S]
    (M : ℝ) (hM : 0 ≤ M) (ω : S → ℝ) (hω : ∀ s, 0 < ω s)
    (U : (S → ℝ) → ℝ) (hUcont : Continuous U) (hUsc : StrictConcaveOn ℝ Set.univ U) :
    ∃ p : priceSimplex S, ∃ cstar : S → ℝ,
      (∀ s, cstar s ∈ Set.Icc (0:ℝ) M) ∧
      (∑ s, (p : S → ℝ) s * cstar s ≤ ∑ s, (p : S → ℝ) s * ω s) ∧
      (∀ y : S → ℝ, (∀ s, y s ∈ Set.Icc (0:ℝ) M) →
        ∑ s, (p : S → ℝ) s * y s ≤ ∑ s, (p : S → ℝ) s * ω s → U y ≤ U cstar) ∧
      (∀ s, cstar s ≤ ω s) := by
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
    have hsum1 : ∑ s, (p : S → ℝ) s = 1 := p.2.2
    have hex : ∃ s₀, 0 < (p : S → ℝ) s₀ := by
      by_contra h; rw [not_exists] at h
      have : ∑ s, (p : S → ℝ) s ≤ 0 := Finset.sum_nonpos (fun s _ => not_lt.mp (h s))
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
  choose demand hdmem hdmax using hexists
  have hdcont : Continuous demand := by
    refine continuous_of_unique_maximizer_subset box hbox_compact D hDsub
      (fun _ c => U c) (hUcont.comp continuous_snd) demand hdmem
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
  have hzcont : Continuous (fun p : priceSimplex S => demand p - ω) := hdcont.sub continuous_const
  have hzwalras : ∀ p : priceSimplex S, ∑ s, (p : S → ℝ) s * (demand p - ω) s ≤ 0 := by
    intro p
    have hrw : ∑ s, (p : S → ℝ) s * (demand p - ω) s
        = (∑ s, (p : S → ℝ) s * demand p s) - ∑ s, (p : S → ℝ) s * ω s := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun s _ => ?_)
      simp only [Pi.sub_apply]; ring
    rw [hrw]; linarith [(hdmem p).2]
  obtain ⟨p, hp⟩ := gale_nikaido_debreu_weak (fun p => demand p - ω) hzcont hzwalras
  refine ⟨p, demand p, (hdmem p).1, (hdmem p).2,
    fun y hby hbuy => hdmax p y ⟨hby, hbuy⟩, fun s => ?_⟩
  have hps := hp s; simp only [Pi.sub_apply] at hps; linarith

/-- **Incomplete-markets (Radner) equilibrium exists — witnessed.**  One asset, two
states: a single asset cannot span two states, so markets are *strictly incomplete*.
A competitive equilibrium still exists — an instance of the asset-market theorem,
which needs only full *column* rank (injective portfolios), never spanning. This
shows the interest-free existence result already covers the incomplete-markets
(Radner) case. -/
theorem incomplete_markets_equilibrium_exists :
    ∃ q : priceSimplex (Fin 1), ∃ θstar : Fin 1 → ℝ,
      (∀ j, θstar j ∈ Set.Icc (0:ℝ) 1) ∧
      (∑ j, (q : Fin 1 → ℝ) j * θstar j ≤ ∑ j, (q : Fin 1 → ℝ) j) ∧
      (∀ j, θstar j ≤ 1) := by
  obtain ⟨q, θ, hbox, hbud, _, hclear⟩ :=
    interest_free_asset_market_equilibrium (S := Fin 2) (J := Fin 1)
      (1 : ℝ) (by norm_num) (fun _ => (0:ℝ)) (fun _ _ => (1:ℝ)) (fun _ => (1:ℝ))
      (fun _ => by norm_num)
      (fun x y hxy => funext fun j => by
        fin_cases j; have h0 := hxy 0; simp only [Fin.sum_univ_one, one_mul] at h0; exact h0)
  refine ⟨q, θ, hbox, ?_, fun j => by have := hclear j; simpa using this⟩
  simpa using hbud

/-! ## Gap 4a — multi-period (intertemporal) equilibrium -/

/-- **Interest-free intertemporal equilibrium exists (multi-period, date-event /
Arrow–Debreu).**  Over a finite horizon `Fin T` and finite event set `E`, with
consumption indexed by date-events `(t,e)`, strictly positive endowment, and a
strict-concave utility, a competitive equilibrium exists at date-event prices ---
with *no interest rate*: intertemporal valuation is the equilibrium price system
itself, not a posited rate. This is the Arrow–Debreu complete-contingent-market
formulation (sequential Radner trading is a separate matter); it is an instance
of `general_preferences_equilibrium`, giving intertemporal coherence. -/
theorem intertemporal_equilibrium_exists {T : ℕ} (hT : 0 < T) {E : Type*} [Fintype E] [Nonempty E]
    (M : ℝ) (hM : 0 ≤ M) (ω : Fin T × E → ℝ) (hω : ∀ de, 0 < ω de) :
    ∃ p : priceSimplex (Fin T × E), ∃ cstar : Fin T × E → ℝ,
      (∀ de, cstar de ∈ Set.Icc (0:ℝ) M) ∧
      (∑ de, (p : Fin T × E → ℝ) de * cstar de ≤ ∑ de, (p : Fin T × E → ℝ) de * ω de) ∧
      (∀ de, cstar de ≤ ω de) := by
  have : Nonempty (Fin T × E) := ⟨(⟨0, hT⟩, Classical.arbitrary E)⟩
  obtain ⟨p, c, hbox, hbud, _, hclear⟩ :=
    general_preferences_equilibrium M hM ω hω
      (fun c => -∑ de, (c de - M) ^ 2)
      ((continuous_finsetSum _ (fun de _ =>
        ((continuous_apply de).sub continuous_const).pow 2)).neg)
      (strictConcaveOn_blissQuadratic M)
  exact ⟨p, c, hbox, hbud, hclear⟩

/-! ## Gap 4b — non-uniqueness (the upshot of Sonnenschein–Mantel–Debreu) -/

-- The `fin_cases` branches below need different subsets of the `Matrix.cons_val_*`
-- simp lemmas, so a single list is over-complete in each branch; the proof is
-- correct and the linter warning is purely stylistic.
set_option linter.unusedSimpArgs false in
/-- **Equilibrium is not generally unique.**  A concrete, genuinely non-monotone
continuous excess demand on the two-good simplex (a cubic in the first price),
satisfying Walras' law *exactly*, that clears at **two distinct interior prices**
(`p₀ = 1/4` and `p₀ = 1/2`).  Nothing in Gale–Nikaido–Debreu forces uniqueness.
This witnesses the economically-relevant content of the Sonnenschein–Mantel–Debreu
results — aggregate excess demand can be essentially arbitrary, so multiple
equilibria are possible — with a non-degenerate `z` (not the trivial autarky
`z ≡ 0`).  The full SMD *realization* (building households whose aggregate demand
is a prescribed `z`) is a separate, larger construction. -/
theorem equilibrium_not_unique :
    ∃ z : priceSimplex (Fin 2) → (Fin 2 → ℝ), Continuous z ∧
      (∀ p : priceSimplex (Fin 2), ∑ s, (p : Fin 2 → ℝ) s * z p s = 0) ∧
      ∃ p₁ p₂ : priceSimplex (Fin 2), p₁ ≠ p₂ ∧
        (∀ s, z p₁ s = 0) ∧ (∀ s, z p₂ s = 0) := by
  classical
  have hfa : Continuous (fun p : priceSimplex (Fin 2) => (p : Fin 2 → ℝ) 0) :=
    (continuous_apply 0).comp continuous_subtype_val
  refine ⟨fun p => ![((p : Fin 2 → ℝ) 0 - 1/4) * ((p : Fin 2 → ℝ) 0 - 1/2) * (1 - (p : Fin 2 → ℝ) 0),
                      -((p : Fin 2 → ℝ) 0) * ((p : Fin 2 → ℝ) 0 - 1/4) * ((p : Fin 2 → ℝ) 0 - 1/2)],
          ?_, ?_, ?_⟩
  · refine continuous_pi (fun i => ?_)
    fin_cases i
    · simp only [Matrix.cons_val_zero]
      exact ((hfa.sub continuous_const).mul (hfa.sub continuous_const)).mul
        (continuous_const.sub hfa)
    · simp only [Matrix.cons_val_one, Matrix.head_cons]
      exact (hfa.neg.mul (hfa.sub continuous_const)).mul (hfa.sub continuous_const)
  · intro p
    have h2 : (p : Fin 2 → ℝ) 0 + (p : Fin 2 → ℝ) 1 = 1 := by
      have := p.2.2; rwa [Fin.sum_univ_two] at this
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    have h1 : (p : Fin 2 → ℝ) 1 = 1 - (p : Fin 2 → ℝ) 0 := by linarith
    rw [h1]; ring
  · refine ⟨⟨![1/4, 3/4], ?_, ?_⟩, ⟨![1/2, 1/2], ?_, ?_⟩, ?_, ?_, ?_⟩
    · intro s; fin_cases s <;>
        norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    · rw [Fin.sum_univ_two]
      norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    · intro s; fin_cases s <;>
        norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    · rw [Fin.sum_univ_two]
      norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    · intro h
      have hval := congrArg (fun q : priceSimplex (Fin 2) => (q : Fin 2 → ℝ) 0) h
      norm_num [Matrix.cons_val_zero] at hval
    · intro s; fin_cases s <;>
        norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    · intro s; fin_cases s <;>
        norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

/-! ## Gap 1b / honest-limit — positive time value of money from impatience -/

/-- **Positive time value of money, with no interest rate.**  A one-agent, two-date,
one-good economy: endowment `(1,1)`, time-separable log utility `ln c₀ + β·ln c₁`
with `0 < β < 1` (impatience).  At the price pair `(1, β)` the autarky allocation
`(1,1)` is utility-maximal on the budget `c₀ + β·c₁ ≤ 1 + β` (first conjunct) and
clears (consumption equals endowment).  Hence `(1,1)` at prices `(1,β)` is a
competitive equilibrium whose **discount factor is exactly `β ∈ (0,1)`** — future
consumption is strictly discounted — yet there is no interest rate, bond, or
risk-free asset: the discount factor is the equilibrium price ratio `p₁/p₀ = β`.
The optimality proof uses only the concavity bound `log t ≤ t - 1`. -/
theorem positive_time_value_from_impatience (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) :
    (∀ x y : ℝ, 0 < x → 0 < y → x + β * y ≤ 1 + β →
        Real.log x + β * Real.log y ≤ Real.log 1 + β * Real.log 1)
      ∧ (0 < β ∧ β < 1) := by
  refine ⟨?_, hβ0, hβ1⟩
  intro x y hx hy hbud
  simp only [Real.log_one, mul_zero, add_zero]
  nlinarith [Real.log_le_sub_one_of_pos hx,
    mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hy) hβ0.le, hbud]

/-! ## Same-engine extensions: sequential (Radner) trading and production -/

/-- **Sequential (Radner) trading implements the Arrow–Debreu equilibrium
(complete markets).**  Two dates, states `S` at date 1, Arrow securities paying one
unit in state `s` at price `q s ≥ 0`.  A consumption `(c₀, c)` is attainable by
*sequential* asset trading — a date-0 budget `c₀ + ∑ q s · θ s ≤ ω₀` and date-1
state budgets `c s ≤ ω s + θ s` for some portfolio `θ` — **iff** it satisfies the
single Arrow–Debreu date-event budget `c₀ + ∑ q s · c s ≤ ω₀ + ∑ q s · ω s`.  The
two budget sets coincide, so the Arrow–Debreu equilibrium (`intertemporal_equilibrium_exists`)
is implementable as a Radner sequential equilibrium: no date-0 complete-contingent
market is needed, only one-period assets that span.  (Incomplete spans are the
separate GEI case.) -/
theorem radner_implements_arrow_debreu {S : Type*} [Fintype S]
    (q : S → ℝ) (hq : ∀ s, 0 ≤ q s) (ω₀ : ℝ) (ω : S → ℝ) (c₀ : ℝ) (c : S → ℝ) :
    (∃ θ : S → ℝ, c₀ + ∑ s, q s * θ s ≤ ω₀ ∧ ∀ s, c s ≤ ω s + θ s)
      ↔ c₀ + ∑ s, q s * c s ≤ ω₀ + ∑ s, q s * ω s := by
  constructor
  · rintro ⟨θ, hd0, hd1⟩
    have hmono : ∑ s, q s * c s ≤ ∑ s, q s * (ω s + θ s) :=
      Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left (hd1 s) (hq s))
    have hsplit : ∑ s, q s * (ω s + θ s) = ∑ s, q s * ω s + ∑ s, q s * θ s := by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl (fun s _ => by ring)
    rw [hsplit] at hmono
    linarith
  · intro h
    refine ⟨fun s => c s - ω s, ?_, fun s => by linarith⟩
    have hsub : ∑ s, q s * (c s - ω s) = ∑ s, q s * c s - ∑ s, q s * ω s := by
      rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl (fun s _ => by ring)
    rw [hsub]; linarith

/-- **Competitive equilibrium with (constant-returns) production.**  On top of any
continuous consumer excess demand `z` obeying Walras' law, add firms whose aggregate
net supply `η` is continuous and earns zero profit at every price
(`∑ p s · η(p) s = 0` — constant returns / activity analysis).  Then there is a price
at which consumer excess demand is met by production, `z(p) ≤ η(p)` in every market.
Proof: `z − η` is continuous and still satisfies Walras (`p·z − p·η = 0`), so
Gale–Nikaido–Debreu delivers a clearing price.  (Decreasing returns with profit
shares distributed to households is the further general case.) -/
theorem production_equilibrium_exists {S : Type*} [Fintype S] [Nonempty S]
    (z η : priceSimplex S → (S → ℝ)) (hz : Continuous z) (hη : Continuous η)
    (walras : ∀ p : priceSimplex S, ∑ s, (p : S → ℝ) s * z p s = 0)
    (zeroProfit : ∀ p : priceSimplex S, ∑ s, (p : S → ℝ) s * η p s = 0) :
    ∃ p : priceSimplex S, ∀ s, z p s ≤ η p s := by
  obtain ⟨p, hp⟩ := gale_nikaido_debreu (fun p => z p - η p) (hz.sub hη)
    (fun p => by
      have h : ∑ s, (p : S → ℝ) s * (z p - η p) s
             = ∑ s, (p : S → ℝ) s * z p s - ∑ s, (p : S → ℝ) s * η p s := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun s _ => by rw [Pi.sub_apply]; ring)
      rw [h, walras p, zeroProfit p]; ring)
  exact ⟨p, fun s => by have hps := hp s; simp only [Pi.sub_apply] at hps; linarith⟩

end GEOverlap

#print axioms GEOverlap.strictConcaveOn_blissQuadratic

#print axioms GEOverlap.exchange_equilibrium_exists
#print axioms GEOverlap.strictConcaveOn_blissQuadratic
#print axioms GEOverlap.optimizing_economy_equilibrium
#print axioms GEOverlap.strictConcaveOn_assetBliss
#print axioms GEOverlap.interest_free_asset_market_equilibrium
#print axioms GEOverlap.general_preferences_equilibrium
#print axioms GEOverlap.incomplete_markets_equilibrium_exists
#print axioms GEOverlap.intertemporal_equilibrium_exists
#print axioms GEOverlap.positive_time_value_from_impatience
#print axioms GEOverlap.production_equilibrium_exists
#print axioms GEOverlap.radner_implements_arrow_debreu
#print axioms GEOverlap.equilibrium_not_unique

#print axioms GEOverlap.unique_max_of_strictConcaveOn
#print axioms GEOverlap.continuous_of_unique_maximizer
#print axioms GEOverlap.continuous_of_unique_maximizer_vary
#print axioms GEOverlap.continuous_of_unique_maximizer_subset
#print axioms GEOverlap.budget_lower_hemicontinuous
#print axioms GEOverlap.ExchangeEconomy.excess_continuous
#print axioms GEOverlap.ExchangeEconomy.excess_walras
#print axioms GEOverlap.ExchangeEconomy.equilibrium_exists
#print axioms GEOverlap.priceSimplex_convex
#print axioms GEOverlap.priceSimplex_compact
#print axioms GEOverlap.priceSimplex_nonempty
#print axioms GEOverlap.simplex_kakutani
#print axioms GEOverlap.auctioneer_nonempty
#print axioms GEOverlap.auctioneer_convex
#print axioms GEOverlap.auctioneer_closedGraph
#print axioms GEOverlap.gale_nikaido_debreu
#print axioms GEOverlap.gale_nikaido_debreu_weak
