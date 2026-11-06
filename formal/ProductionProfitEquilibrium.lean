import GEOverlap

/-!
Stage 230 (draft): the simultaneous production–price fixed point with distributed profit.

The accepted `GEOverlap.production_equilibrium_exists` handles constant-returns production
(net supply `η` earns zero profit at every price). This generalizes it to profit-bearing
production: `η` may earn positive profit `p·η(p)`, provided consumer excess demand `z`
carries that profit back as income so aggregate budgets balance, `p·z(p) = p·η(p)` at
every price. That single budget-balance condition encodes the simultaneity — profit from
the firms' choice `η` feeds the households' demand `z` — and Gale–Nikaido–Debreu (the
sealed Kakutani fixed point) delivers one joint clearing price.
-/

noncomputable section
open scoped BigOperators
open GEOverlap

namespace ProductionProfit

/-- **Simultaneous production–price fixed point with distributed profit.** Given
continuous aggregate consumer excess demand `z` and firm net supply `η` whose values
balance in the sense `p·z(p) = p·η(p)` at every price (profit is fully distributed to
households and spent), there is a price at which consumer excess demand is met by
production in every market. -/
theorem production_equilibrium_with_profit {S : Type*} [Fintype S] [Nonempty S]
    (z η : priceSimplex S → (S → ℝ)) (hz : Continuous z) (hη : Continuous η)
    (budgetBalance : ∀ p : priceSimplex S,
      ∑ s, (p : S → ℝ) s * z p s = ∑ s, (p : S → ℝ) s * η p s) :
    ∃ p : priceSimplex S, ∀ s, z p s ≤ η p s := by
  obtain ⟨p, hp⟩ := gale_nikaido_debreu (fun p => z p - η p) (hz.sub hη)
    (fun p => by
      have h : ∑ s, (p : S → ℝ) s * (z p - η p) s
             = ∑ s, (p : S → ℝ) s * z p s - ∑ s, (p : S → ℝ) s * η p s := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun s _ => by rw [Pi.sub_apply]; ring)
      rw [h, budgetBalance p]; ring)
  exact ⟨p, fun s => by have hps := hp s; simp only [Pi.sub_apply] at hps; linarith⟩

/-- The accepted constant-returns production equilibrium is the special case: separate
Walras (`p·z=0`) and zero-profit (`p·η=0`) imply budget balance. So the profit version
strictly subsumes it. -/
theorem subsumes_constant_returns {S : Type*} [Fintype S] [Nonempty S]
    (z η : priceSimplex S → (S → ℝ)) (hz : Continuous z) (hη : Continuous η)
    (walras : ∀ p : priceSimplex S, ∑ s, (p : S → ℝ) s * z p s = 0)
    (zeroProfit : ∀ p : priceSimplex S, ∑ s, (p : S → ℝ) s * η p s = 0) :
    ∃ p : priceSimplex S, ∀ s, z p s ≤ η p s :=
  production_equilibrium_with_profit z η hz hη
    (fun p => by rw [walras p, zeroProfit p])

/-- **Micro-foundation of the budget-balance condition (Stage 230).** The condition
`p·z = p·η` is not assumed — it is derived. Given household endowments `ω`, demand
functions `x` each exhausting its budget *including* its distributed profit income
`θ_h·(p·η(p))` (household-level Walras' law), and ownership shares summing to one, the
aggregate excess demand `z = ∑ₕ x − ∑ₕ ω` and firm net supply `η` satisfy budget balance;
so `production_equilibrium_with_profit` delivers a clearing price at which aggregate
excess demand is met by production. This closes the "where does `p·z = p·η` come from"
gap for the profit-bearing fixed point: it comes from profit-maximizing firms whose
profit is fully distributed to budget-exhausting owners. -/
theorem micro_founded_production_equilibrium
    {H S : Type*} [Fintype H] [Fintype S] [Nonempty S]
    (ω : H → S → ℝ) (x : H → priceSimplex S → (S → ℝ)) (η : priceSimplex S → (S → ℝ))
    (θ : H → ℝ)
    (hz : Continuous fun p : priceSimplex S => (fun s => (∑ h, x h p s) - (∑ h, ω h s)))
    (hη : Continuous η) (hθ : ∑ h, θ h = 1)
    (hbudget : ∀ (p : priceSimplex S) (h : H),
      ∑ s, (p : S → ℝ) s * x h p s
        = (∑ s, (p : S → ℝ) s * ω h s) + θ h * ∑ s, (p : S → ℝ) s * η p s) :
    ∃ p : priceSimplex S, ∀ s, (∑ h, x h p s) - (∑ h, ω h s) ≤ η p s := by
  refine production_equilibrium_with_profit
    (fun p => fun s => (∑ h, x h p s) - (∑ h, ω h s)) η hz hη ?_
  intro p
  calc ∑ s, (p : S → ℝ) s * ((∑ h, x h p s) - (∑ h, ω h s))
      = ∑ s, ∑ h, ((p : S → ℝ) s * x h p s - (p : S → ℝ) s * ω h s) := by
        apply Finset.sum_congr rfl; intro s _
        rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    _ = ∑ h, ∑ s, ((p : S → ℝ) s * x h p s - (p : S → ℝ) s * ω h s) := Finset.sum_comm
    _ = ∑ h, ((∑ s, (p : S → ℝ) s * x h p s) - (∑ s, (p : S → ℝ) s * ω h s)) := by
        apply Finset.sum_congr rfl; intro h _; rw [Finset.sum_sub_distrib]
    _ = ∑ h, θ h * ∑ s, (p : S → ℝ) s * η p s := by
        apply Finset.sum_congr rfl; intro h _; rw [hbudget p h]; ring
    _ = (∑ h, θ h) * ∑ s, (p : S → ℝ) s * η p s := by rw [Finset.sum_mul]
    _ = ∑ s, (p : S → ℝ) s * η p s := by rw [hθ, one_mul]

end ProductionProfit

#print axioms ProductionProfit.production_equilibrium_with_profit
#print axioms ProductionProfit.subsumes_constant_returns
#print axioms ProductionProfit.micro_founded_production_equilibrium
