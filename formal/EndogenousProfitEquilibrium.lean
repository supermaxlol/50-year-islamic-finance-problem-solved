import EnergyComputeOwnership

/-!
Stage 228 (full connection): endogenous profit-maximizing production joined to a
clearing competitive equilibrium with profit income in household budgets.

The firm chooses its capacity from a feasible menu to maximize economic profit; the
maximized (nonnegative) profit is distributed to owners in proportion to shares and
enters each household's current resources; and the accepted certificate-market
existence engine then yields a competitive equilibrium that clears, now with those
profit-augmented budgets.

Boundary. This is a sequential composition — the firm's profit-maximizing choice,
then market clearing given the distributed profit income — not a single simultaneous
fixed point over production and prices. Profit is modelled as date-0 income added to
resources; it is kept distinct from the asset receipts the market itself prices. The
feasible menu is finite and a costless zero-output fallback is assumed for the
nonnegativity of profit. Not increasing returns, not endogenous entry, not a general
production economy.
-/

noncomputable section
open scoped BigOperators
open OwnershipCRRA OwnershipPositive OwnershipCertificates EnergyComputeOwnership

namespace EndogenousProfit

/-- Economic profit of a chosen capacity at service price `ρ` net of capacity cost. -/
def profit (ρ : ℝ) (cost : Capacity → ℝ) (k : Capacity) : ℝ :=
  ρ * output k - cost k

/-- The firm's profit-maximizing capacity choice exists over any nonempty menu. -/
theorem exists_profit_max (ρ : ℝ) (cost : Capacity → ℝ)
    (menu : Finset Capacity) (hne : menu.Nonempty) :
    ∃ k ∈ menu, ∀ k' ∈ menu, profit ρ cost k' ≤ profit ρ cost k := by
  obtain ⟨k, hk, hk_eq⟩ := Finset.exists_mem_eq_sup' hne (profit ρ cost)
  refine ⟨k, hk, fun k' hk' => ?_⟩
  calc profit ρ cost k' ≤ menu.sup' hne (profit ρ cost) := Finset.le_sup' _ hk'
    _ = profit ρ cost k := hk_eq

/-- Maximized profit is nonnegative given a costless zero-output fallback. -/
theorem profit_max_nonneg (ρ : ℝ) (cost : Capacity → ℝ)
    (menu : Finset Capacity) (hne : menu.Nonempty)
    (k0 : Capacity) (hk0 : k0 ∈ menu) (hzero : output k0 = 0) (hcost0 : cost k0 ≤ 0) :
    ∃ k ∈ menu, (∀ k' ∈ menu, profit ρ cost k' ≤ profit ρ cost k) ∧
      0 ≤ profit ρ cost k := by
  obtain ⟨k, hk, hmax⟩ := exists_profit_max ρ cost menu hne
  refine ⟨k, hk, hmax, ?_⟩
  have h0 : (0 : ℝ) ≤ profit ρ cost k0 := by
    have hval : profit ρ cost k0 = -cost k0 := by
      unfold profit; rw [hzero, mul_zero, zero_sub]
    rw [hval]; linarith
  exact le_trans h0 (hmax k0 hk0)

section Equilibrium
variable {H J S : Type*} [Fintype H] [Fintype J] [Fintype S] [Nonempty H]

/-- **Profit income in the budget preserves equilibrium.** For any nonnegative profit
level distributed by nonnegative ownership shares, the certificate market still clears
with each household's resources augmented by its profit share. -/
theorem profit_augmented_equilibrium_exists
    (D : H → Data J S) (p : S → J → Plan)
    (hrank : Function.Injective (fun a : J → ℝ => fun s => ∑ j, receipt (p s j) * a j))
    (N : Denomination J)
    (e : H → ℝ) (a0 : H → J → ℝ) (supply : J → ℝ)
    (theta : H → ℝ) (profitStar : ℝ)
    (he : ∀ i, 0 < e i) (ha0 : ∀ i j, 0 ≤ a0 i j)
    (hs : ∀ j, 0 < supply j) (hstock : ∀ j, ∑ i, a0 i j = supply j)
    (htheta : ∀ i, 0 ≤ theta i) (hprofit : 0 ≤ profitStar) :
    ∃ r c h, IsEquilibrium (fun i => certificateData (marketData (D i) p hrank) N)
      (fun i => e i + theta i * profitStar) (fun i => encode N (a0 i))
      (encode N supply) r c h :=
  actual_compute_certificate_market_exists D p hrank N
    (fun i => e i + theta i * profitStar) a0 supply
    (fun i => by have h1 := he i
                 have h2 := mul_nonneg (htheta i) hprofit
                 linarith)
    ha0 hs hstock

/-- **Full #1: endogenous production to a clearing equilibrium.** The firm chooses the
profit-maximizing capacity from the menu; its maximized profit is nonnegative; and a
competitive equilibrium exists in which that profit, distributed to owners by shares,
augments household budgets, with every market clearing. -/
theorem endogenous_production_equilibrium
    (D : H → Data J S) (p : S → J → Plan)
    (hrank : Function.Injective (fun a : J → ℝ => fun s => ∑ j, receipt (p s j) * a j))
    (N : Denomination J)
    (e : H → ℝ) (a0 : H → J → ℝ) (supply : J → ℝ) (theta : H → ℝ)
    (ρ : ℝ) (cost : Capacity → ℝ) (menu : Finset Capacity) (hne : menu.Nonempty)
    (k0 : Capacity) (hk0 : k0 ∈ menu) (hzero : output k0 = 0) (hcost0 : cost k0 ≤ 0)
    (he : ∀ i, 0 < e i) (ha0 : ∀ i j, 0 ≤ a0 i j)
    (hs : ∀ j, 0 < supply j) (hstock : ∀ j, ∑ i, a0 i j = supply j)
    (htheta : ∀ i, 0 ≤ theta i) :
    ∃ kstar ∈ menu, (∀ k' ∈ menu, profit ρ cost k' ≤ profit ρ cost kstar) ∧
      ∃ r c h, IsEquilibrium (fun i => certificateData (marketData (D i) p hrank) N)
        (fun i => e i + theta i * profit ρ cost kstar) (fun i => encode N (a0 i))
        (encode N supply) r c h := by
  obtain ⟨kstar, hmem, hmax, hpos⟩ := profit_max_nonneg ρ cost menu hne k0 hk0 hzero hcost0
  exact ⟨kstar, hmem, hmax,
    profit_augmented_equilibrium_exists D p hrank N e a0 supply theta
      (profit ρ cost kstar) he ha0 hs hstock htheta hpos⟩

/-- **#4 — the surplus floor (aggregate form).** In the endogenous-production
equilibrium, aggregate consumption exceeds the baseline aggregate endowment by exactly
the firm's maximized profit `π*`: the production surplus is fully realized as additional
consumption, carried to households through their profit-augmented budgets. With
ownership shares summing to one, the surplus `π*` is distributed as the shares `θ_i·π*`
in each owner's budget. This is the formal content of "owning production pays you the
surplus." It does not claim a per-household consumption lower bound beyond the accepted
Stage-188 floor, nor that the distribution is equitable. -/
theorem surplus_raises_aggregate_consumption
    (D : H → Data J S) (p : S → J → Plan)
    (hrank : Function.Injective (fun a : J → ℝ => fun s => ∑ j, receipt (p s j) * a j))
    (N : Denomination J)
    (e : H → ℝ) (a0 : H → J → ℝ) (supply : J → ℝ) (theta : H → ℝ)
    (ρ : ℝ) (cost : Capacity → ℝ) (menu : Finset Capacity) (hne : menu.Nonempty)
    (k0 : Capacity) (hk0 : k0 ∈ menu) (hzero : output k0 = 0) (hcost0 : cost k0 ≤ 0)
    (he : ∀ i, 0 < e i) (ha0 : ∀ i j, 0 ≤ a0 i j)
    (hs : ∀ j, 0 < supply j) (hstock : ∀ j, ∑ i, a0 i j = supply j)
    (htheta : ∀ i, 0 ≤ theta i) (hthetasum : ∑ i, theta i = 1) :
    ∃ kstar ∈ menu, (∀ k' ∈ menu, profit ρ cost k' ≤ profit ρ cost kstar) ∧
      ∃ r c h, IsEquilibrium (fun i => certificateData (marketData (D i) p hrank) N)
          (fun i => e i + theta i * profit ρ cost kstar) (fun i => encode N (a0 i))
          (encode N supply) r c h ∧
        (∑ i, c i) = (∑ i, e i) + profit ρ cost kstar := by
  obtain ⟨kstar, hmem, hmax, r, c, h, heq⟩ :=
    endogenous_production_equilibrium D p hrank N e a0 supply theta ρ cost menu hne
      k0 hk0 hzero hcost0 he ha0 hs hstock htheta
  refine ⟨kstar, hmem, hmax, r, c, h, heq, ?_⟩
  rw [heq.consumption_clears, Finset.sum_add_distrib]
  congr 1
  rw [← Finset.sum_mul, hthetasum, one_mul]

end Equilibrium

end EndogenousProfit

#print axioms EndogenousProfit.exists_profit_max
#print axioms EndogenousProfit.profit_max_nonneg
#print axioms EndogenousProfit.profit_augmented_equilibrium_exists
#print axioms EndogenousProfit.endogenous_production_equilibrium
#print axioms EndogenousProfit.surplus_raises_aggregate_consumption
