import GEOverlap

/-!
Stage 245 (draft): a reusable `ProductionEconomy` structure (upstream ④).

Bundles consumer excess demand `z` and aggregate net production `η` with the production
Walras law (consumer spending bounded by production value), and proves a clearing price
exists by folding `z − η` into the weak Gale–Nikaido–Debreu engine. This generalizes the
constant-returns `production_equilibrium_exists` into a structure that any production model
(decreasing returns, multiple firms, strictly-convex `Y`, the profit-max scale firm) can
instantiate.
-/

noncomputable section
open scoped BigOperators
open GEOverlap

/-- A production economy on goods `S`: continuous consumer excess demand `z`, continuous
aggregate net production `η`, and the production Walras law — at every price, the value of
consumer excess demand does not exceed the value of net production. -/
structure ProductionEconomy (S : Type*) [Fintype S] where
  z : priceSimplex S → (S → ℝ)
  η : priceSimplex S → (S → ℝ)
  z_cont : Continuous z
  η_cont : Continuous η
  walras : ∀ p : priceSimplex S,
    (∑ s, (p : S → ℝ) s * z p s) ≤ (∑ s, (p : S → ℝ) s * η p s)

namespace ProductionEconomy

variable {S : Type*} [Fintype S]

/-- Net market excess demand: consumer excess demand minus net production. -/
def netExcess (E : ProductionEconomy S) (p : priceSimplex S) : S → ℝ :=
  fun s => E.z p s - E.η p s

theorem netExcess_continuous (E : ProductionEconomy S) : Continuous E.netExcess := by
  refine continuous_pi (fun s => ?_)
  exact ((continuous_apply s).comp E.z_cont).sub ((continuous_apply s).comp E.η_cont)

theorem netExcess_walras (E : ProductionEconomy S) (p : priceSimplex S) :
    (∑ s, (p : S → ℝ) s * E.netExcess p s) ≤ 0 := by
  have h : ∑ s, (p : S → ℝ) s * E.netExcess p s
      = (∑ s, (p : S → ℝ) s * E.z p s) - (∑ s, (p : S → ℝ) s * E.η p s) := by
    simp only [netExcess]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun s _ => by ring)
  rw [h]; linarith [E.walras p]

/-- **Production equilibrium.** Any `ProductionEconomy` has a clearing price: consumer excess
demand does not exceed net production in any good. -/
theorem equilibrium_exists [Nonempty S] (E : ProductionEconomy S) :
    ∃ p : priceSimplex S, ∀ s, E.z p s - E.η p s ≤ 0 := by
  obtain ⟨p, hp⟩ :=
    gale_nikaido_debreu_weak E.netExcess E.netExcess_continuous E.netExcess_walras
  exact ⟨p, fun s => hp s⟩

end ProductionEconomy

#print axioms ProductionEconomy.equilibrium_exists
