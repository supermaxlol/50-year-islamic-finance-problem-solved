import GEOverlap

/-!
Stage 233 (draft): excess-demand realizability (SMD, function level).

Every continuous excess-demand map `z` on the price simplex obeying Walras' law is the
aggregate excess demand of an explicit exchange economy — a single household with demand
`ω + z(p)` about any endowment `ω` — and hence has a free-disposal clearing price. The GND
engine imposes NO restriction on aggregate excess demand beyond continuity + Walras: the
practical content of Sonnenschein–Mantel–Debreu.

Boundary: the realizing demand is a continuous, budget-balanced FUNCTION, not derived from
utility maximization, and the `ExchangeEconomy` structure imposes no consumption-set
nonnegativity. Full SMD with RATIONAL (utility-maximizing) households additionally requires
demand constructed from preferences via the maximum theorem — a separate step.
-/

noncomputable section
open scoped BigOperators
open GEOverlap

namespace SMDRealization

variable {S : Type*} [Fintype S]

/-- The single-household economy whose demand is `ω + z`; its aggregate excess demand is
exactly `z` whenever `z` obeys Walras. -/
def realizingEconomy (z : priceSimplex S → (S → ℝ)) (hz : Continuous z)
    (walras : ∀ p : priceSimplex S, ∑ s, (p : S → ℝ) s * z p s = 0) (ω : S → ℝ) :
    ExchangeEconomy (Fin 1) S where
  demand := fun _ p => fun s => ω s + z p s
  endowment := fun _ => ω
  demand_continuous := fun _ => by
    refine continuous_pi (fun s => ?_)
    exact continuous_const.add ((continuous_apply s).comp hz)
  budget := fun _ p => by
    have h : ∑ s, (p : S → ℝ) s * (ω s + z p s)
        = (∑ s, (p : S → ℝ) s * ω s) + ∑ s, (p : S → ℝ) s * z p s := by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl (fun s _ => by ring)
    rw [h, walras p, add_zero]

/-- The construction realizes `z` exactly: its aggregate excess demand equals `z` at every
price. -/
theorem realizes_excess (z : priceSimplex S → (S → ℝ)) (hz : Continuous z)
    (walras : ∀ p : priceSimplex S, ∑ s, (p : S → ℝ) s * z p s = 0) (ω : S → ℝ)
    (p : priceSimplex S) :
    (realizingEconomy z hz walras ω).excess p = z p := by
  funext s
  simp only [ExchangeEconomy.excess, realizingEconomy, Fin.sum_univ_one]
  ring

/-- **SMD realizability + equilibrium.** Any continuous Walras excess demand is realized by
an explicit exchange economy and has a free-disposal clearing price. -/
theorem smd_realization_equilibrium [Nonempty S] (z : priceSimplex S → (S → ℝ))
    (hz : Continuous z)
    (walras : ∀ p : priceSimplex S, ∑ s, (p : S → ℝ) s * z p s = 0) (ω : S → ℝ) :
    ∃ p : priceSimplex S, ∀ s, z p s ≤ 0 := by
  obtain ⟨p, hp⟩ := (realizingEconomy z hz walras ω).equilibrium_exists
  refine ⟨p, fun s => ?_⟩
  rw [← realizes_excess z hz walras ω p]
  exact hp s

end SMDRealization

#print axioms SMDRealization.realizes_excess
#print axioms SMDRealization.smd_realization_equilibrium
