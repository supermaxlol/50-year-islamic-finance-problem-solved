import PrimaryCRRAFormation

/-!
Stage 229 (draft): multiple simultaneous primary formations.

The accepted `PrimaryCRRAFormation` proves single-issue voluntary formation. Here a
family of issues `j : J`, each with its own plan `P j` and economy `E j`, forms
simultaneously. We prove: all issues form iff each meets its own floor-demand
condition; if each does, a joint family of equilibria exists; and if any single
issue falls short, no all-form outcome exists.

Boundary: this is the INDEPENDENT case (separate economies per issue). The
interacting shared-budget case is the accepted multi-asset certificate market
(whose joint clearing is already proved); joint formation WITH cross-issue budget
interaction is a further target, not claimed here.
-/

noncomputable section
open scoped BigOperators
open PrimaryCRRAFormation VoluntaryPrimaryMarket

namespace SimultaneousFormation

variable {I S : Type*} [Fintype I] [Fintype S]

/-- If every issue's demand at its floor covers its supply, all issues form
simultaneously: a joint family of price/allocation equilibria exists. -/
theorem simultaneous_formation_exists {J : Type*}
    (P : J → Plan) (E : J → Economy I S)
    (hc : ∀ j, supply (P j) ≤ aggregate (E j) (floorPrice (P j))) :
    ∃ (q : J → ℝ) (a : J → I → ℝ), ∀ j, Equilibrium (P j) (E j) (q j) (a j) := by
  choose q a hqa using fun j => voluntary_formation_exists (P j) (E j) (hc j)
  exact ⟨q, a, hqa⟩

/-- All issues form simultaneously **iff** each meets its own cost/demand floor. -/
theorem simultaneous_formation_iff {J : Type*}
    (P : J → Plan) (E : J → Economy I S) :
    (∀ j, ∃ q a, Equilibrium (P j) (E j) q a) ↔
      (∀ j, supply (P j) ≤ aggregate (E j) (floorPrice (P j))) :=
  forall_congr' (fun j => formation_iff_cost_demand (P j) (E j))

/-- If a single issue's floor demand falls short of its supply, there is no
all-issues-form outcome. Formation is selective per issue. -/
theorem simultaneous_no_formation_of_shortfall {J : Type*}
    (P : J → Plan) (E : J → Economy I S) (j0 : J)
    (hj0 : aggregate (E j0) (floorPrice (P j0)) < supply (P j0)) :
    ¬ ∃ (q : J → ℝ) (a : J → I → ℝ), ∀ j, Equilibrium (P j) (E j) (q j) (a j) := by
  rintro ⟨q, a, h⟩
  exact no_funded_formation (P j0) (E j0) hj0 ⟨q j0, a j0, h j0⟩

end SimultaneousFormation

#print axioms SimultaneousFormation.simultaneous_formation_exists
#print axioms SimultaneousFormation.simultaneous_formation_iff
#print axioms SimultaneousFormation.simultaneous_no_formation_of_shortfall
