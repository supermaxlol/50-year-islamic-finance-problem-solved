import GEOverlap

/-!
Stage 231 (draft): interacting multi-issue funded formation.

`J` issues clear *jointly*: issue `j`'s excess demand `z p j` depends on the whole price
vector `p` (shared household budgets, cross-price interaction). Gale–Nikaido–Debreu (the
sealed Kakutani fixed point) gives a joint clearing price. The new content is **funding
with interaction**: under a floor-demand condition — demand strictly exceeds supply
whenever ANY issue's price sits at or below its floor (the vector analog of the accepted
single-issue `supply ≤ aggregate(floor)`) — the joint clearing price has every issue's
price strictly above its floor, so every interacting issue is funded/formed at once.

Boundary. `z` is a given continuous joint excess-demand obeying Walras; constructing it
from primitive household optimization with shared budgets, and deriving the floor-demand
condition from deeper primitives (endowments/preferences), is the further step. This is a
SUFFICIENT condition for funded formation (existence), not an iff, and free-disposal
clearing (`z ≤ 0`) as in GND.
-/

noncomputable section
open scoped BigOperators
open GEOverlap

namespace InteractingFormation

/-- **Interacting multi-issue funded formation.** Joint clearing (GND) plus a
floor-demand condition yields a clearing price at which every interacting issue's price
strictly exceeds its floor — all issues funded simultaneously. -/
theorem interacting_funded_formation {J : Type*} [Fintype J] [Nonempty J]
    (z : priceSimplex J → (J → ℝ)) (hz : Continuous z)
    (walras : ∀ p : priceSimplex J, ∑ j, (p : J → ℝ) j * z p j = 0)
    (floor : J → ℝ)
    (floorDemand : ∀ p : priceSimplex J, ∀ j, (p : J → ℝ) j ≤ floor j → 0 < z p j) :
    ∃ p : priceSimplex J, (∀ j, z p j ≤ 0) ∧ (∀ j, floor j < (p : J → ℝ) j) := by
  obtain ⟨p, hp⟩ := gale_nikaido_debreu z hz walras
  refine ⟨p, hp, fun j => ?_⟩
  by_contra hle
  have hle' : (p : J → ℝ) j ≤ floor j := not_lt.mp hle
  have hpos := floorDemand p j hle'
  have hnp := hp j
  linarith

/-- With nonnegative floors, the funded interacting equilibrium is interior: every issue
is actively priced (`0 < p j`), none pushed to a zero price. -/
theorem interacting_formation_interior {J : Type*} [Fintype J] [Nonempty J]
    (z : priceSimplex J → (J → ℝ)) (hz : Continuous z)
    (walras : ∀ p : priceSimplex J, ∑ j, (p : J → ℝ) j * z p j = 0)
    (floor : J → ℝ) (hfloor_nonneg : ∀ j, 0 ≤ floor j)
    (floorDemand : ∀ p : priceSimplex J, ∀ j, (p : J → ℝ) j ≤ floor j → 0 < z p j) :
    ∃ p : priceSimplex J, (∀ j, z p j ≤ 0) ∧ (∀ j, 0 < (p : J → ℝ) j) := by
  obtain ⟨p, hclear, hfund⟩ :=
    interacting_funded_formation z hz walras floor floorDemand
  exact ⟨p, hclear, fun j => lt_of_le_of_lt (hfloor_nonneg j) (hfund j)⟩

end InteractingFormation

#print axioms InteractingFormation.interacting_funded_formation
#print axioms InteractingFormation.interacting_formation_interior
