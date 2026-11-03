import OwnershipCertificates

/-!
One-settlement application for a supplied, funded compute operating plan.
Engineering capacities and cash-flow parameters are model inputs, not measured
telemetry. Initial enterprise formation and intermediate liquidity are not proved.
-/

noncomputable section
open scoped BigOperators
open OwnershipCRRA OwnershipPositive OwnershipCertificates

namespace EnergyComputeOwnership

structure Capacity where
  hardware : ℝ
  energy : ℝ
  energyPerUnit : ℝ
  cooling : ℝ
  network : ℝ
  demand : ℝ
  hardware_nonneg : 0 ≤ hardware
  energy_nonneg : 0 ≤ energy
  energyPerUnit_pos : 0 < energyPerUnit
  cooling_nonneg : 0 ≤ cooling
  network_nonneg : 0 ≤ network
  demand_nonneg : 0 ≤ demand

def output (k : Capacity) : ℝ :=
  min k.hardware (min (k.energy / k.energyPerUnit)
    (min k.cooling (min k.network k.demand)))

theorem output_nonnegative (k : Capacity) : 0 ≤ output k := by
  exact le_min k.hardware_nonneg (le_min
    (div_nonneg k.energy_nonneg k.energyPerUnit_pos.le)
    (le_min k.cooling_nonneg (le_min k.network_nonneg k.demand_nonneg)))

theorem output_hardware_bound (k : Capacity) : output k ≤ k.hardware :=
  min_le_left _ _

theorem output_energy_bound (k : Capacity) : output k ≤ k.energy / k.energyPerUnit :=
  le_trans (min_le_right _ _) (min_le_left _ _)

theorem output_cooling_bound (k : Capacity) : output k ≤ k.cooling :=
  le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))

theorem output_network_bound (k : Capacity) : output k ≤ k.network :=
  le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
    (le_trans (min_le_right _ _) (min_le_left _ _)))

theorem output_demand_bound (k : Capacity) : output k ≤ k.demand :=
  le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
    (le_trans (min_le_right _ _) (min_le_right _ _)))

theorem energy_use_feasible (k : Capacity) : output k * k.energyPerUnit ≤ k.energy := by
  have h := mul_le_mul_of_nonneg_right (output_energy_bound k) k.energyPerUnit_pos.le
  simpa only [div_mul_cancel₀ _ (ne_of_gt k.energyPerUnit_pos)] using h

theorem energy_bottleneck_output (k : Capacity)
    (hh : k.energy / k.energyPerUnit ≤ k.hardware)
    (hc : k.energy / k.energyPerUnit ≤ k.cooling)
    (hn : k.energy / k.energyPerUnit ≤ k.network)
    (hd : k.energy / k.energyPerUnit ≤ k.demand) :
    output k = k.energy / k.energyPerUnit := by
  unfold output
  rw [min_eq_left (le_min hc (le_min hn hd)), min_eq_right hh]

/-- Funds are already available for the modelled costs. This is a real
funding assumption, not a costless credit line or a dynamic-liquidity theorem. -/
structure Plan where
  capacity : Capacity
  servicePrice : ℝ
  workingFunds : ℝ
  operatingCost : ℝ
  salvage : ℝ
  servicePrice_nonneg : 0 ≤ servicePrice
  workingFunds_nonneg : 0 ≤ workingFunds
  operatingCost_nonneg : 0 ≤ operatingCost
  salvage_nonneg : 0 ≤ salvage
  costs_funded : operatingCost ≤ workingFunds

def receipt (p : Plan) : ℝ :=
  p.servicePrice * output p.capacity + (p.workingFunds - p.operatingCost) + p.salvage

theorem receipt_nonnegative (p : Plan) : 0 ≤ receipt p :=
  add_nonneg (add_nonneg
    (mul_nonneg p.servicePrice_nonneg (output_nonnegative p.capacity))
    (sub_nonneg.mpr p.costs_funded)) p.salvage_nonneg

theorem funded_resource_identity (p : Plan) :
    p.operatingCost + receipt p =
      p.workingFunds + p.servicePrice * output p.capacity + p.salvage := by
  unfold receipt
  ring

section Data
variable {J S : Type*} [Fintype J]

/-- Payoffs come from the plan; full rank must be checked, not presumed. -/
def marketData (D : Data J S) (p : S → J → Plan)
    (hrank : Function.Injective (fun a : J → ℝ => fun s =>
      ∑ j, receipt (p s j) * a j)) : Data J S :=
  { D with
    payoff := fun s j => receipt (p s j)
    payoff_nonneg := fun s j => receipt_nonnegative (p s j)
    payoff_injective := hrank }

theorem marketData_payoff (D : Data J S) (p : S → J → Plan)
    (hrank : Function.Injective (fun a : J → ℝ => fun s =>
      ∑ j, receipt (p s j) * a j)) (s : S) (j : J) :
    (marketData D p hrank).payoff s j = receipt (p s j) := rfl

variable [Fintype S]

theorem actual_compute_household_equivalence (D : Data J S) (p : S → J → Plan)
    (hrank : Function.Injective (fun a : J → ℝ => fun s =>
      ∑ j, receipt (p s j) * a j)) (N : Denomination J)
    (q : J → ℝ) (W c : ℝ) (h : J → ℝ) :
    HouseholdOptimal (certificateData (marketData D p hrank) N) (quote N q) W c h ↔
      HouseholdOptimal (marketData D p hrank) q W c (decode N h) :=
  household_optimization_iff (marketData D p hrank) N q W c h

end Data

section Markets
variable {H J S : Type*} [Fintype H] [Fintype J] [Fintype S]

theorem actual_compute_settlement (D : H → Data J S) (p : S → J → Plan)
    (hrank : Function.Injective (fun a : J → ℝ => fun s =>
      ∑ j, receipt (p s j) * a j)) (N : Denomination J)
    (e : H → ℝ) (a0 : H → J → ℝ) (supply r : J → ℝ)
    (c : H → ℝ) (h : H → J → ℝ)
    (hEq : IsEquilibrium (fun i => certificateData (marketData (D i) p hrank) N)
      e (fun i => encode N (a0 i)) (encode N supply) r c h) (s : S) :
    (∑ i, ∑ j, (certificateData (marketData (D i) p hrank) N).payoff s j * h i j) =
      ∑ j, receipt (p s j) * supply j :=
  equilibrium_settlement_conservation (fun i => marketData (D i) p hrank) N
    (fun s j => receipt (p s j)) (fun _ _ _ => rfl) e a0 supply r c h hEq s

variable [Nonempty H]

theorem actual_compute_certificate_market_exists (D : H → Data J S)
    (p : S → J → Plan)
    (hrank : Function.Injective (fun a : J → ℝ => fun s =>
      ∑ j, receipt (p s j) * a j)) (N : Denomination J)
    (e : H → ℝ) (a0 : H → J → ℝ) (supply : J → ℝ)
    (he : ∀ i, 0 < e i) (ha0 : ∀ i j, 0 ≤ a0 i j)
    (hs : ∀ j, 0 < supply j) (hstock : ∀ j, ∑ i, a0 i j = supply j) :
    ∃ r c h, IsEquilibrium (fun i => certificateData (marketData (D i) p hrank) N)
      e (fun i => encode N (a0 i)) (encode N supply) r c h :=
  certificate_market_exists (fun i => marketData (D i) p hrank) N
    e a0 supply he ha0 hs hstock

end Markets

def senior (available face : ℝ) : ℝ := min face available
def junior (available face : ℝ) : ℝ := available - senior available face

theorem senior_nonnegative (z d : ℝ) (hz : 0 ≤ z) (hd : 0 ≤ d) :
    0 ≤ senior z d := le_min hd hz

theorem junior_nonnegative (z d : ℝ) : 0 ≤ junior z d :=
  sub_nonneg.mpr (min_le_right _ _)

theorem waterfall_conservation (z d : ℝ) : senior z d + junior z d = z := by
  unfold junior
  ring

theorem senior_full_iff (z d : ℝ) : senior z d = d ↔ d ≤ z := min_eq_left_iff

theorem junior_as_residual (z d : ℝ) : junior z d = max 0 (z - d) := by
  by_cases h : d ≤ z
  · rw [junior, senior, min_eq_left h, max_eq_right (sub_nonneg.mpr h)]
  · have h' : z ≤ d := le_of_not_ge h
    rw [junior, senior, min_eq_right h', sub_self,
      max_eq_left (sub_nonpos.mpr h')]

def liquidation (value drop friction : ℝ) : ℝ := (1 - friction) * (1 - drop) * value

theorem liquidation_nonnegative (v d f : ℝ) (hv : 0 ≤ v) (hd : d ≤ 1) (hf : f ≤ 1) :
    0 ≤ liquidation v d f :=
  mul_nonneg (mul_nonneg (sub_nonneg.mpr hf) (sub_nonneg.mpr hd)) hv

section Allocation
variable {H : Type*} [Fintype H]

theorem ownership_allocation_conservation (z : ℝ) (alpha : H → ℝ)
    (hsum : ∑ i, alpha i = 1) : (∑ i, alpha i * z) = z := by
  rw [← Finset.sum_mul, hsum, one_mul]

end Allocation

end EnergyComputeOwnership

#print axioms EnergyComputeOwnership.output_nonnegative
#print axioms EnergyComputeOwnership.output_hardware_bound
#print axioms EnergyComputeOwnership.output_energy_bound
#print axioms EnergyComputeOwnership.output_cooling_bound
#print axioms EnergyComputeOwnership.output_network_bound
#print axioms EnergyComputeOwnership.output_demand_bound
#print axioms EnergyComputeOwnership.energy_use_feasible
#print axioms EnergyComputeOwnership.energy_bottleneck_output
#print axioms EnergyComputeOwnership.receipt_nonnegative
#print axioms EnergyComputeOwnership.funded_resource_identity
#print axioms EnergyComputeOwnership.marketData_payoff
#print axioms EnergyComputeOwnership.actual_compute_household_equivalence
#print axioms EnergyComputeOwnership.actual_compute_settlement
#print axioms EnergyComputeOwnership.actual_compute_certificate_market_exists
#print axioms EnergyComputeOwnership.senior_nonnegative
#print axioms EnergyComputeOwnership.junior_nonnegative
#print axioms EnergyComputeOwnership.waterfall_conservation
#print axioms EnergyComputeOwnership.senior_full_iff
#print axioms EnergyComputeOwnership.junior_as_residual
#print axioms EnergyComputeOwnership.liquidation_nonnegative
#print axioms EnergyComputeOwnership.ownership_allocation_conservation
