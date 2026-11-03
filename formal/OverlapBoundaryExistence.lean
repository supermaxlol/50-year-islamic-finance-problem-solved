import OverlapBoundaryTangent
import CRRAOwnershipLimit

noncomputable section
open scoped BigOperators Topology
open Filter Set OwnershipCRRA OwnershipMarginal OwnershipUnfloored OwnershipPositive
open OwnershipSupported OverlapLocal OverlapPrimitive

namespace OverlapBoundary
variable {H J S : Type*} [Fintype H] [Fintype J] [Fintype S]

omit [Fintype S] in
theorem supply_positive_near_zero (supply : J → ℝ) (hs : ∀ j, 0 < supply j) :
    ∀ᶠ v : PrimitiveShock H J S in 𝓝 0, ∀ j, 0 < assetSupply supply v j := by
  apply Filter.eventually_all.mpr
  intro j
  have hc : Continuous (fun v : PrimitiveShock H J S => assetSupply supply v j) := by
    unfold assetSupply
    fun_prop
  exact hc.continuousAt.eventually (Ioi_mem_nhds (by simpa [assetSupply] using hs j))

theorem boundary_changed_economy_exists [Nonempty H]
    (D : H → Data J S) (e : H → ℝ) (a0 : H → J → ℝ) (supply : J → ℝ)
    (hstock : ∀ j, ∑ i, a0 i j=supply j) (hs : ∀ j, 0 < supply j) :
    ∀ᶠ v in 𝓝 0, ∀ h : Admissible D e a0 v,
      ∃ q c a, IsEquilibrium (changedData D e a0 v h) (currentResources e v)
        (initialPortfolio a0 v) (assetSupply supply v) q c a := by
  filter_upwards [supply_positive_near_zero (H := H) (S := S) supply hs] with v hv
  intro h
  exact OwnershipLimit.nonnegative_initial_ownership_equilibrium
    (changedData D e a0 v h) (currentResources e v) (initialPortfolio a0 v) (assetSupply supply v)
    (fun i => h.1.1.1 i) h.2.1 hv (inventory_consistency a0 supply hstock v)

theorem boundary_existence_and_all_equilibrium_stability [Nonempty H]
    (D : H → Data J S) (e : H → ℝ) (a0 : H → J → ℝ) (supply qstar : J → ℝ)
    (he : ∀ i, 0 < e i) (ha0 : ∀ i j, 0 ≤ a0 i j)
    (hstock : ∀ j, ∑ i, a0 i j=supply j) (hs : ∀ j, 0 < supply j)
    (hsupport : SupportsInitial D e a0 qstar)
    (U : Set (PrimitiveShock H J S × MarketState H J)) (hU : U ∈ 𝓝 (0,(qstar,a0))) :
    ∀ᶠ v in 𝓝 0, ∀ h : Admissible D e a0 v,
      (∃ q c a, IsEquilibrium (changedData D e a0 v h) (currentResources e v)
        (initialPortfolio a0 v) (assetSupply supply v) q c a ∧ (v,(q,a)) ∈ U) ∧
      (∀ q c a, IsEquilibrium (changedData D e a0 v h) (currentResources e v)
        (initialPortfolio a0 v) (assetSupply supply v) q c a → (v,(q,a)) ∈ U) := by
  filter_upwards [boundary_changed_economy_exists D e a0 supply hstock hs,
    all_actual_equilibria_near_boundary_reference D e a0 supply qstar he ha0 hstock hs hsupport U hU]
    with v hv hn
  intro h
  obtain ⟨q,c,a,hEq⟩ := hv h
  exact ⟨⟨q,c,a,hEq,hn h q c a hEq⟩,hn h⟩

namespace WeakCornerControl

def e (_ : Fin 2) : ℝ := 10
def receipt (i : Fin 2) (s : Fin 4) : ℝ :=
  consumption (CornerControl.D i) (CornerControl.initial i) s
def weight (i : Fin 2) (s : Fin 4) : ℝ :=
  ((10 : ℝ)^(CornerControl.gammaNat i))⁻¹ *
    (receipt i s)^(CornerControl.gammaNat i)*InteriorControl.baseMass s/11
def D (i : Fin 2) : Data (Fin 2) (Fin 4) :=
  { CornerControl.D i with
    weight := weight i
    weight_pos := by
      intro s
      fin_cases i <;> fin_cases s <;>
        norm_num [weight,receipt,consumption,CornerControl.D,CornerControl.initial,
          OwnershipMultiplicity.payoff,InteriorControl.baseMass,CornerControl.gammaNat,
          Fin.sum_univ_succ] }

theorem supported_reference :
    SupportsInitial D e CornerControl.initial CornerControl.qstar := by
  intro i j
  simp only [marginal,D,CornerControl.D,OwnershipMultiplicity.negative_nat_power]
  fin_cases i <;> fin_cases j <;>
    norm_num [consumption,D,CornerControl.D,CornerControl.initial,e,CornerControl.qstar,
      OwnershipMultiplicity.payoff,weight,receipt,InteriorControl.baseMass,
      CornerControl.gammaNat,Fin.sum_univ_succ]

theorem actual_weak_boundary_market :
    IsEquilibrium D e CornerControl.initial CornerControl.supply CornerControl.qstar
      e CornerControl.initial ∧
    ∀ q c a, IsEquilibrium D e CornerControl.initial CornerControl.supply q c a →
      q=CornerControl.qstar ∧ c=e ∧ a=CornerControl.initial := by
  apply unique_supported_equilibrium D e CornerControl.initial
    CornerControl.supply CornerControl.qstar
  · intro i; norm_num [e]
  · exact CornerControl.primitive_conditions.2.1
  · exact CornerControl.primitive_conditions.2.2.1
  · exact CornerControl.primitive_conditions.2.2.2.1
  · exact CornerControl.primitive_conditions.2.2.2.2
  · exact supported_reference

theorem two_simultaneous_weak_corners :
    CornerControl.initial 0 1=0 ∧
    OverlapBoundaryTangent.referenceGap D e CornerControl.initial CornerControl.qstar 0 1=0 ∧
    CornerControl.initial 1 0=0 ∧
    OverlapBoundaryTangent.referenceGap D e CornerControl.initial CornerControl.qstar 1 0=0 := by
  simp only [OverlapBoundaryTangent.referenceGap,marginal,D,CornerControl.D,
    OwnershipMultiplicity.negative_nat_power]
  norm_num [consumption,D,CornerControl.D,CornerControl.initial,e,CornerControl.qstar,
    OwnershipMultiplicity.payoff,weight,receipt,InteriorControl.baseMass,
    CornerControl.gammaNat,Fin.sum_univ_succ]

theorem waiting_weight_compatibility :
    (∑ _ : Fin 4, (1/4 : ℝ))=1 ∧
    ∀ i s, 0 < 4*weight i s ∧ 4*weight i s < 1 ∧
      weight i s=(1/4 : ℝ)*(4*weight i s) := by
  constructor
  · norm_num [Fin.sum_univ_succ]
  · intro i s
    fin_cases i <;> fin_cases s <;>
      norm_num [weight,receipt,consumption,CornerControl.D,CornerControl.initial,
        OwnershipMultiplicity.payoff,InteriorControl.baseMass,CornerControl.gammaNat,
        Fin.sum_univ_succ]

end WeakCornerControl
end OverlapBoundary

#print axioms OverlapBoundary.supply_positive_near_zero
#print axioms OverlapBoundary.boundary_changed_economy_exists
#print axioms OverlapBoundary.boundary_existence_and_all_equilibrium_stability
#print axioms OverlapBoundary.WeakCornerControl.supported_reference
#print axioms OverlapBoundary.WeakCornerControl.actual_weak_boundary_market
#print axioms OverlapBoundary.WeakCornerControl.two_simultaneous_weak_corners
#print axioms OverlapBoundary.WeakCornerControl.waiting_weight_compatibility
