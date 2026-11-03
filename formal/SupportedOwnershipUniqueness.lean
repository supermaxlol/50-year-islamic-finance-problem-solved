import OwnershipStrictSupport
import CRRAUniformEquilibriumBounds
import OverlapMultipleEquilibria

/-!
Global price and allocation uniqueness under primitive support of initial
ownership. This is a no-trade-reference class, not an unconditional theorem
for the existence class or a theorem for nearby trading equilibria.
-/

noncomputable section
open scoped BigOperators
open OwnershipCRRA OwnershipMarginal OwnershipUnfloored OwnershipPositive
open OwnershipSufficiency OwnershipStrictSupport

namespace OwnershipSupported

variable {H J S : Type*} [Fintype H] [Fintype J] [Fintype S]

def SupportsInitial (D : H → Data J S) (e : H → ℝ)
    (a0 : H → J → ℝ) (qstar : J → ℝ) : Prop :=
  ∀ i j, marginal (D i) (a0 i) j ≤ qstar j*(e i)^(-(D i).gamma) ∧
    a0 i j*(qstar j*(e i)^(-(D i).gamma)-marginal (D i) (a0 i) j)=0

theorem reference_equilibrium (D : H → Data J S) (e : H → ℝ)
    (a0 : H → J → ℝ) (supply qstar : J → ℝ)
    (he : ∀ i, 0 < e i) (ha0 : ∀ i j, 0 ≤ a0 i j)
    (hstock : ∀ j, ∑ i, a0 i j=supply j) (hq : ∀ j, 0 < qstar j)
    (hsupport : SupportsInitial D e a0 qstar) :
    IsEquilibrium D e a0 supply qstar e a0 := by
  refine ⟨hq,he,ha0,?_,?_,rfl,hstock,hsupport⟩
  · intro i; exact le_rfl
  · intro i
    exact global_optimality_of_corner_conditions (D i) qstar (a0 i) (e i)
      (e i+∑ j, qstar j*a0 i j) (he i) (ha0 i) rfl (hsupport i)

theorem aggregate_cost_equality (q : J → ℝ) (c d : H → ℝ)
    (a b : H → J → ℝ) (hc : ∑ i, c i=∑ i, d i)
    (ha : ∀ j, ∑ i, a i j=∑ i, b i j) :
    (∑ i, (c i+∑ j, q j*a i j)) = ∑ i, (d i+∑ j, q j*b i j) := by
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,hc]
  congr 1
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.mul_sum,← Finset.mul_sum,ha j]

theorem allocation_unique (D : H → Data J S) (e : H → ℝ)
    (a0 : H → J → ℝ) (supply qstar q : J → ℝ)
    (c : H → ℝ) (a : H → J → ℝ)
    (he : ∀ i, 0 < e i) (ha0 : ∀ i j, 0 ≤ a0 i j)
    (hstock : ∀ j, ∑ i, a0 i j=supply j)
    (hsupport : SupportsInitial D e a0 qstar)
    (hEq : IsEquilibrium D e a0 supply q c a) : c=e ∧ a=a0 := by
  classical
  have hbetter : ∀ i, economicValue (D i) (e i) (a0 i) ≤
      economicValue (D i) (c i) (a i) := by
    intro i
    exact hEq.optimal i (e i) (he i) (a0 i) (ha0 i) le_rfl
  let gap : H → ℝ := fun i => (c i+∑ j, qstar j*a i j)-
    (e i+∑ j, qstar j*a0 i j)
  have hnonneg : ∀ i, 0 ≤ gap i := by
    intro i
    have ht := economic_support_le (D i) qstar (a0 i) (a i) (e i) (c i)
      (he i) (hEq.consumption_positive i) (ha0 i) (hEq.holdings_nonneg i) (hsupport i)
    have hp := Real.rpow_pos_of_pos (he i) (-(D i).gamma)
    by_contra hn
    have hg : gap i < 0 := lt_of_not_ge hn
    have hm := mul_neg_of_pos_of_neg hp hg
    dsimp [gap] at hm
    linarith [hbetter i]
  have htotal := aggregate_cost_equality qstar c e a a0 hEq.consumption_clears
    (fun j => (hEq.ownership_clears j).trans (hstock j).symm)
  have hsum : ∑ i, gap i=0 := by
    dsimp [gap]
    rw [Finset.sum_sub_distrib,htotal,sub_self]
  have hpoint : ∀ i, c i=e i ∧ a i=a0 i := by
    intro i
    have hsingle : gap i ≤ ∑ k, gap k :=
      Finset.single_le_sum (fun k _ => hnonneg k) (Finset.mem_univ i)
    rw [hsum] at hsingle
    have hcost : c i+∑ j, qstar j*a i j ≤ e i+∑ j, qstar j*a0 i j := by
      dsimp [gap] at hsingle
      linarith
    exact bundle_equal_of_not_worse_and_cost_le (D i) qstar (a0 i) (a i)
      (e i) (c i) (he i) (hEq.consumption_positive i) (ha0 i)
      (hEq.holdings_nonneg i) (hsupport i) (hbetter i) hcost
  exact ⟨funext (fun i => (hpoint i).1),funext (fun i => (hpoint i).2)⟩

omit [Fintype H] in
theorem supported_price_from_owner (D : H → Data J S) (e : H → ℝ)
    (a0 : H → J → ℝ) (qstar : J → ℝ) (he : ∀ i, 0 < e i)
    (hsupport : SupportsInitial D e a0 qstar) (i : H) (j : J)
    (hown : 0 < a0 i j) :
    qstar j=marginal (D i) (a0 i) j / (e i)^(-(D i).gamma) := by
  have hz := (mul_eq_zero.mp (hsupport i j).2).resolve_left (ne_of_gt hown)
  apply (eq_div_iff (ne_of_gt (Real.rpow_pos_of_pos (he i) (-(D i).gamma)))).mpr
  linarith

theorem price_and_allocation_unique (D : H → Data J S) (e : H → ℝ)
    (a0 : H → J → ℝ) (supply qstar q : J → ℝ)
    (c : H → ℝ) (a : H → J → ℝ)
    (he : ∀ i, 0 < e i) (ha0 : ∀ i j, 0 ≤ a0 i j)
    (hs : ∀ j, 0 < supply j) (hstock : ∀ j, ∑ i, a0 i j=supply j)
    (hsupport : SupportsInitial D e a0 qstar)
    (hEq : IsEquilibrium D e a0 supply q c a) : q=qstar ∧ c=e ∧ a=a0 := by
  obtain ⟨hc,ha⟩ := allocation_unique D e a0 supply qstar q c a he ha0 hstock hsupport hEq
  refine ⟨?_,hc,ha⟩
  funext j
  obtain ⟨i,hi⟩ := OwnershipUniform.some_positive_owner hEq j (hs j)
  have hp := OwnershipUniform.owned_asset_euler hEq i j hi
  rw [ha,hc] at hp
  have hi0 : 0 < a0 i j := by rwa [ha] at hi
  have href := (eq_div_iff
    (ne_of_gt (Real.rpow_pos_of_pos (he i) (-(D i).gamma)))).mp
      (supported_price_from_owner D e a0 qstar he hsupport i j hi0)
  exact mul_right_cancel₀
    (ne_of_gt (Real.rpow_pos_of_pos (he i) (-(D i).gamma))) (hp.symm.trans href.symm)

theorem unique_supported_equilibrium (D : H → Data J S) (e : H → ℝ)
    (a0 : H → J → ℝ) (supply qstar : J → ℝ)
    (he : ∀ i, 0 < e i) (ha0 : ∀ i j, 0 ≤ a0 i j)
    (hs : ∀ j, 0 < supply j) (hstock : ∀ j, ∑ i, a0 i j=supply j)
    (hq : ∀ j, 0 < qstar j) (hsupport : SupportsInitial D e a0 qstar) :
    IsEquilibrium D e a0 supply qstar e a0 ∧
    ∀ q c a, IsEquilibrium D e a0 supply q c a → q=qstar ∧ c=e ∧ a=a0 :=
  ⟨reference_equilibrium D e a0 supply qstar he ha0 hstock hq hsupport,
    fun q c a hEq => price_and_allocation_unique D e a0 supply qstar q c a
      he ha0 hs hstock hsupport hEq⟩

namespace CornerControl

def gammaNat : Fin 2 → ℕ := ![2,3]
def weight : Fin 2 → Fin 4 → ℝ :=
  ![![50/469,50/469,50/469,100/469],![8/401,160/401,8/401,8/401]]
def probability : Fin 4 → ℝ := ![1/6,5/12,1/6,1/4]
def D (i : Fin 2) : Data (Fin 2) (Fin 4) where
  delta := 1/8
  gamma := gammaNat i
  eta := fun _ => gammaNat i
  income := fun _ => 1
  weight := weight i
  payoff := OwnershipMultiplicity.payoff
  delta_pos := by norm_num
  gamma_pos := by fin_cases i <;> norm_num [gammaNat]
  eta_pos := by intro _; fin_cases i <;> norm_num [gammaNat]
  income_pos := by intro _; norm_num
  weight_pos := by intro s; fin_cases i <;> fin_cases s <;> norm_num [weight]
  payoff_nonneg := fun s j => (OwnershipMultiplicity.genuinely_overlapping_payoffs s j).le
  payoff_injective := OwnershipMultiplicity.payoff_injective

def endowment : Fin 2 → ℝ := ![3,3]
def initial : Fin 2 → Fin 2 → ℝ := ![![1,0],![0,1]]
def supply : Fin 2 → ℝ := ![1,1]
def qstar : Fin 2 → ℝ := ![1,1]

theorem primitive_conditions :
    (∀ i, 0 < endowment i) ∧ (∀ i j, 0 ≤ initial i j) ∧
    (∀ j, 0 < supply j) ∧ (∀ j, ∑ i, initial i j=supply j) ∧
    (∀ j, 0 < qstar j) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro i; fin_cases i <;> norm_num [endowment]
  · intro i j; fin_cases i <;> fin_cases j <;> norm_num [initial]
  · intro j; fin_cases j <;> norm_num [supply]
  · intro j; fin_cases j <;> norm_num [initial,supply,Fin.sum_univ_succ]
  · intro j; fin_cases j <;> norm_num [qstar]

theorem primitive_support : SupportsInitial D endowment initial qstar := by
  intro i j
  simp only [marginal,D,OwnershipMultiplicity.negative_nat_power]
  fin_cases i <;> fin_cases j <;>
    norm_num [consumption,D,initial,endowment,qstar,OwnershipMultiplicity.payoff,
      weight,gammaNat,Fin.sum_univ_succ]

theorem unique_actual_market :
    IsEquilibrium D endowment initial supply qstar endowment initial ∧
    ∀ q c a, IsEquilibrium D endowment initial supply q c a →
      q=qstar ∧ c=endowment ∧ a=initial :=
  unique_supported_equilibrium D endowment initial supply qstar
    primitive_conditions.1 primitive_conditions.2.1 primitive_conditions.2.2.1
    primitive_conditions.2.2.2.1 primitive_conditions.2.2.2.2 primitive_support

theorem settlement_weight_compatibility :
    (∑ s, probability s=1) ∧ (∀ s, 0 < probability s) ∧
    ∀ i s, 0 < weight i s / probability s ∧ weight i s / probability s < 1 ∧
      weight i s=probability s*(weight i s / probability s) := by
  refine ⟨?_,?_,?_⟩
  · norm_num [probability,Fin.sum_univ_succ]
  · intro s; fin_cases s <;> norm_num [probability]
  · intro i s; fin_cases i <;> fin_cases s <;> norm_num [weight,probability]

theorem different_current_multipliers :
    (endowment 0)^(-(D 0).gamma) ≠ (endowment 1)^(-(D 1).gamma) := by
  simp only [D,OwnershipMultiplicity.negative_nat_power]
  norm_num [endowment,gammaNat]

theorem strict_nonowner_inequalities :
    marginal (D 0) (initial 0) 1 < qstar 1*(endowment 0)^(-(D 0).gamma) ∧
    marginal (D 1) (initial 1) 0 < qstar 0*(endowment 1)^(-(D 1).gamma) := by
  simp only [marginal,D,OwnershipMultiplicity.negative_nat_power]
  norm_num [consumption,D,initial,endowment,qstar,OwnershipMultiplicity.payoff,
    weight,gammaNat,Fin.sum_univ_succ]

end CornerControl

namespace InteriorControl

def endowment (_ : Fin 2) : ℝ := 4
def initial (_ : Fin 2) : Fin 2 → ℝ := ![1/2,1/2]
def referenceReceipt : Fin 4 → ℝ := ![5/2,5/2,2,7/2]
def baseMass : Fin 4 → ℝ := ![1,4,1,1]
def weight (i : Fin 2) (s : Fin 4) : ℝ :=
  ((4 : ℝ)^(CornerControl.gammaNat i))⁻¹ *
    (referenceReceipt s)^(CornerControl.gammaNat i)*baseMass s/11
def D (i : Fin 2) : Data (Fin 2) (Fin 4) :=
  { CornerControl.D i with
    weight := weight i
    weight_pos := by
      intro s
      fin_cases i <;> fin_cases s <;>
        norm_num [weight,referenceReceipt,baseMass,CornerControl.gammaNat] }

theorem initial_interior : ∀ i j, 0 < initial i j := by
  intro i j
  fin_cases j <;> norm_num [initial]

theorem primitive_support :
    SupportsInitial D endowment initial CornerControl.qstar := by
  intro i j
  simp only [marginal,D,CornerControl.D,OwnershipMultiplicity.negative_nat_power]
  fin_cases i <;> fin_cases j <;>
    norm_num [consumption,D,CornerControl.D,initial,endowment,CornerControl.qstar,
      OwnershipMultiplicity.payoff,weight,referenceReceipt,baseMass,
      CornerControl.gammaNat,Fin.sum_univ_succ]

theorem unique_actual_market :
    IsEquilibrium D endowment initial CornerControl.supply
      CornerControl.qstar endowment initial ∧
    ∀ q c a, IsEquilibrium D endowment initial CornerControl.supply q c a →
      q=CornerControl.qstar ∧ c=endowment ∧ a=initial := by
  apply unique_supported_equilibrium D endowment initial
    CornerControl.supply CornerControl.qstar
  · intro i; norm_num [endowment]
  · intro i j; exact (initial_interior i j).le
  · intro j; fin_cases j <;> norm_num [CornerControl.supply]
  · intro j; fin_cases j <;> norm_num [initial,CornerControl.supply,Fin.sum_univ_succ]
  · intro j; fin_cases j <;> norm_num [CornerControl.qstar]
  · exact primitive_support

theorem waiting_weight_compatibility :
    (∑ _ : Fin 4, (1/4 : ℝ))=1 ∧
    ∀ i s, 0 < 4*weight i s ∧ 4*weight i s < 1 ∧
      weight i s=(1/4 : ℝ)*(4*weight i s) := by
  constructor
  · norm_num [Fin.sum_univ_succ]
  · intro i s
    fin_cases i <;> fin_cases s <;>
      norm_num [weight,referenceReceipt,baseMass,CornerControl.gammaNat]

end InteriorControl
end OwnershipSupported

#print axioms OwnershipSupported.reference_equilibrium
#print axioms OwnershipSupported.aggregate_cost_equality
#print axioms OwnershipSupported.allocation_unique
#print axioms OwnershipSupported.supported_price_from_owner
#print axioms OwnershipSupported.price_and_allocation_unique
#print axioms OwnershipSupported.unique_supported_equilibrium
#print axioms OwnershipSupported.CornerControl.primitive_conditions
#print axioms OwnershipSupported.CornerControl.primitive_support
#print axioms OwnershipSupported.CornerControl.unique_actual_market
#print axioms OwnershipSupported.CornerControl.settlement_weight_compatibility
#print axioms OwnershipSupported.CornerControl.different_current_multipliers
#print axioms OwnershipSupported.CornerControl.strict_nonowner_inequalities
#print axioms OwnershipSupported.InteriorControl.initial_interior
#print axioms OwnershipSupported.InteriorControl.primitive_support
#print axioms OwnershipSupported.InteriorControl.unique_actual_market
#print axioms OwnershipSupported.InteriorControl.waiting_weight_compatibility
