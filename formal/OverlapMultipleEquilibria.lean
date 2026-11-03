import OwnershipKKTSufficiency
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
An exact two-household, two-asset, four-state counterexample to unconditional
market-price uniqueness in the accepted heterogeneous overlapping-payoff CRRA
class. The certificate uses actual global household optimality, not an assumed
Euler system. Every asset pays positively in every state; the payoff map has
full column rank and no portfolio delivers a nonzero constant receipt.
-/

noncomputable section
open scoped BigOperators
open OwnershipCRRA OwnershipMarginal OwnershipUnfloored OwnershipPositive
open OwnershipSufficiency

namespace OwnershipMultiplicity

def payoff : Fin 4 → Fin 2 → ℝ := ![![2,1], ![1,2], ![1,1], ![4,1]]
def gammaNat : Fin 2 → ℕ := ![1,2]
def etaNat : Fin 2 → Fin 4 → ℕ := ![![3,1,1,12], ![2,12,1,1]]
def income : Fin 2 → Fin 4 → ℝ :=
  ![![1/10,1/2,1,1], ![1/10,1/10,1/10,3]]
def weight : Fin 2 → Fin 4 → ℝ :=
  ![![29058304455446746618881/18604874290679046465416,
       12117213494429030008569/18604874290679046465416,
       5777291751738506064993/9302437145339523232708,
       8942162805955456789513013568536122368/567775704671601759808837890625],
    ![2451232757796814187/7378692597646912432,
       3804840364426742527088675067/9007193112361953652343750,
       1285307606883495/15245232639766348,
       5297284882795914225/1844673149411728108]]

theorem payoff_injective :
    Function.Injective (fun a : Fin 2 → ℝ => fun s => ∑ j, payoff s j*a j) := by
  intro a b hab
  have h0 := congrFun hab 0
  have h1 := congrFun hab 1
  norm_num [payoff, Fin.sum_univ_succ] at h0 h1
  funext j
  fin_cases j <;> dsimp <;> linarith

def D (i : Fin 2) : Data (Fin 2) (Fin 4) where
  delta := 1/8
  gamma := gammaNat i
  eta := fun s => etaNat i s
  income := income i
  weight := weight i
  payoff := payoff
  delta_pos := by norm_num
  gamma_pos := by fin_cases i <;> norm_num [gammaNat]
  eta_pos := by intro s; fin_cases i <;> fin_cases s <;> norm_num [etaNat]
  income_pos := by intro s; fin_cases i <;> fin_cases s <;> norm_num [income]
  weight_pos := by intro s; fin_cases i <;> fin_cases s <;> norm_num [weight]
  payoff_nonneg := by intro s j; fin_cases s <;> fin_cases j <;> norm_num [payoff]
  payoff_injective := payoff_injective

def endowment : Fin 2 → ℝ := ![6/5,1/10]
def initial : Fin 2 → Fin 2 → ℝ := ![![0,1], ![1,0]]
def supply : Fin 2 → ℝ := ![1,1]
def prices : Fin 2 → Fin 2 → ℝ := ![![2,1], ![3,1]]
def current : Fin 2 → Fin 2 → ℝ := ![![1/2,4/5], ![1/5,11/10]]
def holdings : Fin 2 → Fin 2 → Fin 2 → ℝ :=
  ![![![7/10,3/10], ![3/10,7/10]],
    ![![3/5,1/5], ![2/5,4/5]]]

theorem primitive_conditions :
    (∀ i, 0 < endowment i) ∧ (∀ i j, 0 ≤ initial i j) ∧
    (∀ j, 0 < supply j) ∧ (∀ j, ∑ i, initial i j = supply j) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i <;> norm_num [endowment]
  · intro i j; fin_cases i <;> fin_cases j <;> norm_num [initial]
  · intro j; fin_cases j <;> norm_num [supply]
  · intro j; fin_cases j <;> norm_num [initial, supply, Fin.sum_univ_succ]

theorem exact_budgets (k i : Fin 2) :
    current k i + ∑ j, prices k j*holdings k i j =
      endowment i + ∑ j, prices k j*initial i j := by
  fin_cases k <;> fin_cases i <;>
    norm_num [current, prices, holdings, endowment, initial, Fin.sum_univ_succ]

theorem exact_clearing (k : Fin 2) :
    (∑ i, current k i = ∑ i, endowment i) ∧
      (∀ j, ∑ i, holdings k i j = supply j) := by
  constructor
  · fin_cases k <;> norm_num [current, endowment, Fin.sum_univ_succ]
  · intro j; fin_cases k <;> fin_cases j <;>
      norm_num [holdings, supply, Fin.sum_univ_succ]

theorem negative_nat_power (x : ℝ) (n : ℕ) :
    x ^ (-(n : ℝ)) = (x ^ n)⁻¹ := by
  rw [Real.rpow_neg_natCast, zpow_neg, zpow_natCast]

theorem exact_euler (k i j : Fin 2) :
    marginal (D i) (holdings k i) j = prices k j*(current k i)^(-(D i).gamma) := by
  simp only [marginal, D, negative_nat_power]
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    norm_num [consumption, D, holdings, payoff, income, weight, etaNat, gammaNat,
      prices, current, Fin.sum_univ_succ]

theorem actual_equilibrium (k : Fin 2) :
    IsEquilibrium D endowment initial supply (prices k) (current k) (holdings k) := by
  have hc : ∀ i, 0 < current k i := by
    intro i; fin_cases k <;> fin_cases i <;> norm_num [current]
  have ha : ∀ i j, 0 ≤ holdings k i j := by
    intro i j; fin_cases k <;> fin_cases i <;> fin_cases j <;> norm_num [holdings]
  have hkkt : ∀ i j,
      marginal (D i) (holdings k i) j ≤ prices k j*(current k i)^(-(D i).gamma) ∧
      holdings k i j *
        (prices k j*(current k i)^(-(D i).gamma)-marginal (D i) (holdings k i) j)=0 := by
    intro i j
    rw [exact_euler]
    exact ⟨le_rfl, by ring⟩
  refine ⟨?_, hc, ha, ?_, ?_, (exact_clearing k).1, (exact_clearing k).2, hkkt⟩
  · intro j; fin_cases k <;> fin_cases j <;> norm_num [prices]
  · intro i; exact (exact_budgets k i).le
  · intro i
    exact global_optimality_of_corner_conditions (D i) (prices k) (holdings k i)
      (current k i) (endowment i+∑ j, prices k j*initial i j)
      (hc i) (ha i) (exact_budgets k i) (hkkt i)

theorem distinct_prices : prices 0 ≠ prices 1 := by
  intro h
  have hh := congrFun h 0
  norm_num [prices] at hh

theorem distinct_holdings : holdings 0 ≠ holdings 1 := by
  intro h
  have hh := congrFun (congrFun h 0) 0
  norm_num [holdings] at hh

theorem no_nonzero_constant_payoff (a : Fin 2 → ℝ) (r : ℝ)
    (h : ∀ s, (∑ j, payoff s j*a j)=r) : r=0 ∧ a=(fun _ => 0) := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  norm_num [payoff, Fin.sum_univ_succ] at h0 h1 h2
  refine ⟨by linarith, ?_⟩
  funext j
  fin_cases j <;> dsimp <;> linarith

theorem genuinely_overlapping_payoffs : ∀ s j, 0 < payoff s j := by
  intro s j
  fin_cases s <;> fin_cases j <;> norm_num [payoff]

theorem two_actual_equilibria :
    IsEquilibrium D endowment initial supply (prices 0) (current 0) (holdings 0) ∧
    IsEquilibrium D endowment initial supply (prices 1) (current 1) (holdings 1) ∧
    prices 0 ≠ prices 1 ∧ holdings 0 ≠ holdings 1 :=
  ⟨actual_equilibrium 0, actual_equilibrium 1, distinct_prices, distinct_holdings⟩

theorem market_price_uniqueness_false :
    ¬(∀ (q r c d : Fin 2 → ℝ) (a b : Fin 2 → Fin 2 → ℝ),
      IsEquilibrium D endowment initial supply q c a →
      IsEquilibrium D endowment initial supply r d b → q=r) := by
  intro h
  exact distinct_prices (h (prices 0) (prices 1) (current 0) (current 1)
    (holdings 0) (holdings 1) (actual_equilibrium 0) (actual_equilibrium 1))

end OwnershipMultiplicity

#print axioms OwnershipMultiplicity.payoff_injective
#print axioms OwnershipMultiplicity.primitive_conditions
#print axioms OwnershipMultiplicity.exact_budgets
#print axioms OwnershipMultiplicity.exact_clearing
#print axioms OwnershipMultiplicity.negative_nat_power
#print axioms OwnershipMultiplicity.exact_euler
#print axioms OwnershipMultiplicity.actual_equilibrium
#print axioms OwnershipMultiplicity.distinct_prices
#print axioms OwnershipMultiplicity.distinct_holdings
#print axioms OwnershipMultiplicity.no_nonzero_constant_payoff
#print axioms OwnershipMultiplicity.genuinely_overlapping_payoffs
#print axioms OwnershipMultiplicity.two_actual_equilibria
#print axioms OwnershipMultiplicity.market_price_uniqueness_false
