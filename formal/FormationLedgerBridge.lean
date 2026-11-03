import FormationLedgerCore
import EnergyComputeOwnership

/-! Dated funding and a conditional integer-grid bridge. Actual subscription
participation, fundraising equilibrium and general rounding are not assumed proved. -/
noncomputable section
open scoped BigOperators
open OwnershipCRRA OwnershipUnfloored OwnershipPositive OwnershipCertificates FormationLedgerCore

namespace FormationLedgerBridge

def planFlows (p : EnergyComputeOwnership.Plan) : List ℝ :=
  [-p.operatingCost, p.servicePrice*EnergyComputeOwnership.output p.capacity, p.salvage]

theorem compute_plan_dated_safe (p : EnergyComputeOwnership.Plan) :
    CashSafe p.workingFunds (planFlows p) := by
  have hrev := mul_nonneg p.servicePrice_nonneg
    (EnergyComputeOwnership.output_nonnegative p.capacity)
  dsimp [planFlows, CashSafe]
  exact ⟨p.workingFunds_nonneg, by linarith [p.costs_funded],
    by linarith [p.costs_funded], by linarith [p.costs_funded, p.salvage_nonneg]⟩

theorem compute_plan_terminal_identity (p : EnergyComputeOwnership.Plan) :
    cashAfter p.workingFunds (planFlows p)=EnergyComputeOwnership.receipt p := by
  rw [cash_after_identity]
  simp only [planFlows, List.sum_cons, List.sum_nil]
  unfold EnergyComputeOwnership.receipt
  ring

section DatedData
variable {J S : Type*} [Fintype J]

/-- Inputs include settled initial cash and an affordable path in every state.
Cash at different dates is not presumed interchangeable without this condition. -/
def datedData (D : Data J S) (funds : J → ℝ) (flows : S → J → List ℝ)
    (hsafe : ∀ s j, CashSafe (funds j) (flows s j))
    (hrank : Function.Injective (fun a : J → ℝ => fun s =>
      ∑ j, cashAfter (funds j) (flows s j)*a j)) : Data J S :=
  {D with
    payoff := fun s j => cashAfter (funds j) (flows s j)
    payoff_nonneg := fun s j => safe_terminal_nonnegative (flows s j) (funds j) (hsafe s j)
    payoff_injective := hrank}

theorem dated_payoff_identity (D : Data J S) (funds : J → ℝ)
    (flows : S → J → List ℝ) (hsafe : ∀ s j, CashSafe (funds j) (flows s j))
    (hrank : Function.Injective (fun a : J → ℝ => fun s =>
      ∑ j, cashAfter (funds j) (flows s j)*a j)) (s : S) (j : J) :
    (datedData D funds flows hsafe hrank).payoff s j=
      funds j+(flows s j).sum := cash_after_identity (flows s j) (funds j)

end DatedData

section Markets
variable {H J S : Type*} [Fintype H] [Fintype J] [Fintype S] [Nonempty H]

theorem dated_certificate_market_exists (D : H → Data J S)
    (funds : J → ℝ) (flows : S → J → List ℝ)
    (hsafe : ∀ s j, CashSafe (funds j) (flows s j))
    (hrank : Function.Injective (fun a : J → ℝ => fun s =>
      ∑ j, cashAfter (funds j) (flows s j)*a j)) (N : Denomination J)
    (e : H → ℝ) (a0 : H → J → ℝ) (supply : J → ℝ)
    (he : ∀ i, 0<e i) (ha0 : ∀ i j, 0≤a0 i j)
    (hs : ∀ j, 0<supply j) (hstock : ∀ j, ∑ i, a0 i j=supply j) :
    ∃ r c h, IsEquilibrium (fun i => certificateData
      (datedData (D i) funds flows hsafe hrank) N)
      e (fun i => encode N (a0 i)) (encode N supply) r c h :=
  certificate_market_exists (fun i => datedData (D i) funds flows hsafe hrank)
    N e a0 supply he ha0 hs hstock

end Markets

section Subscriptions
variable {H : Type*} [Fintype H]

/-- These are paid subscriptions, not initial allocations or unsigned pledges. -/
theorem subscription_cash_identity (paidUnits : H → ℕ) (total : ℕ)
    (N supply q : ℝ) (hN : 0<N) (hstock : ∑ i, paidUnits i=total)
    (hden : (total : ℝ)=N*supply) :
    (∑ i, (q/N)*(paidUnits i : ℝ))=q*supply := by
  have ht : (∑ i, (paidUnits i : ℝ))=(total : ℝ) := by exact_mod_cast hstock
  rw [← Finset.mul_sum, ht, hden]
  field_simp [ne_of_gt hN]

theorem paid_subscriptions_cover_dates (paidUnits : H → ℕ) (total : ℕ)
    (N supply q construction : ℝ) (xs : List ℝ) (hN : 0<N)
    (hstock : ∑ i, paidUnits i=total) (hden : (total : ℝ)=N*supply) :
    CashSafe ((∑ i, (q/N)*(paidUnits i : ℝ))-construction) xs ↔
      construction+bufferNeeded xs≤q*supply := by
  rw [subscription_cash_identity paidUnits total N supply q hN hstock hden,
    formation_funding_iff]

end Subscriptions

section LedgerSettlement
variable {A R : Type*} [Fintype A] [Fintype R]

theorem ledger_proportionate_conservation (s : Ledger A R) (cap : ℕ)
    (hv : Valid cap s) (hc : s.closed=true) (N supply z : ℝ) (hN : 0<N)
    (hden : (cap : ℝ)=N*supply) :
    (∑ i, (z/N)*(s.holdings i : ℝ))=z*supply := by
  apply subscription_cash_identity s.holdings cap N supply z hN
    (hv.stock.trans (hv.closed_full hc)) hden

/-- Exact proportionate cash allocation is affordable when actual custody has
that uncommitted cash. No integer-cash rounding or external custody is proved. -/
theorem funded_proportionate_declaration (s : Ledger A R) (cap period : ℕ)
    (hv : Valid cap s) (hc : s.closed=true) (N supply z : ℝ)
    (hN : 0<N) (hz : 0≤z) (hden : (cap : ℝ)=N*supply)
    (hb : reserved s + z*supply ≤ s.vault) (last : Bool) :
    Valid cap (distribute s period (fun i => (z/N)*(s.holdings i : ℝ)) last) := by
  apply distribute_valid cap s period _ last hv
  · intro i
    exact mul_nonneg (div_nonneg hz hN.le) (Nat.cast_nonneg (s.holdings i))
  · rw [ledger_proportionate_conservation s cap hv hc N supply z hN hden]
    exact hb
  · exact hc

end LedgerSettlement

section IntegerGrid
variable {J S : Type*} [Fintype J] [Fintype S]

def NatPortfolioOptimal (D : Data J S) (q : J → ℝ) (W c : ℝ) (h : J → ℕ) : Prop :=
  0<c ∧ c+(∑ j, q j*(h j : ℝ))≤W ∧
    ∀ d, 0<d → ∀ b : J → ℕ, d+(∑ j, q j*(b j : ℝ))≤W →
      economicValue D d (fun j => (b j : ℝ))≤economicValue D c (fun j => (h j : ℝ))

theorem grid_optimal_of_divisible_optimal (D : Data J S) (q : J → ℝ)
    (W c : ℝ) (h : J → ℕ)
    (ho : HouseholdOptimal D q W c (fun j => (h j : ℝ))) :
    NatPortfolioOptimal D q W c h := by
  refine ⟨ho.1, ho.2.2.1, ?_⟩
  intro d hd b hb
  exact ho.2.2.2 d hd (fun j => (b j : ℝ)) (fun j => Nat.cast_nonneg (b j)) hb

variable {H : Type*} [Fintype H]

structure NatGridMarket (D : H → Data J S) (e : H → ℝ) (h0 : H → J → ℕ)
    (supply : J → ℕ) (q : J → ℝ) (c : H → ℝ) (h : H → J → ℕ) : Prop where
  positive_prices : ∀ j, 0<q j
  household_optimal : ∀ i, NatPortfolioOptimal (D i) q
    (e i+∑ j, q j*(h0 i j : ℝ)) (c i) (h i)
  current_clearing : ∑ i, c i=∑ i, e i
  token_clearing : ∀ j, ∑ i, h i j=supply j

/-- No rounding of a real optimum occurs here. Both the endowment and actual
equilibrium allocation must already belong to the same integer grid. -/
theorem grid_market_of_divisible_equilibrium (D : H → Data J S) (e : H → ℝ)
    (h0 : H → J → ℕ) (supply : J → ℕ) (q : J → ℝ) (c : H → ℝ) (h : H → J → ℕ)
    (hEq : IsEquilibrium D e (fun i j => (h0 i j : ℝ))
      (fun j => (supply j : ℝ)) q c (fun i j => (h i j : ℝ))) :
    NatGridMarket D e h0 supply q c h := by
  refine ⟨hEq.prices_positive, ?_, hEq.consumption_clears, ?_⟩
  · intro i
    apply grid_optimal_of_divisible_optimal
    exact ⟨hEq.consumption_positive i, hEq.holdings_nonneg i,
      hEq.affordable i, hEq.optimal i⟩
  · intro j
    exact_mod_cast hEq.ownership_clears j

end IntegerGrid

end FormationLedgerBridge

#print axioms FormationLedgerBridge.compute_plan_dated_safe
#print axioms FormationLedgerBridge.compute_plan_terminal_identity
#print axioms FormationLedgerBridge.dated_payoff_identity
#print axioms FormationLedgerBridge.dated_certificate_market_exists
#print axioms FormationLedgerBridge.subscription_cash_identity
#print axioms FormationLedgerBridge.paid_subscriptions_cover_dates
#print axioms FormationLedgerBridge.ledger_proportionate_conservation
#print axioms FormationLedgerBridge.funded_proportionate_declaration
#print axioms FormationLedgerBridge.grid_optimal_of_divisible_optimal
#print axioms FormationLedgerBridge.grid_market_of_divisible_equilibrium
