import OwnershipCertificates

/-!
One-settlement funded mutual protection. Claims are target benefits, not
unconditional debts. Exhaustion is explicitly proportional; retained resources
belong to members under supplied nonnegative surplus shares. This is neither
a contribution-demand equilibrium nor legal/Sharia certification.
-/

noncomputable section
open scoped BigOperators
open OwnershipCRRA OwnershipCertificates

namespace FundedProtection

structure Pool (I : Type*) where
  claim : I → ℝ
  claim_nonneg : ∀ i, 0 ≤ claim i
  resources : ℝ
  resources_nonneg : 0 ≤ resources

section Settlement
variable {I : Type*} [Fintype I]

def total (P : Pool I) : ℝ := ∑ i, P.claim i

def payout (P : Pool I) (i : I) : ℝ :=
  if total P ≤ P.resources then P.claim i
  else P.resources*(P.claim i/total P)

def retained (P : Pool I) : ℝ := P.resources-∑ i, payout P i
def unmet (P : Pool I) : ℝ := total P-∑ i, payout P i

theorem total_nonneg (P : Pool I) : 0 ≤ total P :=
  Finset.sum_nonneg (fun i _ => P.claim_nonneg i)

theorem payout_nonneg (P : Pool I) (i : I) : 0 ≤ payout P i := by
  unfold payout
  split_ifs
  · exact P.claim_nonneg i
  · exact mul_nonneg P.resources_nonneg
      (div_nonneg (P.claim_nonneg i) (total_nonneg P))

theorem payout_le_claim (P : Pool I) (i : I) : payout P i ≤ P.claim i := by
  by_cases h : total P ≤ P.resources
  · simp only [payout,ite_eq_left h,le_refl]
  · have ht : 0 < total P := lt_of_le_of_lt P.resources_nonneg (lt_of_not_ge h)
    have hr : P.resources/total P ≤ 1 :=
      (div_le_one ht).2 (le_of_lt (lt_of_not_ge h))
    rw [payout,ite_eq_right h]
    calc
      P.resources*(P.claim i/total P)=P.claim i*(P.resources/total P) := by ring
      _ ≤ P.claim i*1 := mul_le_mul_of_nonneg_left hr (P.claim_nonneg i)
      _ = P.claim i := mul_one _

theorem sum_payout (P : Pool I) :
    (∑ i, payout P i)=min (total P) P.resources := by
  by_cases h : total P ≤ P.resources
  · simp only [payout,ite_eq_left h,min_eq_left h]
    rfl
  · have ht : 0 < total P := lt_of_le_of_lt P.resources_nonneg (lt_of_not_ge h)
    rw [min_eq_right (le_of_lt (lt_of_not_ge h))]
    simp only [payout,ite_eq_right h]
    rw [← Finset.mul_sum,← Finset.sum_div]
    change P.resources*(total P/total P)=P.resources
    rw [div_self (ne_of_gt ht),mul_one]

theorem sum_payout_le_resources (P : Pool I) :
    (∑ i, payout P i) ≤ P.resources := by
  rw [sum_payout]
  exact min_le_right _ _

theorem retained_nonneg (P : Pool I) : 0 ≤ retained P :=
  sub_nonneg.mpr (sum_payout_le_resources P)

theorem unmet_nonneg (P : Pool I) : 0 ≤ unmet P := by
  unfold unmet
  rw [sum_payout]
  exact sub_nonneg.mpr (min_le_left _ _)

theorem settlement_budget (P : Pool I) :
    (∑ i, payout P i)+retained P=P.resources := by
  unfold retained
  ring

theorem unmet_eq_excess (P : Pool I) :
    unmet P=max 0 (total P-P.resources) := by
  by_cases h : total P ≤ P.resources
  · rw [unmet,sum_payout,min_eq_left h,
      max_eq_left (sub_nonpos.mpr h),sub_self]
  · rw [unmet,sum_payout,min_eq_right (le_of_lt (lt_of_not_ge h)),
      max_eq_right (sub_nonneg.mpr (le_of_lt (lt_of_not_ge h)))]

theorem full_payment_iff (P : Pool I) :
    (∀ i, payout P i=P.claim i) ↔ total P ≤ P.resources := by
  constructor
  · intro h
    have hs := sum_payout_le_resources P
    simpa only [h,total] using hs
  · intro h i
    exact ite_eq_left h

/-- No different allocation rule can pay all targets out of insufficient funds. -/
theorem full_payment_impossible (P : Pool I) (h : P.resources < total P)
    (b : I → ℝ) : ¬ ((∀ i, P.claim i ≤ b i) ∧ (∑ i, b i) ≤ P.resources) := by
  rintro ⟨hb,hfund⟩
  have hs : total P ≤ ∑ i, b i := Finset.sum_le_sum (fun i _ => hb i)
  exact (not_le_of_gt h) (hs.trans hfund)

def memberPayoff (P : Pool I) (share : I → ℝ) (i : I) : ℝ :=
  payout P i+share i*retained P

theorem member_payoff_nonneg (P : Pool I) (share : I → ℝ)
    (hshare : ∀ i, 0 ≤ share i) (i : I) : 0 ≤ memberPayoff P share i :=
  add_nonneg (payout_nonneg P i) (mul_nonneg (hshare i) (retained_nonneg P))

theorem member_settlement_budget (P : Pool I) (share : I → ℝ)
    (hsum : ∑ i, share i=1) :
    (∑ i, memberPayoff P share i)=P.resources := by
  simp only [memberPayoff,Finset.sum_add_distrib]
  rw [← Finset.sum_mul,hsum,one_mul,settlement_budget]

end Settlement

section Valuation
variable {I S : Type*} [Fintype I] [Fintype S]

def value (weight X : S → ℝ) : ℝ := ∑ s, weight s*X s

theorem value_nonneg (weight X : S → ℝ) (hw : ∀ s, 0 ≤ weight s)
    (hX : ∀ s, 0 ≤ X s) : 0 ≤ value weight X :=
  Finset.sum_nonneg (fun s _ => mul_nonneg (hw s) (hX s))

theorem value_add (weight X Y : S → ℝ) :
    value weight (fun s => X s+Y s)=value weight X+value weight Y := by
  simp only [value,mul_add,Finset.sum_add_distrib]

theorem value_sum (weight : S → ℝ) (X : I → S → ℝ) :
    (∑ i, value weight (X i))=value weight (fun s => ∑ i, X i s) := by
  unfold value
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]

theorem priced_resource_budget (P : S → Pool I) (weight : S → ℝ) :
    (∑ i, value weight (fun s => payout (P s) i))+
      value weight (fun s => retained (P s))=value weight (fun s => (P s).resources) := by
  rw [value_sum,← value_add]
  congr 1
  funext s
  exact settlement_budget (P s)

theorem priced_member_budget (P : S → Pool I) (weight : S → ℝ)
    (share : I → ℝ) (hsum : ∑ i, share i=1) :
    (∑ i, value weight (fun s => memberPayoff (P s) share i))=
      value weight (fun s => (P s).resources) := by
  rw [value_sum]
  congr 1
  funext s
  exact member_settlement_budget (P s) share hsum

theorem priced_protection_le_resources (P : S → Pool I) (weight : S → ℝ)
    (hw : ∀ s, 0 ≤ weight s) :
    (∑ i, value weight (fun s => payout (P s) i)) ≤
      value weight (fun s => (P s).resources) := by
  have hb := priced_resource_budget P weight
  have hr := value_nonneg weight (fun s => retained (P s)) hw
    (fun s => retained_nonneg (P s))
  linarith

end Valuation

section CertificateBacking
variable {I J S : Type*} [Fintype I] [Fintype J] [Fintype S]

/-- Backing is supplied nonnegative certificate ownership, not an extra promise. -/
def certificatePool (D : Data J S) (N : Denomination J) (h : J → ℝ)
    (hh : ∀ j, 0 ≤ h j) (loss : S → I → ℝ) (hloss : ∀ s i, 0 ≤ loss s i)
    (s : S) : Pool I where
  claim := loss s
  claim_nonneg := hloss s
  resources := ∑ j, (certificateData D N).payoff s j*h j
  resources_nonneg := Finset.sum_nonneg
    (fun j _ => mul_nonneg ((certificateData D N).payoff_nonneg s j) (hh j))

omit [Fintype I] [Fintype S] in
theorem certificate_backing_identity (D : Data J S) (N : Denomination J)
    (h : J → ℝ) (hh : ∀ j, 0 ≤ h j) (loss : S → I → ℝ)
    (hloss : ∀ s i, 0 ≤ loss s i) (s : S) :
    (certificatePool D N h hh loss hloss s).resources=
      ∑ j, D.payoff s j*decode N h j :=
  future_receipt_identity D N h s

omit [Fintype S] in
theorem physical_settlement_budget (D : Data J S) (N : Denomination J)
    (h : J → ℝ) (hh : ∀ j, 0 ≤ h j) (loss : S → I → ℝ)
    (hloss : ∀ s i, 0 ≤ loss s i) (s : S) :
    (∑ i, payout (certificatePool D N h hh loss hloss s) i)+
      retained (certificatePool D N h hh loss hloss s)=
      ∑ j, D.payoff s j*decode N h j := by
  rw [settlement_budget,certificate_backing_identity]

omit [Fintype I] in
/-- The state valuation must price the backing assets consistently. This is an
explicit condition, not a claim that arbitrary weights come from equilibrium. -/
theorem certificate_portfolio_value (D : Data J S) (N : Denomination J)
    (h q : J → ℝ) (hh : ∀ j, 0 ≤ h j) (loss : S → I → ℝ)
    (hloss : ∀ s i, 0 ≤ loss s i) (weight : S → ℝ)
    (hprice : ∀ j, quote N q j=value weight (fun s => (certificateData D N).payoff s j)) :
    (∑ j, quote N q j*h j)=
      value weight (fun s => (certificatePool D N h hh loss hloss s).resources) := by
  simp only [hprice,value,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  change (∑ j, (weight s*(certificateData D N).payoff s j)*h j)=
    weight s*(∑ j, (certificateData D N).payoff s j*h j)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem certificate_protection_priced_budget (D : Data J S) (N : Denomination J)
    (h q : J → ℝ) (hh : ∀ j, 0 ≤ h j) (loss : S → I → ℝ)
    (hloss : ∀ s i, 0 ≤ loss s i) (weight : S → ℝ)
    (hprice : ∀ j, quote N q j=value weight (fun s => (certificateData D N).payoff s j)) :
    (∑ i, value weight (fun s => payout (certificatePool D N h hh loss hloss s) i))+
      value weight (fun s => retained (certificatePool D N h hh loss hloss s))=
      ∑ j, quote N q j*h j := by
  rw [priced_resource_budget]
  exact (certificate_portfolio_value D N h q hh loss hloss weight hprice).symm

/-- Current contributions finance both target protection and members' retained
surplus, plus explicit fees. This is cost accounting, not optimal participation. -/
theorem certificate_contribution_budget (D : Data J S) (N : Denomination J)
    (h q : J → ℝ) (hh : ∀ j, 0 ≤ h j) (loss : S → I → ℝ)
    (hloss : ∀ s i, 0 ≤ loss s i) (weight : S → ℝ)
    (hprice : ∀ j, quote N q j=value weight (fun s => (certificateData D N).payoff s j))
    (share fee : I → ℝ) (hsum : ∑ i, share i=1) :
    (∑ i, (value weight (fun s => memberPayoff
      (certificatePool D N h hh loss hloss s) share i)+fee i))=
      (∑ j, quote N q j*h j)+∑ i, fee i := by
  rw [Finset.sum_add_distrib,priced_member_budget _ _ share hsum]
  rw [← certificate_portfolio_value D N h q hh loss hloss weight hprice]

theorem contribution_nonneg (P : S → Pool I) (weight : S → ℝ)
    (hw : ∀ s, 0 ≤ weight s) (share fee : I → ℝ)
    (hshare : ∀ i, 0 ≤ share i) (hfee : ∀ i, 0 ≤ fee i) (i : I) :
    0 ≤ value weight (fun s => memberPayoff (P s) share i)+fee i :=
  add_nonneg (value_nonneg _ _ hw (fun s => member_payoff_nonneg (P s) share hshare i))
    (hfee i)

end CertificateBacking
end FundedProtection

#print axioms FundedProtection.total_nonneg
#print axioms FundedProtection.payout_nonneg
#print axioms FundedProtection.payout_le_claim
#print axioms FundedProtection.sum_payout
#print axioms FundedProtection.sum_payout_le_resources
#print axioms FundedProtection.retained_nonneg
#print axioms FundedProtection.unmet_nonneg
#print axioms FundedProtection.settlement_budget
#print axioms FundedProtection.unmet_eq_excess
#print axioms FundedProtection.full_payment_iff
#print axioms FundedProtection.full_payment_impossible
#print axioms FundedProtection.member_payoff_nonneg
#print axioms FundedProtection.member_settlement_budget
#print axioms FundedProtection.value_nonneg
#print axioms FundedProtection.value_add
#print axioms FundedProtection.value_sum
#print axioms FundedProtection.priced_resource_budget
#print axioms FundedProtection.priced_member_budget
#print axioms FundedProtection.priced_protection_le_resources
#print axioms FundedProtection.certificate_backing_identity
#print axioms FundedProtection.physical_settlement_budget
#print axioms FundedProtection.certificate_portfolio_value
#print axioms FundedProtection.certificate_protection_priced_budget
#print axioms FundedProtection.certificate_contribution_budget
#print axioms FundedProtection.contribution_nonneg
