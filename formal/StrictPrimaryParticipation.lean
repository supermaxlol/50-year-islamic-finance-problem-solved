import FinanceabilityFrontier
import ConnectedEnterpriseDemo
import Mathlib.Algebra.Order.Ring.Cast

/-! Strict participation, not forced entry or guaranteed project profitability.
All household primitives, productive receipts and the issue remain supplied. -/
noncomputable section
open scoped BigOperators

namespace StrictPrimaryParticipation
open PrimaryCRRA PrimaryCRRAFormation VoluntaryPrimaryMarket

def StrictIssuer (P : Plan) (q : ℝ) : Prop :=
  issuerUtility P q false < issuerUtility P q true

theorem issuer_strict_iff_cost (P : Plan) (q : ℝ) :
    StrictIssuer P q ↔ P.physicalCost+P.buffer+P.outside < q*supply P := by
  change P.outside < q*supply P-P.buffer-P.physicalCost ↔
    P.physicalCost+P.buffer+P.outside < q*supply P
  constructor <;> intro h <;> linarith

theorem issuer_strict_iff_price (P : Plan) (q : ℝ) :
    StrictIssuer P q ↔ floorPrice P < q := by
  rw [issuer_strict_iff_cost]
  exact (div_lt_iff₀ (supply_pos P)).symm

variable {I S : Type*} [Fintype I] [Fintype S]

theorem equilibrium_strict_iff_demand (P : Plan) (E : Economy I S)
    {q : ℝ} {a : I → ℝ} (he : Equilibrium P E q a) :
    StrictIssuer P q ↔ supply P < PrimaryCRRAFormation.aggregate E (floorPrice P) := by
  have hid := actual_optimizer_identified P E he
  have hc : PrimaryCRRAFormation.aggregate E q = supply P := by
    unfold PrimaryCRRAFormation.aggregate
    simpa only [← hid] using he.clearing
  constructor
  · intro hs
    have hp := (issuer_strict_iff_price P q).mp hs
    have hd := PrimaryCRRAFormation.aggregate_strict_on_positive E (floor_pos P)
      he.price_pos hp (by rw [hc]; exact supply_pos P)
    simpa only [hc] using hd
  · intro hd
    apply (issuer_strict_iff_price P q).mpr
    have hle := (funding_iff_floor P q).mp he.funded
    by_contra hn
    have heq : floorPrice P=q := le_antisymm hle (le_of_not_gt hn)
    rw [heq,hc] at hd
    exact (lt_irrefl _) hd

theorem strict_formation_iff (P : Plan) (E : Economy I S) :
    (∃ q a, Equilibrium P E q a ∧ StrictIssuer P q) ↔
      supply P < PrimaryCRRAFormation.aggregate E (floorPrice P) := by
  constructor
  · rintro ⟨q,a,he,hs⟩
    exact (equilibrium_strict_iff_demand P E he).mp hs
  · intro hd
    obtain ⟨q,a,he⟩ := voluntary_formation_exists P E hd.le
    exact ⟨q,a,he,(equilibrium_strict_iff_demand P E he).mpr hd⟩

theorem subscriber_strict_iff_positive (P : Plan) (E : Economy I S)
    {q : ℝ} {a : I → ℝ} (he : Equilibrium P E q a) (i : I) :
    value (E.buyers i) q 0 < value (E.buyers i) q (a i) ↔ 0 < a i := by
  constructor
  · intro hv
    by_contra hn
    have hz : a i=0 := le_antisymm (le_of_not_gt hn) (he.feasible i).1
    rw [hz] at hv
    exact (lt_irrefl _) hv
  · intro ha
    have hid := actual_optimizer_identified P E he
    have hn : (0 : ℝ) ≠ demand (E.buyers i) q := by
      rw [← hid i]
      exact ne_of_lt ha
    have hz : Feasible (E.buyers i) q 0 :=
      ⟨le_refl 0,by simpa [current] using (E.buyers i).cash_pos⟩
    simpa only [← hid i] using actual_unique_optimum (E.buyers i) he.price_pos hz hn

theorem some_subscriber_strict (P : Plan) (E : Economy I S)
    {q : ℝ} {a : I → ℝ} (he : Equilibrium P E q a) :
    ∃ i, 0 < a i ∧ value (E.buyers i) q 0 < value (E.buyers i) q (a i) := by
  classical
  have hex : ∃ i, 0 < a i := by
    by_contra hn
    have hs : (∑ i, a i) ≤ 0 :=
      Finset.sum_nonpos (fun i _ => le_of_not_gt (fun h => hn ⟨i,h⟩))
    rw [he.clearing] at hs
    exact (not_le.mpr (supply_pos P)) hs
  obtain ⟨i,hi⟩ := hex
  exact ⟨i,hi,(subscriber_strict_iff_positive P E he i).mpr hi⟩

def profitablePlan : Plan :=
  ⟨6,6,5,0,by decide,by norm_num,by norm_num,by norm_num,by norm_num⟩

theorem strict_fixture :
    Equilibrium profitablePlan ConnectedEnterpriseDemo.economy 2 (fun _ => 3) ∧
    issuerUtility profitablePlan 2 true=1 ∧ issuerUtility profitablePlan 2 false=0 ∧
    (∀ i : Fin 2, value (ConnectedEnterpriseDemo.buyer i) 2 0 <
      value (ConnectedEnterpriseDemo.buyer i) 2 3) := by
  have he : Equilibrium profitablePlan ConnectedEnterpriseDemo.economy 2 (fun _ => 3) :=
    FinanceabilityFrontier.transfer ConnectedEnterpriseDemo.plan profitablePlan
      ConnectedEnterpriseDemo.economy ConnectedEnterpriseDemo.actual_formation rfl
      (by norm_num [FinanceabilityFrontier.cost,profitablePlan,supply,ConnectedEnterpriseDemo.plan])
  refine ⟨he,?_,?_,?_⟩
  · norm_num [issuerUtility,constructionQuote,supply,profitablePlan]
  · norm_num [issuerUtility,profitablePlan]
  · intro i
    exact (subscriber_strict_iff_positive profitablePlan ConnectedEnterpriseDemo.economy he i).mpr
      (by norm_num)

theorem original_fixture_issuer_indifferent :
    issuerUtility ConnectedEnterpriseDemo.plan 2 true =
      issuerUtility ConnectedEnterpriseDemo.plan 2 false := by
  norm_num [issuerUtility,constructionQuote,supply,ConnectedEnterpriseDemo.plan]

end StrictPrimaryParticipation

namespace CashflowStressReserve
open FormationLedgerCore

def prefixCash (xs : List ℝ) (n : ℕ) : ℝ := (xs.take n).sum

theorem safe_iff_prefix (b : ℝ) (xs : List ℝ) :
    CashSafe b xs ↔ ∀ n, 0 ≤ b+prefixCash xs n := by
  induction xs generalizing b with
  | nil => simp [CashSafe,prefixCash]
  | cons x xs ih =>
    simp only [CashSafe,ih]
    constructor
    · rintro ⟨hb,h⟩ n
      cases n with
      | zero => simpa [prefixCash] using hb
      | succ n => simpa [prefixCash,List.take_succ_cons,List.sum_cons,add_assoc] using h n
    · intro h
      refine ⟨by simpa [prefixCash] using h 0,?_⟩
      intro n
      simpa [prefixCash,List.take_succ_cons,List.sum_cons,add_assoc] using h (n+1)

/-- Every stressed cumulative receipt is within eps below its nominal value.
Lists represent aligned decision dates; calendar alignment is supplied. -/
def PrefixLossBound (eps : ℝ) (nominal stressed : List ℝ) : Prop :=
  ∀ n, prefixCash nominal n-eps ≤ prefixCash stressed n

theorem stress_preserves_safety (b eps : ℝ) (xs ys : List ℝ)
    (hs : CashSafe b xs) (hb : PrefixLossBound eps xs ys) : CashSafe (b+eps) ys := by
  apply (safe_iff_prefix _ _).mpr
  intro n
  have hn := (safe_iff_prefix b xs).mp hs n
  have he := hb n
  linarith

theorem buffer_stress_bound (eps : ℝ) (xs ys : List ℝ)
    (hb : PrefixLossBound eps xs ys) : bufferNeeded ys ≤ bufferNeeded xs+eps := by
  exact (safe_iff_buffer ys _).mp (stress_preserves_safety _ eps xs ys
    ((safe_iff_buffer xs _).mpr (le_refl _)) hb)

theorem buffer_lipschitz (eps : ℝ) (xs ys : List ℝ)
    (hxy : PrefixLossBound eps xs ys) (hyx : PrefixLossBound eps ys xs) :
    |bufferNeeded ys-bufferNeeded xs| ≤ eps := by
  have hx := buffer_stress_bound eps xs ys hxy
  have hy := buffer_stress_bound eps ys xs hyx
  apply abs_le.mpr
  constructor <;> linarith

theorem funded_stress_window {I S T : Type*} [Fintype I] [Fintype S]
    (P Q : VoluntaryPrimaryMarket.Plan) (E : PrimaryCRRAFormation.Economy I S)
    {q : ℝ} {a : I → ℝ} (he : PrimaryCRRAFormation.Equilibrium P E q a)
    (hn : P.cap=Q.cap) (nominal stressed : T → List ℝ) (L eps : ℝ)
    (hl : ∀ t, bufferNeeded (nominal t) ≤ L)
    (hs : ∀ t, PrefixLossBound eps (nominal t) (stressed t))
    (hb : L+eps ≤ Q.buffer)
    (hu : Q.buffer ≤ q*VoluntaryPrimaryMarket.supply P-Q.physicalCost-Q.outside) :
    FinanceabilityFrontier.Formed Q E ∧ ∀ t, CashSafe Q.buffer (stressed t) := by
  apply (FinanceabilityFrontier.safe_reserve_window P Q E he hn stressed).mpr
  refine ⟨?_,hu⟩
  intro t
  have h := buffer_stress_bound eps (nominal t) (stressed t) (hs t)
  have ht := hl t
  linarith

theorem terminal_cash_preserved (b : ℝ) (xs ys : List ℝ) (ht : xs.sum=ys.sum) :
    cashAfter b xs=cashAfter b ys := by
  rw [cash_after_identity,cash_after_identity,ht]

theorem delayed_receipt_example :
    bufferNeeded [3,-5,12]=2 ∧ bufferNeeded [0,-5,15]=5 ∧
    ([3,-5,12] : List ℝ).sum=([0,-5,15] : List ℝ).sum ∧
    PrefixLossBound 3 [3,-5,12] [0,-5,15] := by
  refine ⟨by norm_num [bufferNeeded],by norm_num [bufferNeeded],by norm_num,?_⟩
  intro n
  cases n with
  | zero => norm_num [prefixCash]
  | succ n =>
    cases n with
    | zero => norm_num [prefixCash]
    | succ n =>
      cases n with
      | zero => norm_num [prefixCash]
      | succ n => norm_num [prefixCash,List.take_succ_cons]

end CashflowStressReserve

end

namespace ReserveCalculator

/-- Signed minor-unit cash events. No floating point or rounding. -/
def needed : List ℤ → ℤ
  | [] => 0
  | x::xs => max 0 (needed xs-x)

def Affordable : ℤ → List ℤ → Prop
  | b,[] => 0 ≤ b
  | b,x::xs => 0 ≤ b ∧ Affordable (b+x) xs

def firstShortfall : ℤ → List ℤ → Option ℕ
  | b,[] => if b<0 then some 0 else none
  | b,x::xs => if b<0 then some 0 else (firstShortfall (b+x) xs).map Nat.succ

def inspect (b : ℤ) (xs : List ℤ) : ℤ × Option ℕ := (needed xs,firstShortfall b xs)

theorem needed_nonnegative (xs : List ℤ) : 0 ≤ needed xs := by
  cases xs with
  | nil => exact le_rfl
  | cons x xs => exact le_max_left _ _

theorem affordable_iff (b : ℤ) (xs : List ℤ) : Affordable b xs ↔ needed xs ≤ b := by
  induction xs generalizing b with
  | nil => rfl
  | cons x xs ih =>
    simp only [Affordable,needed,max_le_iff,ih]
    omega

theorem needed_is_least (xs : List ℤ) :
    Affordable (needed xs) xs ∧ ∀ b, Affordable b xs → needed xs ≤ b := by
  exact ⟨(affordable_iff _ _).mpr (le_rfl),fun b hb => (affordable_iff b xs).mp hb⟩

theorem firstShortfall_none_iff (b : ℤ) (xs : List ℤ) :
    firstShortfall b xs=none ↔ Affordable b xs := by
  induction xs generalizing b with
  | nil =>
    by_cases h : b<0
    · have hn : ¬(0 ≤ b) := not_le.mpr h
      simp [firstShortfall,Affordable,h,hn]
    · have hn : 0 ≤ b := le_of_not_gt h
      simp [firstShortfall,Affordable,h,hn]
  | cons x xs ih =>
    by_cases h : b<0
    · have hn : ¬(0 ≤ b) := not_le.mpr h
      simp [firstShortfall,Affordable,h,hn]
    · have hn : 0 ≤ b := le_of_not_gt h
      simp [firstShortfall,h,Affordable,hn,ih]

theorem firstShortfall_certificate (b : ℤ) (xs : List ℤ) (n : ℕ)
    (hn : firstShortfall b xs=some n) :
    n ≤ xs.length ∧ b+(xs.take n).sum < 0 ∧
      ∀ k, k<n → 0 ≤ b+(xs.take k).sum := by
  induction xs generalizing b n with
  | nil =>
    by_cases hb : b<0
    · have he : n=0 := by simpa [firstShortfall,hb] using hn.symm
      subst n
      exact ⟨by simp,by simpa using hb,by intro k hk; omega⟩
    · simp [firstShortfall,hb] at hn
  | cons x xs ih =>
    by_cases hb : b<0
    · have he : n=0 := by simpa [firstShortfall,hb] using hn.symm
      subst n
      exact ⟨by simp,by simpa using hb,by intro k hk; omega⟩
    · have hnon : 0 ≤ b := le_of_not_gt hb
      cases hr : firstShortfall (b+x) xs with
      | none => simp [firstShortfall,hb,hr] at hn
      | some m =>
        have he : n=m+1 := by simpa [firstShortfall,hb,hr] using hn.symm
        subst n
        have ht := ih (b+x) m hr
        refine ⟨by simpa using Nat.succ_le_succ ht.1,?_,?_⟩
        · simpa [List.take_succ_cons,List.sum_cons,add_assoc] using ht.2.1
        · intro k hk
          cases k with
          | zero => simpa using hnon
          | succ k =>
            have hh := ht.2.2 k (by omega)
            simpa [List.take_succ_cons,List.sum_cons,add_assoc] using hh

noncomputable def decoded (delta : ℝ) (xs : List ℤ) : List ℝ :=
  xs.map (fun (x : ℤ) => delta*(x : ℝ))

theorem needed_decodes (delta : ℝ) (hd : 0 ≤ delta) (xs : List ℤ) :
    FormationLedgerCore.bufferNeeded (decoded delta xs)=delta*(needed xs : ℝ) := by
  induction xs with
  | nil => simp [FormationLedgerCore.bufferNeeded,decoded,needed]
  | cons x xs ih =>
    change max 0 (FormationLedgerCore.bufferNeeded (decoded delta xs)-delta*(x : ℝ)) =
      delta*(needed (x::xs) : ℝ)
    rw [ih]
    simp only [needed,Int.cast_max,Int.cast_zero,Int.cast_sub]
    rw [mul_max_of_nonneg _ _ hd]
    simp only [mul_zero,mul_sub]

theorem exact_real_affordability (delta : ℝ) (hd : 0 < delta) (b : ℤ) (xs : List ℤ) :
    FormationLedgerCore.CashSafe (delta*(b : ℝ)) (decoded delta xs) ↔ needed xs ≤ b := by
  rw [FormationLedgerCore.safe_iff_buffer,needed_decodes delta hd.le xs]
  rw [mul_le_mul_iff_of_pos_left hd]
  exact Int.cast_le

theorem calculator_correct (delta : ℝ) (hd : 0 < delta) (b : ℤ) (xs : List ℤ) :
    (inspect b xs).2=none ↔ FormationLedgerCore.CashSafe (delta*(b : ℝ)) (decoded delta xs) := by
  change firstShortfall b xs=none ↔ _
  rw [firstShortfall_none_iff,affordable_iff,exact_real_affordability delta hd]

theorem exact_examples :
    inspect 5 [-5,12]=(5,none) ∧ inspect 4 [-5,12]=(5,some 1) ∧
    inspect 2 [0,-5,15]=(5,some 2) ∧ inspect 2 [3,-5,12]=(2,none) := by decide

theorem certified_strict_funding {I S T : Type*} [Fintype I] [Fintype S]
    (P Q : VoluntaryPrimaryMarket.Plan) (E : PrimaryCRRAFormation.Economy I S)
    {q : ℝ} {a : I → ℝ} (he : PrimaryCRRAFormation.Equilibrium P E q a)
    (hn : P.cap=Q.cap) (delta : ℝ) (hd : 0 < delta) (b : ℤ)
    (hr : Q.buffer=delta*(b : ℝ))
    (hb : Q.physicalCost+Q.buffer+Q.outside < q*VoluntaryPrimaryMarket.supply P)
    (flows : T → List ℤ) (hc : ∀ t, (inspect b (flows t)).2=none) :
    PrimaryCRRAFormation.Equilibrium Q E q a ∧ StrictPrimaryParticipation.StrictIssuer Q q ∧
      ∀ t, FormationLedgerCore.CashSafe Q.buffer (decoded delta (flows t)) := by
  have heq := FinanceabilityFrontier.transfer P Q E he hn
    (by simpa only [FinanceabilityFrontier.cost] using hb.le)
  have hs : VoluntaryPrimaryMarket.supply P=VoluntaryPrimaryMarket.supply Q := by
    simp [VoluntaryPrimaryMarket.supply,hn]
  refine ⟨heq,?_,?_⟩
  · apply (StrictPrimaryParticipation.issuer_strict_iff_cost Q q).mpr
    simpa only [hs] using hb
  · intro t
    rw [hr]
    exact (calculator_correct delta hd b (flows t)).mp (hc t)

end ReserveCalculator

#print axioms StrictPrimaryParticipation.issuer_strict_iff_cost
#print axioms StrictPrimaryParticipation.equilibrium_strict_iff_demand
#print axioms StrictPrimaryParticipation.strict_formation_iff
#print axioms StrictPrimaryParticipation.subscriber_strict_iff_positive
#print axioms StrictPrimaryParticipation.some_subscriber_strict
#print axioms StrictPrimaryParticipation.strict_fixture
#print axioms StrictPrimaryParticipation.original_fixture_issuer_indifferent
#print axioms CashflowStressReserve.safe_iff_prefix
#print axioms CashflowStressReserve.stress_preserves_safety
#print axioms CashflowStressReserve.buffer_stress_bound
#print axioms CashflowStressReserve.buffer_lipschitz
#print axioms CashflowStressReserve.funded_stress_window
#print axioms CashflowStressReserve.terminal_cash_preserved
#print axioms CashflowStressReserve.delayed_receipt_example
#print axioms ReserveCalculator.needed_nonnegative
#print axioms ReserveCalculator.needed_is_least
#print axioms ReserveCalculator.firstShortfall_none_iff
#print axioms ReserveCalculator.firstShortfall_certificate
#print axioms ReserveCalculator.needed_decodes
#print axioms ReserveCalculator.exact_real_affordability
#print axioms ReserveCalculator.calculator_correct
#print axioms ReserveCalculator.exact_examples
#print axioms ReserveCalculator.certified_strict_funding
