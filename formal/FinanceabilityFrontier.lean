import PrimaryCRRAFormation
import FormationLedgerCore

/-! A fixed-supply viability frontier, not a theorem about changing technology.
Household resources/preferences and productive payoffs are held fixed. -/
noncomputable section
open scoped BigOperators
namespace FinanceabilityFrontier
open PrimaryCRRA PrimaryCRRAFormation VoluntaryPrimaryMarket

def cost (P : Plan) : ℝ := P.physicalCost+P.buffer+P.outside
def Formed {I S : Type*} [Fintype I] [Fintype S] (P : Plan) (E : Economy I S) : Prop :=
  ∃ q a, Equilibrium P E q a

variable {I S : Type*} [Fintype I] [Fintype S]

theorem transfer (P Q : Plan) (E : Economy I S) {q : ℝ} {a : I → ℝ}
    (he : Equilibrium P E q a) (hn : P.cap=Q.cap)
    (hc : cost Q ≤ q*supply P) : Equilibrium Q E q a := by
  have hs : supply P=supply Q := by simp [supply,hn]
  refine ⟨he.price_pos,he.feasible,he.optimal,?_,?_,?_⟩
  · exact he.clearing.trans hs
  · simpa only [cost,hs] using hc
  · apply (issuer_entry_iff_funding Q q).mpr
    apply (funding_iff_floor Q q).mp
    simpa only [cost,hs] using hc

theorem formed_prices_holdings_invariant (P Q : Plan) (E : Economy I S)
    {p q : ℝ} {a b : I → ℝ} (hp : Equilibrium P E p a)
    (hq : Equilibrium Q E q b) (hn : P.cap=Q.cap) : p=q ∧ a=b := by
  have hs : supply P=supply Q := by simp [supply,hn]
  have ha := actual_optimizer_identified P E hp
  have hb := actual_optimizer_identified Q E hq
  have hpa : PrimaryCRRAFormation.aggregate E p=supply P := by
    unfold PrimaryCRRAFormation.aggregate; simpa only [← ha] using hp.clearing
  have hqa : PrimaryCRRAFormation.aggregate E q=supply P := by
    unfold PrimaryCRRAFormation.aggregate; simpa only [← hb,hs] using hq.clearing
  have heq := clearing_price_unique P E hp.price_pos hq.price_pos hpa hqa
  refine ⟨heq,?_⟩
  funext i
  rw [ha i,hb i,heq]

theorem exact_frontier (P Q : Plan) (E : Economy I S) {q : ℝ} {a : I → ℝ}
    (he : Equilibrium P E q a) (hn : P.cap=Q.cap) :
    Formed Q E ↔ cost Q ≤ q*supply P := by
  constructor
  · rintro ⟨p,b,hb⟩
    have hid := (formed_prices_holdings_invariant P Q E he hb hn).1
    have hs : supply P=supply Q := by simp [supply,hn]
    simpa only [cost,hid,hs] using hb.funded
  · intro hc
    exact ⟨q,a,transfer P Q E he hn hc⟩

theorem reserve_frontier (P Q : Plan) (E : Economy I S) {q : ℝ} {a : I → ℝ}
    (he : Equilibrium P E q a) (hn : P.cap=Q.cap) :
    Formed Q E ↔ Q.buffer ≤ q*supply P-Q.physicalCost-Q.outside := by
  rw [exact_frontier P Q E he hn]
  unfold cost
  constructor <;> intro h <;> linarith

theorem lower_cost_preserves_formation (P Q : Plan) (E : Economy I S)
    (he : Formed P E) (hn : P.cap=Q.cap) (hc : cost Q ≤ cost P) : Formed Q E := by
  obtain ⟨q,a,ha⟩ := he
  exact ⟨q,a,transfer P Q E ha hn (hc.trans ha.funded)⟩

theorem above_frontier_no_formation (P Q : Plan) (E : Economy I S)
    {q : ℝ} {a : I → ℝ} (he : Equilibrium P E q a) (hn : P.cap=Q.cap)
    (hc : q*supply P < cost Q) : ¬ Formed Q E := by
  rw [exact_frontier P Q E he hn]
  exact not_le.mpr hc

theorem safe_reserve_window {T : Type*} (P Q : Plan) (E : Economy I S)
    {q : ℝ} {a : I → ℝ} (he : Equilibrium P E q a) (hn : P.cap=Q.cap)
    (flows : T → List ℝ) :
    (Formed Q E ∧ ∀ t, FormationLedgerCore.CashSafe Q.buffer (flows t)) ↔
      ((∀ t, FormationLedgerCore.bufferNeeded (flows t) ≤ Q.buffer) ∧
        Q.buffer ≤ q*supply P-Q.physicalCost-Q.outside) := by
  rw [reserve_frontier P Q E he hn]
  simp only [FormationLedgerCore.safe_iff_buffer]
  exact and_comm

end FinanceabilityFrontier
#print axioms FinanceabilityFrontier.transfer
#print axioms FinanceabilityFrontier.formed_prices_holdings_invariant
#print axioms FinanceabilityFrontier.exact_frontier
#print axioms FinanceabilityFrontier.reserve_frontier
#print axioms FinanceabilityFrontier.lower_cost_preserves_formation
#print axioms FinanceabilityFrontier.above_frontier_no_formation
#print axioms FinanceabilityFrontier.safe_reserve_window
