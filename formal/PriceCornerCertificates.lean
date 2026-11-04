import ConnectedPayoutPrice

/-! A zero lower holding needs no score sign. Reuse the checked joint core. -/
noncomputable section
open scoped BigOperators
namespace PrimaryPriceCorners
open PrimaryCRRA PrimaryCRRAFormation VoluntaryPrimaryMarket PrimaryPriceCertificates
variable {I S : Type*} [Fintype I] [Fintype S]

theorem lower_certificate (H : Household S) {q x : ℝ} (hq : 0 < q)
    (hx : Feasible H q x) (hf : x=0 ∨ 0 ≤ score H q x) : x ≤ demand H q := by
  rcases hf with hz | hs
  · rw [hz]
    exact demand_nonnegative H q
  · exact lower_from_score H hq hx hs

theorem zero_demand_certificate (H : Household S) {q : ℝ} (hq : 0 < q)
    (hs : score H q 0 ≤ 0) : demand H q=0 := by
  apply le_antisymm _ (demand_nonnegative H q)
  exact upper_from_score H hq ⟨by norm_num,by simpa [current] using H.cash_pos⟩ hs

theorem certified_formation_with_corners (P : Plan) (E : Economy I S) {lo hi : ℝ}
    (hl : floorPrice P ≤ lo) (hh : lo ≤ hi) (lower upper : I → ℝ)
    (hlo : ∀ i, Feasible (E.buyers i) lo (lower i) ∧
      (lower i=0 ∨ 0 ≤ score (E.buyers i) lo (lower i)))
    (hhi : ∀ i, Feasible (E.buyers i) hi (upper i) ∧ score (E.buyers i) hi (upper i) ≤ 0)
    (lsum : supply P ≤ ∑ i, lower i) (usum : (∑ i, upper i) ≤ supply P) :
    ∃ q a, Equilibrium P E q a ∧ lo ≤ q ∧ q ≤ hi ∧
      |(lo+hi)/2-q| ≤ (hi-lo)/2 := by
  have hp : 0 < lo := lt_of_lt_of_le (floor_pos P) hl
  have ht : 0 < hi := lt_of_lt_of_le hp hh
  have hdlo : supply P ≤ PrimaryCRRAFormation.aggregate E lo :=
    lsum.trans (Finset.sum_le_sum (fun i _ => lower_certificate (E.buyers i) hp (hlo i).1 (hlo i).2))
  have hdhi : PrimaryCRRAFormation.aggregate E hi ≤ supply P :=
    (Finset.sum_le_sum (fun i _ => upper_from_score (E.buyers i) ht (hhi i).1 (hhi i).2)).trans usum
  obtain ⟨q,a,he⟩ := PrimaryCRRAFormation.voluntary_formation_exists P E
    (hdlo.trans (PrimaryCRRAFormation.aggregate_antitone E (floor_pos P) hp hl))
  have hq := price_enclosure P E he hp ht hdlo hdhi
  exact ⟨q,a,he,hq.1,hq.2,midpoint_error hq⟩

end PrimaryPriceCorners
#print axioms PrimaryPriceCorners.lower_certificate
#print axioms PrimaryPriceCorners.zero_demand_certificate
#print axioms PrimaryPriceCorners.certified_formation_with_corners
