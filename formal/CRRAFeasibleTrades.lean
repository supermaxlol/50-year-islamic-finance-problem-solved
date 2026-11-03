import FeasibleRayCalculus
import CRRAOverlapMarginalBounds
import SlackBoundTransfer

/-!
Actual affordable buy/sell paths in the bounded heterogeneous CRRA ownership
problem. The derivative is calculated from the physical payoff objective;
its sign is then derived from actual household optimality. In particular a
small sale remains feasible at a binding current-consumption floor.
-/

noncomputable section
open scoped BigOperators Topology
open Set Filter OwnershipBridge OwnershipCRRA OwnershipMarginal OwnershipBounds

namespace OwnershipTrade

variable {J S : Type*} [Fintype J] [Fintype S]

def ray {G : Type*} (x v : G → ℝ) (t : ℝ) : G → ℝ :=
  fun g => x g + t * v g

@[simp] theorem ray_zero {G : Type*} (x v : G → ℝ) : ray x v 0 = x := by
  ext g
  simp [ray]

def outputDirection (D : Data J S) (v : Option J → ℝ) : Option S → ℝ
  | none => v none
  | some s => ∑ j, D.payoff s j * v (some j)

def objectiveSlope (D : Data J S) (x v : Option J → ℝ) : ℝ :=
  ∑ r, mass D r * (receipts D x r) ^ (-curvature D r) * outputDirection D v r

omit [Fintype S] in
theorem receipts_ray (D : Data J S) (x v : Option J → ℝ) (t : ℝ)
    (r : Option S) :
    receipts D (ray x v t) r = receipts D x r + t * outputDirection D v r := by
  cases r with
  | none => dsimp [receipts, ray, outputDirection]; ring
  | some s =>
    dsimp [receipts, ray, outputDirection]
    have hs : (∑ j, D.payoff s j * (x (some j) + t * v (some j))) =
        ∑ j, (D.payoff s j * x (some j) + t * (D.payoff s j * v (some j))) := by
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hs]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    ring

theorem objective_ray_hasDerivAt (D : Data J S) (x v : Option J → ℝ)
    (hx : ∀ g, 0 ≤ x g) :
    HasDerivAt (fun t : ℝ => objective D (ray x v t)) (objectiveSlope D x v) 0 := by
  have hr : ∀ r, HasDerivAt (fun t : ℝ => receipts D (ray x v t) r)
      (outputDirection D v r) 0 := by
    intro r
    have heq : (fun t : ℝ => receipts D (ray x v t) r) =
        (fun t : ℝ => receipts D x r + t * outputDirection D v r) :=
      funext fun t => receipts_ray D x v t r
    rw [heq]
    convert! (hasDerivAt_const (0 : ℝ) (receipts D x r)).fun_add
      ((hasDerivAt_id (0 : ℝ)).mul_const (outputDirection D v r)) using 1
    simp
  have hu : ∀ r, HasDerivAt
      (fun t : ℝ => mass D r * utility (curvature D r) (receipts D (ray x v t) r))
      (mass D r * ((receipts D x r)^(-curvature D r) * outputDirection D v r)) 0 := by
    intro r
    have hp : 0 < receipts D (ray x v 0) r := by
      simpa only [ray_zero] using receipts_positive D hx r
    have h := (utility_hasDerivAt (g := curvature D r) hp).comp 0 (hr r)
    convert! h.const_mul (mass D r) using 1
    simp only [ray_zero]
  have hs := HasDerivAt.fun_sum (u := Finset.univ) (fun r _ => hu r)
  simpa only [objective, objectiveSlope, mul_assoc] using hs

omit [Fintype S] in
theorem cost_ray (q : J → ℝ) (x v : Option J → ℝ) (t : ℝ) :
    cost q (ray x v t) = cost q x + t * cost q v := by
  have heq : ray x v t = (1 : ℝ) • x + t • v := by
    ext g
    simp [ray]
  rw [heq, cost_combo, one_mul]

theorem optimal_ray_slope_nonpos (D : Data J S) (M : ℝ)
    (ω x v : Option J → ℝ) (q : J → ℝ)
    (hopt : IsNumeraireOptimal M ω (objective D) q x)
    (hcap : ∀ g, x g < M)
    (hnegative : ∀ g, v g < 0 → 0 < x g)
    (hcost : cost q v = 0) : objectiveSlope D x v ≤ 0 := by
  have hf := positive_ray_in_box M x v (fun g => (hopt.1 g).1) hcap hnegative
  apply right_derivative_nonpos (objective_ray_hasDerivAt D x v
    (fun g => (hopt.1 g).1))
  filter_upwards [hf] with t ht
  have hb : cost q (ray x v t) ≤ cost q ω := by
    rw [cost_ray, hcost, mul_zero, add_zero]
    exact hopt.2.1
  have hmax := hopt.2.2 (ray x v t) ht hb
  simpa only [ray_zero] using hmax

def buyDirection (q : J → ℝ) (j : J) : Option J → ℝ := by
  classical
  exact fun g => match g with
    | none => -q j
    | some k => if k = j then 1 else 0

omit [Fintype S] in
theorem buy_direction_cost (q : J → ℝ) (j : J) : cost q (buyDirection q j) = 0 := by
  classical
  simp [cost, buyDirection, mul_ite]

omit [Fintype S] in
theorem outputDirection_buy (D : Data J S) (q : J → ℝ) (j : J) (s : S) :
    outputDirection D (buyDirection q j) (some s) = D.payoff s j := by
  classical
  simp [outputDirection, buyDirection, mul_ite]

theorem slope_buy (D : Data J S) (x : Option J → ℝ) (q : J → ℝ) (j : J) :
    objectiveSlope D x (buyDirection q j) =
      marginal D (fun k => x (some k)) j - q j * (x none + D.delta)^(-D.gamma) := by
  classical
  have hs : (∑ s, mass D (some s) * (receipts D x (some s))^(-curvature D (some s)) *
      outputDirection D (buyDirection q j) (some s)) =
      marginal D (fun k => x (some k)) j := by
    dsimp [marginal, consumption]
    apply Finset.sum_congr rfl
    intro s _
    rw [outputDirection_buy]
    dsimp [mass, receipts, curvature]
    ring
  rw [objectiveSlope, Fintype.sum_option, hs]
  dsimp [mass, curvature, receipts, outputDirection, buyDirection]
  ring

theorem slope_neg (D : Data J S) (x v : Option J → ℝ) :
    objectiveSlope D x (-v) = -objectiveSlope D x v := by
  have ho : ∀ r, outputDirection D (-v) r = -outputDirection D v r := by
    intro r
    cases r with
    | none => rfl
    | some s => simp [outputDirection, Finset.sum_neg_distrib]
  simp [objectiveSlope, ho, Finset.sum_neg_distrib]

omit [Fintype S] in
theorem cost_neg (q : J → ℝ) (v : Option J → ℝ) : cost q (-v) = -cost q v := by
  simp only [cost, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
  ring

theorem buy_inequality (D : Data J S) (M : ℝ) (ω x : Option J → ℝ)
    (q : J → ℝ) (j : J)
    (hopt : IsNumeraireOptimal M ω (objective D) q x)
    (hcap : ∀ g, x g < M) (hfloor : 0 < x none) :
    marginal D (fun k => x (some k)) j ≤ q j * (x none + D.delta)^(-D.gamma) := by
  have hn : ∀ g, buyDirection q j g < 0 → 0 < x g := by
    intro g hg
    cases g with
    | none => exact hfloor
    | some k =>
      have hh : 0 ≤ buyDirection q j (some k) := by
        by_cases hk : k = j <;> simp [buyDirection, hk]
      exact False.elim (not_lt_of_ge hh hg)
  have hs := optimal_ray_slope_nonpos D M ω x (buyDirection q j) q
    hopt hcap hn (buy_direction_cost q j)
  rw [slope_buy] at hs
  linarith

theorem sell_inequality (D : Data J S) (M : ℝ) (ω x : Option J → ℝ)
    (q : J → ℝ) (j : J) (hq : 0 ≤ q j)
    (hopt : IsNumeraireOptimal M ω (objective D) q x)
    (hcap : ∀ g, x g < M) (howned : 0 < x (some j)) :
    q j * (x none + D.delta)^(-D.gamma) ≤ marginal D (fun k => x (some k)) j := by
  have hn : ∀ g, (-buyDirection q j) g < 0 → 0 < x g := by
    intro g hg
    cases g with
    | none =>
      have heq : (-buyDirection q j) none = q j := by simp [buyDirection]
      rw [heq] at hg
      exact False.elim (not_lt_of_ge hq hg)
    | some k =>
      by_cases hk : k = j
      · simpa [hk] using howned
      · simp [buyDirection, hk] at hg
  have hz : cost q (-buyDirection q j) = 0 := by
    rw [cost_neg, buy_direction_cost, neg_zero]
  have hs := optimal_ray_slope_nonpos D M ω x (-buyDirection q j) q hopt hcap hn hz
  rw [slope_neg, slope_buy] at hs
  linarith

theorem owned_asset_euler_equality (D : Data J S) (M : ℝ)
    (ω x : Option J → ℝ) (q : J → ℝ) (j : J) (hq : 0 ≤ q j)
    (hopt : IsNumeraireOptimal M ω (objective D) q x)
    (hcap : ∀ g, x g < M) (hfloor : 0 < x none) (howned : 0 < x (some j)) :
    marginal D (fun k => x (some k)) j = q j * (x none + D.delta)^(-D.gamma) :=
  le_antisymm (buy_inequality D M ω x q j hopt hcap hfloor)
    (sell_inequality D M ω x q j hq hopt hcap howned)

/- Controls: a floor-binding seller is allowed; a buyer at that floor is not.
These do not assume that the entire artificial floor has already been removed. -/
namespace Controls

theorem floor_seller (D : Data J S) (M : ℝ) (ω x : Option J → ℝ)
    (q : J → ℝ) (j : J) (hq : 0 ≤ q j)
    (hopt : IsNumeraireOptimal M ω (objective D) q x)
    (hcap : ∀ g, x g < M) (hfloor : x none = 0) (howned : 0 < x (some j)) :
    q j * D.delta^(-D.gamma) ≤ upper D j := by
  have hs := sell_inequality D M ω x q j hq hopt hcap howned
  rw [hfloor, zero_add] at hs
  exact hs.trans (marginal_le_upper D (fun k => (hopt.1 (some k)).1) j)

omit [Fintype J] [Fintype S] in
theorem floor_buy_is_infeasible (M : ℝ) (x : Option J → ℝ)
    (q : J → ℝ) (j : J) (hq : 0 < q j) (hfloor : x none = 0)
    (t : ℝ) (ht : 0 < t) : ray x (buyDirection q j) t ∉ box M := by
  intro hin
  have h := (hin none).1
  have hp := mul_pos ht hq
  simp [ray, buyDirection, hfloor] at h
  linarith

theorem genuine_one_sided_max_not_stationary :
    HasDerivAt (fun t : ℝ => -t) (-1) 0 ∧
    (∀ᶠ t in 𝓝[>] (0 : ℝ), -t ≤ -(0 : ℝ)) ∧ (-1 : ℝ) < 0 := by
  refine ⟨?_, ?_, by norm_num⟩
  · convert! (hasDerivAt_id (0 : ℝ)).neg using 1
  · have ht : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
    filter_upwards [ht] with t ht
    linarith

end Controls
end OwnershipTrade

#print axioms OwnershipTrade.ray_zero
#print axioms OwnershipTrade.receipts_ray
#print axioms OwnershipTrade.objective_ray_hasDerivAt
#print axioms OwnershipTrade.cost_ray
#print axioms OwnershipTrade.optimal_ray_slope_nonpos
#print axioms OwnershipTrade.buy_direction_cost
#print axioms OwnershipTrade.outputDirection_buy
#print axioms OwnershipTrade.slope_buy
#print axioms OwnershipTrade.slope_neg
#print axioms OwnershipTrade.cost_neg
#print axioms OwnershipTrade.buy_inequality
#print axioms OwnershipTrade.sell_inequality
#print axioms OwnershipTrade.owned_asset_euler_equality
#print axioms OwnershipTrade.Controls.floor_seller
#print axioms OwnershipTrade.Controls.floor_buy_is_infeasible
#print axioms OwnershipTrade.Controls.genuine_one_sided_max_not_stationary
