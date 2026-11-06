import Mathlib

/-!
Stage 232 (draft): three frontier slices.
- Decreasing-returns production → strictly positive economic rent (item 3c).
- A certified worked example (item 4).
- Money object: value from convenience yield, not cashflow (item 1, slice).

All are self-contained real-analysis / finite-sum facts (import Mathlib only). Honest
boundaries are stated per theorem.
-/

noncomputable section
open scoped BigOperators

namespace NewFrontier

/-! ### Decreasing-returns production → positive economic rent (item 3c) -/

/-- Profit of a decreasing-returns (strictly concave quadratic, `b>0`) technology at
scale `x`, price `p`, productivity `a`, input cost `w`. -/
def drProfit (p a b w x : ℝ) : ℝ := p * (a * x - b * x ^ 2) - w * x

/-- The profit-maximizing scale is the first-order condition `2·p·b·x* = p·a − w`;
no other scale does better. (Decreasing returns ⇒ a genuine interior optimum.) -/
theorem dr_profit_max (p a b w xstar x : ℝ) (hp : 0 < p) (hb : 0 < b)
    (hfoc : 2 * p * b * xstar = p * a - w) :
    drProfit p a b w x ≤ drProfit p a b w xstar := by
  have key : drProfit p a b w xstar - drProfit p a b w x = p * b * (x - xstar) ^ 2 := by
    simp only [drProfit]; linear_combination (x - xstar) * hfoc
  nlinarith [key, mul_nonneg (mul_pos hp hb).le (sq_nonneg (x - xstar))]

/-- **Decreasing returns yield strictly positive profit (economic rent)** at the optimum
when price covers marginal input cost (`p·a > w`). This is the surplus distributed to
owners — unlike constant returns, which earns exactly zero profit. -/
theorem dr_profit_positive (p a b w xstar : ℝ) (hp : 0 < p) (hb : 0 < b)
    (hfoc : 2 * p * b * xstar = p * a - w) (hpos : 0 < p * a - w) :
    0 < drProfit p a b w xstar := by
  have hxstar : 0 < xstar := by nlinarith [mul_pos hp hb]
  have hval : drProfit p a b w xstar = p * b * xstar ^ 2 := by
    simp only [drProfit]; linear_combination (-xstar) * hfoc
  rw [hval]
  exact mul_pos (mul_pos hp hb) (pow_pos hxstar 2)

/-! ### Certified worked example (item 4): p=4, a=2, b=1, w=0 ⇒ x*=1, rent=4 -/

example : drProfit 4 2 1 0 1 = 4 := by norm_num [drProfit]

example (x : ℝ) : drProfit 4 2 1 0 x ≤ drProfit 4 2 1 0 1 :=
  dr_profit_max 4 2 1 0 1 x (by norm_num) (by norm_num) (by norm_num)

example : (0 : ℝ) < drProfit 4 2 1 0 1 :=
  dr_profit_positive 4 2 1 0 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-! ### Money object: value from convenience yield, not cashflow (item 1, slice) -/

/-- **Money-object slice.** An asset whose state payoff carries a positive liquidity /
convenience yield `λ` on top of its cashflow has a strictly positive shadow price
`∑ₛ pₛ·mₛ·(cashflowₛ + λ)`. Value can come from convenience, not cashflow. -/
theorem money_object_positive_value {S : Type*} [Fintype S] [Nonempty S]
    (p m cashflow : S → ℝ) (lambda : ℝ)
    (hp : ∀ s, 0 < p s) (hm : ∀ s, 0 < m s) (hcf : ∀ s, 0 ≤ cashflow s) (hlam : 0 < lambda) :
    0 < ∑ s, p s * m s * (cashflow s + lambda) := by
  apply Finset.sum_pos
  · intro s _
    have hpm : 0 < p s * m s := mul_pos (hp s) (hm s)
    have hcl : 0 < cashflow s + lambda := by have := hcf s; linarith
    exact mul_pos hpm hcl
  · exact Finset.univ_nonempty

/-- A **pure** money object — zero cashflow in every state — still has strictly positive
value, equal to the liquidity premium `λ·∑ₛ pₛ·mₛ`. The formal core of why a non-cashflow
money object (cf. Bitcoin) can be valued: from convenience, not from production.
Boundary: `λ` is an exogenous convenience yield here; deriving it endogenously from money's
transaction role is the full monetary model, not this slice. -/
theorem pure_money_object_value {S : Type*} [Fintype S] [Nonempty S]
    (p m : S → ℝ) (lambda : ℝ)
    (hp : ∀ s, 0 < p s) (hm : ∀ s, 0 < m s) (hlam : 0 < lambda) :
    0 < ∑ s, p s * m s * ((0 : ℝ) + lambda) :=
  money_object_positive_value p m (fun _ => 0) lambda hp hm (fun _ => le_refl 0) hlam

end NewFrontier

#print axioms NewFrontier.dr_profit_max
#print axioms NewFrontier.dr_profit_positive
#print axioms NewFrontier.money_object_positive_value
#print axioms NewFrontier.pure_money_object_value
