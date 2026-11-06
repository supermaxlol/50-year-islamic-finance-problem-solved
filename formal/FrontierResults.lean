import Mathlib

/-!
Stages 235–239 combined: welfare, core, uniqueness, money premium, Walras.
Independent finite-economy results compiled together (one Mathlib load; Lean elaborates and
audits each declaration independently).
-/

noncomputable section
open scoped BigOperators

/-! ### First Welfare Theorem -/
namespace Welfare
variable {H S : Type*} [Fintype H] [Fintype S]

theorem first_welfare_theorem
    (M : ℝ) (p : S → ℝ) (hp : ∀ s, 0 ≤ p s)
    (ω c : H → S → ℝ) (U : H → (S → ℝ) → ℝ)
    (hopt : ∀ h (x : S → ℝ), (∀ s, x s ∈ Set.Icc (0:ℝ) M) →
      ∑ s, p s * x s ≤ ∑ s, p s * ω h s → U h x ≤ U h (c h))
    (hLNS : ∀ h (x : S → ℝ), (∀ s, x s ∈ Set.Icc (0:ℝ) M) →
      ∑ s, p s * x s < ∑ s, p s * ω h s →
      ∃ x', (∀ s, x' s ∈ Set.Icc (0:ℝ) M) ∧
        ∑ s, p s * x' s ≤ ∑ s, p s * ω h s ∧ U h x < U h x')
    (c' : H → S → ℝ) (hbox' : ∀ h s, c' h s ∈ Set.Icc (0:ℝ) M)
    (hfeas' : ∀ s, (∑ h, c' h s) ≤ ∑ h, ω h s)
    (hge : ∀ h, U h (c h) ≤ U h (c' h)) (h0 : H) (hstr : U h0 (c h0) < U h0 (c' h0)) :
    False := by
  have hwk : ∀ h, ∑ s, p s * ω h s ≤ ∑ s, p s * c' h s := by
    intro h
    by_contra hlt
    have hlt' : ∑ s, p s * c' h s < ∑ s, p s * ω h s := not_le.mp hlt
    obtain ⟨x', hx'box, hx'aff, hx'better⟩ := hLNS h (c' h) (hbox' h) hlt'
    have h1 : U h x' ≤ U h (c h) := hopt h x' hx'box hx'aff
    have h2 : U h (c h) < U h x' := lt_of_le_of_lt (hge h) hx'better
    linarith
  have hstr' : ∑ s, p s * ω h0 s < ∑ s, p s * c' h0 s := by
    by_contra hle
    have hle' : ∑ s, p s * c' h0 s ≤ ∑ s, p s * ω h0 s := not_lt.mp hle
    have := hopt h0 (c' h0) (hbox' h0) hle'
    linarith
  have hsum : ∑ h, ∑ s, p s * ω h s < ∑ h, ∑ s, p s * c' h s :=
    Finset.sum_lt_sum (fun h _ => hwk h) ⟨h0, Finset.mem_univ h0, hstr'⟩
  have hswap : ∀ f : H → S → ℝ, ∑ h, ∑ s, p s * f h s = ∑ s, p s * (∑ h, f h s) := by
    intro f; rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun s _ => by rw [Finset.mul_sum])
  have hfeas_val : ∑ h, ∑ s, p s * c' h s ≤ ∑ h, ∑ s, p s * ω h s := by
    rw [hswap c', hswap ω]
    exact Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left (hfeas' s) (hp s))
  linarith

end Welfare

/-! ### Core: equilibrium is unblockable -/
namespace Core
variable {H S : Type*} [Fintype H] [Fintype S]

theorem equilibrium_unblocked
    (M : ℝ) (p : S → ℝ) (hp : ∀ s, 0 ≤ p s)
    (ω c : H → S → ℝ) (U : H → (S → ℝ) → ℝ)
    (hopt : ∀ h (z : S → ℝ), (∀ s, z s ∈ Set.Icc (0:ℝ) M) →
      ∑ s, p s * z s ≤ ∑ s, p s * ω h s → U h z ≤ U h (c h))
    (T : Finset H) (hT : T.Nonempty) (x : H → S → ℝ)
    (hxbox : ∀ h ∈ T, ∀ s, x h s ∈ Set.Icc (0:ℝ) M)
    (hcoalfeas : ∀ s, (∑ h ∈ T, x h s) ≤ ∑ h ∈ T, ω h s)
    (hblock : ∀ h ∈ T, U h (c h) < U h (x h)) :
    False := by
  have hstr : ∀ h ∈ T, ∑ s, p s * ω h s < ∑ s, p s * x h s := by
    intro h hh
    by_contra hle
    have hle' : ∑ s, p s * x h s ≤ ∑ s, p s * ω h s := not_lt.mp hle
    have := hopt h (x h) (hxbox h hh) hle'
    linarith [hblock h hh]
  have hsum : ∑ h ∈ T, ∑ s, p s * ω h s < ∑ h ∈ T, ∑ s, p s * x h s :=
    Finset.sum_lt_sum_of_nonempty hT hstr
  have hswap : ∀ f : H → S → ℝ, ∑ h ∈ T, ∑ s, p s * f h s = ∑ s, p s * (∑ h ∈ T, f h s) := by
    intro f; rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun s _ => by rw [Finset.mul_sum])
  have hfeasval : ∑ h ∈ T, ∑ s, p s * x h s ≤ ∑ h ∈ T, ∑ s, p s * ω h s := by
    rw [hswap x, hswap ω]
    exact Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left (hcoalfeas s) (hp s))
  linarith

end Core

/-! ### Uniqueness under WARP -/
namespace Uniqueness
variable {S : Type*} [Fintype S]

theorem equilibrium_unique_of_warp
    (z : (S → ℝ) → (S → ℝ))
    (hwarp : ∀ q q' : S → ℝ,
      (∑ s, q s * z q' s) ≤ 0 → z q' ≠ z q → 0 < ∑ s, q' s * z q s)
    (p p' : S → ℝ) (hp : ∀ s, z p s = 0) (hp' : ∀ s, z p' s = 0) :
    z p = z p' := by
  by_contra hne
  have h1 : ∑ s, p s * z p' s ≤ 0 := by simp [hp']
  have h2 : z p' ≠ z p := fun h => hne h.symm
  have h3 : 0 < ∑ s, p' s * z p s := hwarp p p' h1 h2
  have h4 : ∑ s, p' s * z p s = 0 := by simp [hp]
  linarith

end Uniqueness

/-! ### Money premium = convenience yield -/
namespace Money
variable {S : Type*} [Fintype S]

theorem money_premium_eq_convenience (p m cashflow : S → ℝ) (lambda : ℝ) :
    (∑ s, p s * m s * (cashflow s + lambda)) - (∑ s, p s * m s * cashflow s)
      = lambda * ∑ s, p s * m s := by
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun s _ => by ring)

theorem money_value_exceeds_fundamental [Nonempty S]
    (p m cashflow : S → ℝ) (lambda : ℝ)
    (hp : ∀ s, 0 < p s) (hm : ∀ s, 0 < m s) (hlam : 0 < lambda) :
    (∑ s, p s * m s * cashflow s) < ∑ s, p s * m s * (cashflow s + lambda) := by
  have hprem := money_premium_eq_convenience p m cashflow lambda
  have hpos : 0 < lambda * ∑ s, p s * m s :=
    mul_pos hlam (Finset.sum_pos (fun s _ => mul_pos (hp s) (hm s)) Finset.univ_nonempty)
  linarith

end Money

/-! ### Walras' law closes the last market -/
namespace Walras
variable {S : Type*} [Fintype S]

theorem walras_last_market (p z : S → ℝ)
    (hwalras : ∑ s, p s * z s = 0) (s0 : S) (hp0 : 0 < p s0)
    (hclear : ∀ s, s ≠ s0 → z s = 0) : z s0 = 0 := by
  have hsum : ∑ s, p s * z s = p s0 * z s0 := by
    rw [Finset.sum_eq_single s0]
    · intro s _ hs; rw [hclear s hs, mul_zero]
    · intro h; exact absurd (Finset.mem_univ s0) h
  rw [hsum] at hwalras
  exact (mul_eq_zero.mp hwalras).resolve_left (ne_of_gt hp0)

end Walras

#print axioms Welfare.first_welfare_theorem
#print axioms Core.equilibrium_unblocked
#print axioms Uniqueness.equilibrium_unique_of_warp
#print axioms Money.money_premium_eq_convenience
#print axioms Money.money_value_exceeds_fundamental
#print axioms Walras.walras_last_market
