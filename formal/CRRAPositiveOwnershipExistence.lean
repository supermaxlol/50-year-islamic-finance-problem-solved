import AutomaticFloorChoice
import CRRAFloorExclusion

/-!
Original positive current endowments and positive initial productive ownership
imply genuine uncapped market existence. All artificial floors/caps and their
smallness conditions are constructed internally. The price minorant is chosen
from preferences, current endowments and aggregate supply before choosing the
initial ownership distribution. Zero individual initial shares and market-price
uniqueness are not asserted.
-/

noncomputable section
open scoped BigOperators
open Set OwnershipCRRA OwnershipMarginal OwnershipUnfloored OwnershipFloor
open OwnershipFloorChoice

namespace OwnershipPositive

variable {H J S : Type*} [Fintype H] [Fintype J] [Fintype S]

def refloor (D : Data J S) (delta : ℝ) (hdelta : 0 < delta) : Data J S :=
  { D with delta := delta, delta_pos := hdelta }

theorem refloor_economicValue (D : Data J S) (delta : ℝ) (hdelta : 0 < delta)
    (c : ℝ) (a : J → ℝ) :
    economicValue (refloor D delta hdelta) c a = economicValue D c a := rfl

theorem refloor_marginal (D : Data J S) (delta : ℝ) (hdelta : 0 < delta)
    (a : J → ℝ) (j : J) :
    marginal (refloor D delta hdelta) a j = marginal D a j := rfl

theorem refloor_lower (D : Data J S) (delta : ℝ) (hdelta : 0 < delta)
    (supply : J → ℝ) (j : J) :
    lower (refloor D delta hdelta) supply j = lower D supply j := rfl

theorem refloor_upper (D : Data J S) (delta : ℝ) (hdelta : 0 < delta) (j : J) :
    upper (refloor D delta hdelta) j = upper D j := rfl

structure Prepared (D : H → Data J S) (e : H → ℝ) (supply : J → ℝ) where
  m : ℝ
  L : J → ℝ
  delta : ℝ
  M : ℝ
  m_pos : 0 < m
  m_lt_endowment : ∀ i, m < e i
  L_pos : ∀ j, 0 < L j
  delta_pos : 0 < delta
  delta_lt_m : delta < m
  lower_condition : ∀ i j, L j ≤ lower (D i) supply j * m^(D i).gamma
  small_floor : ∀ i j, upper (D i) j * delta^(D i).gamma < L j
  cap_pos : 0 < M
  current_cap : ∑ i, e i < M
  asset_cap : ∀ j, supply j < M

theorem prepare_floors (D : H → Data J S) (e : H → ℝ) (supply : J → ℝ)
    (he : ∀ i, 0 < e i) (hs : ∀ j, 0 ≤ supply j) :
    Nonempty (Prepared D e supply) := by
  classical
  obtain ⟨m, hm, hme⟩ := finite_positive_minorant e he
  have hpositive : ∀ j, ∃ L : ℝ, 0 < L ∧
      ∀ i, L < lower (D i) supply j * m^(D i).gamma := by
    intro j
    apply finite_positive_minorant
    intro i
    have hd : 0 < lower (D i) supply j := by
      exact marginal_positive (D i) hs j
    exact mul_pos hd (Real.rpow_pos_of_pos hm (D i).gamma)
  choose L hL hbound using hpositive
  obtain ⟨delta, hdelta, hdm, hsmall⟩ := common_small_floor
    (fun i => (D i).gamma) (fun i j => upper (D i) j) L m
    (fun i => (D i).gamma_pos) hL hm
  let goods : Option J → ℝ := fun g => match g with
    | none => ∑ i, e i
    | some j => supply j
  obtain ⟨M, hM, hcap⟩ := finite_positive_majorant goods
  exact ⟨⟨m, L, delta, M, hm, hme, hL, hdelta, hdm,
    (fun i j => (hbound j i).le), hsmall, hM, hcap none, fun j => hcap (some j)⟩⟩

def shiftedEndowment (e : H → ℝ) (a0 : H → J → ℝ) (delta : ℝ)
    (i : H) : Option J → ℝ
  | none => e i - delta
  | some j => a0 i j

/- The certificate includes feasibility and actual global household optimality,
not merely clearing and a presumed first-order system. -/
structure IsEquilibrium (D : H → Data J S) (e : H → ℝ)
    (a0 : H → J → ℝ) (supply : J → ℝ)
    (q : J → ℝ) (c : H → ℝ) (a : H → J → ℝ) : Prop where
  prices_positive : ∀ j, 0 < q j
  consumption_positive : ∀ i, 0 < c i
  holdings_nonneg : ∀ i j, 0 ≤ a i j
  affordable : ∀ i, c i + ∑ j, q j * a i j ≤ e i + ∑ j, q j * a0 i j
  optimal : ∀ i c', 0 < c' → ∀ a' : J → ℝ, (∀ j, 0 ≤ a' j) →
    c' + ∑ j, q j * a' j ≤ e i + ∑ j, q j * a0 i j →
    economicValue (D i) c' a' ≤ economicValue (D i) (c i) (a i)
  consumption_clears : ∑ i, c i = ∑ i, e i
  ownership_clears : ∀ j, ∑ i, a i j = supply j
  corner_conditions : ∀ i j, marginal (D i) (a i) j ≤ q j * (c i)^(-(D i).gamma) ∧
    a i j * (q j * (c i)^(-(D i).gamma) - marginal (D i) (a i) j) = 0

section Market
variable [Nonempty H]

theorem equilibrium_from_preparation (D : H → Data J S)
    (e : H → ℝ) (supply : J → ℝ) (P : Prepared D e supply)
    (a0 : H → J → ℝ) (ha0 : ∀ i j, 0 < a0 i j)
    (hsupply : ∀ j, ∑ i, a0 i j = supply j) :
    ∃ q : J → ℝ, ∃ c : H → ℝ, ∃ a : H → J → ℝ,
      IsEquilibrium D e a0 supply q c a ∧ (∀ j, P.L j ≤ q j) := by
  classical
  let D' : H → Data J S := fun i => refloor (D i) P.delta P.delta_pos
  let ω : H → Option J → ℝ := shiftedEndowment e a0 P.delta
  have hω : ∀ i g, 0 < ω i g := by
    intro i g
    cases g with
    | none =>
      change 0 < e i - P.delta
      linarith [P.delta_lt_m, P.m_lt_endowment i]
    | some j => exact ha0 i j
  have hcap : ∀ g, ∑ i, ω i g < P.M := by
    intro g
    cases g with
    | none =>
      change (∑ i, (e i - P.delta)) < P.M
      exact (Finset.sum_le_sum (fun i _ => sub_le_self (e i) P.delta_pos.le)).trans_lt
        P.current_cap
    | some j =>
      change (∑ i, a0 i j) < P.M
      rw [hsupply j]
      exact P.asset_cap j
  have heq : ∀ i, ω i none + (D' i).delta = e i := by
    intro i
    change e i - P.delta + P.delta = e i
    ring
  have hownership : ∀ i j, ω i (some j) = a0 i j := fun _ _ => rfl
  have hmean : (Fintype.card H : ℝ) * P.m ≤ ∑ i, (ω i none + (D' i).delta) := by
    calc
      (Fintype.card H : ℝ) * P.m = ∑ _ : H, P.m := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ ∑ i, e i := Finset.sum_le_sum (fun i _ => (P.m_lt_endowment i).le)
      _ = _ := Finset.sum_congr rfl (fun i _ => (heq i).symm)
  have hstock : (fun j => ∑ i, ω i (some j)) = supply := by
    funext j
    exact hsupply j
  have hL : ∀ i j, P.L j ≤
      lower (D' i) (fun k => ∑ l, ω l (some k)) j * P.m^(D' i).gamma := by
    intro i j
    rw [hstock]
    exact P.lower_condition i j
  have hsmall : ∀ i j, upper (D' i) j * (D' i).delta^(D' i).gamma < P.L j := by
    intro i j
    exact P.small_floor i j
  obtain ⟨q, c, a, hq, hc, ha, hbud, hopt, hcurrent, hassets, hkkt, hprice⟩ :=
    uncapped_equilibrium_of_small_floors D' P.M P.m ω P.L P.cap_pos.le P.m_pos
      hω hcap hmean (fun _ => P.delta_lt_m) hL hsmall
  refine ⟨q, c, a, ?_, hprice⟩
  refine ⟨hq, hc, ha, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    simpa only [heq, hownership] using hbud i
  · intro i c' hc' a' ha' hb
    have hb' : c' + ∑ j, q j * a' j ≤
        (ω i none + (D' i).delta) + ∑ j, q j * ω i (some j) := by
      simpa only [heq, hownership] using hb
    exact hopt i c' hc' a' ha' hb'
  · exact hcurrent.trans (Finset.sum_congr rfl (fun i _ => heq i))
  · intro j
    exact (hassets j).trans (hsupply j)
  · exact hkkt

theorem positive_initial_ownership_equilibrium_family
    (D : H → Data J S) (e : H → ℝ) (supply : J → ℝ)
    (he : ∀ i, 0 < e i) (hs : ∀ j, 0 ≤ supply j) :
    ∃ L : J → ℝ, (∀ j, 0 < L j) ∧
      ∀ a0 : H → J → ℝ, (∀ i j, 0 < a0 i j) →
        (∀ j, ∑ i, a0 i j = supply j) →
        ∃ q : J → ℝ, ∃ c : H → ℝ, ∃ a : H → J → ℝ,
          IsEquilibrium D e a0 supply q c a ∧ (∀ j, L j ≤ q j) := by
  obtain ⟨P⟩ := prepare_floors D e supply he hs
  exact ⟨P.L, P.L_pos, fun a0 ha0 hsupply =>
    equilibrium_from_preparation D e supply P a0 ha0 hsupply⟩

theorem positive_initial_ownership_equilibrium
    (D : H → Data J S) (e : H → ℝ) (a0 : H → J → ℝ)
    (he : ∀ i, 0 < e i) (ha0 : ∀ i j, 0 < a0 i j) :
    ∃ q : J → ℝ, ∃ c : H → ℝ, ∃ a : H → J → ℝ,
      IsEquilibrium D e a0 (fun j => ∑ i, a0 i j) q c a := by
  have hs : ∀ j, 0 ≤ ∑ i, a0 i j := fun j =>
    Finset.sum_nonneg (fun i _ => (ha0 i j).le)
  obtain ⟨L, _, hfamily⟩ := positive_initial_ownership_equilibrium_family
    D e (fun j => ∑ i, a0 i j) he hs
  obtain ⟨q, c, a, hEq, _⟩ := hfamily a0 ha0 (fun _ => rfl)
  exact ⟨q, c, a, hEq⟩

end Market

namespace Controls
open ObjectiveControls

def sampleOwnership (i : Fin 2) (_ : Fin 2) : ℝ := if i = 0 then 9/20 else 1/20

theorem sample_ownership_positive (i j : Fin 2) : 0 < sampleOwnership i j := by
  fin_cases i <;> norm_num [sampleOwnership]

theorem sample_ownership_clears (j : Fin 2) : ∑ i, sampleOwnership i j = (1/2 : ℝ) := by
  norm_num [sampleOwnership, Fin.sum_univ_two]

theorem unequal_initial_ownership_example :
    ∃ q : Fin 2 → ℝ, ∃ c : Fin 2 → ℝ, ∃ a : Fin 2 → Fin 2 → ℝ,
      IsEquilibrium sampleData (fun i => 1 + (i.val : ℝ)) sampleOwnership
        (fun _ => 1/2) q c a := by
  have he : ∀ i : Fin 2, 0 < 1 + (i.val : ℝ) := by
    intro i
    have hi : 0 ≤ (i.val : ℝ) := Nat.cast_nonneg _
    linarith
  obtain ⟨q, c, a, h⟩ := positive_initial_ownership_equilibrium
    sampleData (fun i => 1 + (i.val : ℝ)) sampleOwnership he sample_ownership_positive
  have hs : (fun j => ∑ i, sampleOwnership i j) = (fun _ : Fin 2 => (1/2 : ℝ)) :=
    funext sample_ownership_clears
  rw [hs] at h
  exact ⟨q, c, a, h⟩

theorem resources_below_old_floor_still_admitted :
    (∀ i : Fin 2, (1/100 : ℝ) < (sampleData i).delta) ∧
    ∃ q : Fin 2 → ℝ, ∃ c : Fin 2 → ℝ, ∃ a : Fin 2 → Fin 2 → ℝ,
      IsEquilibrium sampleData (fun _ => 1/100) sampleOwnership
        (fun _ => 1/2) q c a := by
  refine ⟨by intro i; norm_num [sampleData], ?_⟩
  obtain ⟨q, c, a, h⟩ := positive_initial_ownership_equilibrium
    sampleData (fun _ => (1/100 : ℝ)) sampleOwnership (by intro i; norm_num)
    sample_ownership_positive
  have hs : (fun j => ∑ i, sampleOwnership i j) = (fun _ : Fin 2 => (1/2 : ℝ)) :=
    funext sample_ownership_clears
  rw [hs] at h
  exact ⟨q, c, a, h⟩

end Controls
end OwnershipPositive

#print axioms OwnershipPositive.refloor_economicValue
#print axioms OwnershipPositive.refloor_marginal
#print axioms OwnershipPositive.refloor_lower
#print axioms OwnershipPositive.refloor_upper
#print axioms OwnershipPositive.prepare_floors
#print axioms OwnershipPositive.equilibrium_from_preparation
#print axioms OwnershipPositive.positive_initial_ownership_equilibrium_family
#print axioms OwnershipPositive.positive_initial_ownership_equilibrium
#print axioms OwnershipPositive.Controls.sample_ownership_positive
#print axioms OwnershipPositive.Controls.sample_ownership_clears
#print axioms OwnershipPositive.Controls.unequal_initial_ownership_example
#print axioms OwnershipPositive.Controls.resources_below_old_floor_still_admitted
