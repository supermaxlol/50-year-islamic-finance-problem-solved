import HeterogeneousOverlapBridge
import CRRAScalar

/-!
The explicit productive-payoff CRRA objective satisfies the accepted bounded
heterogeneous engine's utility hypotheses. No demand, market price, common
household multiplier, or upper curvature bound is assumed. Artificial choice
bounds and strictly positive initial endowments remain at the final endpoint.
-/

noncomputable section
open scoped BigOperators
open Set OwnershipBridge

namespace OwnershipCRRA

variable {J S : Type*} [Fintype J] [Fintype S]

structure Data (J S : Type*) [Fintype J] where
  delta : ℝ
  gamma : ℝ
  eta : S → ℝ
  income : S → ℝ
  weight : S → ℝ
  payoff : S → J → ℝ
  delta_pos : 0 < delta
  gamma_pos : 0 < gamma
  eta_pos : ∀ s, 0 < eta s
  income_pos : ∀ s, 0 < income s
  weight_pos : ∀ s, 0 < weight s
  payoff_nonneg : ∀ s j, 0 ≤ payoff s j
  payoff_injective : Function.Injective (fun a : J → ℝ => fun s => ∑ j, payoff s j * a j)

def curvature (D : Data J S) : Option S → ℝ
  | none => D.gamma
  | some s => D.eta s

def mass (D : Data J S) : Option S → ℝ
  | none => 1
  | some s => D.weight s

def baseline (D : Data J S) : Option S → ℝ
  | none => D.delta
  | some s => D.income s

/-- `x none` is consumption above the temporary floor, not a safe future claim. -/
def receipts (D : Data J S) (x : Option J → ℝ) : Option S → ℝ
  | none => x none + D.delta
  | some s => D.income s + ∑ j, D.payoff s j * x (some j)

def objective (D : Data J S) (x : Option J → ℝ) : ℝ :=
  ∑ r, mass D r * utility (curvature D r) (receipts D x r)

/-- Only an analytic extension: on nonnegative choices clipping is inactive. -/
def extendedObjective (D : Data J S) (x : Option J → ℝ) : ℝ :=
  ∑ r, mass D r * utility (curvature D r)
    (max (receipts D x r) (baseline D r / 2))

omit [Fintype S] in
theorem curvature_pos (D : Data J S) (r : Option S) : 0 < curvature D r := by
  cases r with
  | none => exact D.gamma_pos
  | some s => exact D.eta_pos s

omit [Fintype S] in
theorem mass_pos (D : Data J S) (r : Option S) : 0 < mass D r := by
  cases r with
  | none => norm_num [mass]
  | some s => exact D.weight_pos s

omit [Fintype S] in
theorem baseline_pos (D : Data J S) (r : Option S) : 0 < baseline D r := by
  cases r with
  | none => exact D.delta_pos
  | some s => exact D.income_pos s

omit [Fintype S] in
theorem baseline_le_receipts (D : Data J S) {x : Option J → ℝ}
    (hx : ∀ g, 0 ≤ x g) (r : Option S) : baseline D r ≤ receipts D x r := by
  cases r with
  | none => simpa [baseline, receipts] using hx none
  | some s =>
    have hn : 0 ≤ ∑ j, D.payoff s j * x (some j) :=
      Finset.sum_nonneg fun j _ => mul_nonneg (D.payoff_nonneg s j) (hx (some j))
    dsimp [baseline, receipts]
    linarith

omit [Fintype S] in
theorem receipts_positive (D : Data J S) {x : Option J → ℝ}
    (hx : ∀ g, 0 ≤ x g) (r : Option S) : 0 < receipts D x r :=
  lt_of_lt_of_le (baseline_pos D r) (baseline_le_receipts D hx r)

omit [Fintype S] in
theorem receipts_continuous (D : Data J S) (r : Option S) :
    Continuous (fun x : Option J → ℝ => receipts D x r) := by
  cases r with
  | none => exact (continuous_apply none).add continuous_const
  | some s =>
    exact continuous_const.add (continuous_finsetSum _ (fun j _ =>
      continuous_const.mul (continuous_apply (some j))))

omit [Fintype S] in
theorem receipts_combo (D : Data J S) (x y : Option J → ℝ)
    (a b : ℝ) (hab : a + b = 1) (r : Option S) :
    receipts D (a • x + b • y) r = a * receipts D x r + b * receipts D y r := by
  cases r with
  | none =>
    simp only [receipts, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    calc
      a * x none + b * y none + D.delta =
          a * x none + b * y none + (a+b) * D.delta := by rw [hab, one_mul]
      _ = _ := by ring
  | some s =>
    have hs : (∑ j, D.payoff s j * (a • x + b • y) (some j)) =
        a * (∑ j, D.payoff s j * x (some j)) +
        b * (∑ j, D.payoff s j * y (some j)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    simp only [receipts]
    rw [hs]
    calc
      D.income s + (a * (∑ j, D.payoff s j * x (some j)) +
          b * (∑ j, D.payoff s j * y (some j))) =
          (a+b) * D.income s + (a * (∑ j, D.payoff s j * x (some j)) +
          b * (∑ j, D.payoff s j * y (some j))) := by rw [hab, one_mul]
      _ = _ := by ring

omit [Fintype S] in
theorem receipts_injective (D : Data J S) : Function.Injective (receipts D) := by
  intro x y hxy
  have ha : (fun j => x (some j)) = (fun j => y (some j)) := by
    apply D.payoff_injective
    funext s
    have h := congrFun hxy (some s)
    dsimp [receipts] at h
    linarith
  funext g
  cases g with
  | none =>
    have h := congrFun hxy none
    dsimp [receipts] at h
    linarith
  | some j => exact congrFun ha j

omit [Fintype S] in
theorem receipts_monotone (D : Data J S) : Monotone (receipts D) := by
  intro x y hxy r
  cases r with
  | none =>
    change x none + D.delta ≤ y none + D.delta
    linarith [hxy none]
  | some s =>
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
      mul_le_mul_of_nonneg_left (hxy (some j)) (D.payoff_nonneg s j)
      )
    change D.income s + (∑ j, D.payoff s j * x (some j)) ≤
      D.income s + (∑ j, D.payoff s j * y (some j))
    linarith

omit [Fintype J] [Fintype S] in
theorem box_convex (M : ℝ) : Convex ℝ (box M : Set (Option J → ℝ)) := by
  have heq : (box M : Set (Option J → ℝ)) =
      Set.univ.pi (fun _ => Icc (0 : ℝ) M) := by
    ext x
    constructor
    · intro hx
      rw [Set.mem_univ_pi]
      exact hx
    · intro hx
      rw [Set.mem_univ_pi] at hx
      exact hx
  rw [heq]
  exact convex_pi fun _ _ => convex_Icc _ _

theorem extendedObjective_continuous (D : Data J S) : Continuous (extendedObjective D) := by
  apply continuous_finsetSum
  intro r _
  exact continuous_const.mul (utility_clipped_continuous (curvature D r)
    (baseline D r / 2) (div_pos (baseline_pos D r) (by norm_num))
    (fun x => receipts D x r) (receipts_continuous D r))

theorem extendedObjective_eq (D : Data J S) {x : Option J → ℝ}
    (hx : ∀ g, 0 ≤ x g) : extendedObjective D x = objective D x := by
  apply Finset.sum_congr rfl
  intro r _
  have hfloor : baseline D r / 2 ≤ receipts D x r := by
    have hp := baseline_pos D r
    have hl := baseline_le_receipts D hx r
    linarith
  rw [max_eq_left hfloor]

theorem objective_strictConcaveOn (D : Data J S) (M : ℝ) :
    StrictConcaveOn ℝ (box M) (objective D) := by
  classical
  refine ⟨box_convex M, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have hcx : ∀ r, 0 < receipts D x r := receipts_positive D (fun g => (hx g).1)
  have hcy : ∀ r, 0 < receipts D y r := receipts_positive D (fun g => (hy g).1)
  have hweak : ∀ r,
      mass D r * (a * utility (curvature D r) (receipts D x r) +
        b * utility (curvature D r) (receipts D y r)) ≤
      mass D r * utility (curvature D r) (receipts D (a • x + b • y) r) := by
    intro r
    rw [receipts_combo D x y a b hab r]
    exact mul_le_mul_of_nonneg_left
      ((utility_strictConcaveOn (curvature_pos D r)).concaveOn.2
        (hcx r) (hcy r) ha.le hb.le hab) (mass_pos D r).le
  have hex : ∃ r, receipts D x r ≠ receipts D y r := by
    by_contra hn
    apply hxy
    apply receipts_injective D
    funext r
    exact not_not.mp (not_exists.mp hn r)
  obtain ⟨r, hr⟩ := hex
  have hstrict : mass D r * (a * utility (curvature D r) (receipts D x r) +
        b * utility (curvature D r) (receipts D y r)) <
      mass D r * utility (curvature D r) (receipts D (a • x + b • y) r) := by
    rw [receipts_combo D x y a b hab r]
    exact mul_lt_mul_of_pos_left
      ((utility_strictConcaveOn (curvature_pos D r)).2
        (hcx r) (hcy r) hr ha hb hab) (mass_pos D r)
  have hs := Finset.sum_lt_sum (fun k (_ : k ∈ (Finset.univ : Finset (Option S))) => hweak k)
    ⟨r, Finset.mem_univ r, hstrict⟩
  have hsplit : (∑ r, mass D r * (a * utility (curvature D r) (receipts D x r) +
        b * utility (curvature D r) (receipts D y r))) =
      a * objective D x + b * objective D y := by
    dsimp [objective]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hsplit] at hs
  exact hs

theorem objective_increasingOnBox (D : Data J S) (M : ℝ) :
    IncreasingOnBox M (objective D) := by
  classical
  intro x hx y hy hxy hne
  have hcx : ∀ r, 0 < receipts D x r := receipts_positive D (fun g => (hx g).1)
  have hcy : ∀ r, 0 < receipts D y r := receipts_positive D (fun g => (hy g).1)
  have hrc := receipts_monotone D hxy
  have hweak : ∀ r, mass D r * utility (curvature D r) (receipts D x r) ≤
      mass D r * utility (curvature D r) (receipts D y r) := by
    intro r
    exact mul_le_mul_of_nonneg_left
      ((utility_strictMonoOn (curvature D r)).monotoneOn (hcx r) (hcy r) (hrc r))
      (mass_pos D r).le
  have hex : ∃ r, receipts D x r ≠ receipts D y r := by
    by_contra hn
    apply hne
    apply receipts_injective D
    funext r
    exact not_not.mp (not_exists.mp hn r)
  obtain ⟨r, hr⟩ := hex
  have hs : mass D r * utility (curvature D r) (receipts D x r) <
      mass D r * utility (curvature D r) (receipts D y r) :=
    mul_lt_mul_of_pos_left
      ((utility_strictMonoOn (curvature D r)) (hcx r) (hcy r)
        (lt_of_le_of_ne (hrc r) hr)) (mass_pos D r)
  exact Finset.sum_lt_sum (fun k (_ : k ∈ (Finset.univ : Finset (Option S))) => hweak k)
    ⟨r, Finset.mem_univ r, hs⟩

theorem extendedObjective_strictConcaveOn (D : Data J S) (M : ℝ) :
    StrictConcaveOn ℝ (box M) (extendedObjective D) :=
  (objective_strictConcaveOn D M).congr
    (fun _ hx => (extendedObjective_eq D (fun g => (hx g).1)).symm)

theorem extendedObjective_increasingOnBox (D : Data J S) (M : ℝ) :
    IncreasingOnBox M (extendedObjective D) := by
  intro x hx y hy hxy hne
  rw [extendedObjective_eq D (fun g => (hx g).1),
    extendedObjective_eq D (fun g => (hy g).1)]
  exact objective_increasingOnBox D M x hx y hy hxy hne

/-- Finite heterogeneous households, actual CRRA objective and exact clearing.
The choices and endowments are still explicitly bounded/strictly positive.
This theorem does not remove the temporary consumption floor or prove market
price uniqueness. -/
theorem bounded_CRRA_ownership_equilibrium {H : Type*} [Fintype H] [Nonempty H]
    (D : H → Data J S) (M : ℝ) (hM : 0 ≤ M)
    (ω : H → Option J → ℝ) (hω : ∀ i g, 0 < ω i g)
    (hcap : ∀ g, ∑ i, ω i g < M) :
    ∃ q : J → ℝ, ∃ x : H → Option J → ℝ,
      (∀ j, 0 < q j) ∧
      (∀ i, IsNumeraireOptimal M (ω i) (objective (D i)) q (x i)) ∧
      (∑ i, x i none = ∑ i, ω i none) ∧
      (∀ j, ∑ i, x i (some j) = ∑ i, ω i (some j)) := by
  obtain ⟨q, x, hq, hopt, hcurrent, hassets⟩ :=
    heterogeneous_current_consumption_equilibrium M hM ω hω
      (fun i => extendedObjective (D i))
      (fun i => extendedObjective_continuous (D i))
      (fun i => extendedObjective_strictConcaveOn (D i) M) hcap
      (fun i => extendedObjective_increasingOnBox (D i) M)
  refine ⟨q, x, hq, ?_, hcurrent, hassets⟩
  intro i
  refine ⟨(hopt i).1, (hopt i).2.1, ?_⟩
  intro y hy hybud
  have h := (hopt i).2.2 y hy hybud
  rwa [extendedObjective_eq (D i) (fun g => (hy g).1),
    extendedObjective_eq (D i) (fun g => ((hopt i).1 g).1)] at h

end OwnershipCRRA

#print axioms OwnershipCRRA.curvature_pos
#print axioms OwnershipCRRA.mass_pos
#print axioms OwnershipCRRA.baseline_pos
#print axioms OwnershipCRRA.baseline_le_receipts
#print axioms OwnershipCRRA.receipts_positive
#print axioms OwnershipCRRA.receipts_continuous
#print axioms OwnershipCRRA.receipts_combo
#print axioms OwnershipCRRA.receipts_injective
#print axioms OwnershipCRRA.receipts_monotone
#print axioms OwnershipCRRA.box_convex
#print axioms OwnershipCRRA.extendedObjective_continuous
#print axioms OwnershipCRRA.extendedObjective_eq
#print axioms OwnershipCRRA.objective_strictConcaveOn
#print axioms OwnershipCRRA.objective_increasingOnBox
#print axioms OwnershipCRRA.extendedObjective_strictConcaveOn
#print axioms OwnershipCRRA.extendedObjective_increasingOnBox
#print axioms OwnershipCRRA.bounded_CRRA_ownership_equilibrium
