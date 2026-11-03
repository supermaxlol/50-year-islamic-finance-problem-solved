import OverlapLocalWeightFamily
import OwnershipLimitTools

/-!
Every actual equilibrium's initial bundle remains affordable. Concavity makes
its midpoint with that bundle no worse than the initial bundle. Midpoints have
uniformly positive current consumption, even when an unbounded-price sequence
has a zero-consumption allocation limit. Strict reference support then forces
every convergent allocation subsequence back to the initial allocation.
-/

noncomputable section
open scoped BigOperators Topology
open Filter Set OwnershipCRRA OwnershipMarginal OwnershipUnfloored OwnershipPositive
open OwnershipStrictSupport OwnershipSupported OverlapLocal

namespace OverlapStability

section Household
variable {J S : Type*} [Fintype J] [Fintype S]

theorem economic_midpoint (D : Data J S) (c d : ℝ) (a b : J → ℝ)
    (hc : 0 < c) (hd : 0 < d) (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j) :
    (economicValue D c a+economicValue D d b)/2 ≤
      economicValue D ((c+d)/2) (fun j => (a j+b j)/2) := by
  have h := (objective_concaveOn_economicDomain D).2
    (shiftedChoice_mem_domain D c a hc ha) (shiftedChoice_mem_domain D d b hd hb)
    (show (0 : ℝ) ≤ 1/2 by norm_num) (show (0 : ℝ) ≤ 1/2 by norm_num)
    (show (1/2 : ℝ)+1/2=1 by norm_num)
  have hm : (1/2 : ℝ) • shiftedChoice D.delta c a+
      (1/2 : ℝ) • shiftedChoice D.delta d b=
      shiftedChoice D.delta ((c+d)/2) (fun j => (a j+b j)/2) := by
    funext j
    cases j <;> simp only [shiftedChoice,Pi.add_apply,Pi.smul_apply,smul_eq_mul] <;> ring
  rw [hm,shiftedChoice_objective,shiftedChoice_objective,shiftedChoice_objective] at h
  change (1/2 : ℝ)*economicValue D c a+(1/2 : ℝ)*economicValue D d b ≤ _ at h
  linarith

theorem midpoint_not_worse (D : Data J S) (c d : ℝ) (a b : J → ℝ)
    (hc : 0 < c) (hd : 0 < d) (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j)
    (hv : economicValue D c a ≤ economicValue D d b) :
    economicValue D c a ≤ economicValue D ((c+d)/2) (fun j => (a j+b j)/2) := by
  linarith [economic_midpoint D c d a b hc hd ha hb]

end Household

section Market
variable {H J S : Type*} [Fintype H] [Fintype J] [Fintype S]

theorem reference_pareto_rigidity (D : H → Data J S) (e c : H → ℝ)
    (a0 a : H → J → ℝ) (qstar : J → ℝ)
    (he : ∀ i, 0 < e i) (hc : ∀ i, 0 < c i)
    (ha0 : ∀ i j, 0 ≤ a0 i j) (ha : ∀ i j, 0 ≤ a i j)
    (hsupport : SupportsInitial D e a0 qstar)
    (hcurrent : ∑ i, c i=∑ i, e i) (hassets : ∀ j, ∑ i, a i j=∑ i, a0 i j)
    (hbetter : ∀ i, economicValue (D i) (e i) (a0 i) ≤ economicValue (D i) (c i) (a i)) :
    c=e ∧ a=a0 := by
  classical
  let gap : H → ℝ := fun i => (c i+∑ j, qstar j*a i j)-(e i+∑ j, qstar j*a0 i j)
  have hn : ∀ i, 0 ≤ gap i := by
    intro i
    have ht := economic_support_le (D i) qstar (a0 i) (a i) (e i) (c i)
      (he i) (hc i) (ha0 i) (ha i) (hsupport i)
    have hp := Real.rpow_pos_of_pos (he i) (-(D i).gamma)
    by_contra h
    have hm := mul_neg_of_pos_of_neg hp (lt_of_not_ge h)
    dsimp [gap] at hm
    linarith [hbetter i]
  have ht := aggregate_cost_equality qstar c e a a0 hcurrent hassets
  have hsum : ∑ i, gap i=0 := by
    dsimp [gap]
    rw [Finset.sum_sub_distrib,ht,sub_self]
  have hp : ∀ i, c i=e i ∧ a i=a0 i := by
    intro i
    have hs : gap i ≤ ∑ k, gap k := Finset.single_le_sum
      (fun k _ => hn k) (Finset.mem_univ i)
    rw [hsum] at hs
    apply bundle_equal_of_not_worse_and_cost_le (D i) qstar (a0 i) (a i) (e i) (c i)
      (he i) (hc i) (ha0 i) (ha i) (hsupport i) (hbetter i)
    dsimp [gap] at hs
    linarith
  exact ⟨funext (fun i => (hp i).1),funext (fun i => (hp i).2)⟩

omit [Fintype H] in
theorem affine_value_tendsto (D : H → Data J S) (W : H → S → ℝ) (i : H)
    {t cn : ℕ → ℝ} {an : ℕ → J → ℝ} {c : ℝ} {a : J → ℝ}
    (hw : ∀ n i s, 0 < (D i).weight s+t n*W i s)
    (hc : 0 < c) (ha : ∀ j, 0 ≤ a j)
    (ht : Tendsto t atTop (𝓝 0)) (hcn : Tendsto cn atTop (𝓝 c))
    (han : ∀ j, Tendsto (fun n => an n j) atTop (𝓝 (a j))) :
    Tendsto (fun n => economicValue (affineData D W (t n) (hw n) i) (cn n) (an n))
      atTop (𝓝 (economicValue (D i) c a)) := by
  change Tendsto (fun n => utility (D i).gamma (cn n)+
    ∑ s, ((D i).weight s+t n*W i s)*utility ((D i).eta s)
      (consumption (D i) (an n) s)) atTop _
  apply Tendsto.add
  · exact (utility_hasDerivAt (g := (D i).gamma) hc).continuousAt.tendsto.comp hcn
  · apply tendsto_finsetSum
    intro s _
    have hwlim : Tendsto (fun n => (D i).weight s+t n*W i s) atTop
        (𝓝 ((D i).weight s)) := by
      simpa only [zero_mul,add_zero] using tendsto_const_nhds.add (ht.mul_const (W i s))
    exact hwlim.mul ((utility_hasDerivAt (g := (D i).eta s)
      (consumption_positive (D i) ha s)).continuousAt.tendsto.comp
        (OwnershipLimit.future_consumption_tendsto (D i) han s))

omit [Fintype H] in
theorem affine_marginal_tendsto (D : H → Data J S) (W : H → S → ℝ) (i : H)
    {t : ℕ → ℝ} {an : ℕ → J → ℝ} {a : J → ℝ}
    (hw : ∀ n i s, 0 < (D i).weight s+t n*W i s)
    (ha : ∀ j, 0 ≤ a j) (ht : Tendsto t atTop (𝓝 0))
    (han : ∀ j, Tendsto (fun n => an n j) atTop (𝓝 (a j))) (j : J) :
    Tendsto (fun n => marginal (affineData D W (t n) (hw n) i) (an n) j)
      atTop (𝓝 (marginal (D i) a j)) := by
  apply tendsto_finsetSum
  intro s _
  have hwlim : Tendsto (fun n => (D i).weight s+t n*W i s) atTop
      (𝓝 ((D i).weight s)) := by
    simpa only [zero_mul,add_zero] using tendsto_const_nhds.add (ht.mul_const (W i s))
  exact (hwlim.mul_const ((D i).payoff s j)).mul
    ((OwnershipLimit.future_consumption_tendsto (D i) han s).rpow_const
      (Or.inl (ne_of_gt (consumption_positive (D i) ha s))))

theorem allocation_limit_reference (D : H → Data J S) (W : H → S → ℝ)
    (e : H → ℝ) (a0 : H → J → ℝ) (supply qstar : J → ℝ)
    (he : ∀ i, 0 < e i) (ha0 : ∀ i j, 0 ≤ a0 i j)
    (hstock : ∀ j, ∑ i, a0 i j=supply j) (hsupport : SupportsInitial D e a0 qstar)
    (t : ℕ → ℝ) (hw : ∀ n i s, 0 < (D i).weight s+t n*W i s)
    (qn : ℕ → J → ℝ) (cn : ℕ → H → ℝ) (an : ℕ → H → J → ℝ)
    (hEq : ∀ n, IsEquilibrium (affineData D W (t n) (hw n)) e a0 supply
      (qn n) (cn n) (an n))
    (c : H → ℝ) (a : H → J → ℝ)
    (ht : Tendsto t atTop (𝓝 0))
    (hcn : ∀ i, Tendsto (fun n => cn n i) atTop (𝓝 (c i)))
    (han : ∀ i j, Tendsto (fun n => an n i j) atTop (𝓝 (a i j))) :
    c=e ∧ a=a0 := by
  have hcp : ∀ i, 0 ≤ c i := fun i => le_of_tendsto_of_tendsto'
    tendsto_const_nhds (hcn i) (fun n => ((hEq n).consumption_positive i).le)
  have hap : ∀ i j, 0 ≤ a i j := fun i j => le_of_tendsto_of_tendsto'
    tendsto_const_nhds (han i j) (fun n => (hEq n).holdings_nonneg i j)
  have hcTotal : ∑ i, c i=∑ i, e i :=
    tendsto_nhds_unique_of_forall (tendsto_finsetSum Finset.univ (fun i _ => hcn i))
      tendsto_const_nhds (fun n => (hEq n).consumption_clears)
  have haTotal : ∀ j, ∑ i, a i j=supply j := fun j =>
    tendsto_nhds_unique_of_forall (tendsto_finsetSum Finset.univ (fun i _ => han i j))
      tendsto_const_nhds (fun n => (hEq n).ownership_clears j)
  have hmidc : ∀ i, 0 < (e i+c i)/2 := by intro i; linarith [he i,hcp i]
  have hmida : ∀ i j, 0 ≤ (a0 i j+a i j)/2 := by intro i j; linarith [ha0 i j,hap i j]
  have hbetter : ∀ i, economicValue (D i) (e i) (a0 i) ≤
      economicValue (D i) ((e i+c i)/2) (fun j => (a0 i j+a i j)/2) := by
    intro i
    have hcm : Tendsto (fun n => (e i+cn n i)/2) atTop (𝓝 ((e i+c i)/2)) :=
      (tendsto_const_nhds.add (hcn i)).div_const 2
    have ham : ∀ j, Tendsto (fun n => (a0 i j+an n i j)/2) atTop
        (𝓝 ((a0 i j+a i j)/2)) := fun j =>
      (tendsto_const_nhds.add (han i j)).div_const 2
    exact le_of_tendsto_of_tendsto'
      (affine_value_tendsto D W i hw (he i) (ha0 i) ht tendsto_const_nhds
        (fun _ => tendsto_const_nhds))
      (affine_value_tendsto D W i hw (hmidc i) (hmida i) ht hcm ham)
      (fun n => midpoint_not_worse (affineData D W (t n) (hw n) i)
        (e i) (cn n i) (a0 i) (an n i) (he i) ((hEq n).consumption_positive i)
        (ha0 i) ((hEq n).holdings_nonneg i)
        ((hEq n).optimal i (e i) (he i) (a0 i) (ha0 i) le_rfl))
  have hcClear : (∑ i, (e i+c i)/2)=∑ i, e i := by
    simp_rw [add_div]
    rw [Finset.sum_add_distrib,← Finset.sum_div,← Finset.sum_div,hcTotal]
    ring
  have haClear : ∀ j, (∑ i, (a0 i j+a i j)/2)=∑ i, a0 i j := by
    intro j
    simp_rw [add_div]
    rw [Finset.sum_add_distrib,← Finset.sum_div,← Finset.sum_div,haTotal j,← hstock j]
    ring
  obtain ⟨hcEq,haEq⟩ := reference_pareto_rigidity D e (fun i => (e i+c i)/2)
    a0 (fun i j => (a0 i j+a i j)/2) qstar he hmidc ha0 hmida hsupport hcClear haClear hbetter
  constructor
  · funext i
    have hh := congrFun hcEq i
    change (e i+c i)/2=e i at hh
    linarith
  · funext i j
    have hh := congrFun (congrFun haEq i) j
    change (a0 i j+a i j)/2=a0 i j at hh
    linarith

end Market
end OverlapStability

#print axioms OverlapStability.economic_midpoint
#print axioms OverlapStability.midpoint_not_worse
#print axioms OverlapStability.reference_pareto_rigidity
#print axioms OverlapStability.affine_value_tendsto
#print axioms OverlapStability.affine_marginal_tendsto
#print axioms OverlapStability.allocation_limit_reference
