import OverlapBoundaryStability

/-! Uniqueness of the physical mixed-complementarity tangent. This does not
assert existence of a tangent or convergence of nonlinear difference quotients. -/

noncomputable section
open scoped BigOperators
open OwnershipCRRA OwnershipMarginal OverlapLocal

namespace OverlapBoundaryTangent

/-- Positive owners satisfy a differentiated Euler equality. Strictly inactive
positions remain zero. Weak corners obey linearized complementarity. -/
def Corner (own gap u s : ℝ) : Prop :=
  if 0 < own then s=0 else if 0 < gap then u=0 else 0 ≤ u ∧ 0 ≤ s ∧ u*s=0

theorem corner_difference_nonpositive (own gap u v s t : ℝ)
    (hu : Corner own gap u s) (hv : Corner own gap v t) :
    (u-v)*(s-t) ≤ 0 := by
  by_cases ho : 0 < own
  · have hs : s=0 := by simpa [Corner,ho] using hu
    have ht : t=0 := by simpa [Corner,ho] using hv
    simp [hs,ht]
  by_cases hg : 0 < gap
  · have hu0 : u=0 := by simpa [Corner,ho,hg] using hu
    have hv0 : v=0 := by simpa [Corner,ho,hg] using hv
    simp [hu0,hv0]
  have hu' : 0 ≤ u ∧ 0 ≤ s ∧ u*s=0 := by simpa [Corner,ho,hg] using hu
  have hv' : 0 ≤ v ∧ 0 ≤ t ∧ v*t=0 := by simpa [Corner,ho,hg] using hv
  nlinarith [hu'.2.2,hv'.2.2,mul_nonneg hu'.1 hv'.2.1,mul_nonneg hv'.1 hu'.2.1]

variable {H J S : Type*} [Fintype H] [Fintype J]

structure IsResponse (A : H → ((J → ℝ) →ₗ[ℝ] (J → ℝ)))
    (lambda : H → ℝ) (a0 gap force : H → J → ℝ) (total : J → ℝ)
    (z : MarketState H J) : Prop where
  clears : ∀ j, ∑ i, z.2 i j=total j
  corners : ∀ i j, Corner (a0 i j) (gap i j) (z.2 i j)
    (A i (z.2 i) j+lambda i*z.1 j+force i j)

theorem response_energy_inequality
    (A : H → ((J → ℝ) →ₗ[ℝ] (J → ℝ))) (lambda : H → ℝ)
    (a0 gap force : H → J → ℝ) (total : J → ℝ) (z w : MarketState H J)
    (hz : IsResponse A lambda a0 gap force total z)
    (hw : IsResponse A lambda a0 gap force total w) (i : H) :
    pair (z.2 i-w.2 i) (A i (z.2 i-w.2 i))+
      lambda i*pair (z.2 i-w.2 i) (z.1-w.1) ≤ 0 := by
  have hh : ∀ j, (z.2 i j-w.2 i j)*
      ((A i (z.2 i) j+lambda i*z.1 j+force i j)-
       (A i (w.2 i) j+lambda i*w.1 j+force i j)) ≤ 0 :=
    fun j => corner_difference_nonpositive _ _ _ _ _ _ (hz.corners i j) (hw.corners i j)
  have hpair : pair (z.2 i-w.2 i) (A i (z.2 i-w.2 i))+
      lambda i*pair (z.2 i-w.2 i) (z.1-w.1) =
      ∑ j, (z.2 i j-w.2 i j)*
        ((A i (z.2 i) j+lambda i*z.1 j+force i j)-
         (A i (w.2 i) j+lambda i*w.1 j+force i j)) := by
    rw [map_sub]
    simp only [pair,Pi.sub_apply,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hpair]
  exact Finset.sum_nonpos (fun j _ => hh j)

theorem response_unique
    (A : H → ((J → ℝ) →ₗ[ℝ] (J → ℝ))) (lambda : H → ℝ)
    (a0 gap force : H → J → ℝ) (total : J → ℝ)
    (hlambda : ∀ i, 0 < lambda i)
    (hA : ∀ i v, v ≠ 0 → 0 < pair v (A i v))
    (howner : ∀ j, ∃ i, 0 < a0 i j) (z w : MarketState H J)
    (hz : IsResponse A lambda a0 gap force total z)
    (hw : IsResponse A lambda a0 gap force total w) : z=w := by
  classical
  let energy : H → ℝ := fun i => pair (z.2 i-w.2 i) (A i (z.2 i-w.2 i))/lambda i
  have hnonneg : ∀ i, 0 ≤ energy i := by
    intro i
    by_cases hi : z.2 i-w.2 i=0
    · dsimp only [energy]
      rw [hi]
      simp [pair]
    · exact (div_pos (hA i _ hi) (hlambda i)).le
  have hbound : ∀ i, energy i ≤ -pair (z.2 i-w.2 i) (z.1-w.1) := by
    intro i
    apply (div_le_iff₀ (hlambda i)).mpr
    have hh := response_energy_inequality A lambda a0 gap force total z w hz hw i
    nlinarith
  have hclear : ∀ j, ∑ i, (z.2 i-w.2 i) j=0 := by
    intro j
    simp only [Pi.sub_apply,Finset.sum_sub_distrib,hz.clears j,hw.clears j,sub_self]
  have hsumFun : (fun j => ∑ i, (z.2 i-w.2 i) j)=(0 : J → ℝ) := funext hclear
  have hsum : ∑ i, energy i ≤ 0 := calc
    (∑ i, energy i) ≤ ∑ i, -pair (z.2 i-w.2 i) (z.1-w.1) :=
      Finset.sum_le_sum (fun i _ => hbound i)
    _ = 0 := by
      rw [Finset.sum_neg_distrib,pair_sum_left,hsumFun]
      simp [pair]
  have hall : ∀ i, z.2 i-w.2 i=0 := by
    intro i
    by_contra hi
    have hp : 0 < energy i := div_pos (hA i _ hi) (hlambda i)
    have hs : energy i ≤ ∑ k, energy k :=
      Finset.single_le_sum (fun k _ => hnonneg k) (Finset.mem_univ i)
    linarith
  have ha : z.2=w.2 := funext (fun i => sub_eq_zero.mp (hall i))
  refine Prod.ext ?_ ha
  funext j
  obtain ⟨i,hi⟩ := howner j
  have hzu : A i (z.2 i) j+lambda i*z.1 j+force i j=0 :=
    by simpa [Corner,hi] using hz.corners i j
  have hwu : A i (w.2 i) j+lambda i*w.1 j+force i j=0 :=
    by simpa [Corner,hi] using hw.corners i j
  rw [ha] at hzu
  have heq : lambda i*(z.1 j-w.1 j)=0 := by linarith
  exact sub_eq_zero.mp ((mul_eq_zero.mp heq).resolve_left (ne_of_gt (hlambda i)))

section Physical
variable [Fintype S]

omit [Fintype H] in
theorem gram_pairing (P : S → J → ℝ) (k : S → ℝ) (u v : J → ℝ) :
    pair u (gram P k v)=∑ s, k s*pair (P s) u*pair (P s) v := by
  change (∑ j, u j*(∑ s, k s*P s j*pair (P s) v)) = _
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  calc
    (∑ j, u j*(k s*P s j*pair (P s) v)) =
        ∑ j, (k s*pair (P s) v)*(P s j*u j) := by
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = (k s*pair (P s) v)*(∑ j, P s j*u j) := (Finset.mul_sum ..).symm
    _ = k s*pair (P s) u*pair (P s) v := by unfold pair; ring

omit [Fintype H] in
theorem gram_symmetric (P : S → J → ℝ) (k : S → ℝ) (u v : J → ℝ) :
    pair u (gram P k v)=pair v (gram P k u) := by
  rw [gram_pairing,gram_pairing]
  apply Finset.sum_congr rfl
  intro s _
  ring

omit [Fintype H] in
theorem physicalHessian_symmetric (D : Data J S) (e : ℝ)
    (a0 qstar u v : J → ℝ) :
    pair u (physicalHessian D e a0 qstar v)=pair v (physicalHessian D e a0 qstar u) := by
  change pair u (gram D.payoff (physicalCoefficient D a0) v+
      gram (fun _ : Unit => qstar) (fun _ => physicalCurrentCurvature D e) v)=
    pair v (gram D.payoff (physicalCoefficient D a0) u+
      gram (fun _ : Unit => qstar) (fun _ => physicalCurrentCurvature D e) u)
  rw [pair_add_right,pair_add_right]
  exact congrArg₂ (fun x y : ℝ => x+y)
    (gram_symmetric D.payoff (physicalCoefficient D a0) u v)
    (gram_symmetric (fun _ : Unit => qstar) (fun _ => physicalCurrentCurvature D e) u v)

def referenceGap (D : H → Data J S) (e : H → ℝ)
    (a0 : H → J → ℝ) (qstar : J → ℝ) (i : H) (j : J) : ℝ :=
  qstar j*(e i)^(-(D i).gamma)-marginal (D i) (a0 i) j

omit [Fintype H] in
theorem reference_gap_conditions (D : H → Data J S) (e : H → ℝ)
    (a0 : H → J → ℝ) (qstar : J → ℝ)
    (hsupport : OwnershipSupported.SupportsInitial D e a0 qstar) :
    (∀ i j, 0 ≤ referenceGap D e a0 qstar i j) ∧
    (∀ i j, a0 i j*referenceGap D e a0 qstar i j=0) := by
  constructor
  · intro i j
    exact sub_nonneg.mpr (hsupport i j).1
  · intro i j
    exact (hsupport i j).2

def PhysicalResponse (D : H → Data J S) (e : H → ℝ)
    (a0 : H → J → ℝ) (qstar : J → ℝ) (force : H → J → ℝ)
    (total : J → ℝ) (z : MarketState H J) : Prop :=
  IsResponse (fun i => physicalHessian (D i) (e i) (a0 i) qstar)
    (fun i => physicalLambda (D i) (e i)) a0 (referenceGap D e a0 qstar) force total z

theorem physical_tangent_unique (D : H → Data J S) (e : H → ℝ)
    (a0 : H → J → ℝ) (supply qstar : J → ℝ)
    (he : ∀ i, 0 < e i) (ha0 : ∀ i j, 0 ≤ a0 i j)
    (hstock : ∀ j, ∑ i, a0 i j=supply j) (hs : ∀ j, 0 < supply j)
    (force : H → J → ℝ) (total : J → ℝ) (z w : MarketState H J)
    (hz : PhysicalResponse D e a0 qstar force total z)
    (hw : PhysicalResponse D e a0 qstar force total w) : z=w := by
  apply response_unique _ _ a0 _ force total _ _ _ z w hz hw
  · intro i
    exact Real.rpow_pos_of_pos (he i) _
  · intro i v hv
    exact physicalHessian_positive (D i) (e i) (a0 i) qstar (he i) (ha0 i) v hv
  · exact OverlapBoundary.positive_reference_owner a0 supply hstock hs

theorem physical_owner_euler (D : H → Data J S) (e : H → ℝ)
    (a0 : H → J → ℝ) (qstar : J → ℝ) (force : H → J → ℝ)
    (total : J → ℝ) (z : MarketState H J)
    (hz : PhysicalResponse D e a0 qstar force total z) (i : H) (j : J)
    (hi : 0 < a0 i j) :
    physicalHessian (D i) (e i) (a0 i) qstar (z.2 i) j+
      physicalLambda (D i) (e i)*z.1 j+force i j=0 :=
  by simpa [Corner,hi] using hz.corners i j

theorem physical_strict_inactive_zero (D : H → Data J S) (e : H → ℝ)
    (a0 : H → J → ℝ) (qstar : J → ℝ) (force : H → J → ℝ)
    (total : J → ℝ) (z : MarketState H J)
    (hz : PhysicalResponse D e a0 qstar force total z) (i : H) (j : J)
    (hi : a0 i j=0) (hg : 0 < referenceGap D e a0 qstar i j) : z.2 i j=0 :=
  by simpa [Corner,hi,hg] using hz.corners i j

theorem physical_weak_corner (D : H → Data J S) (e : H → ℝ)
    (a0 : H → J → ℝ) (qstar : J → ℝ) (force : H → J → ℝ)
    (total : J → ℝ) (z : MarketState H J)
    (hz : PhysicalResponse D e a0 qstar force total z) (i : H) (j : J)
    (hi : a0 i j=0) (hg : referenceGap D e a0 qstar i j=0) :
    0 ≤ z.2 i j ∧
    0 ≤ physicalHessian (D i) (e i) (a0 i) qstar (z.2 i) j+
      physicalLambda (D i) (e i)*z.1 j+force i j ∧
    z.2 i j*(physicalHessian (D i) (e i) (a0 i) qstar (z.2 i) j+
      physicalLambda (D i) (e i)*z.1 j+force i j)=0 :=
  by simpa [Corner,hi,hg] using hz.corners i j

end Physical

theorem weak_corner_can_enter : Corner 0 0 1 0 := by norm_num [Corner]
theorem weak_corner_can_stay_inactive : Corner 0 0 0 1 := by norm_num [Corner]
theorem weak_corner_excludes_two_positive : ¬ Corner 0 0 1 1 := by norm_num [Corner]

end OverlapBoundaryTangent

#print axioms OverlapBoundaryTangent.corner_difference_nonpositive
#print axioms OverlapBoundaryTangent.response_energy_inequality
#print axioms OverlapBoundaryTangent.response_unique
#print axioms OverlapBoundaryTangent.gram_pairing
#print axioms OverlapBoundaryTangent.gram_symmetric
#print axioms OverlapBoundaryTangent.physicalHessian_symmetric
#print axioms OverlapBoundaryTangent.reference_gap_conditions
#print axioms OverlapBoundaryTangent.physical_tangent_unique
#print axioms OverlapBoundaryTangent.physical_owner_euler
#print axioms OverlapBoundaryTangent.physical_strict_inactive_zero
#print axioms OverlapBoundaryTangent.physical_weak_corner
#print axioms OverlapBoundaryTangent.weak_corner_can_enter
#print axioms OverlapBoundaryTangent.weak_corner_can_stay_inactive
#print axioms OverlapBoundaryTangent.weak_corner_excludes_two_positive
