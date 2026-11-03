import SupportedOwnershipUniqueness
import Mathlib.Analysis.Calculus.ImplicitFunction.ProdDomain

/-!
Positive physical curvature and invertibility of the joint ownership/clearing
linearization at a no-trade reference. No common household multiplier and no
assumed inverse demand map. The analytic identification as the derivative of
the actual nonlinear equilibrium equations is a separate bridge.
-/

noncomputable section
open scoped BigOperators
open OwnershipCRRA OwnershipMarginal

namespace OverlapLocal

section Gram
variable {J S : Type*} [Fintype J] [Fintype S]

def pair (u v : J → ℝ) : ℝ := ∑ j, u j*v j

theorem pair_add_right (u v w : J → ℝ) : pair u (v+w)=pair u v+pair u w := by
  simp [pair,mul_add,Finset.sum_add_distrib]

theorem pair_smul_right (u v : J → ℝ) (r : ℝ) : pair u (r • v)=r*pair u v := by
  simp only [pair,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

def gram (P : S → J → ℝ) (k : S → ℝ) : (J → ℝ) →ₗ[ℝ] (J → ℝ) where
  toFun v j := ∑ s, k s*P s j*pair (P s) v
  map_add' v w := by
    funext j
    simp only [pair_add_right,mul_add,Finset.sum_add_distrib,Pi.add_apply]
  map_smul' r v := by
    funext j
    change (∑ s, k s*P s j*pair (P s) (r • v)) =
      r*(∑ s, k s*P s j*pair (P s) v)
    simp only [pair_smul_right,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    ring

theorem gram_quadratic (P : S → J → ℝ) (k : S → ℝ) (v : J → ℝ) :
    pair v (gram P k v)=∑ s, k s*(pair (P s) v)^2 := by
  change (∑ j, v j*(∑ s, k s*P s j*pair (P s) v)) = _
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  calc
    (∑ j, v j*(k s*P s j*pair (P s) v)) =
        ∑ j, (k s*pair (P s) v)*(P s j*v j) := by
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = (k s*pair (P s) v)*(∑ j, P s j*v j) := (Finset.mul_sum ..).symm
    _ = k s*(pair (P s) v)^2 := by change (k s*pair (P s) v)*pair (P s) v=_; ring

theorem gram_nonnegative (P : S → J → ℝ) (k : S → ℝ)
    (hk : ∀ s, 0 ≤ k s) (v : J → ℝ) : 0 ≤ pair v (gram P k v) := by
  rw [gram_quadratic]
  exact Finset.sum_nonneg (fun s _ => mul_nonneg (hk s) (sq_nonneg _))

theorem gram_positive (P : S → J → ℝ) (k : S → ℝ)
    (hk : ∀ s, 0 < k s)
    (hrank : Function.Injective (fun v : J → ℝ => fun s => pair (P s) v))
    (v : J → ℝ) (hv : v ≠ 0) : 0 < pair v (gram P k v) := by
  classical
  have hex : ∃ s, pair (P s) v ≠ 0 := by
    by_contra hn
    apply hv
    apply hrank
    funext s
    have hh := not_not.mp (not_exists.mp hn s)
    simpa [pair] using hh
  obtain ⟨s,hs⟩ := hex
  rw [gram_quadratic]
  exact Finset.sum_pos'
    (fun r _ => mul_nonneg (hk r).le (sq_nonneg _))
    ⟨s,Finset.mem_univ s,mul_pos (hk s) (sq_pos_of_ne_zero hs)⟩

def curvature (P : S → J → ℝ) (k : S → ℝ) (q : J → ℝ) (t : ℝ) :
    (J → ℝ) →ₗ[ℝ] (J → ℝ) :=
  gram P k+gram (fun _ : Unit => q) (fun _ => t)

theorem curvature_apply (P : S → J → ℝ) (k : S → ℝ) (q : J → ℝ)
    (t : ℝ) (v : J → ℝ) (j : J) :
    curvature P k q t v j = (∑ s, k s*P s j*pair (P s) v)+t*q j*pair q v := by
  change (∑ s, k s*P s j*pair (P s) v)+(∑ _ : Unit, t*q j*pair q v)=_
  simp

theorem curvature_positive (P : S → J → ℝ) (k : S → ℝ) (q : J → ℝ)
    (t : ℝ) (hk : ∀ s, 0 < k s) (ht : 0 ≤ t)
    (hrank : Function.Injective (fun v : J → ℝ => fun s => pair (P s) v))
    (v : J → ℝ) (hv : v ≠ 0) : 0 < pair v (curvature P k q t v) := by
  have h1 := gram_positive P k hk hrank v hv
  have h2 := gram_nonnegative (fun _ : Unit => q) (fun _ => t) (fun _ => ht) v
  change 0 < pair v (gram P k v+gram (fun _ : Unit => q) (fun _ => t) v)
  rw [pair_add_right]
  linarith

def physicalCoefficient (D : Data J S) (a0 : J → ℝ) (s : S) : ℝ :=
  D.weight s*D.eta s*(consumption D a0 s)^(-D.eta s-1)

def physicalLambda (D : Data J S) (e : ℝ) : ℝ := e^(-D.gamma)

def physicalCurrentCurvature (D : Data J S) (e : ℝ) : ℝ :=
  D.gamma*physicalLambda D e/e

def physicalHessian (D : Data J S) (e : ℝ) (a0 q : J → ℝ) :
    (J → ℝ) →ₗ[ℝ] (J → ℝ) :=
  curvature D.payoff (physicalCoefficient D a0) q (physicalCurrentCurvature D e)

theorem physicalHessian_positive (D : Data J S) (e : ℝ) (a0 q : J → ℝ)
    (he : 0 < e) (ha0 : ∀ j, 0 ≤ a0 j) (v : J → ℝ) (hv : v ≠ 0) :
    0 < pair v (physicalHessian D e a0 q v) := by
  apply curvature_positive
  · intro s
    exact mul_pos (mul_pos (D.weight_pos s) (D.eta_pos s))
      (Real.rpow_pos_of_pos (consumption_positive D ha0 s) _)
  · exact (div_pos (mul_pos D.gamma_pos (Real.rpow_pos_of_pos he _)) he).le
  · exact D.payoff_injective
  · exact hv

end Gram

abbrev MarketState (H J : Type*) := (J → ℝ) × (H → J → ℝ)

section Joint
variable {H J : Type*} [Fintype H] [Fintype J]

def jointLinear (A : H → ((J → ℝ) →ₗ[ℝ] (J → ℝ))) (lambda : H → ℝ) :
    MarketState H J →ₗ[ℝ] MarketState H J where
  toFun z := (fun j => ∑ i, z.2 i j, fun i => A i (z.2 i)+lambda i • z.1)
  map_add' z w := by
    apply Prod.ext
    · funext j
      change (∑ i, (z.2 i j+w.2 i j))=(∑ i, z.2 i j)+(∑ i, w.2 i j)
      exact Finset.sum_add_distrib
    · funext i j
      change A i (z.2 i+w.2 i) j+lambda i*(z.1 j+w.1 j)=
        (A i (z.2 i) j+lambda i*z.1 j)+(A i (w.2 i) j+lambda i*w.1 j)
      rw [map_add]
      simp only [Pi.add_apply]
      ring
  map_smul' r z := by
    apply Prod.ext
    · funext j
      change (∑ i, r*z.2 i j)=r*(∑ i, z.2 i j)
      exact (Finset.mul_sum ..).symm
    · funext i j
      change A i (r • z.2 i) j+lambda i*(r*z.1 j)=
        r*(A i (z.2 i) j+lambda i*z.1 j)
      rw [map_smul]
      simp only [Pi.smul_apply,smul_eq_mul]
      ring

theorem pair_sum_left (v : H → J → ℝ) (d : J → ℝ) :
    (∑ i, pair (v i) d)=pair (fun j => ∑ i, v i j) d := by
  simp only [pair,Finset.sum_mul]
  exact Finset.sum_comm

theorem joint_kernel_trivial [Nonempty H]
    (A : H → ((J → ℝ) →ₗ[ℝ] (J → ℝ))) (lambda : H → ℝ)
    (hlambda : ∀ i, 0 < lambda i)
    (hA : ∀ i v, v ≠ 0 → 0 < pair v (A i v))
    (z : MarketState H J) (hz : jointLinear A lambda z=0) : z=0 := by
  classical
  have hclear : ∀ j, ∑ i, z.2 i j=0 := by
    intro j
    exact congrFun (congrArg Prod.fst hz) j
  have hchoice : ∀ i, A i (z.2 i)=(-lambda i) • z.1 := by
    intro i
    funext j
    have hh := congrFun (congrFun (congrArg Prod.snd hz) i) j
    change A i (z.2 i) j+lambda i*z.1 j=0 at hh
    change A i (z.2 i) j=(-lambda i)*z.1 j
    linarith
  let energy : H → ℝ := fun i => pair (z.2 i) (A i (z.2 i))/lambda i
  have henergy : ∀ i, energy i= -pair (z.2 i) z.1 := by
    intro i
    dsimp [energy]
    rw [hchoice i,pair_smul_right]
    field_simp [ne_of_gt (hlambda i)]
  have hnonneg : ∀ i, 0 ≤ energy i := by
    intro i
    by_cases hi : z.2 i=0
    · simp [energy,hi,pair]
    · exact (div_pos (hA i (z.2 i) hi) (hlambda i)).le
  have hsum : ∑ i, energy i=0 := by
    simp_rw [henergy]
    rw [Finset.sum_neg_distrib,pair_sum_left]
    simp [hclear,pair]
  have hv : z.2=0 := by
    funext i
    by_contra hi
    have hp : 0 < energy i := div_pos (hA i (z.2 i) hi) (hlambda i)
    have hs : energy i ≤ ∑ k, energy k :=
      Finset.single_le_sum (fun k _ => hnonneg k) (Finset.mem_univ i)
    rw [hsum] at hs
    linarith
  have hd : z.1=0 := by
    let i : H := Classical.arbitrary H
    have hh := hchoice i
    rw [hv] at hh
    funext j
    have hj := congrFun hh j
    simp only [Pi.zero_apply,map_zero,Pi.smul_apply,smul_eq_mul] at hj
    exact (mul_eq_zero.mp hj.symm).resolve_left (neg_ne_zero.mpr (ne_of_gt (hlambda i)))
  exact Prod.ext hd hv

theorem joint_injective [Nonempty H]
    (A : H → ((J → ℝ) →ₗ[ℝ] (J → ℝ))) (lambda : H → ℝ)
    (hlambda : ∀ i, 0 < lambda i)
    (hA : ∀ i v, v ≠ 0 → 0 < pair v (A i v)) :
    Function.Injective (jointLinear A lambda) := by
  apply (injective_iff_map_eq_zero _).mpr
  exact joint_kernel_trivial A lambda hlambda hA

def jointCLM (A : H → ((J → ℝ) →ₗ[ℝ] (J → ℝ))) (lambda : H → ℝ) :
    MarketState H J →L[ℝ] MarketState H J := (jointLinear A lambda).toContinuousLinearMap

theorem joint_isInvertible [Nonempty H]
    (A : H → ((J → ℝ) →ₗ[ℝ] (J → ℝ))) (lambda : H → ℝ)
    (hlambda : ∀ i, 0 < lambda i)
    (hA : ∀ i v, v ≠ 0 → 0 < pair v (A i v)) :
    (jointCLM A lambda).IsInvertible := by
  let L := LinearEquiv.ofInjectiveEndo (jointLinear A lambda)
    (joint_injective A lambda hlambda hA)
  exact ⟨L.toContinuousLinearEquiv,rfl⟩

end Joint

section Physical
variable {H J S : Type*} [Fintype H] [Fintype J] [Fintype S] [Nonempty H]

def referenceDerivative (D : H → Data J S) (e : H → ℝ)
    (a0 : H → J → ℝ) (q : J → ℝ) : MarketState H J →L[ℝ] MarketState H J :=
  jointCLM (fun i => physicalHessian (D i) (e i) (a0 i) q)
    (fun i => physicalLambda (D i) (e i))

theorem referenceDerivative_isInvertible (D : H → Data J S) (e : H → ℝ)
    (a0 : H → J → ℝ) (q : J → ℝ)
    (he : ∀ i, 0 < e i) (ha0 : ∀ i j, 0 ≤ a0 i j) :
    (referenceDerivative D e a0 q).IsInvertible := by
  apply joint_isInvertible
  · intro i; exact Real.rpow_pos_of_pos (he i) _
  · intro i v hv; exact physicalHessian_positive (D i) (e i) (a0 i) q (he i) (ha0 i) v hv

end Physical
end OverlapLocal

#print axioms OverlapLocal.pair_add_right
#print axioms OverlapLocal.pair_smul_right
#print axioms OverlapLocal.gram_quadratic
#print axioms OverlapLocal.gram_nonnegative
#print axioms OverlapLocal.gram_positive
#print axioms OverlapLocal.curvature_apply
#print axioms OverlapLocal.curvature_positive
#print axioms OverlapLocal.physicalHessian_positive
#print axioms OverlapLocal.pair_sum_left
#print axioms OverlapLocal.joint_kernel_trivial
#print axioms OverlapLocal.joint_injective
#print axioms OverlapLocal.joint_isInvertible
#print axioms OverlapLocal.referenceDerivative_isInvertible
