import TangentProjection

/-! Feasible ownership transfers recover the price multipliers. Together with
the physical Hessian projection, every tangent forcing has exactly one mixed
complementarity response, including simultaneous weak ownership corners. -/

noncomputable section
open scoped BigOperators
open OverlapLocal OverlapBoundaryTangent TangentProjection OwnershipCRRA

namespace TangentMarketExistence
variable {H J S : Type*} [Fintype H] [Fintype J]

def unit [DecidableEq H] [DecidableEq J] (i : H) (j : J) : H → J → ℝ :=
  fun n r => if n=i then if r=j then 1 else 0 else 0

def transfer [DecidableEq H] [DecidableEq J] (u : H → J → ℝ)
    (i k : H) (j : J) (t : ℝ) : H → J → ℝ :=
  u+t • unit i j-t • unit k j

omit [Fintype J] in
theorem unit_aggregate (i : H) (j r : J) :
    letI := Classical.decEq H
    letI := Classical.decEq J
    (∑ n, unit i j n r)=if r=j then 1 else 0 := by
  classical
  simp [unit]

theorem forceLinear_unit (lambda : H → ℝ) (g : H → J → ℝ) (i : H) (j : J) :
    letI := Classical.decEq H
    letI := Classical.decEq J
    forceLinear lambda g (unit i j)=g i j/lambda i := by
  classical
  simp [forceLinear,unit,pair,mul_ite,ite_div]

omit [Fintype J] in
theorem transfer_feasible (a0 gap : H → J → ℝ) (total : J → ℝ)
    (u : H → J → ℝ) (hu : Feasible a0 gap total u)
    (i k : H) (j : J) (t : ℝ) (hk : 0<a0 k j)
    (hi : ¬0<a0 i j → ¬0<gap i j ∧ 0≤u i j+t) :
    letI := Classical.decEq H
    letI := Classical.decEq J
    Feasible a0 gap total (transfer u i k j t) := by
  classical
  constructor
  · intro r
    simp only [transfer,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,
      Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,
      unit_aggregate,hu.1 r]
    ring
  · intro n r hn
    by_cases hr : r=j
    · subst r
      have hnk : n≠k := by intro heq; exact hn (heq ▸ hk)
      by_cases hni : n=i
      · subst n
        obtain ⟨hg,ht⟩ := hi hn
        simp only [ite_eq_right hg]
        simpa [transfer,unit,hnk] using ht
      · simpa [transfer,unit,hni,hnk] using hu.2 n j hn
    · simpa [transfer,unit,hr] using hu.2 n r hn

theorem transfer_inequality (lambda : H → ℝ) (g u : H → J → ℝ)
    (a0 gap : H → J → ℝ) (total : J → ℝ)
    (hvi : ∀ v, Feasible a0 gap total v →
      0≤∑ n, pair (g n) (v n-u n)/lambda n)
    (i k : H) (j : J) (t : ℝ)
    (ht : letI := Classical.decEq H; letI := Classical.decEq J
      Feasible a0 gap total (transfer u i k j t)) :
    0≤t*(g i j/lambda i-g k j/lambda k) := by
  classical
  have hh := hvi (transfer u i k j t) ht
  change 0≤forceLinear lambda g (transfer u i k j t-u) at hh
  simp only [transfer,map_sub,map_add,map_smul,forceLinear_unit,smul_eq_mul] at hh
  linarith

theorem variational_to_response
    (A : H → ((J → ℝ) →ₗ[ℝ] (J → ℝ))) (lambda : H → ℝ)
    (a0 gap force : H → J → ℝ) (total : J → ℝ)
    (hlambda : ∀ i, 0<lambda i) (howner : ∀ j, ∃ i, 0<a0 i j)
    (u : H → J → ℝ) (hu : Feasible a0 gap total u)
    (hvi : ∀ v, Feasible a0 gap total v →
      0≤∑ i, pair (A i (u i)+force i) (v i-u i)/lambda i) :
    ∃ p, IsResponse A lambda a0 gap force total (p,u) := by
  classical
  choose owner ho using howner
  let g : H → J → ℝ := fun i => A i (u i)+force i
  let p : J → ℝ := fun j => -g (owner j) j/lambda (owner j)
  refine ⟨p,hu.1,?_⟩
  intro i j
  have hslack : A i (u i) j+lambda i*p j+force i j=
      lambda i*(g i j/lambda i-g (owner j) j/lambda (owner j)) := by
    dsimp [p,g]
    field_simp [ne_of_gt (hlambda i),ne_of_gt (hlambda (owner j))]
    ring
  by_cases hi : 0<a0 i j
  · have hplus : 0≤1*(g i j/lambda i-g (owner j) j/lambda (owner j)) :=
      transfer_inequality lambda g u a0 gap total hvi i (owner j) j 1
        (transfer_feasible a0 gap total u hu i (owner j) j 1 (ho j)
          (fun hn => False.elim (hn hi)))
    have hminus : 0≤(-1)*(g i j/lambda i-g (owner j) j/lambda (owner j)) :=
      transfer_inequality lambda g u a0 gap total hvi i (owner j) j (-1)
        (transfer_feasible a0 gap total u hu i (owner j) j (-1) (ho j)
          (fun hn => False.elim (hn hi)))
    simp only [Corner,ite_eq_left hi]
    rw [hslack]
    have heq : g i j/lambda i-g (owner j) j/lambda (owner j)=0 := by linarith
    rw [heq,mul_zero]
  by_cases hg : 0<gap i j
  · simpa [Corner,hi,hg] using hu.2 i j hi
  have hn : 0≤u i j := by simpa [hg] using hu.2 i j hi
  have hplus : 0≤1*(g i j/lambda i-g (owner j) j/lambda (owner j)) :=
    transfer_inequality lambda g u a0 gap total hvi i (owner j) j 1
      (transfer_feasible a0 gap total u hu i (owner j) j 1 (ho j)
        (fun _ => ⟨hg,by linarith⟩))
  have hminus : 0≤(-u i j)*(g i j/lambda i-g (owner j) j/lambda (owner j)) :=
    transfer_inequality lambda g u a0 gap total hvi i (owner j) j (-u i j)
      (transfer_feasible a0 gap total u hu i (owner j) j (-u i j) (ho j)
        (fun _ => ⟨hg,by linarith⟩))
  have hd : 0≤g i j/lambda i-g (owner j) j/lambda (owner j) := by linarith
  have hz : u i j*(g i j/lambda i-g (owner j) j/lambda (owner j))=0 :=
    le_antisymm (by nlinarith) (mul_nonneg hn hd)
  simp only [Corner,ite_eq_right hi,ite_eq_right hg]
  rw [hslack]
  refine ⟨hn,mul_nonneg (hlambda i).le hd,?_⟩
  calc
    u i j*(lambda i*(g i j/lambda i-g (owner j) j/lambda (owner j)))=
        lambda i*(u i j*(g i j/lambda i-g (owner j) j/lambda (owner j))) := by ring
    _ = 0 := by rw [hz,mul_zero]

theorem response_exists_unique
    (A : H → ((J → ℝ) →ₗ[ℝ] (J → ℝ))) (lambda : H → ℝ)
    (a0 gap force : H → J → ℝ) (total : J → ℝ)
    (hlambda : ∀ i, 0<lambda i)
    (hA : ∀ i v, v≠0 → 0<pair v (A i v))
    (hsym : ∀ i u v, pair u (A i v)=pair v (A i u))
    (howner : ∀ j, ∃ i, 0<a0 i j) :
    ∃! z, IsResponse A lambda a0 gap force total z := by
  obtain ⟨u,hu,hvi⟩ := variational_solution A lambda a0 gap force total hlambda hA hsym howner
  obtain ⟨p,hp⟩ := variational_to_response A lambda a0 gap force total hlambda howner u hu hvi
  exact ⟨(p,u),hp,fun z hz => response_unique A lambda a0 gap force total
    hlambda hA howner z (p,u) hz hp⟩

theorem corner_nonnegative_scale (own gap u s t : ℝ) (ht : 0≤t)
    (h : Corner own gap u s) : Corner own gap (t*u) (t*s) := by
  by_cases ho : 0<own
  · have hs : s=0 := by simpa [Corner,ho] using h
    simp [Corner,ho,hs]
  by_cases hg : 0<gap
  · have hu : u=0 := by simpa [Corner,ho,hg] using h
    simp [Corner,ho,hg,hu]
  have hh : 0 ≤ u ∧ 0 ≤ s ∧ u*s=0 := by simpa [Corner,ho,hg] using h
  simp only [Corner,ite_eq_right ho,ite_eq_right hg]
  refine ⟨mul_nonneg ht hh.1,mul_nonneg ht hh.2.1,?_⟩
  calc
    (t*u)*(t*s)=t^2*(u*s) := by ring
    _ = 0 := by rw [hh.2.2,mul_zero]

omit [Fintype J] in
theorem response_nonnegative_scale
    (A : H → ((J → ℝ) →ₗ[ℝ] (J → ℝ))) (lambda : H → ℝ)
    (a0 gap force : H → J → ℝ) (total : J → ℝ) (z : MarketState H J)
    (hz : IsResponse A lambda a0 gap force total z) (t : ℝ) (ht : 0≤t) :
    IsResponse A lambda a0 gap (t • force) (t • total) (t • z) := by
  constructor
  · intro j
    change (∑ i, t*z.2 i j)=t*total j
    rw [← Finset.mul_sum,hz.clears]
  · intro i j
    have hh := corner_nonnegative_scale (a0 i j) (gap i j) (z.2 i j)
      (A i (z.2 i) j+lambda i*z.1 j+force i j) t ht (hz.corners i j)
    convert hh using 1
    change A i (t • z.2 i) j+lambda i*(t*z.1 j)+t*force i j=
      t*(A i (z.2 i) j+lambda i*z.1 j+force i j)
    rw [map_smul]
    simp only [Pi.smul_apply,smul_eq_mul]
    ring

section Physical
variable [Fintype S]

theorem physical_tangent_exists_unique (D : H → Data J S) (e : H → ℝ)
    (a0 : H → J → ℝ) (supply qstar : J → ℝ)
    (he : ∀ i, 0<e i) (ha0 : ∀ i j, 0≤a0 i j)
    (hstock : ∀ j, ∑ i, a0 i j=supply j) (hs : ∀ j, 0<supply j)
    (force : H → J → ℝ) (total : J → ℝ) :
    ∃! z, PhysicalResponse D e a0 qstar force total z := by
  apply response_exists_unique
  · intro i
    exact Real.rpow_pos_of_pos (he i) _
  · intro i v hv
    exact physicalHessian_positive (D i) (e i) (a0 i) qstar (he i) (ha0 i) v hv
  · intro i u v
    exact physicalHessian_symmetric (D i) (e i) (a0 i) qstar u v
  · exact OverlapBoundary.positive_reference_owner a0 supply hstock hs

end Physical

theorem weak_entry_control :
    IsResponse (fun _ : Bool => LinearMap.id : Bool → ((Unit → ℝ) →ₗ[ℝ] (Unit → ℝ)))
      (fun _ => 1) (fun i _ => if i then 0 else 1) (fun _ _ => 0)
      (fun i _ => if i then -1 else 0) (fun _ => 0)
      ((fun _ => 1/2),(fun i _ => if i then 1/2 else -1/2)) := by
  constructor
  · intro j
    cases j
    norm_num [Fintype.sum_bool]
  · intro i j
    cases i <;> cases j <;> norm_num [Corner]

theorem opposite_direction_inactive_control :
    IsResponse (fun _ : Bool => LinearMap.id : Bool → ((Unit → ℝ) →ₗ[ℝ] (Unit → ℝ)))
      (fun _ => 1) (fun i _ => if i then 0 else 1) (fun _ _ => 0)
      (fun i _ => if i then 1 else 0) (fun _ => 0)
      ((fun _ => 0),(fun _ _ => 0)) := by
  constructor
  · intro j
    cases j
    norm_num [Fintype.sum_bool]
  · intro i j
    cases i <;> cases j <;> norm_num [Corner]

end TangentMarketExistence

#print axioms TangentMarketExistence.unit_aggregate
#print axioms TangentMarketExistence.forceLinear_unit
#print axioms TangentMarketExistence.transfer_feasible
#print axioms TangentMarketExistence.transfer_inequality
#print axioms TangentMarketExistence.variational_to_response
#print axioms TangentMarketExistence.response_exists_unique
#print axioms TangentMarketExistence.corner_nonnegative_scale
#print axioms TangentMarketExistence.response_nonnegative_scale
#print axioms TangentMarketExistence.physical_tangent_exists_unique
#print axioms TangentMarketExistence.weak_entry_control
#print axioms TangentMarketExistence.opposite_direction_inactive_control
