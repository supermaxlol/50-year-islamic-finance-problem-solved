import OverlapBoundaryTangent
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! A constrained quadratic variational inequality in the actual physical
Hessian. No tangent, optimizer, or multiplier existence is assumed. -/

noncomputable section
open scoped BigOperators RealInnerProductSpace
open OverlapLocal

namespace TangentProjection
variable {H J : Type*} [Fintype H] [Fintype J]

/-- A fresh type synonym avoids conflicting with the ordinary Pi sup norm.
Only its algebraic structure is inherited; its norm is the Hessian norm. -/
def QuadraticSpace (H J : Type*) := H → J → ℝ

instance : AddCommGroup (QuadraticSpace H J) :=
  inferInstanceAs (AddCommGroup (H → J → ℝ))

instance : Module ℝ (QuadraticSpace H J) :=
  inferInstanceAs (Module ℝ (H → J → ℝ))

instance : FiniteDimensional ℝ (QuadraticSpace H J) :=
  inferInstanceAs (FiniteDimensional ℝ (H → J → ℝ))

def Feasible (a0 gap : H → J → ℝ) (total : J → ℝ)
    (u : H → J → ℝ) : Prop :=
  (∀ j, ∑ i, u i j=total j) ∧
  ∀ i j, ¬0<a0 i j → if 0<gap i j then u i j=0 else 0≤u i j

def energyPair (A : H → ((J → ℝ) →ₗ[ℝ] (J → ℝ)))
    (lambda : H → ℝ) (u v : H → J → ℝ) : ℝ :=
  ∑ i, pair (u i) (A i (v i))/lambda i

theorem pair_add_left (u v w : J → ℝ) : pair (u+v) w=pair u w+pair v w := by
  simp [pair,add_mul,Finset.sum_add_distrib]

theorem pair_smul_left (u v : J → ℝ) (r : ℝ) : pair (r • u) v=r*pair u v := by
  simp only [pair,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

@[instance_reducible] def weightedCore (A : H → ((J → ℝ) →ₗ[ℝ] (J → ℝ)))
    (lambda : H → ℝ) (hlambda : ∀ i, 0<lambda i)
    (hA : ∀ i v, v≠0 → 0<pair v (A i v))
    (hsym : ∀ i u v, pair u (A i v)=pair v (A i u)) :
    InnerProductSpace.Core ℝ (H → J → ℝ) where
  inner := energyPair A lambda
  conj_inner_symm u v := by
    simp only [RCLike.conj_to_real,energyPair]
    exact Finset.sum_congr rfl (fun i _ => congrArg (fun x => x/lambda i) (hsym i (v i) (u i)))
  re_inner_nonneg u := by
    change 0≤energyPair A lambda u u
    apply Finset.sum_nonneg
    intro i _
    by_cases hi : u i=0
    · simp [hi,pair]
    · exact (div_pos (hA i _ hi) (hlambda i)).le
  add_left u v w := by
    simp [energyPair,Pi.add_apply,pair_add_left,add_div,Finset.sum_add_distrib]
  smul_left u v r := by
    simp only [RCLike.conj_to_real,energyPair,Pi.smul_apply,pair_smul_left,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  definite u hu := by
    change energyPair A lambda u u=0 at hu
    have hn : ∀ i, 0≤pair (u i) (A i (u i))/lambda i := by
      intro i
      by_cases hi : u i=0
      · simp [hi,pair]
      · exact (div_pos (hA i _ hi) (hlambda i)).le
    funext i
    by_contra hi
    have hp := div_pos (hA i _ hi) (hlambda i)
    have hb := Finset.single_le_sum (fun k _ => hn k) (Finset.mem_univ i)
    change _≤energyPair A lambda u u at hb
    linarith

omit [Fintype J] in
theorem feasible_nonempty (a0 gap : H → J → ℝ) (total : J → ℝ)
    (howner : ∀ j, ∃ i, 0<a0 i j) : ∃ u, Feasible a0 gap total u := by
  classical
  choose owner ho using howner
  refine ⟨fun i j => if i=owner j then total j else 0,?_,?_⟩
  · intro j
    simp
  · intro i j hi
    have hn : i≠owner j := by intro h; exact hi (h ▸ ho j)
    simp only [ite_eq_right hn]
    split_ifs; simp

omit [Fintype J] in
theorem feasible_convex (a0 gap : H → J → ℝ) (total : J → ℝ) :
    Convex ℝ {u | Feasible a0 gap total u} := by
  intro u hu v hv a b ha hb hab
  constructor
  · intro j
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,Finset.sum_add_distrib,
      ← Finset.mul_sum,hu.1 j,hv.1 j]
    rw [← add_mul,hab,one_mul]
  · intro i j hi
    have hu' := hu.2 i j hi
    have hv' := hv.2 i j hi
    by_cases hg : 0<gap i j
    · simp only [ite_eq_left hg] at hu' hv' ⊢
      simp [hu',hv']
    · simp only [ite_eq_right hg] at hu' hv' ⊢
      exact add_nonneg (mul_nonneg ha hu') (mul_nonneg hb hv')

def forceLinear (lambda : H → ℝ) (force : H → J → ℝ) :
    (H → J → ℝ) →ₗ[ℝ] ℝ where
  toFun v := ∑ i, pair (force i) (v i)/lambda i
  map_add' u v := by
    simp [Pi.add_apply,pair_add_right,add_div,Finset.sum_add_distrib]
  map_smul' r v := by
    simp only [Pi.smul_apply,pair_smul_right,smul_eq_mul,Finset.mul_sum,RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro i _
    ring

def coordinate (i : H) (j : J) : (H → J → ℝ) →ₗ[ℝ] ℝ where
  toFun u := u i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def aggregate (j : J) : (H → J → ℝ) →ₗ[ℝ] ℝ := ∑ i, coordinate i j

theorem variational_solution
    (A : H → ((J → ℝ) →ₗ[ℝ] (J → ℝ))) (lambda : H → ℝ)
    (a0 gap force : H → J → ℝ) (total : J → ℝ)
    (hlambda : ∀ i, 0<lambda i)
    (hA : ∀ i v, v≠0 → 0<pair v (A i v))
    (hsym : ∀ i u v, pair u (A i v)=pair v (A i u))
    (howner : ∀ j, ∃ i, 0<a0 i j) :
    ∃ u, Feasible a0 gap total u ∧ ∀ v, Feasible a0 gap total v →
      0≤∑ i, pair (A i (u i)+force i) (v i-u i)/lambda i := by
  classical
  let : InnerProductSpace.Core ℝ (QuadraticSpace H J) := weightedCore A lambda hlambda hA hsym
  let ng : NormedAddCommGroup (QuadraticSpace H J) :=
    InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)
  let : SeminormedAddCommGroup (QuadraticSpace H J) :=
    @NormedAddCommGroup.toSeminormedAddCommGroup _ ng
  let : InnerProductSpace ℝ (QuadraticSpace H J) := InnerProductSpace.ofCore inferInstance
  let : CompleteSpace (QuadraticSpace H J) := FiniteDimensional.complete ℝ (QuadraticSpace H J)
  have heval (i : H) (j : J) : Continuous (fun u : QuadraticSpace H J => u i j) := by
    let ev : QuadraticSpace H J →ₗ[ℝ] ℝ := coordinate i j
    exact ev.continuous_of_finiteDimensional
  have hagg (j : J) : Continuous (fun u : QuadraticSpace H J => ∑ i, u i j) := by
    exact continuous_finsetSum _ (fun i _ => heval i j)
  have hclosed : IsClosed {u : QuadraticSpace H J | Feasible a0 gap total u} := by
    change IsClosed ({u : QuadraticSpace H J | ∀ j, ∑ i, u i j=total j} ∩
      {u : QuadraticSpace H J | ∀ i j, ¬0<a0 i j → if 0<gap i j then u i j=0 else 0≤u i j})
    apply IsClosed.inter
    · simpa only [Set.ofPred_forall] using
        isClosed_iInter (fun j => isClosed_eq (hagg j) continuous_const)
    · simp only [Set.ofPred_forall]
      apply isClosed_iInter
      intro i
      apply isClosed_iInter
      intro j
      apply isClosed_iInter
      intro _
      by_cases hg : 0<gap i j
      · simp only [ite_eq_left hg]
        exact isClosed_eq (heval i j) continuous_const
      · simp only [ite_eq_right hg]
        exact isClosed_le continuous_const (heval i j)
  let fl : QuadraticSpace H J →ₗ[ℝ] ℝ := forceLinear lambda force
  let f : QuadraticSpace H J →L[ℝ] ℝ := fl.toContinuousLinearMap
  let center : QuadraticSpace H J := (InnerProductSpace.toDual ℝ (QuadraticSpace H J)).symm (-f)
  have hn : {u : QuadraticSpace H J | Feasible a0 gap total u}.Nonempty :=
    feasible_nonempty a0 gap total howner
  have hc : Convex ℝ {u : QuadraticSpace H J | Feasible a0 gap total u} :=
    feasible_convex a0 gap total
  obtain ⟨u,hu,hmin⟩ := exists_norm_eq_iInf_of_complete_convex
    hn hclosed.isComplete hc center
  let u0 : H → J → ℝ := u
  refine ⟨u0,hu,?_⟩
  intro v hv
  have hi := (norm_eq_iInf_iff_real_inner_le_zero hc hu).mp hmin
    (show QuadraticSpace H J from v) hv
  rw [inner_sub_left,InnerProductSpace.toDual_symm_apply] at hi
  change -forceLinear lambda force (v-u0)-energyPair A lambda u0 (v-u0)≤0 at hi
  have heq : (∑ i, pair (A i (u0 i)+force i) (v i-u0 i)/lambda i)=
      energyPair A lambda u0 (v-u0)+forceLinear lambda force (v-u0) := by
    simp only [energyPair,forceLinear,LinearMap.coe_mk,AddHom.coe_mk,Pi.sub_apply,
      pair_add_left,add_div,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [hsym i]
    congr 2
    exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
  rw [heq]
  linarith

end TangentProjection

#print axioms TangentProjection.pair_add_left
#print axioms TangentProjection.pair_smul_left
#print axioms TangentProjection.weightedCore
#print axioms TangentProjection.feasible_nonempty
#print axioms TangentProjection.feasible_convex
#print axioms TangentProjection.variational_solution
