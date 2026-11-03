import TangentSolverStability
import OverlapBoundaryExistence

/-! Joint nonlinear connector and physical-response build. The two component
sources are retained and bound by verify.py; the accepted tangent is imported,
not rebuilt. -/


/-! Exact identification of actual nonlinear equilibrium changes. This is
not a replacement of actual household optimization by a posited Euler root. -/

noncomputable section
open scoped BigOperators Topology
open Filter Set OwnershipCRRA OwnershipMarginal OwnershipPositive OwnershipSupported
open OverlapLocal OverlapPrimitive OverlapBoundaryTangent

namespace NonlinearComplementarityBridge
variable {H J S : Type*} [Fintype H] [Fintype J] [Fintype S]

def linearGap (D : H → Data J S) (e : H → ℝ) (a0 : H → J → ℝ)
    (qstar : J → ℝ) (w : MarketState H J) : H → J → ℝ :=
  fun i j => physicalHessian (D i) (e i) (a0 i) qstar (w.2 i) j+
    physicalLambda (D i) (e i)*w.1 j

def nonlinearForce (D : H → Data J S) (e : H → ℝ) (a0 : H → J → ℝ)
    (supply qstar : J → ℝ) (v : PrimitiveShock H J S) (w : MarketState H J) : H → J → ℝ :=
  (primitiveResidual D e a0 supply (v,(qstar,a0)+w)).2-
    referenceGap D e a0 qstar-linearGap D e a0 qstar w

def supplyChange (v : PrimitiveShock H J S) : J → ℝ := fun j => ∑ i, v.2.1 i j

theorem actual_equilibrium_response (D : H → Data J S) (e : H → ℝ)
    (a0 : H → J → ℝ) (supply qstar : J → ℝ)
    (ha0 : ∀ i j, 0 ≤ a0 i j) (hstock : ∀ j, ∑ i, a0 i j=supply j)
    (hsupport : SupportsInitial D e a0 qstar)
    (v : PrimitiveShock H J S) (h : Admissible D e a0 v) (q : J → ℝ)
    (c : H → ℝ) (a : H → J → ℝ)
    (hEq : IsEquilibrium (changedData D e a0 v h) (currentResources e v)
      (initialPortfolio a0 v) (assetSupply supply v) q c a)
    (hown : ∀ i j, 0 < a0 i j → 0 < a i j)
    (hstrict : ∀ i j, 0 < referenceGap D e a0 qstar i j → a i j=0) :
    PhysicalResponse D e a0 qstar
      (nonlinearForce D e a0 supply qstar v ((q,a)-(qstar,a0)))
      (supplyChange v) ((q,a)-(qstar,a0)) := by
  have hg := reference_gap_conditions D e a0 qstar hsupport
  have hgap (i : H) (j : J) :
      (primitiveResidual D e a0 supply (v,(q,a))).2 i j=
      q j*(c i)^(-(changedData D e a0 v h i).gamma)-
        marginal (changedData D e a0 v h i) (a i) j := by
    rw [primitiveResidual_eq_actual]
    change (budgetValue (currentResources e v) (initialPortfolio a0 v) (q,a) i)^
      (-(changedData D e a0 v h i).gamma)*q j-_= _
    rw [equilibrium_budget_value _ _ _ _ _ _ _ hEq]
    ring
  have hslack (i : H) (j : J) :
      physicalHessian (D i) (e i) (a0 i) qstar (((q,a)-(qstar,a0)).2 i) j+
        physicalLambda (D i) (e i)*((q,a)-(qstar,a0)).1 j+
        nonlinearForce D e a0 supply qstar v ((q,a)-(qstar,a0)) i j=
      (primitiveResidual D e a0 supply (v,(q,a))).2 i j-referenceGap D e a0 qstar i j := by
    have ht : (qstar,a0)+((q,a)-(qstar,a0))=(q,a) := by abel
    simp only [nonlinearForce,linearGap,ht,Pi.sub_apply]
    ring
  constructor
  · intro j
    change (∑ i, (a i j - a0 i j)) = ∑ i, v.2.1 i j
    rw [Finset.sum_sub_distrib,hEq.ownership_clears]
    rw [hstock j]
    simp [assetSupply]
  · intro i j
    rw [hslack]
    by_cases ho : 0 < a0 i j
    · have hr : referenceGap D e a0 qstar i j=0 :=
        (mul_eq_zero.mp (hg.2 i j)).resolve_left (ne_of_gt ho)
      have ha := hown i j ho
      have hc := (hEq.corner_conditions i j).2
      have hactual : (primitiveResidual D e a0 supply (v,(q,a))).2 i j=0 := by
        rw [hgap]
        exact (mul_eq_zero.mp hc).resolve_left (ne_of_gt ha)
      simp [Corner,ho,hr,hactual]
    by_cases hs : 0 < referenceGap D e a0 qstar i j
    · have hi := hstrict i j hs
      have hz : a0 i j=0 := le_antisymm (le_of_not_gt ho) (ha0 i j)
      simp [Corner,hs,hi,hz]
    · have hz : a0 i j=0 := le_antisymm (le_of_not_gt ho) (ha0 i j)
      have hr : referenceGap D e a0 qstar i j=0 := le_antisymm (le_of_not_gt hs) (hg.1 i j)
      have hcweak : 0 ≤ a i j ∧ 0 ≤ (primitiveResidual D e a0 supply (v,(q,a))).2 i j ∧
          a i j*(primitiveResidual D e a0 supply (v,(q,a))).2 i j=0 := by
        rw [hgap]
        exact ⟨hEq.holdings_nonneg i j,sub_nonneg.mpr (hEq.corner_conditions i j).1,
          (hEq.corner_conditions i j).2⟩
      simpa [Corner,hz,hr] using hcweak

theorem all_actual_response_eventually (D : H → Data J S) (e : H → ℝ)
    (a0 : H → J → ℝ) (supply qstar : J → ℝ)
    (he : ∀ i, 0 < e i) (ha0 : ∀ i j, 0 ≤ a0 i j)
    (hstock : ∀ j, ∑ i, a0 i j=supply j) (hs : ∀ j, 0 < supply j)
    (hsupport : SupportsInitial D e a0 qstar) :
    ∀ᶠ v in 𝓝 0, ∀ h : Admissible D e a0 v, ∀ q c a,
      IsEquilibrium (changedData D e a0 v h) (currentResources e v)
        (initialPortfolio a0 v) (assetSupply supply v) q c a →
      PhysicalResponse D e a0 qstar
        (nonlinearForce D e a0 supply qstar v ((q,a)-(qstar,a0)))
        (supplyChange v) ((q,a)-(qstar,a0)) := by
  have howners : {p : PrimitiveShock H J S × MarketState H J |
      ∀ i j, 0 < a0 i j → 0 < p.2.2 i j} ∈ 𝓝 (0,(qstar,a0)) := by
    apply Filter.eventually_all.mpr
    intro i
    apply Filter.eventually_all.mpr
    intro j
    by_cases hi : 0 < a0 i j
    · have hc : Continuous (fun p : PrimitiveShock H J S × MarketState H J => p.2.2 i j) := by
        fun_prop
      exact (hc.continuousAt.eventually (Ioi_mem_nhds hi)).mono (fun _ hp _ => hp)
    · exact Filter.Eventually.of_forall (fun _ hp => False.elim (hi hp))
  have hstrict : ∀ᶠ v : PrimitiveShock H J S in 𝓝 0, ∀ i j,
      0 < referenceGap D e a0 qstar i j → ∀ h : Admissible D e a0 v, ∀ q c a,
      IsEquilibrium (changedData D e a0 v h) (currentResources e v)
        (initialPortfolio a0 v) (assetSupply supply v) q c a → a i j=0 := by
    apply Filter.eventually_all.mpr
    intro i
    apply Filter.eventually_all.mpr
    intro j
    by_cases hi : 0 < referenceGap D e a0 qstar i j
    · have hp : marginal (D i) (a0 i) j < qstar j*(e i)^(-(D i).gamma) := by
        exact sub_pos.mp hi
      exact (OverlapBoundary.strict_nonowner_persists D e a0 supply qstar he ha0
        hstock hs hsupport i j hp).mono (fun _ hv _ => hv)
    · exact Filter.Eventually.of_forall (fun _ hp => False.elim (hi hp))
  filter_upwards [OverlapBoundary.all_actual_equilibria_near_boundary_reference
    D e a0 supply qstar he ha0 hstock hs hsupport _ howners,hstrict] with v hv hvs
  intro h q c a hEq
  exact actual_equilibrium_response D e a0 supply qstar ha0 hstock hsupport v h q c a hEq
    (hv h q c a hEq) (fun i j hi => hvs i j hi h q c a hEq)

theorem small_remainder_response_unique
    (A : H → ((J → ℝ) →ₗ[ℝ] (J → ℝ))) (lambda : H → ℝ)
    (a0 gap : H → J → ℝ) (E : MarketState H J → H → J → ℝ)
    (b : J → ℝ) (K eps : ℝ) (hK : 0 ≤ K) (hsmall : K*eps < 1)
    (hbound : ∀ f g b c z w, IsResponse A lambda a0 gap f b z →
      IsResponse A lambda a0 gap g c w → ‖z-w‖ ≤ K*‖(f-g,b-c)‖)
    (z w : MarketState H J) (hz : IsResponse A lambda a0 gap (E z) b z)
    (hw : IsResponse A lambda a0 gap (E w) b w)
    (hE : ‖E z-E w‖ ≤ eps*‖z-w‖) : z=w := by
  have hh := hbound (E z) (E w) b b z w hz hw
  simp only [sub_self,Prod.norm_def,norm_zero,max_eq_left (norm_nonneg _)] at hh
  change ‖z-w‖ ≤ K*‖E z-E w‖ at hh
  have hh' := hh.trans (mul_le_mul_of_nonneg_left hE hK)
  have hzero : ‖z-w‖=0 := by
    by_contra hn
    have hp : 0 < ‖z-w‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hn)
    have hlt : K*(eps*‖z-w‖) < ‖z-w‖ := calc
      K*(eps*‖z-w‖)=(K*eps)*‖z-w‖ := by ring
      _ < 1*‖z-w‖ := mul_lt_mul_of_pos_right hsmall hp
      _ = ‖z-w‖ := one_mul _
    exact (not_lt_of_ge hh') hlt
  exact sub_eq_zero.mp (norm_eq_zero.mp hzero)

theorem physical_small_remainder_unique (D : H → Data J S) (e : H → ℝ)
    (a0 : H → J → ℝ) (supply qstar : J → ℝ)
    (he : ∀ i, 0 < e i) (ha0 : ∀ i j, 0 ≤ a0 i j)
    (hstock : ∀ j, ∑ i, a0 i j=supply j) (hs : ∀ j, 0 < supply j) :
    ∃ K : ℝ, 0 < K ∧ ∀ (E : MarketState H J → H → J → ℝ)
      (b : J → ℝ) (z w : MarketState H J),
      PhysicalResponse D e a0 qstar (E z) b z →
      PhysicalResponse D e a0 qstar (E w) b w →
      ‖E z-E w‖ ≤ (1/(2*K))*‖z-w‖ → z=w := by
  obtain ⟨K,hK,hbound⟩ := TangentSolverStability.physical_response_lipschitz_bound
    D e a0 supply qstar he ha0 hstock hs
  refine ⟨K,hK,?_⟩
  intro E b z w hz hw hE
  apply small_remainder_response_unique _ _ a0 _ E b K (1/(2*K)) hK.le _
    (fun f g b c z w hz hw => hbound f g b c z w hz hw) z w hz hw hE
  have hh : K*(1/(2*K))=1/2 := by field_simp [ne_of_gt hK]
  rw [hh]
  norm_num

theorem scaled_response_tendsto {N : Type*} (l : Filter N)
    (A : H → ((J → ℝ) →ₗ[ℝ] (J → ℝ))) (lambda : H → ℝ)
    (a0 gap : H → J → ℝ) (K : ℝ) (_hK : 0 ≤ K)
    (hbound : ∀ f g b c z w, IsResponse A lambda a0 gap f b z →
      IsResponse A lambda a0 gap g c w → ‖z-w‖ ≤ K*‖(f-g,b-c)‖)
    (t : N → ℝ) (f : N → H → J → ℝ) (b : N → J → ℝ)
    (z : N → MarketState H J) (fstar : H → J → ℝ) (bstar : J → ℝ)
    (zstar : MarketState H J) (ht : ∀ᶠ n in l, 0 ≤ t n)
    (hz : ∀ᶠ n in l, IsResponse A lambda a0 gap (f n) (b n) (z n))
    (hstar : IsResponse A lambda a0 gap fstar bstar zstar)
    (hf : Tendsto (fun n => (t n)⁻¹ • f n) l (𝓝 fstar))
    (hb : Tendsto (fun n => (t n)⁻¹ • b n) l (𝓝 bstar)) :
    Tendsto (fun n => (t n)⁻¹ • z n) l (𝓝 zstar) := by
  have hnorm : Tendsto (fun n => K*‖((t n)⁻¹ • f n-fstar,(t n)⁻¹ • b n-bstar)‖)
      l (𝓝 0) := by
    have hh := ((hf.sub (tendsto_const_nhds (x := fstar))).prodMk_nhds
      (hb.sub (tendsto_const_nhds (x := bstar)))).norm
    simpa using tendsto_const_nhds.mul hh
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Filter.Eventually.of_forall (fun n => norm_nonneg _)) _ hnorm
  filter_upwards [ht,hz] with n htn hzn
  exact hbound _ _ _ _ _ _
    (TangentMarketExistence.response_nonnegative_scale A lambda a0 gap (f n) (b n)
      (z n) hzn (t n)⁻¹ (inv_nonneg.mpr htn)) hstar

end NonlinearComplementarityBridge

#print axioms NonlinearComplementarityBridge.actual_equilibrium_response
#print axioms NonlinearComplementarityBridge.all_actual_response_eventually
#print axioms NonlinearComplementarityBridge.small_remainder_response_unique
#print axioms NonlinearComplementarityBridge.physical_small_remainder_unique
#print axioms NonlinearComplementarityBridge.scaled_response_tendsto


noncomputable section
open scoped BigOperators Topology NNReal
open Filter Set OwnershipCRRA OwnershipMarginal OwnershipPositive OwnershipSupported
open OverlapLocal OverlapPrimitive OverlapBoundaryTangent NonlinearComplementarityBridge

namespace PhysicalBoundaryResponse
variable {H J S : Type*} [Fintype H] [Fintype J] [Fintype S] [Nonempty H]

def parameterForce (D : H → Data J S) (e : H → ℝ) (a0 : H → J → ℝ)
    (supply qstar : J → ℝ) : PrimitiveShock H J S →L[ℝ] (H → J → ℝ) :=
  (ContinuousLinearMap.snd ℝ (J → ℝ) (H → J → ℝ)) ∘L
    fderiv ℝ (primitiveResidual D e a0 supply) (0,(qstar,a0)) ∘L
      ContinuousLinearMap.inl ℝ (PrimitiveShock H J S) (MarketState H J)

def remainder (D : H → Data J S) (e : H → ℝ) (a0 : H → J → ℝ)
    (supply qstar : J → ℝ) (p : PrimitiveShock H J S × MarketState H J) : H → J → ℝ :=
  nonlinearForce D e a0 supply qstar p.1 p.2-parameterForce D e a0 supply qstar p.1

theorem partial_derivative_eq (D : H → Data J S) (e : H → ℝ)
    (a0 : H → J → ℝ) (supply qstar : J → ℝ)
    (he : ∀ i, 0 < e i) (ha0 : ∀ i j, 0 ≤ a0 i j) :
    fderiv ℝ (primitiveResidual D e a0 supply) (0,(qstar,a0)) ∘L
      ContinuousLinearMap.inr ℝ (PrimitiveShock H J S) (MarketState H J)=
    referenceDerivative D e a0 qstar := by
  have hc := primitiveResidual_contDiffAt D e a0 supply qstar he ha0
  have hg : HasFDerivAt (fun z : MarketState H J => ((0 : PrimitiveShock H J S),z))
      (ContinuousLinearMap.inr ℝ (PrimitiveShock H J S) (MarketState H J)) (qstar,a0) :=
    (hasFDerivAt_const (0 : PrimitiveShock H J S) (qstar,a0)).prodMk (hasFDerivAt_id _)
  have hh := (hc.differentiableAt (by norm_num)).hasFDerivAt.comp (qstar,a0) hg
  have hfixed : HasFDerivAt (OverlapLocal.residual D e a0 supply)
      (fderiv ℝ (primitiveResidual D e a0 supply) (0,(qstar,a0)) ∘L
        ContinuousLinearMap.inr ℝ (PrimitiveShock H J S) (MarketState H J)) (qstar,a0) := by
    simpa only [Function.comp_def,primitiveResidual_zero] using hh
  exact hfixed.unique
    (actual_residual_reference_strict_derivative D e a0 supply qstar he ha0).hasFDerivAt

omit [Nonempty H] in
theorem remainder_zero (D : H → Data J S) (e : H → ℝ)
    (a0 : H → J → ℝ) (supply qstar : J → ℝ) :
    remainder D e a0 supply qstar 0=0 := by
  ext i j
  simp [remainder,nonlinearForce,linearGap,primitiveResidual_zero,OverlapLocal.residual,
    choiceEquation,referenceGap,budget_reference,mul_comm]

theorem remainder_strict_derivative_zero (D : H → Data J S) (e : H → ℝ)
    (a0 : H → J → ℝ) (supply qstar : J → ℝ)
    (he : ∀ i, 0 < e i) (ha0 : ∀ i j, 0 ≤ a0 i j) :
    HasStrictFDerivAt (𝕜 := ℝ) (remainder D e a0 supply qstar) 0 0 := by
  let R := fderiv ℝ (primitiveResidual D e a0 supply) (0,(qstar,a0))
  let L := (ContinuousLinearMap.snd ℝ (J → ℝ) (H → J → ℝ)) ∘L
    referenceDerivative D e a0 qstar
  have ht : HasStrictFDerivAt
      (fun p : PrimitiveShock H J S × MarketState H J => (p.1,(qstar,a0)+p.2))
      (ContinuousLinearMap.id ℝ (PrimitiveShock H J S × MarketState H J)) 0 := by
    have hmap : (fun p : PrimitiveShock H J S × MarketState H J => (p.1,(qstar,a0)+p.2))=
        (fun p : PrimitiveShock H J S × MarketState H J => id p+(0,(qstar,a0))) := by
      funext p
      change (p.1,(qstar,a0)+p.2)=(p.1+0,p.2+(qstar,a0))
      rw [add_zero,add_comm (qstar,a0) p.2]
    rw [hmap]
    exact (hasStrictFDerivAt_id (𝕜 := ℝ)
      (0 : PrimitiveShock H J S × MarketState H J)).add_const (0,(qstar,a0))
  have hc := (primitiveResidual_contDiffAt D e a0 supply qstar he ha0).hasStrictFDerivAt
    (by norm_num)
  have hc' : HasStrictFDerivAt (primitiveResidual D e a0 supply) R
      ((0 : PrimitiveShock H J S),(qstar,a0)+(0 : MarketState H J)) := by
    simpa only [add_zero] using hc
  have hcomp : HasStrictFDerivAt
      (fun p : PrimitiveShock H J S × MarketState H J =>
        primitiveResidual D e a0 supply (p.1,(qstar,a0)+p.2))
      (R ∘L ContinuousLinearMap.id ℝ (PrimitiveShock H J S × MarketState H J)) 0 :=
    hc'.comp 0 ht
  have hg := hcomp.snd
  have hL : ∀ w, L w=linearGap D e a0 qstar w := by intro w; rfl
  have hr := ((hg.sub_const (referenceGap D e a0 qstar)).sub
      (L.comp (ContinuousLinearMap.snd ℝ (PrimitiveShock H J S) (MarketState H J))).hasStrictFDerivAt).sub
      ((parameterForce D e a0 supply qstar).comp
        (ContinuousLinearMap.fst ℝ (PrimitiveShock H J S) (MarketState H J))).hasStrictFDerivAt
  have hpart := partial_derivative_eq D e a0 supply qstar he ha0
  have hder : (ContinuousLinearMap.snd ℝ (J → ℝ) (H → J → ℝ)) ∘L
      (R ∘L ContinuousLinearMap.id ℝ (PrimitiveShock H J S × MarketState H J))-
      L ∘L ContinuousLinearMap.snd ℝ (PrimitiveShock H J S) (MarketState H J)-
      parameterForce D e a0 supply qstar ∘L
        ContinuousLinearMap.fst ℝ (PrimitiveShock H J S) (MarketState H J)=0 := by
    apply ContinuousLinearMap.ext
    intro p
    funext i j
    have hd : R p=R (p.1,0)+R (0,p.2) := by
      rw [← map_add]
      congr 1
      simp
    have hp : R (0,p.2)=referenceDerivative D e a0 qstar p.2 :=
      congrArg (fun K : MarketState H J →L[ℝ] MarketState H J => K p.2) hpart
    change (R p).2 i j-L p.2 i j-(R (p.1,0)).2 i j=0
    rw [hd,hp]
    change (R (p.1,0)).2 i j+(referenceDerivative D e a0 qstar p.2).2 i j-
      (referenceDerivative D e a0 qstar p.2).2 i j-(R (p.1,0)).2 i j=0
    ring
  rw [hder] at hr
  convert hr using 1
  funext p i j
  change _= (primitiveResidual D e a0 supply (p.1,(qstar,a0)+p.2)).2 i j-
    referenceGap D e a0 qstar i j-L p.2 i j-parameterForce D e a0 supply qstar p.1 i j
  rw [hL]
  rfl

theorem nonlinear_force_small_state_difference (D : H → Data J S) (e : H → ℝ)
    (a0 : H → J → ℝ) (supply qstar : J → ℝ)
    (he : ∀ i, 0 < e i) (ha0 : ∀ i j, 0 ≤ a0 i j) (eps : ℝ) (heps : 0 < eps) :
    ∃ U ∈ 𝓝 (0 : PrimitiveShock H J S × MarketState H J),
      ∀ v z w, (v,z) ∈ U → (v,w) ∈ U →
        ‖nonlinearForce D e a0 supply qstar v z-
          nonlinearForce D e a0 supply qstar v w‖ ≤ eps*‖z-w‖ := by
  let en : ℝ≥0 := NNReal.mk eps heps.le
  have hen : (0 : ℝ≥0) < en := NNReal.coe_pos.mp heps
  have hr := remainder_strict_derivative_zero D e a0 supply qstar he ha0
  obtain ⟨U,hU,hLip⟩ := hr.exists_lipschitzOnWith_of_nnnorm_lt en (by simpa using hen)
  refine ⟨U,hU,?_⟩
  intro v z w hz hw
  have hh := hLip.norm_sub_le hz hw
  have hcoe : (en : ℝ)=eps := rfl
  rw [hcoe] at hh
  have heq : remainder D e a0 supply qstar (v,z)-remainder D e a0 supply qstar (v,w)=
      nonlinearForce D e a0 supply qstar v z-nonlinearForce D e a0 supply qstar v w := by
    dsimp [remainder]
    abel
  rw [heq] at hh
  have hd : ‖(v,z)-(v,w)‖=‖z-w‖ := by
    change max ‖v-v‖ ‖z-w‖=‖z-w‖
    simp
  simpa only [hd] using hh

theorem nearby_actual_boundary_uniqueness (D : H → Data J S) (e : H → ℝ)
    (a0 : H → J → ℝ) (supply qstar : J → ℝ)
    (he : ∀ i, 0 < e i) (ha0 : ∀ i j, 0 ≤ a0 i j)
    (hstock : ∀ j, ∑ i, a0 i j=supply j) (hs : ∀ j, 0 < supply j)
    (hsupport : SupportsInitial D e a0 qstar) :
    ∀ᶠ v in 𝓝 0, ∀ h : Admissible D e a0 v, ∀ q c a q' c' a',
      IsEquilibrium (changedData D e a0 v h) (currentResources e v)
        (initialPortfolio a0 v) (assetSupply supply v) q c a →
      IsEquilibrium (changedData D e a0 v h) (currentResources e v)
        (initialPortfolio a0 v) (assetSupply supply v) q' c' a' → (q,c,a)=(q',c',a') := by
  obtain ⟨K,hK,hunique⟩ := physical_small_remainder_unique D e a0 supply qstar he ha0 hstock hs
  obtain ⟨U,hU,hsmall⟩ := nonlinear_force_small_state_difference D e a0 supply qstar he ha0
    (1/(2*K)) (by positivity)
  let V : Set (PrimitiveShock H J S × MarketState H J) :=
    {p | (p.1,p.2-(qstar,a0)) ∈ U}
  have hV : V ∈ 𝓝 (0,(qstar,a0)) := by
    have hc : Continuous (fun p : PrimitiveShock H J S × MarketState H J => (p.1,p.2-(qstar,a0))) := by
      fun_prop
    have hx := hc.tendsto ((0 : PrimitiveShock H J S),(qstar,a0))
    have hzero : ((0 : PrimitiveShock H J S),(qstar,a0)-(qstar,a0))=
        (0 : PrimitiveShock H J S × MarketState H J) := by
      apply Prod.ext <;> simp
    change Tendsto (fun p : PrimitiveShock H J S × MarketState H J => (p.1,p.2-(qstar,a0)))
      (𝓝 (0,(qstar,a0))) (𝓝 ((0 : PrimitiveShock H J S),(qstar,a0)-(qstar,a0))) at hx
    rw [hzero] at hx
    exact hx.eventually hU
  filter_upwards [all_actual_response_eventually D e a0 supply qstar he ha0 hstock hs hsupport,
    OverlapBoundary.all_actual_equilibria_near_boundary_reference D e a0 supply qstar
      he ha0 hstock hs hsupport V hV] with v hv hn
  intro h q c a q' c' a' hEq hEq'
  have hz := hv h q c a hEq
  have hw := hv h q' c' a' hEq'
  have hid := hunique (nonlinearForce D e a0 supply qstar v) (supplyChange v)
    ((q,a)-(qstar,a0)) ((q',a')-(qstar,a0)) hz hw
    (hsmall v _ _ (hn h q c a hEq) (hn h q' c' a' hEq'))
  have hqa : (q,a)=(q',a') := by
    simpa using congrArg (fun x => x+(qstar,a0)) hid
  have hq : q=q' := congrArg Prod.fst hqa
  have ha : a=a' := congrArg Prod.snd hqa
  subst q'
  subst a'
  have hc : c=c' := by
    funext i
    exact (congrFun (equilibrium_budget_value _ _ _ _ _ _ _ hEq) i).symm.trans
      (congrFun (equilibrium_budget_value _ _ _ _ _ _ _ hEq') i)
  subst c'
  rfl

theorem nearby_actual_boundary_exists_unique (D : H → Data J S) (e : H → ℝ)
    (a0 : H → J → ℝ) (supply qstar : J → ℝ)
    (he : ∀ i, 0 < e i) (ha0 : ∀ i j, 0 ≤ a0 i j)
    (hstock : ∀ j, ∑ i, a0 i j=supply j) (hs : ∀ j, 0 < supply j)
    (hsupport : SupportsInitial D e a0 qstar) :
    ∀ᶠ v in 𝓝 0, ∀ h : Admissible D e a0 v,
      ∃! z : (J → ℝ) × (H → ℝ) × (H → J → ℝ),
        IsEquilibrium (changedData D e a0 v h) (currentResources e v)
          (initialPortfolio a0 v) (assetSupply supply v) z.1 z.2.1 z.2.2 := by
  filter_upwards [nearby_actual_boundary_uniqueness D e a0 supply qstar he ha0 hstock hs hsupport,
    OverlapBoundary.boundary_changed_economy_exists D e a0 supply hstock hs] with v hu hex
  intro h
  obtain ⟨q,c,a,hEq⟩ := hex h
  exact ⟨(q,c,a),hEq,fun z hz => hu h _ _ _ _ _ _ hz hEq⟩

def supplyDerivative : PrimitiveShock H J S →L[ℝ] (J → ℝ) :=
  let L : PrimitiveShock H J S →ₗ[ℝ] (J → ℝ) :=
    { toFun := supplyChange
      map_add' := by intros; ext j; simp [supplyChange,Finset.sum_add_distrib]
      map_smul' := by intros; ext j; simp [supplyChange,Finset.mul_sum] }
  L.toContinuousLinearMap

omit [Nonempty H] in
theorem supplyDerivative_apply (v : PrimitiveShock H J S) :
    supplyDerivative v=supplyChange v := rfl

omit [Fintype S] [Nonempty H] in
theorem norm_pair_add_bound {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (F : P →L[ℝ] (H → J → ℝ)) (B : P →L[ℝ] (J → ℝ)) (v : P) (r : H → J → ℝ) :
    ‖(F v+r,B v)‖ ≤ (‖F‖+‖B‖)*‖v‖+‖r‖ := by
  rw [Prod.norm_def]
  apply max_le
  · calc
      ‖F v+r‖ ≤ ‖F v‖+‖r‖ := norm_add_le _ _
      _ ≤ ‖F‖*‖v‖+‖r‖ := add_le_add (F.le_opNorm v) le_rfl
      _ ≤ (‖F‖+‖B‖)*‖v‖+‖r‖ := by
        nlinarith [mul_nonneg B.opNorm_nonneg (norm_nonneg v)]
  · have hb := B.le_opNorm v
    nlinarith [norm_nonneg r,mul_nonneg F.opNorm_nonneg (norm_nonneg v)]

omit [Nonempty H] in
theorem physical_zero_response (D : H → Data J S) (e : H → ℝ)
    (a0 : H → J → ℝ) (qstar : J → ℝ) :
    PhysicalResponse D e a0 qstar 0 0 0 := by
  constructor
  · intro j
    simp
  · intro i j
    simp only [Prod.snd_zero,Pi.zero_apply,map_zero,Prod.fst_zero,mul_zero,add_zero]
    unfold Corner
    split_ifs <;> simp

theorem near_actual_linear_size_bound (D : H → Data J S) (e : H → ℝ)
    (a0 : H → J → ℝ) (supply qstar : J → ℝ)
    (he : ∀ i, 0 < e i) (ha0 : ∀ i j, 0 ≤ a0 i j)
    (hstock : ∀ j, ∑ i, a0 i j=supply j) (hs : ∀ j, 0 < supply j)
    (hsupport : SupportsInitial D e a0 qstar) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ v in 𝓝 0, ∀ h : Admissible D e a0 v, ∀ q c a,
      IsEquilibrium (changedData D e a0 v h) (currentResources e v)
        (initialPortfolio a0 v) (assetSupply supply v) q c a →
        ‖(q,a)-(qstar,a0)‖ ≤ C*‖v‖ := by
  obtain ⟨K,hK,hbound⟩ := TangentSolverStability.physical_response_lipschitz_bound
    D e a0 supply qstar he ha0 hstock hs
  let eps : ℝ := 1/(2*K)
  have heps : 0 < eps := by dsimp [eps]; positivity
  let en : ℝ≥0 := NNReal.mk eps heps.le
  have hen : (0 : ℝ≥0) < en := NNReal.coe_pos.mp heps
  have hsr := remainder_strict_derivative_zero D e a0 supply qstar he ha0
  obtain ⟨U,hU,hLip⟩ := hsr.exists_lipschitzOnWith_of_nnnorm_lt en (by simpa using hen)
  let F := parameterForce D e a0 supply qstar
  let B : PrimitiveShock H J S →L[ℝ] (J → ℝ) := supplyDerivative
  let C := 2*K*(‖F‖+‖B‖+eps)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  let V : Set (PrimitiveShock H J S × MarketState H J) :=
    {p | (p.1,p.2-(qstar,a0)) ∈ U}
  have hV : V ∈ 𝓝 (0,(qstar,a0)) := by
    have hc : Continuous (fun p : PrimitiveShock H J S × MarketState H J => (p.1,p.2-(qstar,a0))) := by
      fun_prop
    have hx := hc.tendsto ((0 : PrimitiveShock H J S),(qstar,a0))
    have hzero : ((0 : PrimitiveShock H J S),(qstar,a0)-(qstar,a0))=
        (0 : PrimitiveShock H J S × MarketState H J) := by
      apply Prod.ext <;> simp
    change Tendsto (fun p : PrimitiveShock H J S × MarketState H J => (p.1,p.2-(qstar,a0)))
      (𝓝 (0,(qstar,a0))) (𝓝 ((0 : PrimitiveShock H J S),(qstar,a0)-(qstar,a0))) at hx
    rw [hzero] at hx
    exact hx.eventually hU
  filter_upwards [all_actual_response_eventually D e a0 supply qstar he ha0 hstock hs hsupport,
    OverlapBoundary.all_actual_equilibria_near_boundary_reference D e a0 supply qstar
      he ha0 hstock hs hsupport V hV] with v hv hn
  intro h q c a hEq
  let w : MarketState H J := (q,a)-(qstar,a0)
  let r := remainder D e a0 supply qstar (v,w)
  have hr : ‖r‖ ≤ eps*(‖v‖+‖w‖) := by
    have hh := hLip.norm_sub_le (hn h q c a hEq) (mem_of_mem_nhds hU)
    have hcoe : (en : ℝ)=eps := rfl
    rw [hcoe] at hh
    rw [remainder_zero] at hh
    simp only [sub_zero,Prod.norm_def] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left
      (max_le (le_add_of_nonneg_right (norm_nonneg _)) (le_add_of_nonneg_left (norm_nonneg _))) heps.le)
  have hforce : nonlinearForce D e a0 supply qstar v w=F v+r := by
    dsimp [r,remainder,F]
    abel
  have hh := hbound _ 0 (supplyChange v) 0 w 0 (hv h q c a hEq)
    (physical_zero_response D e a0 qstar)
  simp only [sub_zero] at hh
  rw [hforce] at hh
  have hB : supplyChange v=B v := (supplyDerivative_apply v).symm
  rw [hB] at hh
  have hi := norm_pair_add_bound F B v r
  have hh' : ‖w‖ ≤ K*((‖F‖+‖B‖)*‖v‖+eps*(‖v‖+‖w‖)) :=
    hh.trans (mul_le_mul_of_nonneg_left
      (hi.trans (add_le_add le_rfl hr)) hK.le)
  have hhalf : K*eps=1/2 := by dsimp [eps]; field_simp [ne_of_gt hK]
  have hexpand : K*((‖F‖+‖B‖)*‖v‖+eps*(‖v‖+‖w‖))=
      K*(‖F‖+‖B‖+eps)*‖v‖+(K*eps)*‖w‖ := by ring
  rw [hexpand,hhalf] at hh'
  change ‖w‖ ≤ C*‖v‖
  dsimp [C]
  nlinarith

omit [Nonempty H] in
theorem actual_state_tendsto {N : Type*} (l : Filter N)
    (D : H → Data J S) (e : H → ℝ) (a0 : H → J → ℝ) (supply qstar : J → ℝ)
    (he : ∀ i, 0 < e i) (ha0 : ∀ i j, 0 ≤ a0 i j)
    (hstock : ∀ j, ∑ i, a0 i j=supply j) (hs : ∀ j, 0 < supply j)
    (hsupport : SupportsInitial D e a0 qstar)
    (v : N → PrimitiveShock H J S) (h : ∀ n, Admissible D e a0 (v n))
    (q : N → J → ℝ) (c : N → H → ℝ) (a : N → H → J → ℝ)
    (hEq : ∀ n, IsEquilibrium (changedData D e a0 (v n) (h n)) (currentResources e (v n))
      (initialPortfolio a0 (v n)) (assetSupply supply (v n)) (q n) (c n) (a n))
    (hv : Tendsto v l (𝓝 0)) :
    Tendsto (fun n => (q n,a n)) l (𝓝 (qstar,a0)) := by
  apply tendsto_def.mpr
  intro U hU
  let V : Set (PrimitiveShock H J S × MarketState H J) := Prod.snd ⁻¹' U
  have hV : V ∈ 𝓝 ((0 : PrimitiveShock H J S),(qstar,a0)) :=
    continuous_snd.continuousAt.preimage_mem_nhds hU
  filter_upwards [hv.eventually (OverlapBoundary.all_actual_equilibria_near_boundary_reference
    D e a0 supply qstar he ha0 hstock hs hsupport V hV)] with n hn
  exact hn (h n) (q n) (c n) (a n) (hEq n)

theorem actual_boundary_directional_limit {N : Type*} (l : Filter N)
    (D : H → Data J S) (e : H → ℝ) (a0 : H → J → ℝ) (supply qstar : J → ℝ)
    (he : ∀ i, 0 < e i) (ha0 : ∀ i j, 0 ≤ a0 i j)
    (hstock : ∀ j, ∑ i, a0 i j=supply j) (hs : ∀ j, 0 < supply j)
    (hsupport : SupportsInitial D e a0 qstar)
    (t : N → ℝ) (v : N → PrimitiveShock H J S) (h : ∀ n, Admissible D e a0 (v n))
    (q : N → J → ℝ) (c : N → H → ℝ) (a : N → H → J → ℝ)
    (hEq : ∀ n, IsEquilibrium (changedData D e a0 (v n) (h n)) (currentResources e (v n))
      (initialPortfolio a0 (v n)) (assetSupply supply (v n)) (q n) (c n) (a n))
    (ht : ∀ᶠ n in l, 0 < t n) (hv : Tendsto v l (𝓝 0))
    (d : PrimitiveShock H J S) (hd : Tendsto (fun n => (t n)⁻¹ • v n) l (𝓝 d))
    (zstar : MarketState H J)
    (hzstar : PhysicalResponse D e a0 qstar (parameterForce D e a0 supply qstar d)
      (supplyDerivative d) zstar) :
    Tendsto (fun n => (t n)⁻¹ • ((q n,a n)-(qstar,a0))) l (𝓝 zstar) := by
  let w : N → MarketState H J := fun n => (q n,a n)-(qstar,a0)
  have hw : Tendsto w l (𝓝 0) := by
    simpa [w] using (actual_state_tendsto l D e a0 supply qstar he ha0 hstock hs hsupport
      v h q c a hEq hv).sub (tendsto_const_nhds (x := (qstar,a0)))
  have hx : Tendsto (fun n => (v n,w n)) l (𝓝 0) := hv.prodMk_nhds hw
  obtain ⟨C,hC,hsize⟩ := near_actual_linear_size_bound D e a0 supply qstar he ha0 hstock hs hsupport
  have hwb : ∀ᶠ n in l, ‖w n‖ ≤ C*‖v n‖ := by
    filter_upwards [hv.eventually hsize] with n hn
    exact hn (h n) (q n) (c n) (a n) (hEq n)
  have hjoint : (fun n => (v n,w n)) =O[l] v := by
    apply Asymptotics.isBigO_iff.mpr
    refine ⟨1+C,?_⟩
    filter_upwards [hwb] with n hn
    rw [Prod.norm_def]
    apply max_le <;> nlinarith [norm_nonneg (v n)]
  have hvb : v =O[l] t := by
    apply Asymptotics.isBigO_iff.mpr
    refine ⟨‖d‖+1,?_⟩
    have hb := hd.norm.eventually (Iio_mem_nhds (show ‖d‖ < ‖d‖+1 by linarith))
    filter_upwards [ht,hb] with n htn hbn
    have hid : v n=t n • ((t n)⁻¹ • v n) := by
      rw [smul_smul,mul_inv_cancel₀ (ne_of_gt htn),one_smul]
    rw [hid,norm_smul]
    nlinarith [norm_nonneg (t n)]
  have hrho : (fun p => remainder D e a0 supply qstar p) =o[𝓝 0]
      (fun p : PrimitiveShock H J S × MarketState H J => p) := by
    simpa only [remainder_zero,sub_zero,zero_apply] using
      (remainder_strict_derivative_zero D e a0 supply qstar he ha0).hasFDerivAt.isLittleO
  have hrlim := ((hrho.comp_tendsto hx).trans_isBigO (hjoint.trans hvb)).tendsto_inv_smul_nhds_zero
  let F := parameterForce D e a0 supply qstar
  have hforce : Tendsto (fun n => (t n)⁻¹ • nonlinearForce D e a0 supply qstar (v n) (w n))
      l (𝓝 (F d)) := by
    have hh : Tendsto (fun n => F ((t n)⁻¹ • v n)+
        (t n)⁻¹ • remainder D e a0 supply qstar (v n,w n)) l (𝓝 (F d)) := by
      simpa only [Function.comp_def,add_zero] using (F.continuous.tendsto d |>.comp hd).add hrlim
    have hid : (fun n => F ((t n)⁻¹ • v n)+(t n)⁻¹ • remainder D e a0 supply qstar (v n,w n))=
        (fun n => (t n)⁻¹ • nonlinearForce D e a0 supply qstar (v n) (w n)) := by
      funext n
      simp only [remainder,map_smul,smul_sub,F]
      abel
    rw [hid] at hh
    exact hh
  have hsupply : Tendsto (fun n => (t n)⁻¹ • supplyChange (v n)) l
      (𝓝 (supplyDerivative d)) := by
    simpa only [Function.comp_def,map_smul,supplyDerivative_apply] using
      ((supplyDerivative (H := H) (J := J) (S := S)).continuous.tendsto d |>.comp hd)
  obtain ⟨K,hK,hbound⟩ := TangentSolverStability.physical_response_lipschitz_bound
    D e a0 supply qstar he ha0 hstock hs
  apply scaled_response_tendsto l _ _ a0 _ K hK.le
    (fun f g b c z w hz hw => hbound f g b c z w hz hw)
    t _ _ w (F d) (supplyDerivative d) zstar (ht.mono (fun _ hn => hn.le)) _ hzstar hforce hsupply
  filter_upwards [hv.eventually (all_actual_response_eventually D e a0 supply qstar
    he ha0 hstock hs hsupport)] with n hn
  exact hn (h n) (q n) (c n) (a n) (hEq n)

theorem actual_boundary_response_exists_unique {N : Type*} (l : Filter N)
    (D : H → Data J S) (e : H → ℝ) (a0 : H → J → ℝ) (supply qstar : J → ℝ)
    (he : ∀ i, 0 < e i) (ha0 : ∀ i j, 0 ≤ a0 i j)
    (hstock : ∀ j, ∑ i, a0 i j=supply j) (hs : ∀ j, 0 < supply j)
    (hsupport : SupportsInitial D e a0 qstar)
    (t : N → ℝ) (v : N → PrimitiveShock H J S) (h : ∀ n, Admissible D e a0 (v n))
    (q : N → J → ℝ) (c : N → H → ℝ) (a : N → H → J → ℝ)
    (hEq : ∀ n, IsEquilibrium (changedData D e a0 (v n) (h n)) (currentResources e (v n))
      (initialPortfolio a0 (v n)) (assetSupply supply (v n)) (q n) (c n) (a n))
    (ht : ∀ᶠ n in l, 0 < t n) (hv : Tendsto v l (𝓝 0))
    (d : PrimitiveShock H J S) (hd : Tendsto (fun n => (t n)⁻¹ • v n) l (𝓝 d)) :
    ∃! zstar : MarketState H J,
      PhysicalResponse D e a0 qstar (parameterForce D e a0 supply qstar d)
        (supplyDerivative d) zstar ∧
      Tendsto (fun n => (t n)⁻¹ • ((q n,a n)-(qstar,a0))) l (𝓝 zstar) := by
  obtain ⟨z,hz,hu⟩ := TangentMarketExistence.physical_tangent_exists_unique D e a0 supply qstar
    he ha0 hstock hs (parameterForce D e a0 supply qstar d) (supplyDerivative d)
  exact ⟨z,⟨hz,actual_boundary_directional_limit l D e a0 supply qstar he ha0 hstock hs hsupport
    t v h q c a hEq ht hv d hd z hz⟩,fun w hw => hu w hw.1⟩

end PhysicalBoundaryResponse

#print axioms PhysicalBoundaryResponse.partial_derivative_eq
#print axioms PhysicalBoundaryResponse.remainder_zero
#print axioms PhysicalBoundaryResponse.remainder_strict_derivative_zero
#print axioms PhysicalBoundaryResponse.nonlinear_force_small_state_difference
#print axioms PhysicalBoundaryResponse.nearby_actual_boundary_uniqueness
#print axioms PhysicalBoundaryResponse.nearby_actual_boundary_exists_unique
#print axioms PhysicalBoundaryResponse.physical_zero_response
#print axioms PhysicalBoundaryResponse.near_actual_linear_size_bound
#print axioms PhysicalBoundaryResponse.actual_state_tendsto
#print axioms PhysicalBoundaryResponse.actual_boundary_directional_limit
#print axioms PhysicalBoundaryResponse.actual_boundary_response_exists_unique

