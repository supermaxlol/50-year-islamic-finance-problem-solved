import TangentMarketExistence

/-! Stability for the actual physical mixed-complementarity tangent. The
norms in all public statements are the ordinary finite-dimensional Pi norms.
The Hessian norm is used only inside the proof. -/

noncomputable section
open scoped BigOperators RealInnerProductSpace
open OverlapLocal OverlapBoundaryTangent TangentProjection TangentMarketExistence

namespace TangentSolverStability
variable {H J : Type*} [Fintype H] [Fintype J]

theorem force_norm_bound (lambda : H → ℝ) (hlambda : ∀ i, 0 < lambda i)
    (f u : H → J → ℝ) :
    ‖forceLinear lambda f u‖ ≤
      (∑ i, (Fintype.card J : ℝ)/lambda i)*‖f‖*‖u‖ := by
  have hp (i : H) : ‖pair (f i) (u i)‖ ≤ (Fintype.card J : ℝ)*‖f‖*‖u‖ := by
    calc
      ‖pair (f i) (u i)‖ ≤ ∑ j, ‖f i j*u i j‖ := norm_sum_le _ _
      _ ≤ ∑ _j : J, ‖f‖*‖u‖ := by
        apply Finset.sum_le_sum
        intro j _
        rw [norm_mul]
        exact mul_le_mul
          ((norm_le_pi_norm (f i) j).trans (norm_le_pi_norm f i))
          ((norm_le_pi_norm (u i) j).trans (norm_le_pi_norm u i))
          (norm_nonneg _) (norm_nonneg _)
      _ = (Fintype.card J : ℝ)*‖f‖*‖u‖ := by simp [mul_assoc]
  calc
    ‖forceLinear lambda f u‖ ≤ ∑ i, ‖pair (f i) (u i)/lambda i‖ := norm_sum_le _ _
    _ ≤ ∑ i, ((Fintype.card J : ℝ)/lambda i)*‖f‖*‖u‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_div,Real.norm_eq_abs (lambda i),abs_of_pos (hlambda i)]
      calc
        ‖pair (f i) (u i)‖/lambda i ≤ ((Fintype.card J : ℝ)*‖f‖*‖u‖)/lambda i :=
          div_le_div_of_nonneg_right (hp i) (hlambda i).le
        _ = _ := by ring
    _ = _ := by rw [Finset.sum_mul,Finset.sum_mul]

theorem same_total_energy
    (A : H → ((J → ℝ) →ₗ[ℝ] (J → ℝ))) (lambda : H → ℝ)
    (a0 gap f g : H → J → ℝ) (b : J → ℝ)
    (hlambda : ∀ i, 0 < lambda i) (z w : MarketState H J)
    (hz : IsResponse A lambda a0 gap f b z)
    (hw : IsResponse A lambda a0 gap g b w) :
    energyPair A lambda (z.2-w.2) (z.2-w.2) ≤
      -forceLinear lambda (f-g) (z.2-w.2) := by
  have hi (i : H) : pair (z.2 i-w.2 i) (A i (z.2 i-w.2 i))/lambda i ≤
      -pair (z.2 i-w.2 i) (z.1-w.1)-
        pair (f i-g i) (z.2 i-w.2 i)/lambda i := by
    have hc := Finset.sum_nonpos (s := Finset.univ) (fun j _ =>
      corner_difference_nonpositive _ _ _ _ _ _ (hz.corners i j) (hw.corners i j))
    have heq : (∑ j, (z.2 i j-w.2 i j)*
        ((A i (z.2 i) j+lambda i*z.1 j+f i j)-
         (A i (w.2 i) j+lambda i*w.1 j+g i j))) =
        pair (z.2 i-w.2 i) (A i (z.2 i-w.2 i))+
        lambda i*pair (z.2 i-w.2 i) (z.1-w.1)+
        pair (f i-g i) (z.2 i-w.2 i) := by
      rw [map_sub]
      simp only [pair,Pi.sub_apply,Finset.mul_sum,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [heq] at hc
    apply (div_le_iff₀ (hlambda i)).mpr
    field_simp [ne_of_gt (hlambda i)]
    nlinarith
  have hclear : (fun j => ∑ i, (z.2 i-w.2 i) j)=(0 : J → ℝ) := by
    funext j
    simp only [Pi.sub_apply,Finset.sum_sub_distrib,hz.clears,hw.clears,sub_self,Pi.zero_apply]
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hi i)
  rw [Finset.sum_sub_distrib,Finset.sum_neg_distrib,pair_sum_left,hclear] at hh
  simpa [energyPair,forceLinear,pair] using hh

theorem holdings_same_total_bound
    (A : H → ((J → ℝ) →ₗ[ℝ] (J → ℝ))) (lambda : H → ℝ)
    (hlambda : ∀ i, 0 < lambda i)
    (hA : ∀ i v, v ≠ 0 → 0 < pair v (A i v))
    (hsym : ∀ i u v, pair u (A i v)=pair v (A i u)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a0 gap f g : H → J → ℝ) (b : J → ℝ)
      (z w : MarketState H J), IsResponse A lambda a0 gap f b z →
      IsResponse A lambda a0 gap g b w → ‖z.2-w.2‖ ≤ C*‖f-g‖ := by
  let : InnerProductSpace.Core ℝ (QuadraticSpace H J) := weightedCore A lambda hlambda hA hsym
  let ng : NormedAddCommGroup (QuadraticSpace H J) :=
    InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)
  let : NormedAddCommGroup (QuadraticSpace H J) := ng
  let : SeminormedAddCommGroup (QuadraticSpace H J) :=
    @NormedAddCommGroup.toSeminormedAddCommGroup _ ng
  let : InnerProductSpace ℝ (QuadraticSpace H J) := InnerProductSpace.ofCore inferInstance
  let backL : QuadraticSpace H J →ₗ[ℝ] (H → J → ℝ) := LinearMap.id
  let back : QuadraticSpace H J →L[ℝ] (H → J → ℝ) :=
    ⟨backL,backL.continuous_of_finiteDimensional⟩
  let c : ℝ := ∑ i, (Fintype.card J : ℝ)/lambda i
  have hc : 0 ≤ c := Finset.sum_nonneg (fun i _ => div_nonneg (Nat.cast_nonneg _) (hlambda i).le)
  let D : ℝ := c*‖back‖
  have hD : 0 ≤ D := mul_nonneg hc back.opNorm_nonneg
  refine ⟨‖back‖*D,mul_nonneg back.opNorm_nonneg hD,?_⟩
  intro a0 gap f g b z w hz hw
  let d : QuadraticSpace H J := z.2-w.2
  have he := same_total_energy A lambda a0 gap f g b hlambda z w hz hw
  have he' : ‖d‖^2 ≤ -forceLinear lambda (f-g) (back d) := by
    rw [← real_inner_self_eq_norm_sq]
    exact he
  have hb : -forceLinear lambda (f-g) (back d) ≤ D*‖f-g‖*‖d‖ := calc
    -forceLinear lambda (f-g) (back d) ≤ ‖forceLinear lambda (f-g) (back d)‖ := neg_le_abs _
    _ ≤ c*‖f-g‖*‖back d‖ := force_norm_bound lambda hlambda (f-g) (back d)
    _ ≤ c*‖f-g‖*(‖back‖*‖d‖) := mul_le_mul_of_nonneg_left (back.le_opNorm d)
      (mul_nonneg hc (norm_nonneg _))
    _ = D*‖f-g‖*‖d‖ := by dsimp [D]; ring
  have hd : ‖d‖ ≤ D*‖f-g‖ := by
    by_cases hzero : ‖d‖=0
    · rw [hzero]
      exact mul_nonneg hD (norm_nonneg _)
    · have hp : 0 < ‖d‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
      nlinarith
  calc
    ‖z.2-w.2‖=‖back d‖ := rfl
    _ ≤ ‖back‖*‖d‖ := back.le_opNorm d
    _ ≤ ‖back‖*(D*‖f-g‖) := mul_le_mul_of_nonneg_left hd back.opNorm_nonneg
    _ = (‖back‖*D)*‖f-g‖ := by ring

def recover (A : H → ((J → ℝ) →ₗ[ℝ] (J → ℝ))) (lambda : H → ℝ)
    (owner : J → H) : ((H → J → ℝ) × (H → J → ℝ)) →ₗ[ℝ] MarketState H J where
  toFun v := ((fun j => -(A (owner j) (v.1 (owner j)) j+v.2 (owner j) j)/lambda (owner j)),v.1)
  map_add' v w := by
    apply Prod.ext
    · funext j
      simp only [map_add,Pi.add_apply,Prod.fst_add,Prod.snd_add]
      ring
    · rfl
  map_smul' r v := by
    apply Prod.ext
    · funext j
      change -(A (owner j) (r • v.1 (owner j)) j+r*v.2 (owner j) j)/lambda (owner j)=_
      rw [map_smul]
      change -(r*(A (owner j) (v.1 (owner j))) j+r*v.2 (owner j) j)/lambda (owner j)=
        r*(-(A (owner j) (v.1 (owner j)) j+v.2 (owner j) j)/lambda (owner j))
      ring
    · rfl

theorem same_total_bound
    (A : H → ((J → ℝ) →ₗ[ℝ] (J → ℝ))) (lambda : H → ℝ)
    (a0 : H → J → ℝ) (hlambda : ∀ i, 0 < lambda i)
    (hA : ∀ i v, v ≠ 0 → 0 < pair v (A i v))
    (hsym : ∀ i u v, pair u (A i v)=pair v (A i u))
    (howner : ∀ j, ∃ i, 0 < a0 i j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (gap f g : H → J → ℝ) (b : J → ℝ)
      (z w : MarketState H J), IsResponse A lambda a0 gap f b z →
      IsResponse A lambda a0 gap g b w → ‖z-w‖ ≤ C*‖f-g‖ := by
  classical
  choose owner ho using howner
  obtain ⟨C,hC,hbound⟩ := holdings_same_total_bound A lambda hlambda hA hsym
  let recovery := (recover A lambda owner).toContinuousLinearMap
  refine ⟨‖recovery‖*(C+1),mul_nonneg (norm_nonneg _) (by linarith),?_⟩
  intro gap f g b z w hz hw
  have hid : z-w=recovery (z.2-w.2,f-g) := by
    apply Prod.ext
    · funext j
      have hzi : A (owner j) (z.2 (owner j)) j+lambda (owner j)*z.1 j+f (owner j) j=0 :=
        by simpa [Corner,ho j] using hz.corners (owner j) j
      have hwi : A (owner j) (w.2 (owner j)) j+lambda (owner j)*w.1 j+g (owner j) j=0 :=
        by simpa [Corner,ho j] using hw.corners (owner j) j
      change z.1 j-w.1 j=-(A (owner j) (z.2 (owner j)-w.2 (owner j)) j+
        (f (owner j) j-g (owner j) j))/lambda (owner j)
      rw [map_sub]
      apply (eq_div_iff (ne_of_gt (hlambda (owner j)))).mpr
      change _=-(A (owner j) (z.2 (owner j)) j-A (owner j) (w.2 (owner j)) j+_)
      nlinarith
    · rfl
  have hp : ‖(z.2-w.2,f-g)‖ ≤ (C+1)*‖f-g‖ := by
    rw [Prod.norm_def]
    apply max_le
    · have hh := hbound a0 gap f g b z w hz hw
      nlinarith [norm_nonneg (f-g)]
    · nlinarith [norm_nonneg (f-g)]
  rw [hid]
  exact (recovery.le_opNorm _).trans (by
    calc
      ‖recovery‖*‖(z.2-w.2,f-g)‖ ≤ ‖recovery‖*((C+1)*‖f-g‖) :=
        mul_le_mul_of_nonneg_left hp (norm_nonneg _)
      _ = (‖recovery‖*(C+1))*‖f-g‖ := by ring)

def lift [DecidableEq H] (owner : J → H) : (J → ℝ) →ₗ[ℝ] (H → J → ℝ) where
  toFun b i j := if i=owner j then b j else 0
  map_add' b c := by ext i j; by_cases h : i=owner j <;> simp [h]
  map_smul' r b := by ext i j; by_cases h : i=owner j <;> simp [h]

omit [Fintype J] in
theorem shift_total
    (A : H → ((J → ℝ) →ₗ[ℝ] (J → ℝ))) (lambda : H → ℝ)
    (a0 gap f : H → J → ℝ) (b : J → ℝ) (z : MarketState H J)
    (owner : J → H) (ho : ∀ j, 0 < a0 (owner j) j)
    (hz : IsResponse A lambda a0 gap f b z) :
    letI := Classical.decEq H
    IsResponse A lambda a0 gap (fun i => f i+A i (lift owner b i)) 0
      (z.1,z.2-lift owner b) := by
  classical
  constructor
  · intro j
    simp only [Pi.sub_apply,Finset.sum_sub_distrib,hz.clears,lift,
      LinearMap.coe_mk,AddHom.coe_mk]
    simp
  · intro i j
    have heq : A i ((z.2-lift owner b) i) j+lambda i*z.1 j+
        (f i+A i (lift owner b i)) j=A i (z.2 i) j+lambda i*z.1 j+f i j := by
      rw [show (z.2-lift owner b) i=z.2 i-lift owner b i from rfl,map_sub]
      simp only [Pi.sub_apply,Pi.add_apply]
      ring
    rw [heq]
    by_cases hi : 0 < a0 i j
    · simpa [Corner,hi] using hz.corners i j
    · have hn : i ≠ owner j := by intro h; exact hi (h ▸ ho j)
      simpa [Corner,hi,lift,hn] using hz.corners i j

theorem response_lipschitz_bound
    (A : H → ((J → ℝ) →ₗ[ℝ] (J → ℝ))) (lambda : H → ℝ)
    (a0 : H → J → ℝ) (hlambda : ∀ i, 0 < lambda i)
    (hA : ∀ i v, v ≠ 0 → 0 < pair v (A i v))
    (hsym : ∀ i u v, pair u (A i v)=pair v (A i u))
    (howner : ∀ j, ∃ i, 0 < a0 i j) :
    ∃ K : ℝ, 0 < K ∧ ∀ (gap f g : H → J → ℝ) (b c : J → ℝ)
      (z w : MarketState H J), IsResponse A lambda a0 gap f b z →
      IsResponse A lambda a0 gap g c w → ‖z-w‖ ≤ K*‖(f-g,b-c)‖ := by
  classical
  choose owner ho using howner
  obtain ⟨C,hC,hbound⟩ := same_total_bound A lambda a0 hlambda hA hsym (fun j => ⟨owner j,ho j⟩)
  let adjL : ((H → J → ℝ) × (J → ℝ)) →ₗ[ℝ] (H → J → ℝ) :=
    { toFun := fun v i => v.1 i+A i (lift owner v.2 i)
      map_add' := by intros; ext i j; simp [map_add]; ring
      map_smul' := by intros; ext i j; simp [map_smul]; ring }
  let adj := adjL.toContinuousLinearMap
  let outL : (J → ℝ) →ₗ[ℝ] MarketState H J :=
    (0 : (J → ℝ) →ₗ[ℝ] (J → ℝ)).prod (lift owner)
  let out := outL.toContinuousLinearMap
  refine ⟨C*‖adj‖+‖out‖+1,by positivity,?_⟩
  intro gap f g b c z w hz hw
  have hzs := shift_total A lambda a0 gap f b z owner ho hz
  have hws := shift_total A lambda a0 gap g c w owner ho hw
  have hh := hbound gap _ _ 0 _ _ hzs hws
  have hadj : (fun i => f i+A i (lift owner b i))-
      (fun i => g i+A i (lift owner c i))=adj (f-g,b-c) := by
    ext i j
    change _=(f i-g i+A i (lift owner (b-c) i)) j
    rw [map_sub]
    rw [show ((lift owner b-lift owner c) i)=lift owner b i-lift owner c i from rfl,map_sub]
    change _=(f i-g i+(A i (lift owner b i)-A i (lift owner c i))) j
    simp only [Pi.sub_apply,Pi.add_apply]
    ring
  rw [hadj] at hh
  have hid : z-w=((z.1,z.2-lift owner b)-(w.1,w.2-lift owner c))+out (b-c) := by
    apply Prod.ext
    · simp [out,outL]
    · change z.2-w.2=z.2-lift owner b-(w.2-lift owner c)+lift owner (b-c)
      rw [map_sub]
      abel
  have hb : ‖b-c‖ ≤ ‖(f-g,b-c)‖ := by rw [Prod.norm_def]; exact le_max_right _ _
  calc
    ‖z-w‖ ≤ ‖(z.1,z.2-lift owner b)-(w.1,w.2-lift owner c)‖+‖out (b-c)‖ :=
      hid ▸ norm_add_le _ _
    _ ≤ C*‖adj (f-g,b-c)‖+‖out‖*‖b-c‖ := add_le_add hh (out.le_opNorm _)
    _ ≤ C*(‖adj‖*‖(f-g,b-c)‖)+‖out‖*‖(f-g,b-c)‖ :=
      add_le_add (mul_le_mul_of_nonneg_left (adj.le_opNorm _) hC)
        (mul_le_mul_of_nonneg_left hb (norm_nonneg _))
    _ ≤ (C*‖adj‖+‖out‖+1)*‖(f-g,b-c)‖ := by nlinarith [norm_nonneg (f-g,b-c)]

section Physical
variable {S : Type*} [Fintype S]
open OwnershipCRRA

theorem physical_response_lipschitz_bound (D : H → Data J S) (e : H → ℝ)
    (a0 : H → J → ℝ) (supply qstar : J → ℝ)
    (he : ∀ i, 0 < e i) (ha0 : ∀ i j, 0 ≤ a0 i j)
    (hstock : ∀ j, ∑ i, a0 i j=supply j) (hs : ∀ j, 0 < supply j) :
    ∃ K : ℝ, 0 < K ∧ ∀ (f g : H → J → ℝ) (b c : J → ℝ)
      (z w : MarketState H J), PhysicalResponse D e a0 qstar f b z →
      PhysicalResponse D e a0 qstar g c w → ‖z-w‖ ≤ K*‖(f-g,b-c)‖ := by
  obtain ⟨K,hK,hbound⟩ := response_lipschitz_bound
    (fun i => physicalHessian (D i) (e i) (a0 i) qstar)
    (fun i => physicalLambda (D i) (e i)) a0
    (fun i => Real.rpow_pos_of_pos (he i) _)
    (fun i v hv => physicalHessian_positive (D i) (e i) (a0 i) qstar (he i) (ha0 i) v hv)
    (fun i u v => physicalHessian_symmetric (D i) (e i) (a0 i) qstar u v)
    (OverlapBoundary.positive_reference_owner a0 supply hstock hs)
  exact ⟨K,hK,fun f g b c z w hz hw => hbound _ f g b c z w hz hw⟩
end Physical
end TangentSolverStability

#print axioms TangentSolverStability.force_norm_bound
#print axioms TangentSolverStability.same_total_energy
#print axioms TangentSolverStability.holdings_same_total_bound
#print axioms TangentSolverStability.same_total_bound
#print axioms TangentSolverStability.shift_total
#print axioms TangentSolverStability.response_lipschitz_bound
#print axioms TangentSolverStability.physical_response_lipschitz_bound
