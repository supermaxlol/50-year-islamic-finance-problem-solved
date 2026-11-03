import GEOverlap

/-!
# Heterogeneous optimizing households: a bounded GE bridge

This module reuses the unchanged GE companion. Demand is constructed from
optimization for each household, not assumed. Utilities may differ. The first
endpoint is explicitly bounded and free-disposal; later endpoints strengthen
it only under stated monotonicity and resource conditions. No universal market
uniqueness, CRRA boundary lifting or exclusion of safe payoffs is asserted.
-/

noncomputable section
open scoped BigOperators
open Set
open GEOverlap

namespace OwnershipBridge

variable {G H : Type*} [Fintype G] [Fintype H]

def box (M : ℝ) : Set (G → ℝ) := {x | ∀ g, x g ∈ Icc (0 : ℝ) M}

def budget (M : ℝ) (ω : G → ℝ) (p : priceSimplex G) : Set (G → ℝ) :=
  {x | x ∈ box M ∧ ∑ g, (p : G → ℝ) g * x g ≤ ∑ g, (p : G → ℝ) g * ω g}

def IsOptimal (M : ℝ) (ω : G → ℝ) (U : (G → ℝ) → ℝ)
    (p : priceSimplex G) (x : G → ℝ) : Prop :=
  x ∈ budget M ω p ∧ ∀ y ∈ budget M ω p, U y ≤ U x

theorem exists_continuous_optimal_demand [Nonempty G]
    (M : ℝ) (hM : 0 ≤ M) (ω : G → ℝ) (hω : ∀ g, 0 < ω g)
    (U : (G → ℝ) → ℝ) (hUcont : Continuous U)
    (hUsc : StrictConcaveOn ℝ (box M) U) :
    ∃ d : priceSimplex G → (G → ℝ), Continuous d ∧
      (∀ p, IsOptimal M ω U p (d p)) ∧
      (∀ p x, IsOptimal M ω U p x → x = d p) := by
  classical
  have hbox : IsCompact (box M : Set (G → ℝ)) := by
    have hc : IsCompact (Set.univ.pi fun _ : G => Icc (0 : ℝ) M) :=
      isCompact_univ_pi fun _ => isCompact_Icc
    apply hc.of_isClosed_subset
    · have heq : (box M : Set (G → ℝ)) = ⋂ g, {x | x g ∈ Icc (0 : ℝ) M} := by
        ext x
        simp [box]
      rw [heq]
      exact isClosed_iInter fun g => isClosed_Icc.preimage (continuous_apply g)
    · intro x hx
      rw [Set.mem_univ_pi]
      exact hx
  have hval : ∀ v : G → ℝ, Continuous (fun x : G → ℝ => ∑ g, v g * x g) :=
    fun v => continuous_finsetSum _ (fun g _ => continuous_const.mul (continuous_apply g))
  have hwpos : ∀ p : priceSimplex G, 0 < ∑ g, (p : G → ℝ) g * ω g := by
    intro p
    have hex : ∃ g, 0 < (p : G → ℝ) g := by
      by_contra hn
      have hs : ∑ g, (p : G → ℝ) g ≤ 0 :=
        Finset.sum_nonpos fun g _ => not_lt.mp (not_exists.mp hn g)
      linarith [p.2.2]
    obtain ⟨g, hg⟩ := hex
    exact Finset.sum_pos' (fun k _ => mul_nonneg (p.2.1 k) (hω k).le)
      ⟨g, Finset.mem_univ g, mul_pos hg (hω g)⟩
  have hsub : ∀ p, budget M ω p ⊆ box M := fun _ _ hx => hx.1
  have hconvex : ∀ p, Convex ℝ (budget M ω p) := by
    intro p x hx y hy a b ha hb hab
    refine ⟨fun g => ?_, ?_⟩
    · have hxi := hx.1 g
      have hyi := hy.1 g
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      refine ⟨by nlinarith [mul_nonneg ha hxi.1, mul_nonneg hb hyi.1], ?_⟩
      have h1 := mul_le_mul_of_nonneg_left hxi.2 ha
      have h2 := mul_le_mul_of_nonneg_left hyi.2 hb
      nlinarith [show a * M + b * M = M by rw [← add_mul, hab, one_mul]]
    · have hr : ∑ g, (p : G → ℝ) g * (a • x + b • y) g =
          a * (∑ g, (p : G → ℝ) g * x g) + b * (∑ g, (p : G → ℝ) g * y g) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro g _
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
      rw [hr]
      have h1 := mul_le_mul_of_nonneg_left hx.2 ha
      have h2 := mul_le_mul_of_nonneg_left hy.2 hb
      nlinarith [show a * (∑ g, (p : G → ℝ) g * ω g) +
          b * (∑ g, (p : G → ℝ) g * ω g) = ∑ g, (p : G → ℝ) g * ω g by
        rw [← add_mul, hab, one_mul]]
  have hex : ∀ p : priceSimplex G, ∃ x, IsOptimal M ω U p x := by
    intro p
    have hc : IsCompact (budget M ω p) := by
      apply hbox.of_isClosed_subset _ (hsub p)
      have hb : IsClosed {x : G → ℝ | ∑ g, (p : G → ℝ) g * x g ≤
          ∑ g, (p : G → ℝ) g * ω g} := isClosed_le (hval _) continuous_const
      exact hbox.isClosed.inter hb
    have hn : (budget M ω p).Nonempty := by
      refine ⟨0, ⟨fun _ => ⟨le_rfl, hM⟩, ?_⟩⟩
      simpa using (hwpos p).le
    obtain ⟨x, hx, hmax⟩ := hc.exists_isMaxOn hn hUcont.continuousOn
    exact ⟨x, hx, fun y hy => hmax hy⟩
  choose d hd using hex
  have huniq : ∀ p x, IsOptimal M ω U p x → x = d p := by
    intro p x hx
    exact unique_max_of_strictConcaveOn
      (hUsc.subset (hsub p) (hconvex p)) hx.1 (hd p).1 hx.2 (hd p).2
  have hdcont : Continuous d := by
    refine continuous_of_unique_maximizer_subset (box M) hbox (budget M ω) hsub
      (fun _ x => U x) (hUcont.comp continuous_snd) d
      (fun p => (hd p).1) (fun p y hy => (hd p).2 y hy) ?_ ?_ ?_
    · intro p x hx hm
      exact huniq p x ⟨hx, hm⟩
    · have hb : IsClosed {px : priceSimplex G × (G → ℝ) |
          ∑ g, (px.1 : G → ℝ) g * px.2 g ≤ ∑ g, (px.1 : G → ℝ) g * ω g} := by
        apply isClosed_le
        · exact continuous_finsetSum _ (fun g _ =>
            (((continuous_apply g).comp (continuous_subtype_val.comp continuous_fst)).mul
              ((continuous_apply g).comp continuous_snd)))
        · exact continuous_finsetSum _ (fun g _ =>
            ((continuous_apply g).comp (continuous_subtype_val.comp continuous_fst)).mul
              continuous_const)
      exact (hbox.isClosed.preimage continuous_snd).inter hb
    · intro p pn hpn y hy
      exact budget_lower_hemicontinuous M ω (fun g => (hω g).le)
        p pn hpn (hwpos p) y hy.1 hy.2
  exact ⟨d, hdcont, hd, huniq⟩

theorem aggregate_budget_identity (p : priceSimplex G) (x ω : H → G → ℝ) :
    ∑ g, (p : G → ℝ) g * ((∑ i, x i g) - ∑ i, ω i g) =
      ∑ i, ((∑ g, (p : G → ℝ) g * x i g) - ∑ g, (p : G → ℝ) g * ω i g) := by
  have swap : ∀ f : H → G → ℝ,
      (∑ g, (p : G → ℝ) g * ∑ i, f i g) = ∑ i, ∑ g, (p : G → ℝ) g * f i g := by
    intro f
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, swap, swap, Finset.sum_sub_distrib]

theorem heterogeneous_free_disposal_exists [Nonempty G]
    (M : ℝ) (hM : 0 ≤ M) (ω : H → G → ℝ) (hω : ∀ i g, 0 < ω i g)
    (U : H → (G → ℝ) → ℝ) (hUc : ∀ i, Continuous (U i))
    (hUsc : ∀ i, StrictConcaveOn ℝ (box M) (U i)) :
    ∃ p : priceSimplex G, ∃ x : H → G → ℝ,
      (∀ i, IsOptimal M (ω i) (U i) p (x i)) ∧
      (∀ g, ∑ i, x i g ≤ ∑ i, ω i g) := by
  classical
  choose d hdc hdopt _hduniq using
    (fun i => exists_continuous_optimal_demand M hM (ω i) (hω i) (U i) (hUc i) (hUsc i))
  let z : priceSimplex G → G → ℝ :=
    fun p g => (∑ i, d i p g) - ∑ i, ω i g
  have hzc : Continuous z := by
    apply continuous_pi
    intro g
    exact (continuous_finsetSum _ (fun i _ => (continuous_apply g).comp (hdc i))).sub
      continuous_const
  have hzw : ∀ p : priceSimplex G, ∑ g, (p : G → ℝ) g * z p g ≤ 0 := by
    intro p
    rw [show (∑ g, (p : G → ℝ) g * z p g) =
        ∑ i, ((∑ g, (p : G → ℝ) g * d i p g) -
          ∑ g, (p : G → ℝ) g * ω i g) from aggregate_budget_identity p (fun i => d i p) ω]
    exact Finset.sum_nonpos fun i _ => sub_nonpos.mpr (hdopt i p).1.2
  obtain ⟨p, hp⟩ := gale_nikaido_debreu_weak z hzc hzw
  refine ⟨p, fun i => d i p, fun i => hdopt i p, fun g => ?_⟩
  exact sub_nonpos.mp (hp g)

def IncreasingOnBox (M : ℝ) (U : (G → ℝ) → ℝ) : Prop :=
  ∀ x ∈ box M, ∀ y ∈ box M, x ≤ y → x ≠ y → U x < U y

omit [Fintype G] in
theorem allocation_lt_cap (M : ℝ) (x ω : H → G → ℝ)
    (hx : ∀ i, x i ∈ box M)
    (hclear : ∀ g, ∑ i, x i g ≤ ∑ i, ω i g)
    (hcap : ∀ g, ∑ i, ω i g < M) : ∀ i g, x i g < M := by
  intro i g
  have hs : x i g ≤ ∑ k, x k g :=
    Finset.single_le_sum (fun k _ => ((hx k) g).1) (Finset.mem_univ i)
  exact lt_of_le_of_lt (hs.trans (hclear g)) (hcap g)

theorem cost_update [DecidableEq G] (p x : G → ℝ) (g : G) (v : ℝ) :
    ∑ k, p k * Function.update x g v k =
      (∑ k, p k * x k) + p g * (v - x g) := by
  classical
  calc
    ∑ k, p k * Function.update x g v k =
        ∑ k, (p k * x k + if k = g then p g * (v - x g) else 0) := by
      apply Finset.sum_congr rfl
      intro k _
      by_cases hk : k = g
      · subst k
        simp only [Function.update_self, ↓reduceIte]
        ring
      · simp [hk]
    _ = _ := by rw [Finset.sum_add_distrib]; simp

theorem optimal_prices_positive [Nonempty H]
    (M : ℝ) (ω x : H → G → ℝ) (U : H → (G → ℝ) → ℝ)
    (p : priceSimplex G)
    (hopt : ∀ i, IsOptimal M (ω i) (U i) p (x i))
    (hclear : ∀ g, ∑ i, x i g ≤ ∑ i, ω i g)
    (hcap : ∀ g, ∑ i, ω i g < M)
    (hmono : ∀ i, IncreasingOnBox M (U i)) : ∀ g, 0 < (p : G → ℝ) g := by
  classical
  intro g
  by_contra hn
  have hpg : (p : G → ℝ) g = 0 := le_antisymm (not_lt.mp hn) (p.2.1 g)
  let i : H := Classical.choice inferInstance
  have hxlt := allocation_lt_cap M x ω (fun k => (hopt k).1.1) hclear hcap i g
  let y := Function.update (x i) g M
  have hybox : y ∈ box M := by
    intro k
    by_cases hk : k = g
    · subst k
      simp only [y, Function.update_self]
      exact ⟨le_trans ((hopt i).1.1 g).1 hxlt.le, le_rfl⟩
    · simpa [y, hk] using (hopt i).1.1 k
  have hxy : x i ≤ y := by
    intro k
    by_cases hk : k = g
    · subst k
      simpa [y] using hxlt.le
    · simp [y, hk]
  have hne : x i ≠ y := by
    intro heq
    have he := congrFun heq g
    simp only [y, Function.update_self] at he
    linarith
  have hbud : y ∈ budget M (ω i) p := by
    refine ⟨hybox, ?_⟩
    dsimp [y]
    rw [cost_update, hpg, zero_mul, add_zero]
    exact (hopt i).1.2
  have hu := hmono i (x i) (hopt i).1.1 y hybox hxy hne
  have hm := (hopt i).2 y hbud
  linarith

theorem optimal_budget_exhausts [Nonempty G]
    (M : ℝ) (ω : G → ℝ) (U : (G → ℝ) → ℝ) (p : priceSimplex G)
    (x : G → ℝ) (hx : IsOptimal M ω U p x)
    (hxp : ∀ g, x g < M) (hp : ∀ g, 0 < (p : G → ℝ) g)
    (hmono : IncreasingOnBox M U) :
    ∑ g, (p : G → ℝ) g * x g = ∑ g, (p : G → ℝ) g * ω g := by
  classical
  by_contra hne
  have hlt := lt_of_le_of_ne hx.1.2 hne
  let g : G := Classical.choice inferInstance
  let C := ∑ k, (p : G → ℝ) k * x k
  let W := ∑ k, (p : G → ℝ) k * ω k
  have hgap : 0 < W - C := sub_pos.mpr hlt
  have hmin : 0 < min (M - x g) ((W - C) / (p : G → ℝ) g) :=
    lt_min (sub_pos.mpr (hxp g)) (div_pos hgap (hp g))
  let δ := min (M - x g) ((W - C) / (p : G → ℝ) g) / 2
  have hδ : 0 < δ := div_pos hmin (by norm_num)
  have hhalf : δ ≤ min (M - x g) ((W - C) / (p : G → ℝ) g) := by
    dsimp [δ]
    linarith
  have hδcap : δ ≤ M - x g := hhalf.trans (min_le_left _ _)
  have hδcost : δ * (p : G → ℝ) g ≤ W - C :=
    (le_div_iff₀ (hp g)).mp (hhalf.trans (min_le_right _ _))
  let y := Function.update x g (x g + δ)
  have hybox : y ∈ box M := by
    intro k
    by_cases hk : k = g
    · subst k
      simp only [y, Function.update_self]
      exact ⟨by linarith [(hx.1.1 g).1], by linarith⟩
    · simpa [y, hk] using hx.1.1 k
  have hxy : x ≤ y := by
    intro k
    by_cases hk : k = g
    · subst k
      simp only [y, Function.update_self]
      linarith
    · simp [y, hk]
  have hxyne : x ≠ y := by
    intro heq
    have he := congrFun heq g
    simp only [y, Function.update_self] at he
    linarith
  have hybud : y ∈ budget M ω p := by
    refine ⟨hybox, ?_⟩
    have heq : ∑ k, (p : G → ℝ) k * y k = C + (p : G → ℝ) g * δ := by
      dsimp [y]
      rw [cost_update]
      dsimp [C]
      ring
    rw [heq]
    change C + (p : G → ℝ) g * δ ≤ W
    nlinarith
  have hu := hmono x hx.1.1 y hybox hxy hxyne
  have hm := hx.2 y hybud
  linarith

theorem heterogeneous_exact_clearing_exists [Nonempty G] [Nonempty H]
    (M : ℝ) (hM : 0 ≤ M) (ω : H → G → ℝ) (hω : ∀ i g, 0 < ω i g)
    (U : H → (G → ℝ) → ℝ) (hUc : ∀ i, Continuous (U i))
    (hUsc : ∀ i, StrictConcaveOn ℝ (box M) (U i))
    (hcap : ∀ g, ∑ i, ω i g < M)
    (hmono : ∀ i, IncreasingOnBox M (U i)) :
    ∃ p : priceSimplex G, ∃ x : H → G → ℝ,
      (∀ g, 0 < (p : G → ℝ) g) ∧
      (∀ i, IsOptimal M (ω i) (U i) p (x i)) ∧
      (∀ g, ∑ i, x i g = ∑ i, ω i g) := by
  classical
  obtain ⟨p, x, hopt, hclear⟩ :=
    heterogeneous_free_disposal_exists M hM ω hω U hUc hUsc
  have hxp := allocation_lt_cap M x ω (fun i => (hopt i).1.1) hclear hcap
  have hp := optimal_prices_positive M ω x U p hopt hclear hcap hmono
  have hbud : ∀ i, ∑ g, (p : G → ℝ) g * x i g = ∑ g, (p : G → ℝ) g * ω i g :=
    fun i => optimal_budget_exhausts M (ω i) (U i) p (x i) (hopt i) (hxp i) hp (hmono i)
  have hval : ∑ g, (p : G → ℝ) g * ((∑ i, x i g) - ∑ i, ω i g) = 0 := by
    rw [aggregate_budget_identity]
    apply Finset.sum_eq_zero
    intro i _
    rw [hbud i]
    ring
  have hslack : ∑ g, (p : G → ℝ) g * ((∑ i, ω i g) - ∑ i, x i g) = 0 := by
    have heq : (∑ g, (p : G → ℝ) g * ((∑ i, ω i g) - ∑ i, x i g)) =
        -(∑ g, (p : G → ℝ) g * ((∑ i, x i g) - ∑ i, ω i g)) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro g _
      ring
    rw [heq, hval]
    ring
  refine ⟨p, x, hp, hopt, fun g => ?_⟩
  have hn : ∀ k, 0 ≤ (p : G → ℝ) k * ((∑ i, ω i k) - ∑ i, x i k) :=
    fun k => mul_nonneg (hp k).le (sub_nonneg.mpr (hclear k))
  have hle := Finset.single_le_sum (fun k _ => hn k) (Finset.mem_univ g)
  rw [hslack] at hle
  have hz : (p : G → ℝ) g * ((∑ i, ω i g) - ∑ i, x i g) = 0 :=
    le_antisymm hle (hn g)
  have hd := (mul_eq_zero.mp hz).resolve_left (ne_of_gt (hp g))
  linarith

variable {J : Type*} [Fintype J]

/-- The `none` coordinate is current consumption, not a risk-free future asset. -/
def IsNumeraireOptimal (M : ℝ) (ω : Option J → ℝ)
    (U : (Option J → ℝ) → ℝ) (q : J → ℝ) (x : Option J → ℝ) : Prop :=
  x ∈ box M ∧
  x none + ∑ j, q j * x (some j) ≤ ω none + ∑ j, q j * ω (some j) ∧
  ∀ y ∈ box M,
    y none + ∑ j, q j * y (some j) ≤ ω none + ∑ j, q j * ω (some j) → U y ≤ U x

theorem normalized_cost_mul (p x : Option J → ℝ) (hp : p none ≠ 0) :
    p none * (x none + ∑ j, (p (some j) / p none) * x (some j)) =
      ∑ g, p g * x g := by
  rw [Fintype.sum_option, mul_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  field_simp

theorem normalized_budget_iff (p x ω : Option J → ℝ) (hp : 0 < p none) :
    (x none + ∑ j, (p (some j) / p none) * x (some j) ≤
      ω none + ∑ j, (p (some j) / p none) * ω (some j)) ↔
      ∑ g, p g * x g ≤ ∑ g, p g * ω g := by
  constructor
  · intro h
    have hh := mul_le_mul_of_nonneg_left h hp.le
    rwa [normalized_cost_mul p x (ne_of_gt hp), normalized_cost_mul p ω (ne_of_gt hp)] at hh
  · intro h
    apply (mul_le_mul_iff_right₀ hp).mp
    rwa [normalized_cost_mul p x (ne_of_gt hp), normalized_cost_mul p ω (ne_of_gt hp)]

theorem heterogeneous_current_consumption_equilibrium [Nonempty H]
    (M : ℝ) (hM : 0 ≤ M) (ω : H → Option J → ℝ)
    (hω : ∀ i g, 0 < ω i g) (U : H → (Option J → ℝ) → ℝ)
    (hUc : ∀ i, Continuous (U i))
    (hUsc : ∀ i, StrictConcaveOn ℝ (box M) (U i))
    (hcap : ∀ g, ∑ i, ω i g < M)
    (hmono : ∀ i, IncreasingOnBox M (U i)) :
    ∃ q : J → ℝ, ∃ x : H → Option J → ℝ,
      (∀ j, 0 < q j) ∧
      (∀ i, IsNumeraireOptimal M (ω i) (U i) q (x i)) ∧
      (∑ i, x i none = ∑ i, ω i none) ∧
      (∀ j, ∑ i, x i (some j) = ∑ i, ω i (some j)) := by
  classical
  obtain ⟨p, x, hp, hopt, hclear⟩ :=
    heterogeneous_exact_clearing_exists M hM ω hω U hUc hUsc hcap hmono
  let q : J → ℝ := fun j => (p : Option J → ℝ) (some j) / (p : Option J → ℝ) none
  refine ⟨q, x, fun j => div_pos (hp (some j)) (hp none), ?_, hclear none,
    fun j => hclear (some j)⟩
  intro i
  refine ⟨(hopt i).1.1, ?_, ?_⟩
  · exact (normalized_budget_iff (p : Option J → ℝ) (x i) (ω i) (hp none)).mpr
      (hopt i).1.2
  · intro y hy hybud
    exact (hopt i).2 y ⟨hy,
      (normalized_budget_iff (p : Option J → ℝ) y (ω i) (hp none)).mp hybud⟩

end OwnershipBridge

#print axioms OwnershipBridge.exists_continuous_optimal_demand
#print axioms OwnershipBridge.aggregate_budget_identity
#print axioms OwnershipBridge.heterogeneous_free_disposal_exists
#print axioms OwnershipBridge.allocation_lt_cap
#print axioms OwnershipBridge.cost_update
#print axioms OwnershipBridge.optimal_prices_positive
#print axioms OwnershipBridge.optimal_budget_exhausts
#print axioms OwnershipBridge.heterogeneous_exact_clearing_exists
#print axioms OwnershipBridge.normalized_cost_mul
#print axioms OwnershipBridge.normalized_budget_iff
#print axioms OwnershipBridge.heterogeneous_current_consumption_equilibrium
