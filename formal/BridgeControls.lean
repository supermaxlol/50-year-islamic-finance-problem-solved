import HeterogeneousOverlapBridge

noncomputable section
open scoped BigOperators
open Set GEOverlap OwnershipBridge

namespace BridgeControls

variable {G : Type*} [Fintype G]

omit [Fintype G] in
theorem box_convex (M : ℝ) : Convex ℝ (OwnershipBridge.box M : Set (G → ℝ)) := by
  intro x hx y hy a b ha hb hab g
  have hxi := hx g
  have hyi := hy g
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  refine ⟨by nlinarith [mul_nonneg ha hxi.1, mul_nonneg hb hyi.1], ?_⟩
  have h1 := mul_le_mul_of_nonneg_left hxi.2 ha
  have h2 := mul_le_mul_of_nonneg_left hyi.2 hb
  nlinarith [show a * M + b * M = M by rw [← add_mul, hab, one_mul]]

theorem quadratic_increasing (M L : ℝ) (hML : M < L) :
    IncreasingOnBox M (fun x : G → ℝ => -∑ g, (x g - L)^2) := by
  classical
  intro x hx y hy hxy hne
  have hpoint : ∀ g, (y g - L)^2 ≤ (x g - L)^2 := by
    intro g
    have h1 := hxy g
    have h2 := (hy g).2
    have h3 := (hx g).2
    nlinarith [mul_nonneg (sub_nonneg.mpr h1)
      (show 0 ≤ 2*L - x g - y g by linarith)]
  obtain ⟨g, hg⟩ := Function.ne_iff.mp hne
  have hstrict : (y g - L)^2 < (x g - L)^2 := by
    have h1 : x g < y g := lt_of_le_of_ne (hxy g) hg
    have h2 := (hx g).2
    have h3 := (hy g).2
    nlinarith [mul_pos (sub_pos.mpr h1)
      (show 0 < 2*L - x g - y g by linarith)]
  have hs : (∑ k, (y k - L)^2) < ∑ k, (x k - L)^2 :=
    Finset.sum_lt_sum (fun k _ => hpoint k) ⟨g, Finset.mem_univ g, hstrict⟩
  linarith

/-- Genuine optimizing heterogeneous households; no demand functions are supplied. -/
theorem two_household_probe :
    ∃ p : priceSimplex (Fin 2), ∃ x : Fin 2 → Fin 2 → ℝ,
      (∀ g, 0 < (p : Fin 2 → ℝ) g) ∧
      (∀ i, IsOptimal 2 (fun _ => 1/4)
        (fun z => -∑ g, (z g - (3 + (i.val : ℝ)))^2) p (x i)) ∧
      (∀ g, ∑ i, x i g = (1/2 : ℝ)) := by
  have hc : ∀ i : Fin 2, Continuous (fun z : Fin 2 → ℝ =>
      -∑ g, (z g - (3 + (i.val : ℝ)))^2) := by
    intro i
    exact (continuous_finsetSum _ (fun g _ =>
      ((continuous_apply g).sub continuous_const).pow 2)).neg
  have hsc : ∀ i : Fin 2, StrictConcaveOn ℝ (OwnershipBridge.box 2)
      (fun z : Fin 2 → ℝ => -∑ g, (z g - (3 + (i.val : ℝ)))^2) := by
    intro i
    exact (strictConcaveOn_blissQuadratic (3 + (i.val : ℝ))).subset
      (Set.subset_univ _) (box_convex 2)
  have hm : ∀ i : Fin 2, IncreasingOnBox 2
      (fun z : Fin 2 → ℝ => -∑ g, (z g - (3 + (i.val : ℝ)))^2) := by
    intro i
    exact quadratic_increasing 2 (3 + (i.val : ℝ))
      (by have hi : 0 ≤ (i.val : ℝ) := Nat.cast_nonneg _; linarith)
  obtain ⟨p, x, hp, hopt, hclear⟩ := heterogeneous_exact_clearing_exists
    2 (by norm_num) (fun _ : Fin 2 => fun _ : Fin 2 => (1/4 : ℝ))
    (by intros; norm_num)
    (fun i : Fin 2 => fun z : Fin 2 → ℝ => -∑ g, (z g - (3 + (i.val : ℝ)))^2)
    hc hsc (by intro g; norm_num [Fin.sum_univ_two]) hm
  refine ⟨p, x, hp, hopt, fun g => ?_⟩
  calc
    (∑ i, x i g) = ∑ _ : Fin 2, (1/4 : ℝ) := hclear g
    _ = (1/2 : ℝ) := by norm_num [Fin.sum_univ_two]

theorem constant_not_increasing :
    ¬ IncreasingOnBox 1 (fun _ : Fin 1 → ℝ => (0 : ℝ)) := by
  intro h
  have hs := h (fun _ => 0) (by intro g; norm_num)
    (fun _ => 1) (by intro g; norm_num) (by intro g; norm_num)
    (by intro heq; have h0 := congrFun heq 0; norm_num at h0)
  norm_num at hs

/-- Both assets pay in all three states; this is not an exclusive-block matrix. -/
def riskyPayoff : Fin 3 → Fin 2 → ℝ := ![![2,1], ![1,2], ![1,1]]

theorem risky_full_column_rank (x y : Fin 2 → ℝ)
    (h : ∀ s, ∑ j, riskyPayoff s j * x j = ∑ j, riskyPayoff s j * y j) : x = y := by
  have h0 := h 0
  have h1 := h 1
  norm_num [riskyPayoff, Fin.sum_univ_two] at h0 h1
  have hx0 : x 0 = y 0 := by linarith
  have hx1 : x 1 = y 1 := by linarith
  funext j
  fin_cases j
  · exact hx0
  · exact hx1

theorem risky_no_nonzero_certain_receipt (x : Fin 2 → ℝ) (k : ℝ)
    (h : ∀ s, ∑ j, riskyPayoff s j * x j = k) : x = 0 ∧ k = 0 := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  norm_num [riskyPayoff, Fin.sum_univ_two] at h0 h1 h2
  have hx0 : x 0 = 0 := by linarith
  have hx1 : x 1 = 0 := by linarith
  refine ⟨?_, by linarith⟩
  funext j
  fin_cases j <;> simp_all

end BridgeControls

#print axioms BridgeControls.box_convex
#print axioms BridgeControls.quadratic_increasing
#print axioms BridgeControls.two_household_probe
#print axioms BridgeControls.constant_not_increasing
#print axioms BridgeControls.risky_full_column_rank
#print axioms BridgeControls.risky_no_nonzero_certain_receipt
