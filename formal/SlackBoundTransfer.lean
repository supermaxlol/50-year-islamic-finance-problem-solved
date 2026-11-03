import HeterogeneousOverlapBridge

/-!
Generic optimizer lifting when every artificial upper cap and the current
consumption floor are strictly slack. This proves a step of bound removal,
not the economic argument that the floor is indeed slack at equilibrium.
-/

noncomputable section
open scoped BigOperators
open Set OwnershipBridge

namespace OwnershipBounds

variable {J : Type*} [Fintype J]

theorem short_segment_in_box (M : ℝ) (x z : Option J → ℝ)
    (hx : x ∈ box M) (hcurrent : 0 < x none) (hcap : ∀ g, x g < M)
    (hz : ∀ j, 0 ≤ z (some j)) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ (1-t) • x + t • z ∈ box M := by
  let O : Set (Option J → ℝ) := {v | (∀ g, v g < M) ∧ 0 < v none}
  have hO : IsOpen O := by
    have heq : O = (⋂ g, {v : Option J → ℝ | v g < M}) ∩ {v | 0 < v none} := by
      ext v
      simp [O]
    rw [heq]
    exact (isOpen_iInter_of_finite fun g =>
      isOpen_lt (continuous_apply g) continuous_const).inter
      (isOpen_lt continuous_const (continuous_apply none))
  let f : ℝ → Option J → ℝ := fun t => (1-t) • x + t • z
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hf0 : f 0 ∈ O := by simpa [f, O] using And.intro hcap hcurrent
  obtain ⟨eps, heps, hball⟩ := Metric.isOpen_iff.mp (hO.preimage hf) 0 hf0
  let t := min eps 1 / 2
  have hm : 0 < min eps 1 := lt_min heps (by norm_num)
  have ht : 0 < t := div_pos hm (by norm_num)
  have ht1 : t < 1 := by
    have hle := min_le_right eps (1 : ℝ)
    dsimp [t]
    linarith
  have hteps : t < eps := by
    have hle := min_le_left eps (1 : ℝ)
    dsimp [t]
    linarith
  have hin : t ∈ Metric.ball 0 eps := by
    rw [Metric.mem_ball, Real.dist_eq]
    simpa only [sub_zero, abs_of_pos ht] using hteps
  have hcond : f t ∈ O := hball hin
  refine ⟨t, ht, ht1, fun g => ⟨?_, (hcond.1 g).le⟩⟩
  cases g with
  | none => exact hcond.2.le
  | some j =>
    change 0 ≤ (1-t) * x (some j) + t * z (some j)
    exact add_nonneg (mul_nonneg (by linarith) ((hx (some j)).1))
      (mul_nonneg ht.le (hz j))

def cost (q : J → ℝ) (x : Option J → ℝ) : ℝ :=
  x none + ∑ j, q j * x (some j)

theorem cost_combo (q : J → ℝ) (x z : Option J → ℝ) (a b : ℝ) :
    cost q (a • x + b • z) = a * cost q x + b * cost q z := by
  have hs : (∑ j, q j * (a • x + b • z) (some j)) =
      a * (∑ j, q j * x (some j)) + b * (∑ j, q j * z (some j)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  simp only [cost, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hs ⊢
  rw [hs]
  ring

/-- Concavity and slack artificial bounds transfer a true bounded optimum to
every affordable choice in the larger economic domain, including arbitrarily
large portfolios. The domain must retain nonnegative asset holdings, but its
current coordinate may lie below the old floor. -/
theorem slack_optimum_transfers (M : ℝ) (ω : Option J → ℝ)
    (U : (Option J → ℝ) → ℝ) (q : J → ℝ) (x : Option J → ℝ)
    (domain : Set (Option J → ℝ))
    (hopt : IsNumeraireOptimal M ω U q x)
    (hcurrent : 0 < x none) (hcap : ∀ g, x g < M)
    (hU : ConcaveOn ℝ domain U) (hxD : x ∈ domain)
    (hassets : ∀ z ∈ domain, ∀ j, 0 ≤ z (some j)) :
    ∀ z ∈ domain, cost q z ≤ cost q ω → U z ≤ U x := by
  intro z hzD hzbud
  by_contra hn
  have hbetter : U x < U z := lt_of_not_ge hn
  obtain ⟨t, ht, ht1, hbox⟩ := short_segment_in_box M x z
    hopt.1 hcurrent hcap (hassets z hzD)
  have hb : cost q ((1-t) • x + t • z) ≤ cost q ω := by
    rw [cost_combo]
    have h1 := mul_le_mul_of_nonneg_left hopt.2.1 (show 0 ≤ 1-t by linarith)
    have h2 := mul_le_mul_of_nonneg_left hzbud ht.le
    change (1-t) * cost q x ≤ (1-t) * cost q ω at h1
    nlinarith
  have hm := hopt.2.2 ((1-t) • x + t • z) hbox hb
  have hc := hU.2 hxD hzD (show 0 ≤ 1-t by linarith)
    (show 0 ≤ t from ht.le) (show (1-t)+t = 1 by ring)
  simp only [smul_eq_mul] at hc
  nlinarith [mul_pos ht (sub_pos.mpr hbetter)]

end OwnershipBounds

#print axioms OwnershipBounds.short_segment_in_box
#print axioms OwnershipBounds.cost_combo
#print axioms OwnershipBounds.slack_optimum_transfers
