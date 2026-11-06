import Mathlib

/-!
Stage 249 (draft): expenditure minimization (② application).

The dual consumer problem: minimize cost `p·x` over bundles in the box `[0,M]^S` meeting a
utility floor `U x ≥ u`. The feasible set is compact (closed utility-floor ∩ compact box), so
Weierstrass gives an expenditure-minimizing bundle. The Hicksian demand's existence.
-/

noncomputable section
open scoped BigOperators

namespace ExpenditureMin

/-- **Expenditure minimization.** Over the box `[0,M]^S` with a utility floor `u`, if some
bundle meets the floor, there is a cost-minimizing bundle meeting it. -/
theorem expenditure_min_exists {S : Type*} [Fintype S]
    (M : ℝ) (p : S → ℝ) (U : (S → ℝ) → ℝ) (hUcont : Continuous U) (u : ℝ)
    (x0 : S → ℝ) (hx0box : ∀ s, x0 s ∈ Set.Icc (0 : ℝ) M) (hx0u : u ≤ U x0) :
    ∃ x : S → ℝ, (∀ s, x s ∈ Set.Icc (0 : ℝ) M) ∧ u ≤ U x ∧
      ∀ y : S → ℝ, (∀ s, y s ∈ Set.Icc (0 : ℝ) M) → u ≤ U y →
        ∑ s, p s * x s ≤ ∑ s, p s * y s := by
  classical
  set F : Set (S → ℝ) := {x | (∀ s, x s ∈ Set.Icc (0 : ℝ) M) ∧ u ≤ U x} with hF
  have hbox : IsCompact {x : S → ℝ | ∀ s, x s ∈ Set.Icc (0 : ℝ) M} := by
    have heq : {x : S → ℝ | ∀ s, x s ∈ Set.Icc (0 : ℝ) M}
        = Set.univ.pi (fun _ : S => Set.Icc (0 : ℝ) M) := by
      ext x; simp only [Set.mem_ofPred_eq, Set.mem_univ_pi]
    rw [heq]; exact isCompact_univ_pi (fun _ => isCompact_Icc)
  have hUcl : IsClosed {x : S → ℝ | u ≤ U x} := isClosed_le continuous_const hUcont
  have hFcmp : IsCompact F := by
    have hFeq : F = {x | ∀ s, x s ∈ Set.Icc (0 : ℝ) M} ∩ {x | u ≤ U x} := by
      ext x; simp only [hF, Set.mem_inter_iff, Set.mem_ofPred_eq]
    rw [hFeq]; exact hbox.inter_right hUcl
  have hFne : F.Nonempty := ⟨x0, hx0box, hx0u⟩
  have hcont : ContinuousOn (fun x : S → ℝ => ∑ s, p s * x s) F :=
    (continuous_finsetSum _ (fun s _ => continuous_const.mul (continuous_apply s))).continuousOn
  obtain ⟨x, hxF, hxmin⟩ := hFcmp.exists_isMinOn hFne hcont
  exact ⟨x, hxF.1, hxF.2, fun y hyb hyu => hxmin (show y ∈ F from ⟨hyb, hyu⟩)⟩

end ExpenditureMin

#print axioms ExpenditureMin.expenditure_min_exists
