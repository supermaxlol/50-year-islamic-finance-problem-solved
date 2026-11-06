import GEOverlap

/-!
Stage 247 (draft): Nash bargaining solution (② application).

A strictly-concave continuous objective over a compact convex nonempty bargaining set has a
UNIQUE maximizer (existence by Weierstrass, uniqueness by `unique_max_of_strictConcaveOn`).
With the objective the (log) Nash product, this is the Nash bargaining solution: a unique,
well-defined cooperative outcome.
-/

noncomputable section
open GEOverlap

namespace NashBargaining

/-- **Nash bargaining solution (existence + uniqueness).** A strictly-concave continuous
objective on a compact convex nonempty set has a unique maximizer. -/
theorem nash_bargaining_solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Set E) (hKcmp : IsCompact K) (hKne : K.Nonempty)
    (f : E → ℝ) (hfcont : ContinuousOn f K) (hfsc : StrictConcaveOn ℝ K f) :
    ∃! x : E, x ∈ K ∧ ∀ y ∈ K, f y ≤ f x := by
  obtain ⟨x, hxK, hxmax⟩ := hKcmp.exists_isMaxOn hKne hfcont
  refine ⟨x, ⟨hxK, fun y hy => hxmax hy⟩, ?_⟩
  rintro x' ⟨hx'K, hx'max⟩
  exact unique_max_of_strictConcaveOn hfsc hx'K hxK hx'max (fun y hy => hxmax hy)

end NashBargaining

#print axioms NashBargaining.nash_bargaining_solution
