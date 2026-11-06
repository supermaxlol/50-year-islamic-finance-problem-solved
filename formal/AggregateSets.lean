import Mathlib

/-!
Stage 240 (draft): aggregate-set lemmas for the SWT econ-wrapper and Mantel aggregation.

Two high-reuse facts about the finite Minkowski sum `∑ i, A i` of a family of sets in the
good space `S → ℝ`:
* `convex_finsetSum` — a finite sum of convex sets is convex;
* `isOpen_finsetSum_of_open` — if ANY one summand is open, the whole finite sum is open.

These turn the per-household strictly-preferred sets `P_h` into a convex, open AGGREGATE
better set `B = ∑_h P_h`, discharging the hypotheses of the stage-237 separating-hyperplane
core and the Mantel aggregation.
-/

noncomputable section
open scoped BigOperators Pointwise

namespace AggregateSets

variable {ι S : Type*} [Fintype ι] [Fintype S]

/-- A finite Minkowski sum of convex sets in `S → ℝ` is convex. -/
theorem convex_finsetSum (A : ι → Set (S → ℝ)) (hA : ∀ i, Convex ℝ (A i)) :
    Convex ℝ (∑ i, A i) := by
  classical
  refine Finset.sum_induction A (Convex ℝ) (fun a b ha hb => ha.add hb) ?_ (fun i _ => hA i)
  exact convex_singleton 0

/-- If one summand of a finite Minkowski sum in `S → ℝ` is open, the whole sum is open. -/
theorem isOpen_finsetSum_of_open (A : ι → Set (S → ℝ)) (i₀ : ι) (hi₀ : IsOpen (A i₀)) :
    IsOpen (∑ i, A i) := by
  classical
  rw [← Finset.add_sum_erase Finset.univ A (Finset.mem_univ i₀)]
  exact hi₀.add_right

end AggregateSets

#print axioms AggregateSets.convex_finsetSum
#print axioms AggregateSets.isOpen_finsetSum_of_open
