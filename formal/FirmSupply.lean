import GEOverlap

/-!
Stage 248 (draft): continuous profit-maximizing firm supply over a production set
(② application — finishes the endogenous-`η` capstone properly).

A firm maximizing profit `p·y − Cost y` (strictly concave in `y`, e.g. strictly convex cost)
over a compact production set `Y` has a CONTINUOUS, price-responsive supply `η(p)` — the
missing continuity that lets a genuine production set (not just a one-parameter scale) feed
the equilibrium engine. Direct application of the general Berge argmax engine (`berge_argmax`,
stage 243 — re-proved locally here to keep the file self-contained) with the fixed
(constant-in-`p`) constraint `Y`.
-/

noncomputable section
open scoped BigOperators
open GEOverlap

namespace FirmSupply

/-- Stage-243 `berge_argmax`, local copy. -/
theorem berge_argmax {P K : Type*}
    [TopologicalSpace P] [SequentialSpace P]
    [TopologicalSpace K] [T2Space K] [FirstCountableTopology K]
    [AddCommGroup K] [Module ℝ K]
    (C : Set K) (hC : IsCompact C)
    (D : P → Set K) (hDC : ∀ p, D p ⊆ C) (hDne : ∀ p, (D p).Nonempty)
    (hDclosed : IsClosed {pk : P × K | pk.2 ∈ D pk.1})
    (f : P → K → ℝ) (hf : Continuous (fun pk : P × K => f pk.1 pk.2))
    (hfsc : ∀ p, StrictConcaveOn ℝ (D p) (f p))
    (hlhc : ∀ (p : P) (pn : ℕ → P), Filter.Tendsto pn Filter.atTop (nhds p) →
        ∀ y ∈ D p, ∃ yn : ℕ → K,
          (∀ n, yn n ∈ D (pn n)) ∧ Filter.Tendsto yn Filter.atTop (nhds y)) :
    ∃ g : P → K, Continuous g ∧ (∀ p, g p ∈ D p) ∧
      (∀ p, ∀ y ∈ D p, f p y ≤ f p (g p)) := by
  classical
  have hDcl : ∀ p, IsClosed (D p) := by
    intro p
    have hpre : D p = (fun y => (p, y)) ⁻¹' {pk : P × K | pk.2 ∈ D pk.1} := by
      ext y; simp
    rw [hpre]; exact hDclosed.preimage (continuous_const.prodMk continuous_id)
  have hDcmp : ∀ p, IsCompact (D p) := fun p => hC.of_isClosed_subset (hDcl p) (hDC p)
  have hmax_ex : ∀ p, ∃ x ∈ D p, ∀ y ∈ D p, f p y ≤ f p x := by
    intro p
    have hcont : ContinuousOn (f p) (D p) :=
      (hf.comp (continuous_const.prodMk continuous_id)).continuousOn
    obtain ⟨x, hx, hxmax⟩ := (hDcmp p).exists_isMaxOn (hDne p) hcont
    exact ⟨x, hx, fun y hy => hxmax hy⟩
  choose g hg_mem hg_max using hmax_ex
  have huniq : ∀ p x, x ∈ D p → (∀ y ∈ D p, f p y ≤ f p x) → x = g p := by
    intro p x hx hxmax
    exact unique_max_of_strictConcaveOn (hfsc p) hx (hg_mem p) hxmax (hg_max p)
  refine ⟨g, ?_, hg_mem, hg_max⟩
  exact continuous_of_unique_maximizer_subset C hC D hDC f hf g hg_mem hg_max huniq hDclosed hlhc

/-- **Continuous firm supply.** With a compact production set `Y` and a profit criterion
`p·y − Cost y` strictly concave in `y`, the profit-maximizing net supply `η` is continuous in
the price, lies in `Y`, and maximizes profit at every price. -/
theorem firm_supply_continuous {S : Type*} [Fintype S] [Nonempty S]
    (Y : Set (S → ℝ)) (hYcmp : IsCompact Y) (hYcl : IsClosed Y) (hYne : Y.Nonempty)
    (Cost : (S → ℝ) → ℝ) (hCostcont : Continuous Cost)
    (hprofit_sc : ∀ p : priceSimplex S,
        StrictConcaveOn ℝ Y (fun y => (∑ s, (p : S → ℝ) s * y s) - Cost y)) :
    ∃ η : priceSimplex S → (S → ℝ), Continuous η ∧ (∀ p, η p ∈ Y) ∧
      (∀ (p : priceSimplex S), ∀ y ∈ Y, (∑ s, (p : S → ℝ) s * y s) - Cost y
        ≤ (∑ s, (p : S → ℝ) s * η p s) - Cost (η p)) := by
  have hf : Continuous (fun pk : priceSimplex S × (S → ℝ) =>
      (∑ s, (pk.1 : S → ℝ) s * pk.2 s) - Cost pk.2) := by
    refine Continuous.sub ?_ (hCostcont.comp continuous_snd)
    exact continuous_finsetSum _ (fun s _ =>
      ((continuous_apply s).comp (continuous_subtype_val.comp continuous_fst)).mul
        ((continuous_apply s).comp continuous_snd))
  have hDclosed : IsClosed {pk : priceSimplex S × (S → ℝ) | pk.2 ∈ Y} :=
    hYcl.preimage continuous_snd
  have hlhc : ∀ (p : priceSimplex S) (pn : ℕ → priceSimplex S),
      Filter.Tendsto pn Filter.atTop (nhds p) → ∀ y ∈ Y, ∃ yn : ℕ → (S → ℝ),
        (∀ n, yn n ∈ Y) ∧ Filter.Tendsto yn Filter.atTop (nhds y) :=
    fun p pn _ y hy => ⟨fun _ => y, fun _ => hy, tendsto_const_nhds⟩
  exact berge_argmax Y hYcmp (fun _ => Y) (fun _ => subset_rfl) (fun _ => hYne)
    hDclosed (fun p y => (∑ s, (p : S → ℝ) s * y s) - Cost y) hf hprofit_sc hlhc

end FirmSupply

#print axioms FirmSupply.firm_supply_continuous
