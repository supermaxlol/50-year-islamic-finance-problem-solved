import GEOverlap

/-!
Stage 243 (draft): general Berge maximum theorem — argmax existence over an abstract
continuous compact-valued constraint correspondence (upstream ②).

`berge_argmax` upgrades `continuous_of_unique_maximizer_subset` (which takes the maximizer
`g` as given) into an EXISTENCE engine: supply a constraint correspondence `D` (values in a
fixed compact `C`, nonempty, closed graph, lower hemicontinuous) and a jointly continuous,
per-slice strictly-concave objective `f`, and obtain a CONTINUOUS demand selection `g` that
maximizes `f p` over `D p`. This is the single engine behind production-set firms, GEI
portfolio choice, bargaining, and expenditure minimization — "maximize a continuous
objective over a continuously-moving constraint."
-/

noncomputable section
open scoped BigOperators
open GEOverlap

namespace BergeArgmax

/-- **General Berge (argmax existence).** A constraint correspondence `D` with values in a
fixed compact set `C`, nonempty and closed-graph and lower-hemicontinuous, together with a
jointly continuous objective `f` that is strictly concave on each `D p`, admits a continuous
maximizing selection. -/
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
  -- each slice D p is closed, hence compact (closed subset of the compact C)
  have hDcl : ∀ p, IsClosed (D p) := by
    intro p
    have hpre : D p = (fun y => (p, y)) ⁻¹' {pk : P × K | pk.2 ∈ D pk.1} := by
      ext y; simp
    rw [hpre]; exact hDclosed.preimage (continuous_const.prodMk continuous_id)
  have hDcmp : ∀ p, IsCompact (D p) := fun p => hC.of_isClosed_subset (hDcl p) (hDC p)
  -- maximizer per parameter
  have hmax_ex : ∀ p, ∃ x ∈ D p, ∀ y ∈ D p, f p y ≤ f p x := by
    intro p
    have hcont : ContinuousOn (f p) (D p) :=
      (hf.comp (continuous_const.prodMk continuous_id)).continuousOn
    obtain ⟨x, hx, hxmax⟩ := (hDcmp p).exists_isMaxOn (hDne p) hcont
    exact ⟨x, hx, fun y hy => hxmax hy⟩
  choose g hg_mem hg_max using hmax_ex
  -- strict concavity makes the maximizer unique
  have huniq : ∀ p x, x ∈ D p → (∀ y ∈ D p, f p y ≤ f p x) → x = g p := by
    intro p x hx hxmax
    exact unique_max_of_strictConcaveOn (hfsc p) hx (hg_mem p) hxmax (hg_max p)
  refine ⟨g, ?_, hg_mem, hg_max⟩
  exact continuous_of_unique_maximizer_subset C hC D hDC f hf g hg_mem hg_max huniq hDclosed hlhc

end BergeArgmax

#print axioms BergeArgmax.berge_argmax
