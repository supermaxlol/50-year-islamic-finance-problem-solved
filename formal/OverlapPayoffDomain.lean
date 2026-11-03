import OverlapResourceGlobal
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Payoff perturbations preserve rank locally. Nonnegativity is retained as
an honest cone condition when reference entries may be zero. -/

noncomputable section
open scoped BigOperators Topology
open Filter OwnershipCRRA OwnershipMarginal OwnershipUnfloored OwnershipPositive
open OverlapLocal

namespace OverlapPayoff
variable {H J S : Type*} [Fintype H] [Fintype J] [Fintype S]

abbrev PayoffShock (H J S : Type*) := OverlapResource.ResourceShock H S × (H → S → J → ℝ)

def changedEndowment (e : H → ℝ) (v : PayoffShock H J S) : H → ℝ :=
  OverlapResource.changedEndowment e v.1

def changedPayoff (D : H → Data J S) (v : PayoffShock H J S) (i : H) (s : S) (j : J) : ℝ :=
  (D i).payoff s j+v.2 i s j

def Nonnegative (D : H → Data J S) (v : PayoffShock H J S) : Prop :=
  ∀ i s j, 0 ≤ changedPayoff D v i s j

def Admissible (D : H → Data J S) (e : H → ℝ) (v : PayoffShock H J S) : Prop :=
  OverlapResource.Admissible D e v.1 ∧ Nonnegative D v ∧
    ∀ i, Function.Injective (fun a : J → ℝ => fun s => ∑ j, changedPayoff D v i s j*a j)

def changedData (D : H → Data J S) (e : H → ℝ) (v : PayoffShock H J S)
    (h : Admissible D e v) (i : H) : Data J S :=
  { D i with
    income := fun s => (D i).income s+v.1.2.1 i s
    weight := fun s => (D i).weight s+v.1.2.2 i s
    payoff := changedPayoff D v i
    income_pos := h.1.2.1 i
    weight_pos := h.1.2.2 i
    payoff_nonneg := h.2.1 i
    payoff_injective := h.2.2 i }

def futureReceipt (D : H → Data J S) (v : PayoffShock H J S)
    (i : H) (a : J → ℝ) (s : S) : ℝ :=
  (D i).income s+v.1.2.1 i s+∑ j, changedPayoff D v i s j*a j

omit [Fintype H] [Fintype S] in
theorem linearIndependent_columns_iff (P : S → J → ℝ) :
    LinearIndependent ℝ (fun j s => P s j) ↔
      Function.Injective (fun a : J → ℝ => fun s => ∑ j, P s j*a j) := by
  classical
  constructor
  · intro h a b hab
    have hh : (∑ j, (a j-b j) • (fun s => P s j))=(0 : S → ℝ) := by
      funext s
      simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply]
      simp_rw [sub_mul]
      rw [Finset.sum_sub_distrib]
      apply sub_eq_zero.mpr
      simpa only [mul_comm] using congrFun hab s
    have hz := Fintype.linearIndependent_iff.mp h (fun j => a j-b j) hh
    funext j
    exact sub_eq_zero.mp (hz j)
  · intro h
    apply Fintype.linearIndependent_iff.mpr
    intro g hg j
    have heq : (fun s => ∑ j, P s j*g j)=(fun s => ∑ j, P s j*(0 : J → ℝ) j) := by
      funext s
      simpa [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,mul_comm] using congrFun hg s
    have hh := congrFun (h heq) j
    exact hh

theorem rank_near_zero (D : H → Data J S) :
    ∀ᶠ v : PayoffShock H J S in 𝓝 0,
      ∀ i, Function.Injective (fun a : J → ℝ => fun s => ∑ j, changedPayoff D v i s j*a j) := by
  classical
  apply Filter.eventually_all.mpr
  intro i
  have hbase : LinearIndependent ℝ (fun j s => (D i).payoff s j) :=
    (linearIndependent_columns_iff _).mpr (D i).payoff_injective
  have hc : Continuous (fun v : PayoffShock H J S => fun j s => changedPayoff D v i s j) := by
    unfold changedPayoff
    fun_prop
  have hl : Tendsto (fun v : PayoffShock H J S => fun j s => changedPayoff D v i s j)
      (𝓝 0) (𝓝 (fun j s => (D i).payoff s j)) := by
    simpa [changedPayoff] using hc.tendsto 0
  filter_upwards [hl.eventually hbase.eventually] with v hv
  exact (linearIndependent_columns_iff _).mp hv

theorem admissible_near_zero (D : H → Data J S) (e : H → ℝ) (he : ∀ i, 0 < e i) :
    ∀ᶠ v : PayoffShock H J S in 𝓝 0, Nonnegative D v → Admissible D e v := by
  have hr : ∀ᶠ v : PayoffShock H J S in 𝓝 0, OverlapResource.Admissible D e v.1 :=
    (continuous_fst.tendsto (0 : PayoffShock H J S)).eventually
      (OverlapResource.admissible_near_zero D e he)
  filter_upwards [hr,rank_near_zero D] with v hrv hkv
  intro hp
  exact ⟨hrv,hp,hkv⟩

theorem positive_payoffs_near_zero (D : H → Data J S)
    (hP : ∀ i s j, 0 < (D i).payoff s j) :
    ∀ᶠ v : PayoffShock H J S in 𝓝 0, Nonnegative D v := by
  apply Filter.eventually_all.mpr
  intro i
  apply Filter.eventually_all.mpr
  intro s
  apply Filter.eventually_all.mpr
  intro j
  have hc : Continuous (fun v : PayoffShock H J S => changedPayoff D v i s j) := by
    unfold changedPayoff
    fun_prop
  have hh : ∀ᶠ v : PayoffShock H J S in 𝓝 0, 0 < changedPayoff D v i s j :=
    hc.continuousAt.eventually (Ioi_mem_nhds (by simpa [changedPayoff] using hP i s j))
  exact hh.mono (fun _ hv => hv.le)

end OverlapPayoff

#print axioms OverlapPayoff.linearIndependent_columns_iff
#print axioms OverlapPayoff.rank_near_zero
#print axioms OverlapPayoff.admissible_near_zero
#print axioms OverlapPayoff.positive_payoffs_near_zero
