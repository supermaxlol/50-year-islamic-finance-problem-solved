import NonlinearPhysicalBoundary

/-!
Fully backed proportional ownership certificates: an actual-objective coordinate
equivalence, not a legal/Sharia certification or an endogenous production model.
Fixed positive denomination factors and divisible holdings are assumed. No loan,
funding rate, demand function or equilibrium derivative is supplied as a premise.
-/

noncomputable section
open scoped BigOperators Topology
open Filter OwnershipCRRA OwnershipUnfloored OwnershipMarginal OwnershipPositive
open OwnershipSupported OverlapLocal OverlapPrimitive OverlapBoundaryTangent

namespace OwnershipCertificates

structure Denomination (J : Type*) where
  units : J → ℝ
  positive : ∀ j, 0 < units j

section Coordinates
variable {J : Type*}

def encode (N : Denomination J) (a : J → ℝ) : J → ℝ := fun j => N.units j*a j
def decode (N : Denomination J) (h : J → ℝ) : J → ℝ := fun j => h j/N.units j
def quote (N : Denomination J) (q : J → ℝ) : J → ℝ := fun j => q j/N.units j
def unquote (N : Denomination J) (r : J → ℝ) : J → ℝ := fun j => r j*N.units j

theorem decode_encode (N : Denomination J) (a : J → ℝ) :
    decode N (encode N a)=a := by
  funext j
  dsimp [decode,encode]
  field_simp [ne_of_gt (N.positive j)]

theorem encode_decode (N : Denomination J) (h : J → ℝ) :
    encode N (decode N h)=h := by
  funext j
  dsimp [decode,encode]
  field_simp [ne_of_gt (N.positive j)]

theorem quote_unquote (N : Denomination J) (r : J → ℝ) :
    quote N (unquote N r)=r := by
  funext j
  dsimp [quote,unquote]
  field_simp [ne_of_gt (N.positive j)]

theorem unquote_quote (N : Denomination J) (q : J → ℝ) :
    unquote N (quote N q)=q := by
  funext j
  dsimp [quote,unquote]
  field_simp [ne_of_gt (N.positive j)]

theorem encode_nonneg (N : Denomination J) (a : J → ℝ) (ha : ∀ j, 0 ≤ a j) :
    ∀ j, 0 ≤ encode N a j := fun j => mul_nonneg (N.positive j).le (ha j)

theorem decode_nonneg (N : Denomination J) (h : J → ℝ) (hh : ∀ j, 0 ≤ h j) :
    ∀ j, 0 ≤ decode N h j := fun j => div_nonneg (hh j) (N.positive j).le

end Coordinates

section Payoffs
variable {J S : Type*} [Fintype J]

/-- Invertible positive column scaling preserves full rank and nonnegative payoffs. -/
def certificateData (D : Data J S) (N : Denomination J) : Data J S :=
  { D with
    payoff := fun s j => D.payoff s j/N.units j
    payoff_nonneg := fun s j => div_nonneg (D.payoff_nonneg s j) (N.positive j).le
    payoff_injective := by
      intro a b hab
      have hd : decode N a=decode N b := by
        apply D.payoff_injective
        funext s
        have hx := congrFun hab s
        convert hx using 1 <;> apply Finset.sum_congr rfl <;>
          intro j _ <;> dsimp [decode] <;> ring
      have he := congrArg (encode N) hd
      simpa only [encode_decode] using he }

theorem future_receipt_identity (D : Data J S) (N : Denomination J)
    (h : J → ℝ) (s : S) :
    (∑ j, (certificateData D N).payoff s j*h j)=
      ∑ j, D.payoff s j*decode N h j := by
  apply Finset.sum_congr rfl
  intro j _
  dsimp [certificateData,decode]
  ring

theorem expenditure_identity (N : Denomination J) (q h : J → ℝ) :
    (∑ j, quote N q j*h j)=∑ j, q j*decode N h j := by
  apply Finset.sum_congr rfl
  intro j _
  dsimp [quote,decode]
  ring

theorem encoded_expenditure (N : Denomination J) (q a : J → ℝ) :
    (∑ j, quote N q j*encode N a j)=∑ j, q j*a j := by
  rw [expenditure_identity,decode_encode]

theorem state_consumption_identity (D : Data J S) (N : Denomination J)
    (h : J → ℝ) (s : S) :
    consumption (certificateData D N) h s=consumption D (decode N h) s := by
  change D.income s+(∑ j, (certificateData D N).payoff s j*h j)=_
  rw [future_receipt_identity]
  rfl

variable [Fintype S]

theorem utility_identity (D : Data J S) (N : Denomination J) (c : ℝ) (h : J → ℝ) :
    economicValue (certificateData D N) c h=economicValue D c (decode N h) := by
  unfold economicValue
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  change D.weight s*OwnershipCRRA.utility (D.eta s)
      (D.income s+∑ j, (certificateData D N).payoff s j*h j)=_
  rw [future_receipt_identity]

theorem marginal_identity (D : Data J S) (N : Denomination J) (h : J → ℝ) (j : J) :
    marginal (certificateData D N) h j=marginal D (decode N h) j/N.units j := by
  unfold marginal
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro s _
  rw [state_consumption_identity]
  change D.weight s*(D.payoff s j/N.units j)*(consumption D (decode N h) s)^(-D.eta s)=_
  ring

def HouseholdOptimal (D : Data J S) (q : J → ℝ) (W c : ℝ) (a : J → ℝ) : Prop :=
  0 < c ∧ (∀ j, 0 ≤ a j) ∧ c+∑ j, q j*a j ≤ W ∧
    ∀ d, 0 < d → ∀ b : J → ℝ, (∀ j, 0 ≤ b j) → d+∑ j, q j*b j ≤ W →
      economicValue D d b ≤ economicValue D c a

/-- Feasibility and global optimality correspond for every affordable competitor. -/
theorem household_optimization_iff (D : Data J S) (N : Denomination J)
    (q : J → ℝ) (W c : ℝ) (h : J → ℝ) :
    HouseholdOptimal (certificateData D N) (quote N q) W c h ↔
      HouseholdOptimal D q W c (decode N h) := by
  constructor
  · intro ho
    refine ⟨ho.1,decode_nonneg N h ho.2.1,?_,?_⟩
    · simpa only [expenditure_identity] using ho.2.2.1
    · intro d hd a ha hb
      have hb' : d+∑ j, quote N q j*encode N a j ≤ W := by
        simpa only [encoded_expenditure] using hb
      have hop := ho.2.2.2 d hd (encode N a) (encode_nonneg N a ha) hb'
      simpa only [utility_identity,decode_encode] using hop
  · intro ho
    have hh : ∀ j, 0 ≤ h j := by
      simpa only [encode_decode] using encode_nonneg N (decode N h) ho.2.1
    refine ⟨ho.1,hh,?_,?_⟩
    · simpa only [expenditure_identity] using ho.2.2.1
    · intro d hd b hb hbudget
      rw [utility_identity,utility_identity]
      exact ho.2.2.2 d hd (decode N b) (decode_nonneg N b hb)
        (by simpa only [expenditure_identity] using hbudget)

end Payoffs

section Markets
variable {H J S : Type*} [Fintype H] [Fintype J] [Fintype S]

theorem equilibrium_to_certificates (D : H → Data J S) (N : Denomination J)
    (e : H → ℝ) (a0 : H → J → ℝ) (supply q : J → ℝ)
    (c : H → ℝ) (a : H → J → ℝ) (hEq : IsEquilibrium D e a0 supply q c a) :
    IsEquilibrium (fun i => certificateData (D i) N) e (fun i => encode N (a0 i))
      (encode N supply) (quote N q) c (fun i => encode N (a i)) := by
  refine ⟨fun j => div_pos (hEq.prices_positive j) (N.positive j),
    hEq.consumption_positive,fun i => encode_nonneg N (a i) (hEq.holdings_nonneg i),
    ?_,?_,hEq.consumption_clears,?_,?_⟩
  · intro i
    simpa only [encoded_expenditure] using hEq.affordable i
  · intro i d hd h hh hb
    have hbudget : d+∑ j, q j*decode N h j ≤ e i+∑ j, q j*a0 i j := by
      simpa only [expenditure_identity,encoded_expenditure,decode_encode] using hb
    rw [utility_identity,utility_identity,decode_encode]
    exact hEq.optimal i d hd (decode N h) (decode_nonneg N h hh) hbudget
  · intro j
    change (∑ i, N.units j*a i j)=N.units j*supply j
    rw [← Finset.mul_sum,hEq.ownership_clears j]
  · intro i j
    have hm : marginal (certificateData (D i) N) (encode N (a i)) j=
        marginal (D i) (a i) j/N.units j := by rw [marginal_identity,decode_encode]
    change marginal (certificateData (D i) N) (encode N (a i)) j ≤
      (q j/N.units j)*(c i)^(-(D i).gamma) ∧
      (N.units j*a i j)*((q j/N.units j)*(c i)^(-(D i).gamma)-
        marginal (certificateData (D i) N) (encode N (a i)) j)=0
    rw [hm]
    constructor
    · calc
        marginal (D i) (a i) j/N.units j ≤
            (q j*(c i)^(-(D i).gamma))/N.units j :=
          (div_le_div_iff_of_pos_right (N.positive j)).mpr (hEq.corner_conditions i j).1
        _ = (q j/N.units j)*(c i)^(-(D i).gamma) := by ring
    · calc
        (N.units j*a i j)*((q j/N.units j)*(c i)^(-(D i).gamma)-
            marginal (D i) (a i) j/N.units j)=
            a i j*(q j*(c i)^(-(D i).gamma)-marginal (D i) (a i) j) := by
          field_simp [ne_of_gt (N.positive j)]
        _ = 0 := (hEq.corner_conditions i j).2

theorem equilibrium_iff_decoded (D : H → Data J S) (N : Denomination J)
    (e : H → ℝ) (a0 : H → J → ℝ) (supply q : J → ℝ)
    (c : H → ℝ) (h : H → J → ℝ) :
    IsEquilibrium (fun i => certificateData (D i) N) e (fun i => encode N (a0 i))
      (encode N supply) (quote N q) c h ↔
      IsEquilibrium D e a0 supply q c (fun i => decode N (h i)) := by
  constructor
  · intro hEq
    refine ⟨?_,hEq.consumption_positive,
      fun i => decode_nonneg N (h i) (hEq.holdings_nonneg i),?_,?_,
      hEq.consumption_clears,?_,?_⟩
    · intro j
      have hp := mul_pos (hEq.prices_positive j) (N.positive j)
      change 0 < (q j/N.units j)*N.units j at hp
      simpa only [div_mul_cancel₀ _ (ne_of_gt (N.positive j))] using hp
    · intro i
      simpa only [expenditure_identity,encoded_expenditure,decode_encode] using hEq.affordable i
    · intro i d hd a ha hb
      have hc : d+∑ j, quote N q j*encode N a j ≤
          e i+∑ j, quote N q j*encode N (a0 i) j := by
        simpa only [encoded_expenditure] using hb
      have hv := hEq.optimal i d hd (encode N a) (encode_nonneg N a ha) hc
      simpa only [utility_identity,decode_encode] using hv
    · intro j
      have hs := hEq.ownership_clears j
      change (∑ i, h i j)=N.units j*supply j at hs
      change (∑ i, h i j/N.units j)=supply j
      rw [← Finset.sum_div,hs]
      field_simp [ne_of_gt (N.positive j)]
    · intro i j
      have hi := (hEq.corner_conditions i j).1
      have hz := (hEq.corner_conditions i j).2
      rw [marginal_identity] at hi hz
      change marginal (D i) (decode N (h i)) j/N.units j ≤
          (q j/N.units j)*(c i)^(-(D i).gamma) at hi
      change h i j*((q j/N.units j)*(c i)^(-(D i).gamma)-
          marginal (D i) (decode N (h i)) j/N.units j)=0 at hz
      constructor
      · calc
          marginal (D i) (decode N (h i)) j=
              (marginal (D i) (decode N (h i)) j/N.units j)*N.units j := by
                field_simp [ne_of_gt (N.positive j)]
          _ ≤ ((q j/N.units j)*(c i)^(-(D i).gamma))*N.units j :=
                mul_le_mul_of_nonneg_right hi (N.positive j).le
          _ = q j*(c i)^(-(D i).gamma) := by
                field_simp [ne_of_gt (N.positive j)]
      · calc
          decode N (h i) j*(q j*(c i)^(-(D i).gamma)-
              marginal (D i) (decode N (h i)) j)=
              h i j*((q j/N.units j)*(c i)^(-(D i).gamma)-
                marginal (D i) (decode N (h i)) j/N.units j) := by
                  dsimp [decode]
                  ring
          _ = 0 := hz
  · intro hEq
    have hc := equilibrium_to_certificates D N e a0 supply q c
      (fun i => decode N (h i)) hEq
    simpa only [encode_decode] using hc

theorem equilibrium_from_certificates (D : H → Data J S) (N : Denomination J)
    (e : H → ℝ) (a0 : H → J → ℝ) (supply r : J → ℝ)
    (c : H → ℝ) (h : H → J → ℝ)
    (hEq : IsEquilibrium (fun i => certificateData (D i) N) e
      (fun i => encode N (a0 i)) (encode N supply) r c h) :
    IsEquilibrium D e a0 supply (unquote N r) c (fun i => decode N (h i)) := by
  apply (equilibrium_iff_decoded D N e a0 supply (unquote N r) c h).mp
  simpa only [quote_unquote] using hEq

omit [Fintype S] in
/-- Statewise settlement conserves the supplied productive receipts. -/
theorem settlement_conservation (N : Denomination J) (P : S → J → ℝ)
    (supply : J → ℝ) (h : H → J → ℝ)
    (hstock : ∀ j, ∑ i, h i j=encode N supply j) (s : S) :
    (∑ i, ∑ j, (P s j/N.units j)*h i j)=∑ j, P s j*supply j := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.mul_sum,hstock j]
  dsimp [encode]
  field_simp [ne_of_gt (N.positive j)]

omit [Fintype H] [Fintype S] in
/-- Each holder receives nonnegative net receipts when the supplied pool does. -/
theorem settlement_nonnegative (N : Denomination J) (P : S → J → ℝ)
    (h : H → J → ℝ) (hP : ∀ s j, 0 ≤ P s j) (hh : ∀ i j, 0 ≤ h i j)
    (i : H) (s : S) : 0 ≤ ∑ j, (P s j/N.units j)*h i j :=
  Finset.sum_nonneg (fun j _ => mul_nonneg
    (div_nonneg (hP s j) (N.positive j).le) (hh i j))

theorem equilibrium_settlement_conservation (D : H → Data J S) (N : Denomination J)
    (P : S → J → ℝ) (hcommon : ∀ i s j, (D i).payoff s j=P s j)
    (e : H → ℝ) (a0 : H → J → ℝ) (supply r : J → ℝ)
    (c : H → ℝ) (h : H → J → ℝ)
    (hEq : IsEquilibrium (fun i => certificateData (D i) N) e
      (fun i => encode N (a0 i)) (encode N supply) r c h) (s : S) :
    (∑ i, ∑ j, (certificateData (D i) N).payoff s j*h i j)=
      ∑ j, P s j*supply j := by
  calc
    (∑ i, ∑ j, (certificateData (D i) N).payoff s j*h i j)=
        ∑ i, ∑ j, (P s j/N.units j)*h i j := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      change ((D i).payoff s j/N.units j)*h i j=_
      rw [hcommon]
    _ = ∑ j, P s j*supply j :=
      settlement_conservation N P supply h hEq.ownership_clears s

variable [Nonempty H]

theorem certificate_market_exists (D : H → Data J S) (N : Denomination J)
    (e : H → ℝ) (a0 : H → J → ℝ) (supply : J → ℝ)
    (he : ∀ i, 0 < e i) (ha0 : ∀ i j, 0 ≤ a0 i j)
    (hs : ∀ j, 0 < supply j) (hstock : ∀ j, ∑ i, a0 i j=supply j) :
    ∃ r c h, IsEquilibrium (fun i => certificateData (D i) N) e
      (fun i => encode N (a0 i)) (encode N supply) r c h := by
  obtain ⟨q,c,a,hEq⟩ := OwnershipLimit.nonnegative_initial_ownership_equilibrium
    D e a0 supply he ha0 hs hstock
  exact ⟨quote N q,c,fun i => encode N (a i),
    equilibrium_to_certificates D N e a0 supply q c a hEq⟩

end Markets

section MarketStates
variable {H J : Type*}

def quoteMarket (N : Denomination J) (z : MarketState H J) : MarketState H J :=
  (quote N z.1,fun i => encode N (z.2 i))

def unquoteMarket (N : Denomination J) (z : MarketState H J) : MarketState H J :=
  (unquote N z.1,fun i => decode N (z.2 i))

theorem quote_unquote_market (N : Denomination J) (z : MarketState H J) :
    quoteMarket N (unquoteMarket N z)=z := by
  cases z
  simp only [quoteMarket,unquoteMarket,quote_unquote,encode_decode]

theorem unquote_quote_market (N : Denomination J) (z : MarketState H J) :
    unquoteMarket N (quoteMarket N z)=z := by
  cases z
  simp only [quoteMarket,unquoteMarket,unquote_quote,decode_encode]

theorem quote_market_sub (N : Denomination J) (z w : MarketState H J) :
    quoteMarket N (z-w)=quoteMarket N z-quoteMarket N w := by
  apply Prod.ext
  · funext j
    change (z.1 j-w.1 j)/N.units j=z.1 j/N.units j-w.1 j/N.units j
    ring
  · funext i j
    change N.units j*(z.2 i j-w.2 i j)=N.units j*z.2 i j-N.units j*w.2 i j
    ring

theorem quote_market_smul (N : Denomination J) (t : ℝ) (z : MarketState H J) :
    quoteMarket N (t • z)=t • quoteMarket N z := by
  apply Prod.ext
  · funext j
    change (t*z.1 j)/N.units j=t*(z.1 j/N.units j)
    ring
  · funext i j
    change N.units j*(t*z.2 i j)=t*(N.units j*z.2 i j)
    ring

theorem quote_market_continuous (N : Denomination J) :
    Continuous (quoteMarket (H := H) N) := by
  unfold quoteMarket quote encode
  fun_prop

theorem scaled_response_limit {A : Type*} (l : Filter A) (N : Denomination J)
    (t : A → ℝ) (z : A → MarketState H J) (z0 v : MarketState H J)
    (hz : Tendsto (fun a => (t a)⁻¹ • (z a-z0)) l (𝓝 v)) :
    Tendsto (fun a => (t a)⁻¹ • (quoteMarket N (z a)-quoteMarket N z0))
      l (𝓝 (quoteMarket N v)) := by
  have hc := (quote_market_continuous (H := H) N).tendsto v |>.comp hz
  simpa only [Function.comp_def,quote_market_smul,quote_market_sub] using hc

end MarketStates

section UniqueMarkets
variable {H J S : Type*} [Fintype H] [Fintype J] [Fintype S]

theorem certificate_unique_of_unique (D : H → Data J S) (N : Denomination J)
    (e : H → ℝ) (a0 : H → J → ℝ) (supply : J → ℝ)
    (hex : ∃! z : (J → ℝ) × (H → ℝ) × (H → J → ℝ),
      IsEquilibrium D e a0 supply z.1 z.2.1 z.2.2) :
    ∃! z : (J → ℝ) × (H → ℝ) × (H → J → ℝ),
      IsEquilibrium (fun i => certificateData (D i) N) e
        (fun i => encode N (a0 i)) (encode N supply) z.1 z.2.1 z.2.2 := by
  obtain ⟨z,hz,hu⟩ := hex
  refine ⟨(quote N z.1,z.2.1,fun i => encode N (z.2.2 i)),
    equilibrium_to_certificates D N e a0 supply z.1 z.2.1 z.2.2 hz,?_⟩
  intro w hw
  have hp := equilibrium_from_certificates D N e a0 supply w.1 w.2.1 w.2.2 hw
  have hid := hu (unquote N w.1,w.2.1,fun i => decode N (w.2.2 i)) hp
  have ht := congrArg (fun x : (J → ℝ) × (H → ℝ) × (H → J → ℝ) =>
    (quote N x.1,x.2.1,fun i => encode N (x.2.2 i))) hid
  simpa only [quote_unquote,encode_decode] using ht

variable [Nonempty H]

theorem nearby_certificate_boundary_exists_unique (D : H → Data J S)
    (N : Denomination J) (e : H → ℝ) (a0 : H → J → ℝ) (supply qstar : J → ℝ)
    (he : ∀ i, 0 < e i) (ha0 : ∀ i j, 0 ≤ a0 i j)
    (hstock : ∀ j, ∑ i, a0 i j=supply j) (hs : ∀ j, 0 < supply j)
    (hsupport : SupportsInitial D e a0 qstar) :
    ∀ᶠ v in 𝓝 0, ∀ hv : Admissible D e a0 v,
      ∃! z : (J → ℝ) × (H → ℝ) × (H → J → ℝ),
        IsEquilibrium (fun i => certificateData (changedData D e a0 v hv i) N)
          (currentResources e v) (fun i => encode N (initialPortfolio a0 v i))
          (encode N (assetSupply supply v)) z.1 z.2.1 z.2.2 := by
  filter_upwards [PhysicalBoundaryResponse.nearby_actual_boundary_exists_unique
    D e a0 supply qstar he ha0 hstock hs hsupport] with v huniq
  intro hv
  exact certificate_unique_of_unique (changedData D e a0 v hv) N
    (currentResources e v) (initialPortfolio a0 v) (assetSupply supply v) (huniq hv)

omit [Nonempty H] in
def CertificateResponse (D : H → Data J S) (N : Denomination J)
    (e : H → ℝ) (a0 : H → J → ℝ) (qstar : J → ℝ)
    (f : H → J → ℝ) (b : J → ℝ) (z : MarketState H J) : Prop :=
  PhysicalResponse D e a0 qstar f b (unquoteMarket N z)

/-- Any actual certificate-equilibrium path has the transported unique physical
directional response. Certificate optimization is not a separate premise. -/
theorem actual_certificate_boundary_response {A : Type*} (l : Filter A)
    (D : H → Data J S) (N : Denomination J) (e : H → ℝ)
    (a0 : H → J → ℝ) (supply qstar : J → ℝ)
    (he : ∀ i, 0 < e i) (ha0 : ∀ i j, 0 ≤ a0 i j)
    (hstock : ∀ j, ∑ i, a0 i j=supply j) (hs : ∀ j, 0 < supply j)
    (hsupport : SupportsInitial D e a0 qstar)
    (t : A → ℝ) (v : A → PrimitiveShock H J S) (hv : ∀ n, Admissible D e a0 (v n))
    (r : A → J → ℝ) (c : A → H → ℝ) (h : A → H → J → ℝ)
    (hEq : ∀ n, IsEquilibrium (fun i => certificateData (changedData D e a0 (v n) (hv n) i) N)
      (currentResources e (v n)) (fun i => encode N (initialPortfolio a0 (v n) i))
      (encode N (assetSupply supply (v n))) (r n) (c n) (h n))
    (ht : ∀ᶠ n in l, 0 < t n) (hzero : Tendsto v l (𝓝 0))
    (d : PrimitiveShock H J S) (hd : Tendsto (fun n => (t n)⁻¹ • v n) l (𝓝 d)) :
    ∃! zstar : MarketState H J,
      CertificateResponse D N e a0 qstar
        (PhysicalBoundaryResponse.parameterForce D e a0 supply qstar d)
        (PhysicalBoundaryResponse.supplyDerivative d) zstar ∧
      Tendsto (fun n => (t n)⁻¹ • ((r n,h n)-quoteMarket N (qstar,a0)))
        l (𝓝 zstar) := by
  let q : A → J → ℝ := fun n => unquote N (r n)
  let a : A → H → J → ℝ := fun n i => decode N (h n i)
  have hphysical : ∀ n, IsEquilibrium (changedData D e a0 (v n) (hv n))
      (currentResources e (v n)) (initialPortfolio a0 (v n))
      (assetSupply supply (v n)) (q n) (c n) (a n) := by
    intro n
    exact equilibrium_from_certificates (changedData D e a0 (v n) (hv n)) N
      (currentResources e (v n)) (initialPortfolio a0 (v n))
      (assetSupply supply (v n)) (r n) (c n) (h n) (hEq n)
  obtain ⟨z,hz,hu⟩ := TangentMarketExistence.physical_tangent_exists_unique D e a0 supply qstar
    he ha0 hstock hs (PhysicalBoundaryResponse.parameterForce D e a0 supply qstar d)
    (PhysicalBoundaryResponse.supplyDerivative d)
  have hlim := PhysicalBoundaryResponse.actual_boundary_directional_limit l D e a0 supply qstar
    he ha0 hstock hs hsupport t v hv q c a hphysical ht hzero d hd z hz
  have hcert := scaled_response_limit l N t (fun n => (q n,a n)) (qstar,a0) z hlim
  refine ⟨quoteMarket N z,⟨?_,?_⟩,?_⟩
  · simpa only [CertificateResponse,unquote_quote_market] using hz
  · simpa only [q,a,quoteMarket,quote_unquote,encode_decode] using hcert
  · intro w hw
    have hid := hu (unquoteMarket N w) hw.1
    have hm := congrArg (quoteMarket N) hid
    simpa only [quote_unquote_market] using hm

end UniqueMarkets

end OwnershipCertificates

#print axioms OwnershipCertificates.decode_encode
#print axioms OwnershipCertificates.encode_decode
#print axioms OwnershipCertificates.quote_unquote
#print axioms OwnershipCertificates.unquote_quote
#print axioms OwnershipCertificates.encode_nonneg
#print axioms OwnershipCertificates.decode_nonneg
#print axioms OwnershipCertificates.future_receipt_identity
#print axioms OwnershipCertificates.expenditure_identity
#print axioms OwnershipCertificates.encoded_expenditure
#print axioms OwnershipCertificates.state_consumption_identity
#print axioms OwnershipCertificates.utility_identity
#print axioms OwnershipCertificates.marginal_identity
#print axioms OwnershipCertificates.household_optimization_iff
#print axioms OwnershipCertificates.equilibrium_to_certificates
#print axioms OwnershipCertificates.equilibrium_iff_decoded
#print axioms OwnershipCertificates.equilibrium_from_certificates
#print axioms OwnershipCertificates.settlement_conservation
#print axioms OwnershipCertificates.settlement_nonnegative
#print axioms OwnershipCertificates.equilibrium_settlement_conservation
#print axioms OwnershipCertificates.certificate_market_exists
#print axioms OwnershipCertificates.quote_unquote_market
#print axioms OwnershipCertificates.unquote_quote_market
#print axioms OwnershipCertificates.quote_market_sub
#print axioms OwnershipCertificates.quote_market_smul
#print axioms OwnershipCertificates.quote_market_continuous
#print axioms OwnershipCertificates.scaled_response_limit
#print axioms OwnershipCertificates.certificate_unique_of_unique
#print axioms OwnershipCertificates.nearby_certificate_boundary_exists_unique
#print axioms OwnershipCertificates.actual_certificate_boundary_response
