/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.ChoquetCone
import SpatialLine.ProfileUniqueness
import SpatialLine.SemigroupCase

/-!
# `prop:choquet-cone`: injectivity of the superposition map, and the extreme rays

Blueprint: `blueprint/src/parts/08-cone.tex`, `prop:choquet-cone`. The node's remaining four
declarations, all of which spend uniqueness of the Levy pair (`prop:fourier-toolbox`(3), ledger
**A3**, admitted as `fourier_toolbox_levy_unique`). The four proved in wave 2 -- the map, its
surjectivity, the domain condition and the linearity -- are in `SpatialLine/ChoquetCone.lean`
and rest on Lean core.

## The two measure-theoretic steps injectivity needs

Uniqueness of the pair identifies the Levy *measures*, hence the profiles only almost
everywhere, hence the tails of the Choquet measures only at almost every point. Two steps close
the gap, and both are stated here in the generality in which they are true rather than at the
profile:

* `tail_eq_of_ae_tail_eq` -- two measures whose tails `x` maps to `m (Ioi x)` agree at almost
  every positive point agree at *every* positive point. The tail is continuous from below along
  the monotone family `Ioi (x + 1/(n+1))`, and each of those tails is squeezed between two tails
  at points of the co-null good set, which meets every subinterval.
* `measure_eq_of_tail_eq` -- two folded measures with equal tails on the positive half-line, one
  of them finite on every `Ioi x` with `x > 0`, are equal. The restrictions to `Ioi eps` are
  finite measures and agree on every `Iic t`, an `Ioc eps t` being a difference of two finite
  tails, so `Measure.ext_of_Iic` identifies them; the sets `s` intersect `Ioi (1/(n+1))` then
  exhaust the part of `s` in the positive half-line, which carries the whole of a folded measure.

Neither is about this article's objects, and both are `ScaleSpaceCore` candidates: Paper I's
`HasLevyTail` has the same two obligations.

## The route through the profile

`sdProfile_unique` is the single place the ledger interface is spent in this file: two profiles
with the same exponent have the same Gaussian coefficient and the same profile measure. Every
other declaration below consumes it through `ae_eq_k_of_exponent_eq`, the almost-everywhere
equality of the profiles that `ProfileUniqueness.lean`'s `ae_eq_of_profileMeasure_eq` extracts
from it.

## What the extremality arguments actually need

The blueprint transports extremality through the Choquet coordinates. Only
`choquet_cone_extreme_only` does that here; the two positive clauses are cheaper read at the
profile:

* **The Gaussian ray.** If two admissible exponents sum to the Gaussian one, the summed profile
  has the same exponent as the Gaussian datum, so its profile measure vanishes, so both profiles
  vanish almost everywhere on the positive half-line -- and an exponent whose profile is null
  almost everywhere is a multiple of the Gaussian one. No cone structure and no Choquet
  coordinate is used.
* **The `Cin` rays.** If two admissible exponents sum to `Cin (tau .)`, then on `(0,tau)` the
  two profiles sum to `1` almost everywhere while both are nonincreasing; so on the co-null set
  where the sum is exactly `1`, each is *both* nonincreasing and nondecreasing, hence constant.
  This replaces the blueprint's transport through the coordinates, and it is the route the proof
  of record now follows.

Proving campaign, wave 3, chapter 8 (2026-09-09).
-/

namespace SpatialLine

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-! ## Two facts about tails of measures on the half-line -/

/-- Continuity from below along `Ioi (x + 1/(n+1))`. -/
theorem measure_Ioi_eq_iSup (m : Measure ℝ) (x : ℝ) :
    m (Ioi x) = ⨆ n : ℕ, m (Ioi (x + 1 / ((n : ℝ) + 1))) := by
  have hmono : Monotone (fun n : ℕ => Ioi (x + 1 / ((n : ℝ) + 1))) := by
    intro p q hpq
    refine Ioi_subset_Ioi ?_
    have hle : (1 : ℝ) / ((q : ℝ) + 1) ≤ 1 / ((p : ℝ) + 1) := by
      refine one_div_le_one_div_of_le (by positivity) ?_
      have : (p : ℝ) ≤ (q : ℝ) := by exact_mod_cast hpq
      linarith
    linarith
  have hcover : (⋃ n : ℕ, Ioi (x + 1 / ((n : ℝ) + 1))) = Ioi x := by
    ext z
    simp only [mem_iUnion, mem_Ioi]
    constructor
    · rintro ⟨n, hn⟩
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    · intro hz
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0 : ℝ) < z - x by linarith)
      exact ⟨n, by linarith⟩
  rw [← hcover, hmono.measure_iUnion]

/-- A measure of the positive half-line is the supremum of the masses of the `Ioc 0 (n+1)`. -/
theorem measure_Ioi_zero_eq_iSup (m : Measure ℝ) :
    m (Ioi (0 : ℝ)) = ⨆ n : ℕ, m (Ioc (0 : ℝ) ((n : ℝ) + 1)) := by
  have hmono : Monotone (fun n : ℕ => Ioc (0 : ℝ) ((n : ℝ) + 1)) := by
    intro p q hpq
    refine Ioc_subset_Ioc le_rfl ?_
    have : (p : ℝ) ≤ (q : ℝ) := by exact_mod_cast hpq
    linarith
  have hcover : (⋃ n : ℕ, Ioc (0 : ℝ) ((n : ℝ) + 1)) = Ioi 0 := by
    ext z
    simp only [mem_iUnion, mem_Ioc, mem_Ioi]
    constructor
    · rintro ⟨n, hn, -⟩
      exact hn
    · intro hz
      obtain ⟨n, hn⟩ := exists_nat_ge z
      exact ⟨n, hz, by linarith⟩
  rw [← hcover, hmono.measure_iUnion]

private theorem tail_le_of_ae_tail_eq {a b : Measure ℝ}
    (hmeet : ∀ u v : ℝ, 0 ≤ u → u < v → ∃ y ∈ Ioo u v, a (Ioi y) = b (Ioi y))
    {x : ℝ} (hx : 0 < x) : a (Ioi x) ≤ b (Ioi x) := by
  have hval := measure_Ioi_eq_iSup a x
  rw [hval]
  refine iSup_le fun n => ?_
  have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  obtain ⟨y, hy, hyeq⟩ := hmeet x (x + 1 / ((n : ℝ) + 1)) hx.le (by linarith)
  calc a (Ioi (x + 1 / ((n : ℝ) + 1))) ≤ a (Ioi y) :=
        measure_mono (Ioi_subset_Ioi hy.2.le)
    _ = b (Ioi y) := hyeq
    _ ≤ b (Ioi x) := measure_mono (Ioi_subset_Ioi hy.1.le)

/-- **Tails equal almost everywhere are tails equal everywhere.** Two measures whose tails
`x ↦ m (Ioi x)` agree at almost every `x > 0` agree at every `x > 0`.

The good set is co-null, so it meets every interval `(x, x + 1/(n+1))`; picking `y` there
squeezes `a (Ioi (x + 1/(n+1))) ≤ a (Ioi y) = b (Ioi y) ≤ b (Ioi x)`, and the left-hand sides
increase to `a (Ioi x)` by continuity from below. -/
theorem tail_eq_of_ae_tail_eq {a b : Measure ℝ}
    (hae : ∀ᵐ y ∂(volume.restrict (Ioi (0 : ℝ))), a (Ioi y) = b (Ioi y))
    {x : ℝ} (hx : 0 < x) : a (Ioi x) = b (Ioi x) := by
  have hnull : volume {y : ℝ | y ∈ Ioi (0 : ℝ) ∧ a (Ioi y) ≠ b (Ioi y)} = 0 := by
    have h := (ae_restrict_iff' measurableSet_Ioi).mp hae
    rw [MeasureTheory.ae_iff] at h
    refine measure_mono_null ?_ h
    rintro y ⟨hy, hne⟩
    exact fun hcon => hne (hcon hy)
  have hmeet : ∀ u v : ℝ, 0 ≤ u → u < v → ∃ y ∈ Ioo u v, a (Ioi y) = b (Ioi y) := by
    intro u v hu huv
    by_contra hcon
    push Not at hcon
    have hsub : Ioo u v ⊆ {y : ℝ | y ∈ Ioi (0 : ℝ) ∧ a (Ioi y) ≠ b (Ioi y)} := fun y hy =>
      ⟨lt_of_le_of_lt hu hy.1, hcon y hy⟩
    have hz : volume (Ioo u v) = 0 := measure_mono_null hsub hnull
    rw [Real.volume_Ioo, ENNReal.ofReal_eq_zero] at hz
    linarith
  refine le_antisymm (tail_le_of_ae_tail_eq hmeet hx) (tail_le_of_ae_tail_eq ?_ hx)
  intro u v hu huv
  obtain ⟨y, hy, hyeq⟩ := hmeet u v hu huv
  exact ⟨y, hy, hyeq.symm⟩

/-- The restrictions to `Ioi ε` of two measures with equal tails are equal: both are finite, and
`Ioc ε t` is the difference of two finite tails. -/
theorem restrict_eq_of_tail_eq {a b : Measure ℝ}
    (hfin : ∀ x : ℝ, 0 < x → a (Ioi x) ≠ ⊤)
    (h : ∀ x : ℝ, 0 < x → a (Ioi x) = b (Ioi x)) {ε : ℝ} (hε : 0 < ε) :
    a.restrict (Ioi ε) = b.restrict (Ioi ε) := by
  have hfa : IsFiniteMeasure (a.restrict (Ioi ε)) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.mpr (hfin ε hε)
  have hIoc : ∀ (m : Measure ℝ) (t : ℝ), (m.restrict (Ioi ε)) (Iic t) = m (Ioc ε t) := by
    intro m t
    rw [Measure.restrict_apply measurableSet_Iic]
    congr 1
    ext z
    simp only [mem_inter_iff, mem_Iic, mem_Ioi, mem_Ioc]
    tauto
  refine Measure.ext_of_Iic _ _ fun t => ?_
  rw [hIoc, hIoc]
  rcases le_or_gt t ε with ht | ht
  · rw [Ioc_eq_empty (by simpa using ht), measure_empty, measure_empty]
  · have hsplit : ∀ m : Measure ℝ, m (Ioi ε) = m (Ioc ε t) + m (Ioi t) := by
      intro m
      rw [← measure_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi, Ioc_union_Ioi_eq_Ioi ht.le]
    have he := h ε hε
    rw [hsplit a, hsplit b, h t (lt_trans hε ht)] at he
    exact WithTop.add_right_cancel
      (by rw [← h t (lt_trans hε ht)]; exact hfin t (lt_trans hε ht)) he

/-- **Two folded measures with the same tails on the positive half-line are equal**, provided one
of them is finite on every `Ioi x` with `x > 0`. -/
theorem measure_eq_of_tail_eq {a b : Measure ℝ} (hfa : IsFolded a) (hfb : IsFolded b)
    (hfin : ∀ x : ℝ, 0 < x → a (Ioi x) ≠ ⊤)
    (h : ∀ x : ℝ, 0 < x → a (Ioi x) = b (Ioi x)) : a = b := by
  refine Measure.ext fun s hs => ?_
  have hzero : ∀ m : Measure ℝ, m (Iic 0) = 0 → m s = m (s ∩ Ioi 0) := by
    intro m hm
    refine le_antisymm ?_ (measure_mono inter_subset_left)
    have hsub : s ⊆ (s ∩ Ioi 0) ∪ Iic 0 := by
      intro z hz
      rcases le_or_gt z 0 with hz0 | hz0
      · exact Or.inr hz0
      · exact Or.inl ⟨hz, hz0⟩
    calc m s ≤ m ((s ∩ Ioi 0) ∪ Iic 0) := measure_mono hsub
      _ ≤ m (s ∩ Ioi 0) + m (Iic 0) := measure_union_le _ _
      _ = m (s ∩ Ioi 0) := by rw [hm, add_zero]
  rw [hzero a hfa, hzero b hfb]
  have hmono : Monotone (fun n : ℕ => s ∩ Ioi (1 / ((n : ℝ) + 1))) := by
    intro p q hpq
    refine inter_subset_inter_right _ (Ioi_subset_Ioi ?_)
    refine one_div_le_one_div_of_le (by positivity) ?_
    have : (p : ℝ) ≤ (q : ℝ) := by exact_mod_cast hpq
    linarith
  have hcover : (⋃ n : ℕ, s ∩ Ioi (1 / ((n : ℝ) + 1))) = s ∩ Ioi 0 := by
    rw [← inter_iUnion]
    congr 1
    ext z
    simp only [mem_iUnion, mem_Ioi]
    constructor
    · rintro ⟨n, hn⟩
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    · intro hz
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hz
      exact ⟨n, hn⟩
  rw [← hcover, hmono.measure_iUnion, hmono.measure_iUnion]
  refine iSup_congr fun n => ?_
  have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  have hres := restrict_eq_of_tail_eq hfin h hpos
  rw [show a (s ∩ Ioi (1 / ((n : ℝ) + 1))) = (a.restrict (Ioi (1 / ((n : ℝ) + 1)))) s from
      (Measure.restrict_apply hs).symm,
    show b (s ∩ Ioi (1 / ((n : ℝ) + 1))) = (b.restrict (Ioi (1 / ((n : ℝ) + 1)))) s from
      (Measure.restrict_apply hs).symm, hres]

/-! ## Uniqueness at the profile -- the one place ledger A3 is spent here -/

/-- **Two profiles with the same exponent have the same data.** The Gaussian coefficients agree
and the Levy measures agree; the profiles themselves agree only almost everywhere, which is
`ae_eq_k_of_exponent_eq`.

**Spends ledger A3** through `fourier_toolbox_levy_unique`. -/
theorem sdProfile_unique {P Q : SDProfile} (h : ∀ ω, P.exponent ω = Q.exponent ω) :
    P.a = Q.a ∧ profileMeasure P.k = profileMeasure Q.k := by
  obtain ⟨P', hPa, hPν, hPe⟩ := profile_integrability_pair P
  obtain ⟨Q', hQa, hQν, hQe⟩ := profile_integrability_pair Q
  have hE : ∀ ω, P'.exponent ω = Q'.exponent ω := fun ω => by
    rw [← hPe, ← hQe]; exact h ω
  obtain ⟨ha, hν⟩ := fourier_toolbox_levy_unique P' Q' hE
  exact ⟨by rw [← hPa, ← hQa]; exact ha, by rw [← hPν, ← hQν]; exact hν⟩

/-- Two profiles with the same exponent agree almost everywhere on the positive half-line. -/
theorem ae_eq_k_of_exponent_eq {P Q : SDProfile} (h : ∀ ω, P.exponent ω = Q.exponent ω) :
    ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))), P.k x = Q.k x :=
  ae_eq_of_profileMeasure_eq P.k_antitone P.k_nonneg Q.aemeasurable_k Q.k_nonneg
    (sdProfile_unique h).2

/-- The exponent sees the profile only up to a null set of the positive half-line. -/
theorem SDProfile.exponentL_congr {P Q : SDProfile} (ha : P.a = Q.a)
    (hk : ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))), P.k x = Q.k x) (ω : ℝ) :
    P.exponentL ω = Q.exponentL ω := by
  rw [SDProfile.exponentL, SDProfile.exponentL, ha]
  congr 1
  refine lintegral_congr_ae ?_
  filter_upwards [hk] with x hx
  rw [hx]

/-- The same, at the real-valued exponent. -/
theorem SDProfile.exponent_congr {P Q : SDProfile} (ha : P.a = Q.a)
    (hk : ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))), P.k x = Q.k x) (ω : ℝ) :
    P.exponent ω = Q.exponent ω := by
  rw [SDProfile.exponent, SDProfile.exponent, SDProfile.exponentL_congr ha hk]

/-! ## `prop:choquet-cone`, injectivity -/

/-- **`prop:choquet-cone`, injectivity.** The pair `(a,ϖ)` is determined by the exponent, on the
domain the node names.

The domain hypothesis is load-bearing and not decoration: on `ℝ≥0∞` two pairs outside the domain
both send every `ω ≠ 0` to `⊤`.

**Spends ledger A3** through `sdProfile_unique`. -/
theorem choquet_cone_injective {a₁ a₂ : ℝ} (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (ϖ₁ ϖ₂ : Measure ℝ)
    (hf₁ : IsFolded ϖ₁) (hf₂ : IsFolded ϖ₂)
    (hd₁ : ∫⁻ τ, ENNReal.ofReal (min (τ ^ 2) (1 + Real.log (max 1 τ))) ∂ϖ₁ ≠ ⊤)
    (hd₂ : ∫⁻ τ, ENNReal.ofReal (min (τ ^ 2) (1 + Real.log (max 1 τ))) ∂ϖ₂ ≠ ⊤)
    (h : ∀ ω : ℝ, cinSuperpositionL a₁ ϖ₁ ω = cinSuperpositionL a₂ ϖ₂ ω) :
    a₁ = a₂ ∧ ϖ₁ = ϖ₂ := by
  have hd₁' : (∫⁻ τ, ENNReal.ofReal (domainIntegrand τ) ∂ϖ₁) ≠ ⊤ := hd₁
  have hd₂' : (∫⁻ τ, ENNReal.ofReal (domainIntegrand τ) ∂ϖ₂) ≠ ⊤ := hd₂
  set Q₁ := choquetSDProfile ha₁ ϖ₁ hf₁ hd₁' with hQ₁
  set Q₂ := choquetSDProfile ha₂ ϖ₂ hf₂ hd₂' with hQ₂
  have he₁ : ∀ ω, Q₁.exponentL ω = cinSuperpositionL a₁ ϖ₁ ω := fun ω =>
    cin_superposition Q₁ ϖ₁ (hasProfileTail_choquetSDProfile ha₁ ϖ₁ hf₁ hd₁') ω
  have he₂ : ∀ ω, Q₂.exponentL ω = cinSuperpositionL a₂ ϖ₂ ω := fun ω =>
    cin_superposition Q₂ ϖ₂ (hasProfileTail_choquetSDProfile ha₂ ϖ₂ hf₂ hd₂') ω
  have hexp : ∀ ω, Q₁.exponent ω = Q₂.exponent ω := by
    intro ω
    rw [SDProfile.exponent, SDProfile.exponent, he₁, he₂, h]
  refine ⟨(sdProfile_unique hexp).1, ?_⟩
  have hae := ae_eq_k_of_exponent_eq hexp
  have haetail : ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))), ϖ₁ (Ioi x) = ϖ₂ (Ioi x) := by
    filter_upwards [hae, self_mem_ae_restrict measurableSet_Ioi] with x hx hx0
    have hx0' : (0 : ℝ) < x := hx0
    have e1 : ϖ₁ (Ioi x) = ENNReal.ofReal (Q₁.k x) := by
      change ϖ₁ (Ioi x) = ENNReal.ofReal (tailProfile ϖ₁ x)
      simp only [tailProfile, if_pos hx0']
      rw [ENNReal.ofReal_toReal (measure_Ioi_ne_top_of_domain hd₁' hx0')]
    have e2 : ϖ₂ (Ioi x) = ENNReal.ofReal (Q₂.k x) := by
      change ϖ₂ (Ioi x) = ENNReal.ofReal (tailProfile ϖ₂ x)
      simp only [tailProfile, if_pos hx0']
      rw [ENNReal.ofReal_toReal (measure_Ioi_ne_top_of_domain hd₂' hx0')]
    rw [e1, e2, hx]
  exact measure_eq_of_tail_eq hf₁ hf₂ (fun x hx => measure_Ioi_ne_top_of_domain hd₁' hx)
    (fun x hx => tail_eq_of_ae_tail_eq haetail hx)

/-! ## The exponent of a `Cin` ray -/

/-- The exponent of the unit-step profile at the real level: `Cin(tau omega)`.

`cin_ray` is the same fact packaged existentially, as `lem:cin-rays`(1) states it; this form is
what the extremality clauses rewrite with. -/
theorem cinSDProfile_exponent {τ : ℝ} (hτ : 0 < τ) (ω : ℝ) :
    (cinSDProfile τ).exponent ω = cin (τ * ω) := by
  rw [SDProfile.exponent, cinSDProfile_exponentL hτ ω, ENNReal.toReal_ofReal (cin_nonneg' _)]

/-! ## `prop:choquet-cone`, the Gaussian ray is extreme -/

/-- **`prop:choquet-cone`, the Gaussian ray is extreme.**

Reading: extremality of a ray is stated as the splitting property directly -- if the Gaussian
exponent is the sum of two admissible exponents then both are nonnegative multiples of it --
rather than through a general notion of extreme ray, which would need a cone structure on the
admissible exponents that nothing else in the development uses.

Priced **M**, paid **S** once the route is read at the profile rather than in the Choquet
coordinates: the summed profile has the same exponent as the Gaussian datum, so
`ae_eq_k_of_exponent_eq` makes both summand profiles null almost everywhere on the positive
half-line, and `SDProfile.exponent_congr` then reads each exponent off its Gaussian coefficient.
The constants are the coefficients themselves, so no normalisation is needed and the annotation's
"a summand's Levy measure is dominated by the sum's" is not the step taken -- domination is not
available in this development, and equality with the null measure is.

**Spends ledger A3** through `sdProfile_unique`. -/
theorem choquet_cone_extreme_gaussian (P₁ P₂ : SDProfile)
    (h : ∀ ω : ℝ, P₁.exponent ω + P₂.exponent ω = ω ^ 2) :
    ∃ c₁ c₂ : ℝ, 0 ≤ c₁ ∧ 0 ≤ c₂ ∧ (∀ ω : ℝ, P₁.exponent ω = c₁ * ω ^ 2) ∧
      ∀ ω : ℝ, P₂.exponent ω = c₂ * ω ^ 2 := by
  have hsum : ∀ ω, (P₁.add P₂).exponent ω = (gaussianDatum 1 zero_le_one).exponent ω := by
    intro ω
    rw [SDProfile.exponent_add, h ω, gaussianDatum_exponent, one_mul]
  have hae := ae_eq_k_of_exponent_eq hsum
  have hz : ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))), P₁.k x = 0 ∧ P₂.k x = 0 := by
    filter_upwards [hae, self_mem_ae_restrict measurableSet_Ioi] with x hx hxm
    have h0 : P₁.k x + P₂.k x = 0 := by
      have := hx
      simpa using this
    have h1 := P₁.k_nonneg x hxm
    have h2 := P₂.k_nonneg x hxm
    constructor <;> linarith
  refine ⟨P₁.a, P₂.a, P₁.a_nonneg, P₂.a_nonneg, fun ω => ?_, fun ω => ?_⟩
  · have hc : ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))),
        P₁.k x = (gaussianDatum P₁.a P₁.a_nonneg).k x := by
      filter_upwards [hz] with x hx
      simpa using hx.1
    rw [SDProfile.exponent_congr (P := P₁) (Q := gaussianDatum P₁.a P₁.a_nonneg) rfl hc ω,
      gaussianDatum_exponent]
  · have hc : ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))),
        P₂.k x = (gaussianDatum P₂.a P₂.a_nonneg).k x := by
      filter_upwards [hz] with x hx
      simpa using hx.2
    rw [SDProfile.exponent_congr (P := P₂) (Q := gaussianDatum P₂.a P₂.a_nonneg) rfl hc ω,
      gaussianDatum_exponent]
/-! ## `prop:choquet-cone`, the `Cin` rays are extreme -/

/-- **`prop:choquet-cone`, the `Cin` rays are extreme.**

Priced **M** and paid **M**. The route is the one wave 2 recorded at the statement and is *not*
the blueprint's transport through the Choquet coordinates: uniqueness of the pair gives
`k_1 + k_2 = 1` almost everywhere on `(0,tau)` and `k_1 + k_2 = 0` almost everywhere above
`tau`; on the co-null set where the first holds each summand is nonincreasing (it is a profile)
and nondecreasing (its complement in the constant sum is), hence constant there; above `tau`
both vanish by nonnegativity. So each profile agrees almost everywhere with a nonnegative
multiple of the ray's own, and `SDProfile.exponent_congr` with `SDProfile.exponent_smul`
finishes. `choquet_cone_injective` is not used.

**Spends ledger A3** through `sdProfile_unique`. -/
theorem choquet_cone_extreme_cin {τ : ℝ} (hτ : 0 < τ) (P₁ P₂ : SDProfile)
    (h : ∀ ω : ℝ, P₁.exponent ω + P₂.exponent ω = cin (τ * ω)) :
    ∃ c₁ c₂ : ℝ, 0 ≤ c₁ ∧ 0 ≤ c₂ ∧ (∀ ω : ℝ, P₁.exponent ω = c₁ * cin (τ * ω)) ∧
      ∀ ω : ℝ, P₂.exponent ω = c₂ * cin (τ * ω) := by
  have hsum : ∀ ω, (P₁.add P₂).exponent ω = (cinSDProfile τ).exponent ω := by
    intro ω
    rw [SDProfile.exponent_add, h ω, cinSDProfile_exponent hτ]
  have haa : P₁.a + P₂.a = 0 := (sdProfile_unique hsum).1
  have ha₁ : P₁.a = 0 := by linarith [P₁.a_nonneg, P₂.a_nonneg]
  have ha₂ : P₂.a = 0 := by linarith [P₁.a_nonneg, P₂.a_nonneg]
  have hae : ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))),
      P₁.k x + P₂.k x = cinProfile τ x := ae_eq_k_of_exponent_eq hsum
  -- The co-null good set meets `(0,τ)`, so a witness of the value exists there.
  have hnull : volume {x : ℝ | x ∈ Ioi (0 : ℝ) ∧ P₁.k x + P₂.k x ≠ cinProfile τ x} = 0 := by
    have h' := (ae_restrict_iff' measurableSet_Ioi).mp hae
    rw [MeasureTheory.ae_iff] at h'
    refine measure_mono_null ?_ h'
    rintro y ⟨hy, hne⟩
    exact fun hcon => hne (hcon hy)
  obtain ⟨x₀, hx₀m, hx₀e⟩ : ∃ x ∈ Ioo (0 : ℝ) τ, P₁.k x + P₂.k x = cinProfile τ x := by
    by_contra hcon
    push Not at hcon
    have hsub : Ioo (0 : ℝ) τ
        ⊆ {x : ℝ | x ∈ Ioi (0 : ℝ) ∧ P₁.k x + P₂.k x ≠ cinProfile τ x} := fun y hy =>
      ⟨hy.1, hcon y hy⟩
    have hz : volume (Ioo (0 : ℝ) τ) = 0 := measure_mono_null hsub hnull
    rw [Real.volume_Ioo, ENNReal.ofReal_eq_zero] at hz
    linarith
  -- On the good set inside `(0,τ)` each profile is both nonincreasing and nondecreasing.
  have hconst : ∀ x ∈ Ioo (0 : ℝ) τ, P₁.k x + P₂.k x = cinProfile τ x →
      P₁.k x = P₁.k x₀ ∧ P₂.k x = P₂.k x₀ := by
    intro x hx hxe
    rw [cinProfile_eq_one hx] at hxe
    rw [cinProfile_eq_one hx₀m] at hx₀e
    rcases le_total x x₀ with hxy | hxy
    · have h1 := P₁.k_antitone (mem_Ioi.mpr hx.1) (mem_Ioi.mpr hx₀m.1) hxy
      have h2 := P₂.k_antitone (mem_Ioi.mpr hx.1) (mem_Ioi.mpr hx₀m.1) hxy
      exact ⟨by linarith, by linarith⟩
    · have h1 := P₁.k_antitone (mem_Ioi.mpr hx₀m.1) (mem_Ioi.mpr hx.1) hxy
      have h2 := P₂.k_antitone (mem_Ioi.mpr hx₀m.1) (mem_Ioi.mpr hx.1) hxy
      exact ⟨by linarith, by linarith⟩
  have hc₁ : 0 ≤ P₁.k x₀ := P₁.k_nonneg x₀ (mem_Ioi.mpr hx₀m.1)
  have hc₂ : 0 ≤ P₂.k x₀ := P₂.k_nonneg x₀ (mem_Ioi.mpr hx₀m.1)
  have key : ∀ (Q : SDProfile) (c : ℝ) (hc : 0 ≤ c), Q.a = 0 →
      (∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))), Q.k x = c * cinProfile τ x) →
      ∀ ω : ℝ, Q.exponent ω = c * cin (τ * ω) := by
    intro Q c hc hQa hQk ω
    have hka : ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))),
        Q.k x = ((cinSDProfile τ).smul hc).k x := by
      filter_upwards [hQk] with x hx
      exact hx
    have haa' : Q.a = ((cinSDProfile τ).smul hc).a := by
      rw [hQa, SDProfile.smul_a, show (cinSDProfile τ).a = 0 from rfl, mul_zero]
    rw [SDProfile.exponent_congr haa' hka ω, SDProfile.exponent_smul,
      cinSDProfile_exponent hτ]
  refine ⟨P₁.k x₀, P₂.k x₀, hc₁, hc₂, ?_, ?_⟩
  · refine key P₁ _ hc₁ ha₁ ?_
    filter_upwards [hae, self_mem_ae_restrict measurableSet_Ioi] with x hx hxm
    have hxm' : (0 : ℝ) < x := hxm
    by_cases hcase : x ∈ Ioo (0 : ℝ) τ
    · rw [(hconst x hcase hx).1, cinProfile_eq_one hcase, mul_one]
    · have hc0 : cinProfile τ x = 0 := cinProfile_eq_zero hcase
      rw [hc0] at hx
      have h1 := P₁.k_nonneg x hxm
      have h2 := P₂.k_nonneg x hxm
      rw [hc0, mul_zero]
      linarith
  · refine key P₂ _ hc₂ ha₂ ?_
    filter_upwards [hae, self_mem_ae_restrict measurableSet_Ioi] with x hx hxm
    have hxm' : (0 : ℝ) < x := hxm
    by_cases hcase : x ∈ Ioo (0 : ℝ) τ
    · rw [(hconst x hcase hx).2, cinProfile_eq_one hcase, mul_one]
    · have hc0 : cinProfile τ x = 0 := cinProfile_eq_zero hcase
      rw [hc0] at hx
      have h1 := P₁.k_nonneg x hxm
      have h2 := P₂.k_nonneg x hxm
      rw [hc0, mul_zero]
      linarith
/-! ## `prop:choquet-cone`, there are no other extreme rays -/

/-- **`prop:choquet-cone`, there are no other extreme rays.**

Reading: the hypothesis is extremality as a splitting property, quantified over all admissible
decompositions; the conclusion is that the exponent is a nonnegative multiple of the Gaussian
exponent or of one `Cin (tau .)`. Together with the two previous declarations this is the node's
"the extreme rays of the cone are the Gaussian ray together with the family `Cin (tau .)`".

Priced **L** and paid **L**. The proof is in three parts, and the part the annotation named as
"the whole cost" -- that a positive measure which is not a multiple of a Dirac splits -- is here
an infimum argument rather than a piece of measure theory Mathlib would have to supply. Writing
`T` for the set of thresholds below which the Choquet measure carries mass and `tau` for its
infimum, either some threshold has mass on both sides of it, or every threshold has mass on at
most one side and then the measure is carried by the single point `tau`: above `tau` the tails
vanish by the defining property of an infimum, below it by minimality, and continuity from below
along `Ioi (x + 1/(n+1))` and along `Ioc 0 (n+1)` supplies the two limits. In the first case the
two restrictions of the measure give two admissible exponents summing to the whole, extremality
makes the lower one a multiple of the whole, and `choquet_cone_injective` turns that back into an
equality of measures which the upper interval's mass refutes. The Gaussian alternative is what
remains when the Choquet measure vanishes, and the Gaussian coefficient must be zero as soon as
it does not, by the same splitting applied to the pair `(a, 0)` and `(0, varpi)`.

**Spends ledger A3** through `sdProfile_unique` and `choquet_cone_injective`. -/
theorem choquet_cone_extreme_only (P : SDProfile)
    (hext : ∀ P₁ P₂ : SDProfile, (∀ ω : ℝ, P₁.exponent ω + P₂.exponent ω = P.exponent ω) →
      ∃ c₁ c₂ : ℝ, (∀ ω : ℝ, P₁.exponent ω = c₁ * P.exponent ω) ∧
        ∀ ω : ℝ, P₂.exponent ω = c₂ * P.exponent ω) :
    (∃ c : ℝ, 0 ≤ c ∧ ∀ ω : ℝ, P.exponent ω = c * ω ^ 2) ∨
      ∃ c τ : ℝ, 0 ≤ c ∧ 0 < τ ∧ ∀ ω : ℝ, P.exponent ω = c * cin (τ * ω) := by
  obtain ⟨ϖ, htail, hdom, hsup⟩ := choquet_cone_surjective P
  have hdom' : (∫⁻ t, ENNReal.ofReal (domainIntegrand t) ∂ϖ) ≠ ⊤ := hdom
  have hfold : IsFolded ϖ := htail.1
  have hfin : ∀ x : ℝ, 0 < x → ϖ (Ioi x) ≠ ⊤ := fun x hx =>
    measure_Ioi_ne_top_of_domain hdom' hx
  -- Both directions between "the profile vanishes" and "the Choquet measure vanishes".
  have hk_of_zero : ϖ = 0 → ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))), P.k x = 0 := by
    intro hz
    filter_upwards [htail.2, self_mem_ae_restrict measurableSet_Ioi] with x hx hxm
    rw [hz] at hx
    have : ENNReal.ofReal (P.k x) = 0 := hx.symm
    have hle : P.k x ≤ 0 := ENNReal.ofReal_eq_zero.mp this
    exact le_antisymm hle (P.k_nonneg x hxm)
  have hzero_of_k : (∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))), P.k x = 0) → ϖ = 0 := by
    intro hk
    refine measure_eq_of_tail_eq hfold (by simp [IsFolded]) hfin fun x hx => ?_
    refine tail_eq_of_ae_tail_eq ?_ hx
    filter_upwards [htail.2, hk] with y hy hky
    rw [hy, hky, ENNReal.ofReal_zero]
    simp
  have hgauss_of_k : (∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))), P.k x = 0) →
      ∀ ω, P.exponent ω = P.a * ω ^ 2 := by
    intro hk ω
    have hc : ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))),
        P.k x = (gaussianDatum P.a P.a_nonneg).k x := by
      filter_upwards [hk] with x hx
      simpa using hx
    rw [SDProfile.exponent_congr (P := P) (Q := gaussianDatum P.a P.a_nonneg) rfl hc ω,
      gaussianDatum_exponent]
  have hk_of_gauss : ∀ b : ℝ, 0 ≤ b → (∀ ω : ℝ, P.exponent ω = b * ω ^ 2) →
      ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))), P.k x = 0 := by
    intro b hb hbe
    have hE : ∀ ω, P.exponent ω = (gaussianDatum b hb).exponent ω := by
      intro ω; rw [hbe ω, gaussianDatum_exponent]
    filter_upwards [ae_eq_k_of_exponent_eq hE] with x hx
    simpa using hx
  by_cases h0 : ϖ = 0
  · exact Or.inl ⟨P.a, P.a_nonneg, hgauss_of_k (hk_of_zero h0)⟩
  -- From here on the Choquet measure is nonzero.
  have hPa : P.a = 0 := by
    by_contra hane
    have hapos : 0 < P.a := lt_of_le_of_ne P.a_nonneg (Ne.symm hane)
    set G := gaussianDatum P.a P.a_nonneg with hG
    set Q := choquetSDProfile (le_refl (0 : ℝ)) ϖ hfold hdom' with hQ
    have hQL : ∀ ω, Q.exponentL ω = cinSuperpositionL 0 ϖ ω := fun ω =>
      cin_superposition Q ϖ (hasProfileTail_choquetSDProfile (le_refl (0 : ℝ)) ϖ hfold hdom') ω
    have hGL : ∀ ω, G.exponentL ω = ENNReal.ofReal (P.a * ω ^ 2) := by
      intro ω
      rw [SDProfile.exponentL]
      have hzz : (fun x : ℝ => ENNReal.ofReal ((1 - Real.cos (ω * x)) * G.k x / x))
          = fun _ : ℝ => (0 : ℝ≥0∞) := by
        funext x
        change ENNReal.ofReal ((1 - Real.cos (ω * x)) * (0 : ℝ) / x) = 0
        simp
      rw [hzz]
      simp [hG]
    have hL : ∀ ω, G.exponentL ω + Q.exponentL ω = P.exponentL ω := by
      intro ω
      rw [hGL ω, hQL ω, cin_superposition P ϖ htail ω, cinSuperpositionL, cinSuperpositionL]
      simp
    have hsplit : ∀ ω, G.exponent ω + Q.exponent ω = P.exponent ω := by
      intro ω
      rw [SDProfile.exponent, SDProfile.exponent, SDProfile.exponent, ← ENNReal.toReal_add
        (G.exponentL_ne_top ω) (Q.exponentL_ne_top ω), hL ω]
    obtain ⟨c₁, c₂, hc₁, -⟩ := hext G Q hsplit
    have h1 : ∀ ω : ℝ, P.a * ω ^ 2 = c₁ * P.exponent ω := by
      intro ω
      rw [← gaussianDatum_exponent P.a P.a_nonneg ω]
      exact hc₁ ω
    rcases eq_or_ne c₁ 0 with hc | hc
    · have := h1 1
      rw [hc, zero_mul, one_pow, mul_one] at this
      exact hane this
    · have hbe : ∀ ω : ℝ, P.exponent ω = (P.a / c₁) * ω ^ 2 := by
        intro ω
        field_simp
        linarith [h1 ω]
      have hbnn : 0 ≤ P.a / c₁ := by
        have := hbe 1
        rw [one_pow, mul_one] at this
        rw [← this]
        exact ENNReal.toReal_nonneg
      exact h0 (hzero_of_k (hk_of_gauss _ hbnn hbe))
  refine Or.inr ?_
  by_cases hsep : ∀ s : ℝ, 0 < s → ϖ (Ioc 0 s) ≠ 0 → ϖ (Ioi s) = 0
  · -- The Choquet measure is concentrated at a single point.
    set T := {s : ℝ | 0 < s ∧ ϖ (Ioc 0 s) ≠ 0} with hT
    have hTne : T.Nonempty := by
      by_contra hc
      rw [Set.not_nonempty_iff_eq_empty] at hc
      refine h0 ?_
      rw [← Measure.measure_univ_eq_zero]
      have hIoi0 : ϖ (Ioi (0 : ℝ)) = 0 := by
        rw [measure_Ioi_zero_eq_iSup]
        refine iSup_eq_bot.mpr fun n => ?_
        by_contra hne
        have : ((n : ℝ) + 1) ∈ T := ⟨by positivity, hne⟩
        rw [hc] at this
        exact this
      have : ϖ univ ≤ ϖ (Ioi (0 : ℝ)) + ϖ (Iic (0 : ℝ)) := by
        refine le_trans (measure_mono ?_) (measure_union_le _ _)
        intro z _
        rcases le_or_gt z 0 with hz | hz
        · exact Or.inr hz
        · exact Or.inl hz
      rw [hIoi0, hfold, add_zero] at this
      exact le_antisymm this (zero_le)
    have hbdd : BddBelow T := ⟨0, fun t ht => ht.1.le⟩
    set τ := sInf T with hτdef
    have hτ0 : 0 ≤ τ := le_csInf hTne fun t ht => ht.1.le
    have hIoi : ∀ s : ℝ, τ < s → ϖ (Ioi s) = 0 := by
      intro s hsτ
      obtain ⟨t, htT, hts⟩ := exists_lt_of_csInf_lt hTne hsτ
      exact measure_mono_null (Ioi_subset_Ioi hts.le) (hsep t htT.1 htT.2)
    have hIoiτ : ϖ (Ioi τ) = 0 := by
      rw [measure_Ioi_eq_iSup]
      refine iSup_eq_bot.mpr fun n => hIoi _ ?_
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    have hτpos : 0 < τ := by
      rcases hτ0.lt_or_eq with h | h
      · exact h
      · exfalso
        refine h0 ?_
        rw [← Measure.measure_univ_eq_zero]
        have hIoi0 : ϖ (Ioi (0 : ℝ)) = 0 := by rw [h]; exact hIoiτ
        have hu : ϖ univ ≤ ϖ (Ioi (0 : ℝ)) + ϖ (Iic (0 : ℝ)) := by
          refine le_trans (measure_mono ?_) (measure_union_le _ _)
          intro z _
          rcases le_or_gt z 0 with hz | hz
          · exact Or.inr hz
          · exact Or.inl hz
        rw [hIoi0, hfold, add_zero] at hu
        exact le_antisymm hu (zero_le)
    have hIoo : ϖ (Ioo 0 τ) = 0 := by
      have hmono : Monotone (fun n : ℕ => Ioc (0 : ℝ) (max (τ / 2) (τ - 1 / ((n : ℝ) + 1)))) := by
        intro p q hpq
        refine Ioc_subset_Ioc le_rfl (max_le_max le_rfl ?_)
        have hle : (1 : ℝ) / ((q : ℝ) + 1) ≤ 1 / ((p : ℝ) + 1) := by
          refine one_div_le_one_div_of_le (by positivity) ?_
          have : (p : ℝ) ≤ (q : ℝ) := by exact_mod_cast hpq
          linarith
        linarith
      have hlt : ∀ n : ℕ, max (τ / 2) (τ - 1 / ((n : ℝ) + 1)) < τ := by
        intro n
        have h1 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        exact max_lt (by linarith) (by linarith)
      have hgt : ∀ n : ℕ, 0 < max (τ / 2) (τ - 1 / ((n : ℝ) + 1)) :=
        fun n => lt_of_lt_of_le (by linarith) (le_max_left _ _)
      have hcover : (⋃ n : ℕ, Ioc (0 : ℝ) (max (τ / 2) (τ - 1 / ((n : ℝ) + 1)))) = Ioo 0 τ := by
        ext z
        simp only [mem_iUnion, mem_Ioc, mem_Ioo]
        constructor
        · rintro ⟨n, hz0, hzn⟩
          exact ⟨hz0, lt_of_le_of_lt hzn (hlt n)⟩
        · rintro ⟨hz0, hzτ⟩
          rcases le_or_gt z (τ / 2) with hz | hz
          · exact ⟨0, hz0, le_trans hz (le_max_left _ _)⟩
          · obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0 : ℝ) < τ - z by linarith)
            exact ⟨n, hz0, le_trans (by linarith) (le_max_right _ _)⟩
      rw [← hcover, hmono.measure_iUnion]
      refine iSup_eq_bot.mpr fun n => ?_
      by_contra hne
      have hmem : max (τ / 2) (τ - 1 / ((n : ℝ) + 1)) ∈ T := ⟨hgt n, hne⟩
      exact absurd (csInf_le hbdd hmem) (not_le.mpr (hlt n))
    have hcompl : ϖ ({τ}ᶜ) = 0 := by
      have hsub : ({τ}ᶜ : Set ℝ) ⊆ Iic 0 ∪ (Ioo 0 τ ∪ Ioi τ) := by
        intro z hz
        rcases le_or_gt z 0 with h1 | h1
        · exact Or.inl h1
        · rcases lt_trichotomy z τ with h2 | h2 | h2
          · exact Or.inr (Or.inl ⟨h1, h2⟩)
          · exact absurd h2 hz
          · exact Or.inr (Or.inr h2)
      refine le_antisymm ?_ (zero_le)
      calc ϖ ({τ}ᶜ) ≤ ϖ (Iic 0 ∪ (Ioo 0 τ ∪ Ioi τ)) := measure_mono hsub
        _ ≤ ϖ (Iic 0) + ϖ (Ioo 0 τ ∪ Ioi τ) := measure_union_le _ _
        _ ≤ ϖ (Iic 0) + (ϖ (Ioo 0 τ) + ϖ (Ioi τ)) :=
            add_le_add le_rfl (measure_union_le _ _)
        _ = 0 := by rw [hfold, hIoo, hIoiτ]; simp
    have hres : ϖ.restrict {τ} = ϖ := by
      refine Measure.restrict_eq_self_of_ae_mem ?_
      rw [ae_iff]
      exact hcompl
    have hmassfin : ϖ {τ} ≠ ⊤ :=
      ne_top_of_le_ne_top (hfin (τ / 2) (by linarith))
        (measure_mono (by intro z hz; simp only [mem_singleton_iff] at hz; simp [hz]; linarith))
    refine ⟨(ϖ {τ}).toReal, τ, ENNReal.toReal_nonneg, hτpos, fun ω => ?_⟩
    have hval : P.exponentL ω = ENNReal.ofReal (cin (τ * ω)) * ϖ {τ} := by
      rw [cin_superposition P ϖ htail ω, cinSuperpositionL, hPa]
      simp only [zero_mul, ENNReal.ofReal_zero, zero_add]
      conv_lhs => rw [← hres]
      rw [setLIntegral_congr_fun (measurableSet_singleton τ)
        (g := fun _ : ℝ => ENNReal.ofReal (cin (τ * ω))) ?_, setLIntegral_const]
      intro z hz
      simp only [mem_singleton_iff] at hz
      rw [hz]
    rw [SDProfile.exponent, hval, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (cin_nonneg' _), mul_comm]
  · -- The Choquet measure splits, and the splitting property is contradicted.
    exfalso
    push Not at hsep
    obtain ⟨s, hs, hs1, hs2⟩ := hsep
    have hIic₁ : (Iic (0 : ℝ)) ∩ Ioc 0 s = (∅ : Set ℝ) := by
      ext z; simp only [mem_inter_iff, mem_Iic, mem_Ioc, mem_empty_iff_false, iff_false]
      rintro ⟨h1, h2, -⟩; linarith
    have hIic₂ : (Iic (0 : ℝ)) ∩ Ioi s = (∅ : Set ℝ) := by
      ext z; simp only [mem_inter_iff, mem_Iic, mem_Ioi, mem_empty_iff_false, iff_false]
      rintro ⟨h1, h2⟩; linarith
    have hf₁ : IsFolded (ϖ.restrict (Ioc 0 s)) := by
      rw [IsFolded, Measure.restrict_apply measurableSet_Iic, hIic₁, measure_empty]
    have hf₂ : IsFolded (ϖ.restrict (Ioi s)) := by
      rw [IsFolded, Measure.restrict_apply measurableSet_Iic, hIic₂, measure_empty]
    have hdA : (∫⁻ t, ENNReal.ofReal (domainIntegrand t) ∂(ϖ.restrict (Ioc 0 s))) ≠ ⊤ :=
      ne_top_of_le_ne_top hdom' (lintegral_mono' Measure.restrict_le_self le_rfl)
    have hdB : (∫⁻ t, ENNReal.ofReal (domainIntegrand t) ∂(ϖ.restrict (Ioi s))) ≠ ⊤ :=
      ne_top_of_le_ne_top hdom' (lintegral_mono' Measure.restrict_le_self le_rfl)
    set P₁ := choquetSDProfile (le_refl (0 : ℝ)) (ϖ.restrict (Ioc 0 s)) hf₁ hdA with hP₁
    set P₂ := choquetSDProfile (le_refl (0 : ℝ)) (ϖ.restrict (Ioi s)) hf₂ hdB with hP₂
    have hP₁L : ∀ ω, P₁.exponentL ω = cinSuperpositionL 0 (ϖ.restrict (Ioc 0 s)) ω := fun ω =>
      cin_superposition P₁ _
        (hasProfileTail_choquetSDProfile (le_refl (0 : ℝ)) _ hf₁ hdA) ω
    have hP₂L : ∀ ω, P₂.exponentL ω = cinSuperpositionL 0 (ϖ.restrict (Ioi s)) ω := fun ω =>
      cin_superposition P₂ _
        (hasProfileTail_choquetSDProfile (le_refl (0 : ℝ)) _ hf₂ hdB) ω
    have hadd : ϖ.restrict (Ioc 0 s) + ϖ.restrict (Ioi s) = ϖ := by
      rw [← Measure.restrict_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi,
        Ioc_union_Ioi_eq_Ioi hs.le]
      refine Measure.restrict_eq_self_of_ae_mem ?_
      have hcomp : {a : ℝ | ¬ a ∈ Ioi (0 : ℝ)} = Iic 0 := by ext z; simp
      rw [ae_iff, hcomp]
      exact hfold
    have hLsum : ∀ ω, P₁.exponentL ω + P₂.exponentL ω = P.exponentL ω := by
      intro ω
      have hsplitint : (∫⁻ t, ENNReal.ofReal (cin (t * ω)) ∂ϖ)
          = (∫⁻ t, ENNReal.ofReal (cin (t * ω)) ∂(ϖ.restrict (Ioc 0 s)))
            + ∫⁻ t, ENNReal.ofReal (cin (t * ω)) ∂(ϖ.restrict (Ioi s)) := by
        rw [← lintegral_add_measure, hadd]
      rw [hP₁L ω, hP₂L ω, cin_superposition P ϖ htail ω, cinSuperpositionL, cinSuperpositionL,
        cinSuperpositionL, hPa, hsplitint]
      simp
    have hsplit : ∀ ω, P₁.exponent ω + P₂.exponent ω = P.exponent ω := by
      intro ω
      rw [SDProfile.exponent, SDProfile.exponent, SDProfile.exponent, ← ENNReal.toReal_add
        (P₁.exponentL_ne_top ω) (P₂.exponentL_ne_top ω), hLsum ω]
    obtain ⟨c₁, c₂, hc₁, -⟩ := hext P₁ P₂ hsplit
    have hPne : ∃ ω₀ : ℝ, 0 < P.exponent ω₀ := by
      by_contra hcon
      push Not at hcon
      have hz : ∀ ω : ℝ, P.exponent ω = 0 * ω ^ 2 := by
        intro ω
        have h1 : (0 : ℝ) ≤ P.exponent ω := ENNReal.toReal_nonneg
        have h2 := hcon ω
        rw [zero_mul]
        linarith
      exact h0 (hzero_of_k (hk_of_gauss 0 le_rfl hz))
    obtain ⟨ω₀, hω₀⟩ := hPne
    have hc₁nn : 0 ≤ c₁ := by
      have hp : (0 : ℝ) ≤ P₁.exponent ω₀ := ENNReal.toReal_nonneg
      rw [hc₁ ω₀] at hp
      nlinarith
    -- the scaled Choquet measure, and injectivity
    have hf' : IsFolded (ENNReal.ofReal c₁ • ϖ) := by
      rw [IsFolded, Measure.smul_apply, hfold]
      simp
    have hd' : (∫⁻ t, ENNReal.ofReal (domainIntegrand t) ∂(ENNReal.ofReal c₁ • ϖ)) ≠ ⊤ := by
      rw [lintegral_smul_measure]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hdom'
    have hEq : ∀ ω : ℝ, cinSuperpositionL 0 (ϖ.restrict (Ioc 0 s)) ω
        = cinSuperpositionL 0 (ENNReal.ofReal c₁ • ϖ) ω := by
      intro ω
      have hPL : P.exponentL ω = ∫⁻ t, ENNReal.ofReal (cin (t * ω)) ∂ϖ := by
        rw [cin_superposition P ϖ htail ω, cinSuperpositionL, hPa]
        simp
      have h1 : P₁.exponentL ω = ENNReal.ofReal c₁ * P.exponentL ω := by
        rw [← ENNReal.ofReal_toReal (P₁.exponentL_ne_top ω), ← SDProfile.exponent, hc₁ ω,
          ENNReal.ofReal_mul hc₁nn, SDProfile.exponent,
          ENNReal.ofReal_toReal (P.exponentL_ne_top ω)]
      rw [← hP₁L ω, h1, hPL, cinSuperpositionL, lintegral_smul_measure]
      simp
    obtain ⟨-, hmeas⟩ := choquet_cone_injective (le_refl (0 : ℝ)) (le_refl (0 : ℝ))
      (ϖ.restrict (Ioc 0 s)) (ENNReal.ofReal c₁ • ϖ) hf₁ hf' hdA hd' hEq
    have hzeroIoi : (ϖ.restrict (Ioc 0 s)) (Ioi s) = 0 := by
      rw [Measure.restrict_apply measurableSet_Ioi]
      convert measure_empty (μ := ϖ)
      ext z
      simp only [mem_inter_iff, mem_Ioi, mem_Ioc, mem_empty_iff_false, iff_false]
      rintro ⟨h1, -, h2⟩
      linarith
    rw [hmeas, Measure.smul_apply, smul_eq_mul] at hzeroIoi
    have hc₁z : c₁ = 0 := by
      rcases mul_eq_zero.mp hzeroIoi with hc | hc
      · exact le_antisymm (ENNReal.ofReal_eq_zero.mp hc) hc₁nn
      · exact absurd hc hs2
    rw [hc₁z, ENNReal.ofReal_zero, zero_smul] at hmeas
    have : ϖ (Ioc 0 s) = 0 := by
      have := congrArg (fun m : Measure ℝ => m univ) hmeas
      simpa [Measure.restrict_apply_univ] using this
    exact hs1 this

end SpatialLine
