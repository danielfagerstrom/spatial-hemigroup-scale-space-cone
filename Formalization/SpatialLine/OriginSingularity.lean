/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.TwoSidedProfile
import SpatialLine.AdmissibleCone
import SpatialLine.Interfaces

/-!
# `prop:cin-origin-singularity` and `cor:origin-boundedness`

Blueprint: `blueprint/src/parts/08-cone.tex`.

Ledger **A10** was admitted on 2026-09-15 (the author's decision) as the three axioms
`sato_origin_singular`, `sato_origin_smooth` and `sato_origin_threshold` of
`SpatialLine/Interfaces.lean`, stated at Sato's letter over a `TwoSidedProfile`. This file is
where the article consumes them.

* The three `cin_origin_singularity_*` theorems are `prop:cin-origin-singularity`'s three regimes
  in this article's folded convention. Each is one application of the corresponding
  `_of_sato` theorem of `SpatialLine/TwoSidedProfile.lean` — the folding translation, Lean core —
  to the corresponding axiom, so each spends exactly one name and the translation stays outside
  the trust boundary. They moved here from `Skeleton/Chapter8.lean`, at the signatures the
  reviewed skeleton gave them.
* `origin_boundedness` is `cor:origin-boundedness`(1): an admissible kernel with no Gaussian part
  is bounded at the origin exactly when its folded `k(0+)` exceeds `1`. It spends all three
  names, which is what made the admission the campaign's rule allows.

## What the corollary's proof adds to the three regimes

Two steps, and both are this article's rather than the source's.

*Above the threshold*, the integer `N` has to be produced: for finite `c > 1` it is
`⌈c⌉₊ − 1`, which is `≥ 1` and satisfies `N < c ≤ N+1`, and `C^{N−1}` with `N ≥ 1` gives
continuity.

*At and below the threshold* the regimes give **one** representative with a divergent lower
bound, and the statement is about **every** representative — the reading that makes "unbounded at
the origin" a statement about the kernel rather than about a choice of version (judgement point
3). The passage compares measures and not functions: if some representative were bounded by `M`
on the punctured `δ`-neighbourhood then `μ((0,ε)) ≤ Mε` for `ε ≤ δ`, while the regime's own lower
bound makes `μ((0,ε))` at least `c₁ m(ε) ε` with `m(ε)` a lower bound for the comparison function
on `(0,ε)` — `ε^{c−1}` below the threshold and `log(1/ε)` at it — and `c₁ m(ε) > M` for small
`ε`. Neither step needs measurability of the competing representative, `lintegral` being monotone
without it, and `withDensity_apply` asking only that the *set* be measurable.

Below the threshold the comparison function is `|x|^{c−1}K(x)` and not `|x|^{c−1}` (2026-09-19,
R171: the factor `K` of Sato's (53.25) was missing from the axiom, which made it false). What the
corollary reads off `K` is the lower bound `K ≥ 1` alone (`one_le_satoK`), which follows from
`k ≤ c` on `(0,∞)`; `K` is slowly varying at the origin and need not be bounded above, so no upper
bound on it is used anywhere.

At the threshold the lower bound `L(x) ≥ log(1/|x|)` is proved here and is not cited: `k` is
nonincreasing with `k(0+) = 1`, so `k ≤ 1` on `(0,∞)`, the inner integrand `(1 − k(u))u^{−1}` is
nonnegative, `K ≥ 1`, and `L(x) ≥ ∫_{|x|}^1 y^{−1}dy`. The comparison of the two integrals needs
the integrand of `L` to be integrable on `(|x|,1)`, which is where the antitonicity of `K` is
spent: `K(y)/y ≤ K(|x|)/|x|` there, and `K` is antitone because its exponent is an integral of a
nonnegative function over the shrinking window `(y,1)`.
-/

namespace SpatialLine

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-! ## `prop:cin-origin-singularity`: the three regimes, in the folded convention -/

/-- **`prop:cin-origin-singularity`, the singular regime `c < 1`** — `[A]`, ledger **A10**
through `sato_origin_singular`.

The comparability is two-sided on a punctured neighbourhood of the origin, with the constants and
the neighbourhood existential; "unbounded" is a consequence of it for `c < 1` and is not stated
separately. The density is produced by the statement rather than quantified over (review R17): a
pointwise bound on an arbitrary representative is not a statement about the density.

**The comparison function is `|x|^{c−1}K(x)`**, with the slowly varying
`K(x) = exp[∫_{|x|}^1 (c − k(u))u⁻¹du]` of Sato's (53.25) (2026-09-19, R171: the factor was
missing here and in the axiom, and without it both were false — `K` is slowly varying at the
origin but need not be bounded). It satisfies `K ≥ 1` on `(0,1)`, because `k ≤ c` there, and that
is the only property `origin_boundedness` below reads off it.

Moved here from `Skeleton.cin_origin_singularity_unbounded` on 2026-09-15, at that signature. -/
theorem cin_origin_singularity_unbounded (P : SDProfile) (ha : P.a = 0) {c : ℝ}
    (hc0 : 0 < c) (hc1 : c < 1) (hk : Tendsto P.k (𝓝[>] 0) (𝓝 c))
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hsym : IsSymmetric μ)
    (hcos : ∀ ω : ℝ, fourierCos μ ω = Real.exp (-P.exponent ω)) :
    ∃ p : ℝ → ℝ, μ = volume.withDensity (fun x => ENNReal.ofReal (p x)) ∧
      ∃ c₁ c₂ δ : ℝ, 0 < c₁ ∧ c₁ ≤ c₂ ∧ 0 < δ ∧
        ∀ x : ℝ, 0 < |x| → |x| < δ →
          c₁ * (|x| ^ (c - 1) * Real.exp (∫ u in Ioo |x| 1, (c - P.k u) / u)) ≤ p x ∧
            p x ≤ c₂ * (|x| ^ (c - 1) * Real.exp (∫ u in Ioo |x| 1, (c - P.k u) / u)) :=
  cin_origin_singularity_unbounded_of_sato sato_origin_singular P ha hc0 hc1 hk μ hsym hcos

/-- **`prop:cin-origin-singularity`, the smooth regime `N < c ≤ N+1`** — `[A]`, ledger **A10**
through `sato_origin_smooth`.

"Extends continuously and has `N−1` derivatives" is read as: the density has a representative of
class `C^{N−1}` on the whole line, the representative being existential.

Moved here from `Skeleton.cin_origin_singularity_smooth` on 2026-09-15, at that signature. -/
theorem cin_origin_singularity_smooth (P : SDProfile) (ha : P.a = 0) {c : ℝ} {N : ℕ}
    (hN : 1 ≤ N) (hcN : (N : ℝ) < c) (hcN' : c ≤ N + 1) (hk : Tendsto P.k (𝓝[>] 0) (𝓝 c))
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hsym : IsSymmetric μ)
    (hcos : ∀ ω : ℝ, fourierCos μ ω = Real.exp (-P.exponent ω)) :
    ∃ p : ℝ → ℝ, μ = volume.withDensity (fun x => ENNReal.ofReal (p x)) ∧
      ContDiff ℝ (((N - 1 : ℕ) : ℕ∞) : WithTop ℕ∞) p :=
  cin_origin_singularity_smooth_of_sato sato_origin_smooth P ha hN hcN hcN' hk μ hsym hcos

/-- **`prop:cin-origin-singularity`, the threshold `c = 1`** — `[A]`, ledger **A10** through
`sato_origin_threshold`.

The comparison function is the node's `L`, with its inner `K`, written out in the statement
rather than named, since they occur nowhere else. The node claims the order and not the constant.

Moved here from `Skeleton.cin_origin_singularity_threshold` on 2026-09-15, at that signature. -/
theorem cin_origin_singularity_threshold (P : SDProfile) (ha : P.a = 0)
    (hk : Tendsto P.k (𝓝[>] 0) (𝓝 1)) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hsym : IsSymmetric μ)
    (hcos : ∀ ω : ℝ, fourierCos μ ω = Real.exp (-P.exponent ω)) :
    ∃ p : ℝ → ℝ, μ = volume.withDensity (fun x => ENNReal.ofReal (p x)) ∧
      ∃ c₁ c₂ δ : ℝ, 0 < c₁ ∧ c₁ ≤ c₂ ∧ 0 < δ ∧
        ∀ x : ℝ, 0 < |x| → |x| < δ →
          c₁ * (∫ y in Ioo |x| 1, Real.exp (∫ u in Ioo y 1, (1 - P.k u) / u) / y) ≤ p x ∧
            p x ≤ c₂ * ∫ y in Ioo |x| 1, Real.exp (∫ u in Ioo y 1, (1 - P.k u) / u) / y :=
  cin_origin_singularity_threshold_of_sato sato_origin_threshold P ha hk μ hsym hcos

/-! ## The two steps the corollary adds to the three regimes -/

/-- **A profile is bounded by its right limit**: `k` is nonincreasing on `(0,∞)` with
`k(0+) = c`, so `k ≤ c` there. At the threshold this is `k ≤ 1`, which is what makes the
comparison function of the threshold regime diverge. -/
theorem SDProfile.k_le_of_tendsto_nhdsGT (P : SDProfile) {c : ℝ}
    (hk : Tendsto P.k (𝓝[>] (0 : ℝ)) (𝓝 c)) {x : ℝ} (hx : 0 < x) : P.k x ≤ c := by
  refine ge_of_tendsto hk ?_
  filter_upwards [Ioo_mem_nhdsGT hx] with u hu
  exact P.k_antitone (mem_Ioi.mpr hu.1) (mem_Ioi.mpr hx) hu.2.le

/-- **Sato's factor `K` is at least `1`**: `k ≤ c` on `(0,∞)`, so the inner integrand
`(c − k(u))u⁻¹` is nonnegative and its integral over `(y,1)` is nonnegative. This is all that
either regime's lower bound needs of `K` (2026-09-19, R171) — the factor is slowly varying and
need not be bounded above, so nothing here reads an upper bound on it. -/
theorem one_le_satoK (P : SDProfile) {c : ℝ} (hkc : ∀ u : ℝ, 0 < u → P.k u ≤ c) {y : ℝ}
    (hy : 0 < y) : 1 ≤ Real.exp (∫ u in Ioo y 1, (c - P.k u) / u) := by
  have hnn : 0 ≤ ∫ u in Ioo y 1, (c - P.k u) / u := by
    refine setIntegral_nonneg measurableSet_Ioo fun u hu => ?_
    have hu0 : 0 < u := lt_trans hy hu.1
    exact div_nonneg (by linarith [hkc u hu0]) hu0.le
  simpa using Real.exp_le_exp.mpr hnn

/-- **The upper half of the comparison of measures.** A representative bounded by `M` on
`(0,ε)` gives the law of that interval at most `Mε`. The representative need not be measurable:
`withDensity_apply` asks only that the *set* be measurable, and `lintegral_mono_ae` is monotone
without it. -/
theorem measure_Ioo_le_of_density_le {μ : Measure ℝ} {p : ℝ → ℝ}
    (hp : μ = volume.withDensity fun x => ENNReal.ofReal (p x)) {M ε : ℝ}
    (hbdd : ∀ x : ℝ, 0 < x → x < ε → p x ≤ M) :
    μ (Ioo 0 ε) ≤ ENNReal.ofReal M * ENNReal.ofReal ε := by
  rw [hp, withDensity_apply _ measurableSet_Ioo]
  have hmono : (∫⁻ x in Ioo (0 : ℝ) ε, ENNReal.ofReal (p x))
      ≤ ∫⁻ _ in Ioo (0 : ℝ) ε, ENNReal.ofReal M := by
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact ENNReal.ofReal_le_ofReal (hbdd x hx.1 hx.2)
  refine hmono.trans ?_
  rw [setLIntegral_const, Real.volume_Ioo, sub_zero]

/-- **The lower half of the same comparison.** A representative at least `m` on `(0,ε)` gives the
law of that interval at least `mε`. -/
theorem le_measure_Ioo_of_le_density {μ : Measure ℝ} {p : ℝ → ℝ}
    (hp : μ = volume.withDensity fun x => ENNReal.ofReal (p x)) {m ε : ℝ}
    (hlow : ∀ x : ℝ, 0 < x → x < ε → m ≤ p x) :
    ENNReal.ofReal m * ENNReal.ofReal ε ≤ μ (Ioo 0 ε) := by
  rw [hp, withDensity_apply _ measurableSet_Ioo]
  have hmono : (∫⁻ _ in Ioo (0 : ℝ) ε, ENNReal.ofReal m)
      ≤ ∫⁻ x in Ioo (0 : ℝ) ε, ENNReal.ofReal (p x) := by
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact ENNReal.ofReal_le_ofReal (hlow x hx.1 hx.2)
  refine le_trans ?_ hmono
  rw [setLIntegral_const, Real.volume_Ioo, sub_zero]

/-- **Two representatives of one law cannot straddle a constant on an interval.** This is the
passage from *one* unbounded representative to *every* representative: the two bounds are
compared as measures of `(0,ε)`, not as functions. -/
theorem not_le_of_le_density {μ : Measure ℝ} {p q : ℝ → ℝ}
    (hp : μ = volume.withDensity fun x => ENNReal.ofReal (p x))
    (hq : μ = volume.withDensity fun x => ENNReal.ofReal (q x))
    {M m ε : ℝ} (hε : 0 < ε) (hm : 0 < m) (hMm : M < m)
    (hbdd : ∀ x : ℝ, 0 < x → x < ε → p x ≤ M)
    (hlow : ∀ x : ℝ, 0 < x → x < ε → m ≤ q x) : False := by
  have h1 : ENNReal.ofReal m * ENNReal.ofReal ε ≤ ENNReal.ofReal M * ENNReal.ofReal ε :=
    le_trans (le_measure_Ioo_of_le_density hq hlow) (measure_Ioo_le_of_density_le hp hbdd)
  have h2 : ENNReal.ofReal M * ENNReal.ofReal ε < ENNReal.ofReal m * ENNReal.ofReal ε :=
    ENNReal.mul_lt_mul_left (ENNReal.ofReal_pos.mpr hε).ne' ENNReal.ofReal_ne_top
      ((ENNReal.ofReal_lt_ofReal_iff hm).mpr hMm)
  exact absurd h1 (not_le.mpr h2)

/-! ### The comparison function at the threshold diverges

The threshold regime compares the density to `L(x) = ∫_{|x|}^1 K(y)y^{−1}dy` with
`K(y) = exp∫_y^1 (1 − k(u))u^{−1}du`, and says nothing about the size of `L`. That `L(x)` is at
least `log(1/|x|)` is proved here, from the profile's own monotonicity, and it is the argument
row R100 wrote down in prose: `k` is nonincreasing with `k(0+) = 1`, so `k ≤ 1`, the inner
integrand is nonnegative, `K ≥ 1`, and `L` dominates `∫_{|x|}^1 y^{−1}dy`. -/

/-- The inner integrand is nonnegative where the profile is at most `1`. -/
theorem thresholdIntegrand_nonneg (P : SDProfile) (hk1 : ∀ u : ℝ, 0 < u → P.k u ≤ 1) {u : ℝ}
    (hu : 0 < u) : 0 ≤ (1 - P.k u) / u :=
  div_nonneg (by linarith [hk1 u hu]) hu.le

/-- The inner integrand is integrable on `(y,1)` for `y > 0`: it is measurable, the profile being
antitone, and bounded there by `y⁻¹`. -/
theorem integrableOn_thresholdIntegrand (P : SDProfile) (hk1 : ∀ u : ℝ, 0 < u → P.k u ≤ 1)
    {y : ℝ} (hy : 0 < y) : IntegrableOn (fun u => (1 - P.k u) / u) (Ioo y 1) := by
  have hfin : volume (Ioo y (1 : ℝ)) ≠ ⊤ := by
    rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
  have hsub : Ioo y (1 : ℝ) ⊆ Ioi 0 := fun u hu => mem_Ioi.mpr (lt_trans hy hu.1)
  have hmeas : AEMeasurable (fun u : ℝ => (1 - P.k u) / u) (volume.restrict (Ioo y 1)) :=
    (aemeasurable_const.sub (P.aemeasurable_k_mono hsub)).div aemeasurable_id
  refine Integrable.mono' (g := fun _ : ℝ => 1 / y) (integrableOn_const (hs := hfin))
    hmeas.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
  have hu0 : 0 < u := lt_trans hy hu.1
  have hk0 : 0 ≤ P.k u := P.k_nonneg u (mem_Ioi.mpr hu0)
  rw [Real.norm_eq_abs, abs_of_nonneg (thresholdIntegrand_nonneg P hk1 hu0), div_le_div_iff₀ hu0 hy]
  nlinarith [hu.1.le, hy.le]

/-- The inner integral is nonnegative. -/
theorem thresholdExponent_nonneg (P : SDProfile) (hk1 : ∀ u : ℝ, 0 < u → P.k u ≤ 1) {y : ℝ}
    (hy : 0 < y) : 0 ≤ ∫ u in Ioo y 1, (1 - P.k u) / u :=
  setIntegral_nonneg measurableSet_Ioo fun _ hu =>
    thresholdIntegrand_nonneg P hk1 (lt_trans hy hu.1)

/-- The inner integral is antitone in its lower limit: the window `(y,1)` shrinks as `y` grows
and the integrand is nonnegative. -/
theorem thresholdExponent_antitone (P : SDProfile) (hk1 : ∀ u : ℝ, 0 < u → P.k u ≤ 1) {y z : ℝ}
    (hy : 0 < y) (hyz : y ≤ z) :
    (∫ u in Ioo z 1, (1 - P.k u) / u) ≤ ∫ u in Ioo y 1, (1 - P.k u) / u := by
  refine setIntegral_mono_set (integrableOn_thresholdIntegrand P hk1 hy) ?_ ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    exact thresholdIntegrand_nonneg P hk1 (lt_trans hy hu.1)
  · exact HasSubset.Subset.eventuallyLE (Ioo_subset_Ioo hyz le_rfl)

/-- The outer integrand is integrable on `(x,1)` for `x > 0`: `K` is antitone, so `K(y)/y` is
bounded there by `K(x)/x`, and it is measurable because an antitone function is. -/
theorem integrableOn_thresholdComparison (P : SDProfile) (hk1 : ∀ u : ℝ, 0 < u → P.k u ≤ 1)
    {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun y => Real.exp (∫ u in Ioo y 1, (1 - P.k u) / u) / y) (Ioo x 1) := by
  have hfin : volume (Ioo x (1 : ℝ)) ≠ ⊤ := by
    rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
  have hanti : AntitoneOn (fun y : ℝ => ∫ u in Ioo y 1, (1 - P.k u) / u) (Ioi 0) :=
    fun _ ha _ _ hab => thresholdExponent_antitone P hk1 ha hab
  have hmeas : AEMeasurable (fun y : ℝ => ∫ u in Ioo y 1, (1 - P.k u) / u)
      (volume.restrict (Ioo x 1)) :=
    (aemeasurable_restrict_of_antitoneOn measurableSet_Ioi hanti).mono_measure
      (Measure.restrict_mono (fun y hy => mem_Ioi.mpr (lt_trans hx hy.1)) le_rfl)
  refine Integrable.mono' (g := fun _ : ℝ => Real.exp (∫ u in Ioo x 1, (1 - P.k u) / u) / x)
    (integrableOn_const (hs := hfin))
    ((Real.continuous_exp.measurable.comp_aemeasurable hmeas).div
      aemeasurable_id).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
  have hy0 : 0 < y := lt_trans hx hy.1
  have hexp : Real.exp (∫ u in Ioo y 1, (1 - P.k u) / u)
      ≤ Real.exp (∫ u in Ioo x 1, (1 - P.k u) / u) :=
    Real.exp_le_exp.mpr (thresholdExponent_antitone P hk1 hx hy.1.le)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_le_div_iff₀ hy0 hx]
  nlinarith [Real.exp_pos (∫ u in Ioo y 1, (1 - P.k u) / u),
    Real.exp_pos (∫ u in Ioo x 1, (1 - P.k u) / u), hy.1.le, hx.le]

/-- **The comparison function of the threshold regime is at least `log(1/x)`.** -/
theorem log_le_thresholdComparison (P : SDProfile) (hk1 : ∀ u : ℝ, 0 < u → P.k u ≤ 1) {x : ℝ}
    (hx : 0 < x) (hx1 : x < 1) :
    Real.log (1 / x) ≤ ∫ y in Ioo x 1, Real.exp (∫ u in Ioo y 1, (1 - P.k u) / u) / y := by
  have hfin : volume (Ioo x (1 : ℝ)) ≠ ⊤ := by
    rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
  have hinv : IntegrableOn (fun y : ℝ => y⁻¹) (Ioo x 1) := by
    refine Integrable.mono' (g := fun _ : ℝ => x⁻¹) (integrableOn_const (hs := hfin))
      measurable_inv.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    have hy0 : 0 < y := lt_trans hx hy.1
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [inv_eq_one_div, inv_eq_one_div]
    exact one_div_le_one_div_of_le hx hy.1.le
  have hval : (∫ y in Ioo x 1, y⁻¹) = Real.log (1 / x) := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hx1.le,
      integral_inv_of_pos hx zero_lt_one]
  rw [← hval]
  refine setIntegral_mono_on hinv (integrableOn_thresholdComparison P hk1 hx)
    measurableSet_Ioo fun y hy => ?_
  have hy0 : 0 < y := lt_trans hx hy.1
  have h1 : (1 : ℝ) ≤ Real.exp (∫ u in Ioo y 1, (1 - P.k u) / u) := by
    have := Real.exp_le_exp.mpr (thresholdExponent_nonneg P hk1 hy0)
    simpa using this
  rw [inv_eq_one_div, div_le_div_iff₀ hy0 hy0]
  nlinarith [hy0]

/-! ## `cor:origin-boundedness`(1): the boundedness threshold -/

/-- **`cor:origin-boundedness`(1)** — `[A]`, ledger **A10** at all three of its regimes.

An admissible kernel with no Gaussian part is bounded at the origin exactly when its folded
`k(0+)` exceeds `1`. Above the threshold the claim is that *some* representative is continuous,
which is the only form a density admits; at and below it the claim is about *every*
representative, which is what makes "unbounded at the origin" a statement about the kernel and
not about a choice of version.

Moved here from `Skeleton.origin_boundedness` on 2026-09-15 and proved, at that signature. -/
theorem origin_boundedness (P : SDProfile) (ha : P.a = 0) {c : ℝ} (hc0 : 0 < c)
    (hk : Tendsto P.k (𝓝[>] 0) (𝓝 c))
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hsym : IsSymmetric μ)
    (hcos : ∀ ω : ℝ, fourierCos μ ω = Real.exp (-P.exponent ω)) :
    (1 < c → ∃ p : ℝ → ℝ, μ = volume.withDensity (fun x => ENNReal.ofReal (p x)) ∧
        Continuous p) ∧
      (c ≤ 1 → ∀ p : ℝ → ℝ, μ = volume.withDensity (fun x => ENNReal.ofReal (p x)) →
        ∀ δ : ℝ, 0 < δ → ∀ M : ℝ, ∃ x : ℝ, 0 < |x| ∧ |x| < δ ∧ M < p x) := by
  constructor
  · -- Above the threshold: the smooth regime at `N = ⌈c⌉₊ − 1`.
    intro hc1
    have hceil : 1 < ⌈c⌉₊ := Nat.lt_ceil.mpr (by exact_mod_cast hc1)
    have hcast : ((⌈c⌉₊ - 1 : ℕ) : ℝ) = (⌈c⌉₊ : ℝ) - 1 := by
      rw [Nat.cast_sub hceil.le, Nat.cast_one]
    obtain ⟨p, hp, hcd⟩ :=
      cin_origin_singularity_smooth P ha (N := ⌈c⌉₊ - 1) (by omega)
        (by rw [hcast]; linarith [Nat.ceil_lt_add_one hc0.le])
        (by rw [hcast]; linarith [Nat.le_ceil c]) hk μ hsym hcos
    exact ⟨p, hp, hcd.continuous⟩
  · -- At and below it: a divergent lower bound, carried to every representative.
    intro hc1 p hp δ hδ M
    by_contra hcon
    push_neg at hcon
    have hbdd : ∀ x : ℝ, 0 < x → x < δ → p x ≤ M := fun x hx hxδ =>
      hcon x (by rwa [abs_of_pos hx]) (by rwa [abs_of_pos hx])
    rcases lt_or_eq_of_le hc1 with hlt | heq
    · -- `c < 1`: the singular regime, whose lower bound `c₁|x|^{c−1}` is antitone.
      obtain ⟨q, hq, c₁, c₂, δ₀, hc₁, -, hδ₀, hbound⟩ :=
        cin_origin_singularity_unbounded P ha hc0 hlt hk μ hsym hcos
      have hten : Tendsto (fun ε : ℝ => c₁ * ε ^ (c - 1)) (𝓝[>] (0 : ℝ)) atTop := by
        have h1 : Tendsto (fun z : ℝ => z ^ (1 - c)) atTop atTop :=
          tendsto_rpow_atTop (by linarith)
        have h2 : Tendsto (fun ε : ℝ => (ε⁻¹) ^ (1 - c)) (𝓝[>] (0 : ℝ)) atTop :=
          h1.comp tendsto_inv_nhdsGT_zero
        have h3 : Tendsto (fun ε : ℝ => ε ^ (c - 1)) (𝓝[>] (0 : ℝ)) atTop := by
          refine h2.congr' ?_
          filter_upwards [self_mem_nhdsWithin] with ε hε
          have hε0 : (0 : ℝ) < ε := hε
          rw [Real.inv_rpow hε0.le, ← Real.rpow_neg hε0.le, neg_sub]
        exact Tendsto.const_mul_atTop hc₁ h3
      obtain ⟨ε, hεM, hεmem⟩ := ((hten.eventually_gt_atTop (max M 0)).and
        (Ioo_mem_nhdsGT (lt_min hδ hδ₀))).exists
      have hε0 : 0 < ε := hεmem.1
      have hεδ : ε < δ := lt_of_lt_of_le hεmem.2 (min_le_left _ _)
      have hεδ₀ : ε < δ₀ := lt_of_lt_of_le hεmem.2 (min_le_right _ _)
      refine not_le_of_le_density hp hq hε0 (lt_of_le_of_lt (le_max_right M 0) hεM)
        (lt_of_le_of_lt (le_max_left M 0) hεM) (fun x hx hxε => hbdd x hx (lt_trans hxε hεδ))
        (fun x hx hxε => ?_)
      have hxb := (hbound x (by rwa [abs_of_pos hx]) (by
        rw [abs_of_pos hx]; exact lt_trans hxε hεδ₀)).1
      rw [abs_of_pos hx] at hxb
      refine le_trans ?_ hxb
      have hmono : ε ^ (c - 1) ≤ x ^ (c - 1) := by
        have h1 : x ^ (1 - c) ≤ ε ^ (1 - c) := Real.rpow_le_rpow hx.le hxε.le (by linarith)
        have h2 : (ε ^ (1 - c))⁻¹ ≤ (x ^ (1 - c))⁻¹ := by
          rw [inv_eq_one_div, inv_eq_one_div]
          exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos hx _) h1
        rwa [← Real.rpow_neg hx.le, ← Real.rpow_neg hε0.le, neg_sub] at h2
      -- The comparison function is `x^{c−1}K(x)`, and `K ≥ 1` because `k ≤ c` on `(0,∞)`.
      have hK : 1 ≤ Real.exp (∫ u in Ioo x 1, (c - P.k u) / u) :=
        one_le_satoK P (fun u hu => P.k_le_of_tendsto_nhdsGT hk hu) hx
      have hxpos : (0 : ℝ) ≤ x ^ (c - 1) := (Real.rpow_pos_of_pos hx _).le
      refine mul_le_mul_of_nonneg_left ?_ hc₁.le
      nlinarith [hmono, mul_nonneg hxpos (sub_nonneg.mpr hK)]
    · -- `c = 1`: the threshold regime, whose comparison function dominates `log(1/x)`.
      subst heq
      obtain ⟨q, hq, c₁, c₂, δ₀, hc₁, -, hδ₀, hbound⟩ :=
        cin_origin_singularity_threshold P ha hk μ hsym hcos
      have hk1 : ∀ u : ℝ, 0 < u → P.k u ≤ 1 := fun u hu => P.k_le_of_tendsto_nhdsGT hk hu
      have hten : Tendsto (fun ε : ℝ => c₁ * Real.log (1 / ε)) (𝓝[>] (0 : ℝ)) atTop := by
        have h1 : Tendsto (fun ε : ℝ => Real.log (1 / ε)) (𝓝[>] (0 : ℝ)) atTop := by
          refine (tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero).congr fun ε => ?_
          simp [one_div, Real.log_inv]
        exact Tendsto.const_mul_atTop hc₁ h1
      obtain ⟨ε, hεM, hεmem⟩ := ((hten.eventually_gt_atTop (max M 0)).and
        (Ioo_mem_nhdsGT (lt_min (lt_min hδ hδ₀) zero_lt_one))).exists
      have hε0 : 0 < ε := hεmem.1
      have hεδ : ε < δ := lt_of_lt_of_le hεmem.2 (le_trans (min_le_left _ _) (min_le_left _ _))
      have hεδ₀ : ε < δ₀ := lt_of_lt_of_le hεmem.2 (le_trans (min_le_left _ _) (min_le_right _ _))
      have hε1 : ε < 1 := lt_of_lt_of_le hεmem.2 (min_le_right _ _)
      refine not_le_of_le_density hp hq hε0 (lt_of_le_of_lt (le_max_right M 0) hεM)
        (lt_of_le_of_lt (le_max_left M 0) hεM) (fun x hx hxε => hbdd x hx (lt_trans hxε hεδ))
        (fun x hx hxε => ?_)
      have hxb := (hbound x (by rwa [abs_of_pos hx]) (by
        rw [abs_of_pos hx]; exact lt_trans hxε hεδ₀)).1
      rw [abs_of_pos hx] at hxb
      refine le_trans ?_ hxb
      have hlog : Real.log (1 / ε) ≤ Real.log (1 / x) := by
        refine Real.log_le_log (by positivity) ?_
        exact one_div_le_one_div_of_le hx hxε.le
      refine mul_le_mul_of_nonneg_left (le_trans hlog ?_) hc₁.le
      exact log_le_thresholdComparison P hk1 hx (lt_trans hxε hε1)

end SpatialLine
