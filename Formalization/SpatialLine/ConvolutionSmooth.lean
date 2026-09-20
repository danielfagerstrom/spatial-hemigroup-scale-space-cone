/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.Generator
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

/-!
# Differentiating a convolution by a finite measure, and the second-derivative test

Blueprint: `blueprint/src/parts/13-noncreation.tex`, `thm:non-enhancement`(2) and (3). Nothing
here is a blueprint node.

## Why the chapter needs this

`thm:non-enhancement`(2) reads: at a global maximum, `u_{xx}(t,x_0) \le 0`; clause (3) reads the
same at a local maximum. The generator's first term is `2at\,\partial_x^2u`, written in Lean as
`iteratedDeriv 2`, and `iteratedDeriv` returns junk where the function is not twice
differentiable — so *neither clause is true as stated* unless the scale space is genuinely twice
differentiable. It is, and the reason is not the kernel but the signal: `u(t,\cdot) = \mu * f`
with `f` in `\mathcal{D}` inherits the derivatives of `f`, because differentiation passes under
an integral against a **finite** measure with a constant dominating function. The scale space's
own regularity (`prop:kernel-regularity`) is not needed and is not used.

That is `hasDerivAt_mconv` below, and `iteratedDeriv_two_mconv` is the two-fold application of it
that the chapter consumes: the second derivative of `\mu * f` is `\mu * f''`.

## The second-derivative test

Mathlib has `IsLocalMax.hasDerivAt_eq_zero` and no second-derivative test, so
`le_zero_of_isLocalMax_of_hasDerivAt` is proved here from the mean value theorem: if the second
derivative at a local maximum were positive, the first derivative would be positive throughout a
right neighbourhood, and the mean value theorem would then place a point of that neighbourhood
strictly above the value at the maximum.
-/

namespace SpatialLine

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-! ## Differentiating under a finite measure -/

/-- **Differentiation under the convolution.** For a differentiable `f` that is bounded and has a
continuous bounded derivative, `\mu * f` is differentiable with derivative `\mu * f'`, for every
finite measure `\mu`.

The dominating function is the constant `C`, integrable because `\mu` is finite; that is the
whole proof, and it is why no decay of `f` is needed beyond boundedness. -/
theorem hasDerivAt_mconv {μ : Measure ℝ} [IsFiniteMeasure μ] {f f' : ℝ → ℝ}
    (hf : Continuous f) (hf' : Continuous f') {C₀ C : ℝ} (hC₀ : ∀ x, |f x| ≤ C₀)
    (hC : ∀ x, |f' x| ≤ C) (hd : ∀ x, HasDerivAt f (f' x) x) (x : ℝ) :
    HasDerivAt (mconv μ f) (mconv μ f' x) x := by
  have hmeas : ∀ z : ℝ, AEStronglyMeasurable (fun y => f (z - y)) μ := fun z =>
    (hf.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  have hmeas' : ∀ z : ℝ, AEStronglyMeasurable (fun y => f' (z - y)) μ := fun z =>
    (hf'.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  have hint : Integrable (fun y => f (x - y)) μ :=
    Integrable.mono' (integrable_const C₀) (hmeas x)
      (.of_forall fun y => by simpa [Real.norm_eq_abs] using hC₀ (x - y))
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun z y => f (z - y)) (F' := fun z y => f' (z - y)) (x₀ := x)
    (bound := fun _ => C) (s := univ) univ_mem
    (.of_forall fun z => hmeas z) hint (hmeas' x)
    (.of_forall fun y z _ => by simpa [Real.norm_eq_abs] using hC (z - y))
    (integrable_const C) (.of_forall fun y z _ => (hd (z - y)).comp_sub_const z y)
  exact key.2

/-- The derivative of a convolution, as a function. -/
theorem deriv_mconv {μ : Measure ℝ} [IsFiniteMeasure μ] {f f' : ℝ → ℝ}
    (hf : Continuous f) (hf' : Continuous f') {C₀ C : ℝ} (hC₀ : ∀ x, |f x| ≤ C₀)
    (hC : ∀ x, |f' x| ≤ C) (hd : ∀ x, HasDerivAt f (f' x) x) :
    deriv (mconv μ f) = mconv μ f' :=
  funext fun x => (hasDerivAt_mconv hf hf' hC₀ hC hd x).deriv

/-! ## The Schwartz case -/

/-- A Schwartz function on the line is bounded. -/
theorem SignalClass.exists_bound (f : SignalClass) : ∃ C : ℝ, ∀ x, |f x| ≤ C :=
  ⟨SchwartzMap.seminorm ℝ 0 0 f, fun x => by
    simpa [Real.norm_eq_abs] using SchwartzMap.norm_le_seminorm ℝ f x⟩

/-- The derivative of a Schwartz function, as a Schwartz function. -/
theorem SignalClass.deriv_eq (f : SignalClass) :
    deriv (⇑f) = ⇑(SchwartzMap.derivCLM ℝ (F := ℝ) f) :=
  funext fun x => (SchwartzMap.derivCLM_apply ℝ (F := ℝ) f x).symm

theorem SignalClass.hasDerivAt (f : SignalClass) (x : ℝ) :
    HasDerivAt (⇑f) (SchwartzMap.derivCLM ℝ (F := ℝ) f x) x := by
  rw [SchwartzMap.derivCLM_apply]
  exact ((f.smooth 1).differentiable (by norm_num) x).hasDerivAt

/-- The first derivative of the scale space of a test signal. -/
theorem deriv_mconv_signal (μ : Measure ℝ) [IsFiniteMeasure μ] (f : SignalClass) :
    deriv (mconv μ (⇑f)) = mconv μ (⇑(SchwartzMap.derivCLM ℝ (F := ℝ) f)) := by
  obtain ⟨C₀, hC₀⟩ := SignalClass.exists_bound f
  obtain ⟨C, hC⟩ := SignalClass.exists_bound (SchwartzMap.derivCLM ℝ (F := ℝ) f)
  exact deriv_mconv f.continuous (SchwartzMap.derivCLM ℝ (F := ℝ) f).continuous hC₀ hC
    (fun x => SignalClass.hasDerivAt f x)

/-- The scale space of a test signal is differentiable. -/
theorem differentiable_mconv_signal (μ : Measure ℝ) [IsFiniteMeasure μ] (f : SignalClass) :
    Differentiable ℝ (mconv μ (⇑f)) := by
  obtain ⟨C₀, hC₀⟩ := SignalClass.exists_bound f
  obtain ⟨C, hC⟩ := SignalClass.exists_bound (SchwartzMap.derivCLM ℝ (F := ℝ) f)
  exact fun x => (hasDerivAt_mconv f.continuous
    (SchwartzMap.derivCLM ℝ (F := ℝ) f).continuous hC₀ hC
    (fun y => SignalClass.hasDerivAt f y) x).differentiableAt

/-- **The second derivative of the scale space of a test signal is the smoothing of the signal's
second derivative**, which is what `thm:non-enhancement` consumes. -/
theorem iteratedDeriv_two_mconv (μ : Measure ℝ) [IsFiniteMeasure μ] (f : SignalClass) :
    iteratedDeriv 2 (mconv μ (⇑f)) = mconv μ (iteratedDeriv 2 (⇑f)) := by
  have h2 : ∀ g : ℝ → ℝ, iteratedDeriv 2 g = deriv (deriv g) := fun g => by
    funext y; rw [iteratedDeriv_succ, iteratedDeriv_one]
  rw [h2, deriv_mconv_signal μ f, deriv_mconv_signal μ (SchwartzMap.derivCLM ℝ (F := ℝ) f),
    h2 (⇑f), SignalClass.deriv_eq f, SignalClass.deriv_eq (SchwartzMap.derivCLM ℝ (F := ℝ) f)]

/-- The scale space of a test signal is twice differentiable at every point, which is what makes
the second-derivative test applicable to it. -/
theorem hasDerivAt_deriv_mconv (μ : Measure ℝ) [IsFiniteMeasure μ] (f : SignalClass) (x : ℝ) :
    HasDerivAt (deriv (mconv μ (⇑f))) (mconv μ (iteratedDeriv 2 (⇑f)) x) x := by
  set g := SchwartzMap.derivCLM ℝ (F := ℝ) f with hg
  obtain ⟨C₀, hC₀⟩ := SignalClass.exists_bound g
  obtain ⟨C, hC⟩ := SignalClass.exists_bound (SchwartzMap.derivCLM ℝ (F := ℝ) g)
  have hgoal : mconv μ (iteratedDeriv 2 (⇑f)) x
      = mconv μ (⇑(SchwartzMap.derivCLM ℝ (F := ℝ) g)) x := by
    have h2 : iteratedDeriv 2 (⇑f) = deriv (deriv (⇑f)) := by
      funext y; rw [iteratedDeriv_succ, iteratedDeriv_one]
    rw [h2, SignalClass.deriv_eq f, ← hg, SignalClass.deriv_eq g]
  rw [deriv_mconv_signal μ f, ← hg, hgoal]
  exact hasDerivAt_mconv g.continuous (SchwartzMap.derivCLM ℝ (F := ℝ) g).continuous hC₀ hC
    (fun y => SignalClass.hasDerivAt g y) x

/-! ## The second-derivative test -/

/-- **The second-derivative test at a local maximum.** If `g` is differentiable with derivative
`g'`, and `g'` is differentiable at `x_0` with derivative `L`, then a local maximum of `g` at
`x_0` forces `L \le 0`.

Mathlib has the first-derivative statement (`IsLocalMax.hasDerivAt_eq_zero`) and not this one.
The proof is the mean value theorem: were `L > 0`, the slope of `g'` at `x_0` would be positive
on a punctured neighbourhood, hence `g'` positive throughout a right neighbourhood since
`g'(x_0) = 0`, and the mean value theorem would then place a point of that neighbourhood strictly
above `g(x_0)`. -/
theorem le_zero_of_isLocalMax_of_hasDerivAt {g g' : ℝ → ℝ} (hg : ∀ x, HasDerivAt g (g' x) x)
    {x₀ L : ℝ} (hg' : HasDerivAt g' L x₀) (hmax : IsLocalMax g x₀) : L ≤ 0 := by
  by_contra hL
  rw [not_le] at hL
  have hzero : g' x₀ = 0 := hmax.hasDerivAt_eq_zero (hg x₀)
  have hslope : ∀ᶠ y in 𝓝[≠] x₀, 0 < slope g' x₀ y :=
    (hasDerivAt_iff_tendsto_slope.mp hg').eventually (eventually_gt_nhds hL)
  have hpos : ∀ᶠ y in 𝓝[>] x₀, 0 < g' y := by
    filter_upwards [nhdsWithin_mono _ (fun y hy => ne_of_gt hy) hslope,
      self_mem_nhdsWithin] with y hy hy'
    have hlt : x₀ < y := hy'
    rw [slope_def_field, hzero, sub_zero] at hy
    have hden : (0 : ℝ) < y - x₀ := sub_pos.mpr hlt
    have hmul : 0 < g' y / (y - x₀) * (y - x₀) := mul_pos hy hden
    rwa [div_mul_cancel₀ _ (ne_of_gt hden)] at hmul
  have hle : ∀ᶠ y in 𝓝[>] x₀, g y ≤ g x₀ := nhdsWithin_le_nhds hmax
  obtain ⟨u, hu, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset (a := x₀)).mp (hpos.and hle)
  set y : ℝ := (x₀ + u) / 2 with hydef
  have hxu : x₀ < u := hu
  have hy₁ : x₀ < y := by rw [hydef]; linarith
  have hy₂ : y < u := by rw [hydef]; linarith
  obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope g g' hy₁
    (fun z _ => (hg z).continuousAt.continuousWithinAt) (fun z _ => hg z)
  have hcpos : 0 < g' c := (hsub ⟨hc.1, hc.2.trans hy₂⟩).1
  have hyle : g y ≤ g x₀ := (hsub ⟨hy₁, hy₂⟩).2
  rw [hceq] at hcpos
  have hden : (0 : ℝ) < y - x₀ := sub_pos.mpr hy₁
  have hnum : 0 < g y - g x₀ := by
    have hmul : 0 < (g y - g x₀) / (y - x₀) * (y - x₀) := mul_pos hcpos hden
    rwa [div_mul_cancel₀ _ (ne_of_gt hden)] at hmul
  linarith

/-- The mirror statement at a local minimum. -/
theorem nonneg_of_isLocalMin_of_hasDerivAt {g g' : ℝ → ℝ} (hg : ∀ x, HasDerivAt g (g' x) x)
    {x₀ L : ℝ} (hg' : HasDerivAt g' L x₀) (hmin : IsLocalMin g x₀) : 0 ≤ L := by
  have h := le_zero_of_isLocalMax_of_hasDerivAt (g := fun x => -g x) (g' := fun x => -g' x)
    (fun x => (hg x).neg) hg'.neg hmin.neg
  linarith

end SpatialLine
