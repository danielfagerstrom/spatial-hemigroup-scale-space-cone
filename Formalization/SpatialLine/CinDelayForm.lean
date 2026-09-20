/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.CinDelay
import SpatialLine.Symbol

/-!
# `lem:cin-delay-equation`: the delay equation of the `Cin` kernels

Blueprint: `blueprint/src/parts/08-cone.tex`, `lem:cin-delay-equation`.

Wave 5 reduced the node to a single obligation and named the route: read at the *law* rather
than at the density, the node's two displays are the same identity between two finite signed
measures, and what remains is uniqueness for signed measures, closed by `Measure.ext_of_charFun`
at the Jordan recombination as in chapter 3. This file carries that out and closes the node.

## The two measures, and why the window replaces the signed Levy weight

The identity to be proved is `x·μ(dx) = (P - ½[P(·-τ) + P(·+τ)])dx`. Its right-hand side is
`½[μ(x-τ, x] - μ(x, x+τ]]dx`, and the first of those two window masses is the density of

`μ ∗ delayWindow τ`,   `delayWindow τ = ` Lebesgue measure on `[0,τ)`,

while the second is the same measure translated by `τ`. That observation is what removes the
Fourier computation the printed proof performs by hand: the transform of a convolution is
`charFun_conv`, and the transform of the window is an elementary interval integral. The
printed proof's signed Levy weight `y ν₂(dy) = ½ sgn(y)1_{|y|<τ}dy` is exactly the difference
of the window and its translate, halved, so nothing about the mathematics changes --- what
changes is that no signed measure has to be convolved, only two positive ones subtracted at the
end.

The left-hand side's transform is `∫ x e^{iωx}μ(dx)`, and for a symmetric law it is `i` times
the sine moment (`charFun_jordan_sub`); differentiating `fourierCos μ` under the integral sign,
which the first absolute moment `cin_law_integrable_abs` justifies, identifies that moment with
`τ·Cin'(τω)e^{-Cin(τω)}` (`integral_mul_sin_cin`). The two transforms then agree by the
elementary ODE

`ω c'(ω) = -c(ω)(1 - cos τω)`,

which is `hasDerivAt_cin` and the chain rule at `c = e^{-Cin(τ·)}` and nothing else. Since both
sides are signed, uniqueness is applied after the Jordan recombination
`2·x⁺μ(dx) + ν_τ = 2·x⁻μ(dx) + ν` (`cin_delay_jordan`), the same closing move as
`ae_eq_zero_of_even_of_integral_cos_eq_zero` in chapter 3.

## What writing it down found

**The reviewed statements of both node declarations are false without `AEMeasurable p`**, and
not merely unprovable. `volume.withDensity (ofReal ∘ p)` sees a non-measurable `p` only through
the measurable functions below it: raising `p` on a Bernstein set --- inner measure zero, full
outer measure --- leaves the hypothesis `μ = volume.withDensity (ofReal ∘ p)` intact, because
every measurable simple function below the raised density is below the original one almost
everywhere, while the conclusion `∀ᵐ x, x p x = …` fails on a set that no null set contains. The
derivative form fails for the same reason, at a test function supported where `p` was altered
but `p(·±τ)` was not: one side is junk-zero and the other is not. Wave 5 recorded the missing
hypothesis as a review question carried by `cin_delay_deriv_of_measure_form`; it is a defect of
the statement, and both declarations now carry it. Every call site supplies it, the densities
being produced by `prop:kernel-regularity`.

**No Parseval, no inversion, and no hand-written Fubini.** The estimates of waves 2 and 3 priced
a multiplication formula pairing a finite measure with a Schwartz function, which Mathlib does
not carry. The route above needs none: the only exchange of order is the one inside
`conv_delayWindow_eq_withDensity`, which is a Tonelli in `ℝ≥0∞` with no integrability side
condition, and it is spent identifying the *density* of the convolution --- a step the measure
form does not need at all, and which only `cin_delay_equation` consumes.

**The derivative form is now genuinely free.** `cin_delay_deriv_of_measure_form` (wave 5) takes
the measure form and returns the node's second declaration; `cin_delay_equation_deriv` below is
one line.

Proving campaign, wave 6, chapter 8 (2026-09-10).
-/

namespace SpatialLine

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

/-! ## The delay window and its convolution -/

/-- **The delay window**: Lebesgue measure on `[0,τ)`. Convolving a law with it produces the
window masses `μ(z-τ, z]` as a density, which is what the delay equation's right-hand side is
built from. -/
noncomputable def delayWindow (τ : ℝ) : Measure ℝ := volume.restrict (Ico (0 : ℝ) τ)

instance isFiniteMeasure_delayWindow (τ : ℝ) : IsFiniteMeasure (delayWindow τ) := by
  constructor
  rw [delayWindow, Measure.restrict_apply_univ, Real.volume_Ico]
  exact ENNReal.ofReal_lt_top

/-- The window mass `z ↦ μ(z-τ, z]` is measurable, by measurability of the slices of a
measurable set in the product. -/
theorem measurable_windowMass (μ : Measure ℝ) [SFinite μ] (τ : ℝ) :
    Measurable fun z : ℝ => μ (Ioc (z - τ) z) := by
  have hs : MeasurableSet {p : ℝ × ℝ | p.1 - τ < p.2 ∧ p.2 ≤ p.1} :=
    (measurableSet_lt (measurable_fst.sub_const τ) measurable_snd).inter
      (measurableSet_le measurable_snd measurable_fst)
  have h := measurable_measure_prodMk_left (ν := μ) hs
  have heq : (fun z : ℝ => μ (Prod.mk z ⁻¹' {p : ℝ × ℝ | p.1 - τ < p.2 ∧ p.2 ≤ p.1}))
      = fun z : ℝ => μ (Ioc (z - τ) z) := by
    funext z; congr 1
  rwa [heq] at h

/-- **The convolution of a law with the delay window has the window masses as its density.**
One Tonelli exchange; nothing about `Cin` enters. -/
theorem conv_delayWindow_eq_withDensity (μ : Measure ℝ) [IsFiniteMeasure μ] (τ : ℝ) :
    μ ∗ delayWindow τ = volume.withDensity fun z => μ (Ioc (z - τ) z) := by
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  rw [delayWindow, Measure.lintegral_conv hf,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_windowMass μ τ) hf]
  set S : Set (ℝ × ℝ) := {p : ℝ × ℝ | p.1 ≤ p.2 ∧ p.2 < p.1 + τ} with hS
  have hSm : MeasurableSet S :=
    (measurableSet_le measurable_fst measurable_snd).inter
      (measurableSet_lt measurable_snd (measurable_fst.add_const τ))
  set F : ℝ → ℝ → ℝ≥0∞ := fun x y => S.indicator (fun p => f p.2) (x, y) with hF
  have hFm : Measurable (Function.uncurry F) := by
    have huncurry : Function.uncurry F = S.indicator (fun p : ℝ × ℝ => f p.2) := by
      funext p; simp [hF, Function.uncurry]
    rw [huncurry]
    exact (hf.comp measurable_snd).indicator hSm
  have hinner : ∀ x : ℝ, ∫⁻ y, f (x + y) ∂(volume.restrict (Ico (0 : ℝ) τ)) = ∫⁻ y, F x y := by
    intro x
    rw [← lintegral_indicator measurableSet_Ico]
    rw [← lintegral_sub_right_eq_self (fun y => (Ico (0 : ℝ) τ).indicator (fun u => f (x + u)) y) x]
    refine lintegral_congr fun y => ?_
    by_cases hy : y - x ∈ Ico (0 : ℝ) τ
    · rw [Set.indicator_of_mem hy]
      have hxy : (x, y) ∈ S := by
        simp only [hS, Set.mem_setOf_eq]
        simp only [Set.mem_Ico] at hy
        constructor <;> linarith [hy.1, hy.2]
      rw [hF]
      simp only
      rw [Set.indicator_of_mem hxy]
      ring_nf
    · rw [Set.indicator_of_notMem hy]
      have hxy : (x, y) ∉ S := by
        simp only [hS, Set.mem_setOf_eq]
        simp only [Set.mem_Ico, not_and_or, not_le, not_lt] at hy
        rcases hy with h | h
        · intro hc; linarith [hc.1]
        · intro hc; linarith [hc.2]
      rw [hF]
      simp only
      rw [Set.indicator_of_notMem hxy]
  simp_rw [hinner]
  rw [lintegral_lintegral_swap hFm.aemeasurable]
  refine lintegral_congr fun y => ?_
  have hmem : ∀ x : ℝ, x ∈ Ioc (y - τ) y → (x, y) ∈ S := by
    intro x hx
    simp only [Set.mem_Ioc] at hx
    simp only [hS, Set.mem_setOf_eq]
    constructor <;> linarith [hx.1, hx.2]
  have hnmem : ∀ x : ℝ, x ∉ Ioc (y - τ) y → (x, y) ∉ S := by
    intro x hx hc
    simp only [hS, Set.mem_setOf_eq] at hc
    exact hx (Set.mem_Ioc.mpr ⟨by linarith [hc.2], hc.1⟩)
  have hFy : ∀ x : ℝ, F x y = (Ioc (y - τ) y).indicator (fun _ => f y) x := by
    intro x
    by_cases hx : x ∈ Ioc (y - τ) y
    · rw [Set.indicator_of_mem hx, hF]
      simp only
      rw [Set.indicator_of_mem (hmem x hx)]
    · rw [Set.indicator_of_notMem hx, hF]
      simp only
      rw [Set.indicator_of_notMem (hnmem x hx)]
  simp_rw [hFy]
  rw [lintegral_indicator measurableSet_Ioc, setLIntegral_const]
  simp [Pi.mul_apply, mul_comm]

/-- **The transform of the delay window**, at a nonzero frequency. -/
theorem charFun_delayWindow {τ : ℝ} (hτ : 0 ≤ τ) {ω : ℝ} (hω : ω ≠ 0) :
    charFun (delayWindow τ) ω
      = (Complex.exp ((ω : ℂ) * (τ : ℂ) * Complex.I) - 1) / ((ω : ℂ) * Complex.I) := by
  have hset : delayWindow τ = volume.restrict (Ioc (0 : ℝ) τ) := by
    rw [delayWindow]
    exact Measure.restrict_congr_set Ico_ae_eq_Ioc
  rw [charFun_apply_real, hset, ← intervalIntegral.integral_of_le hτ]
  have hc : ((ω : ℂ) * Complex.I) ≠ 0 := by simp [Complex.ext_iff, hω]
  have hrw : ∀ x : ℝ, Complex.exp ((ω : ℂ) * (x : ℂ) * Complex.I)
      = Complex.exp (((ω : ℂ) * Complex.I) * (x : ℂ)) := by
    intro x; ring_nf
  rw [intervalIntegral.integral_congr
    (g := fun x : ℝ => Complex.exp (((ω : ℂ) * Complex.I) * (x : ℂ))) (fun x _ => hrw x),
    integral_exp_mul_complex hc]
  push_cast
  ring_nf
  simp

/-! ## The transform of the signed measure `x·μ(dx)` -/

/-- The characteristic function of `μ` weighted by the positive part of a real function. -/
theorem charFun_withDensity_ofReal {μ : Measure ℝ} {f : ℝ → ℝ} (hf : AEMeasurable f μ) (ω : ℝ) :
    charFun (μ.withDensity fun x => ENNReal.ofReal (f x)) ω
      = ∫ x, ((f x).toNNReal : ℝ) • Complex.exp ((ω : ℂ) * (x : ℂ) * Complex.I) ∂μ := by
  have hcast : (fun x : ℝ => ENNReal.ofReal (f x))
      = fun x : ℝ => (((f x).toNNReal : ℝ≥0) : ℝ≥0∞) := rfl
  rw [charFun_apply_real, hcast, integral_withDensity_eq_integral_smul₀ hf.real_toNNReal]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp [NNReal.smul_def])

/-- A measure with an integrable real density is finite. -/
theorem isFiniteMeasure_withDensity_ofReal {μ : Measure ℝ} {f : ℝ → ℝ} (hf : Integrable f μ) :
    IsFiniteMeasure (μ.withDensity fun x => ENNReal.ofReal (f x)) := by
  refine ⟨?_⟩
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  refine lt_of_le_of_lt (lintegral_mono fun x => ?_) hf.hasFiniteIntegral
  calc ENNReal.ofReal (f x) ≤ ENNReal.ofReal ‖f x‖ := ENNReal.ofReal_le_ofReal (le_abs_self (f x))
    _ = ‖f x‖ₑ := ofReal_norm (f x)

/-- **Differentiation of the cosine transform under the integral sign.** The dominating function
is `|x|`, so a finite first absolute moment is exactly what the step costs. -/
theorem hasDerivAt_fourierCos {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hmom : Integrable (fun x : ℝ => |x|) μ) (ω : ℝ) :
    HasDerivAt (fourierCos μ) (∫ x, -(x * Real.sin (ω * x)) ∂μ) ω := by
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun w x => Real.cos (w * x)) (F' := fun w x => -(x * Real.sin (w * x))) (x₀ := ω)
    (bound := fun x => |x|) (s := univ) univ_mem
    (.of_forall fun w =>
      (Real.continuous_cos.comp (continuous_const.mul continuous_id)).aestronglyMeasurable)
    (integrable_cos_mul μ ω)
    (by fun_prop)
    (.of_forall fun x w _ => by
      rw [Real.norm_eq_abs, abs_neg, abs_mul]
      have hs : |Real.sin (w * x)| ≤ 1 := Real.abs_sin_le_one _
      nlinarith [abs_nonneg x, abs_nonneg (Real.sin (w * x))])
    hmom
    (.of_forall fun x w _ => by
      have h1 : HasDerivAt (fun w : ℝ => w * x) x w := by simpa using (hasDerivAt_id w).mul_const x
      simpa [mul_comm] using h1.cos)
  have hfc : fourierCos μ = fun w => ∫ x, Real.cos (w * x) ∂μ := by
    funext w; rw [fourierCos_apply]
  rw [hfc]
  exact key.2

/-- **The sine moment of a `Cin` law**, `∫ x sin(ωx) μ(dx) = τ·Cin'(τω)·e^{-Cin(τω)}`.

This is the elementary ODE `ω c'(ω) = -c(ω)(1 - cos τω)` of the node's proof, written without
dividing by `ω`: `Cin'(v) = (1 - cos v)/v` is `cinIntegrand`, and the identity holds at `ω = 0`
as well, both sides vanishing. -/
theorem integral_mul_sin_cin {τ : ℝ} {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hsym : IsSymmetric μ) (hcos : ∀ ω : ℝ, fourierCos μ ω = Real.exp (-cin (τ * ω))) (ω : ℝ) :
    ∫ x, x * Real.sin (ω * x) ∂μ = τ * cinIntegrand (τ * ω) * Real.exp (-cin (τ * ω)) := by
  have hmom : Integrable (fun x : ℝ => |x|) μ := cin_law_integrable_abs hsym hcos
  have h1 := hasDerivAt_fourierCos hmom ω
  have h2 : HasDerivAt (fun w : ℝ => Real.exp (-cin (τ * w)))
      (Real.exp (-cin (τ * ω)) * -(cinIntegrand (τ * ω) * τ)) ω := by
    have hlin : HasDerivAt (fun w : ℝ => τ * w) τ ω := by
      simpa using (hasDerivAt_id ω).const_mul τ
    exact (((hasDerivAt_cin (τ * ω)).comp ω hlin).neg).exp
  have hfc : fourierCos μ = fun w => Real.exp (-cin (τ * w)) := funext hcos
  rw [hfc] at h1
  have huniq := h1.unique h2
  rw [integral_neg] at huniq
  linarith [huniq]

/-- **The cosine moment of a symmetric law vanishes**: `x cos(ωx)` is odd. -/
theorem integral_mul_cos_eq_zero_of_symmetric {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hsym : IsSymmetric μ) (ω : ℝ) : ∫ x, x * Real.cos (ω * x) ∂μ = 0 := by
  have hneg : Measurable fun x : ℝ => -x := measurable_neg
  have h2 : ∫ x, x * Real.cos (ω * x) ∂μ = ∫ x, (-x) * Real.cos (ω * (-x)) ∂μ := by
    conv_lhs => rw [← hsym]
    rw [integral_map hneg.aemeasurable (by fun_prop)]
  have h3 : ∫ x, (-x) * Real.cos (ω * (-x)) ∂μ = -∫ x, x * Real.cos (ω * x) ∂μ := by
    rw [← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp [mul_neg, Real.cos_neg]
  linarith [h2.trans h3]

/-! ## The Jordan recombination and the signed-measure uniqueness -/

/-- An integrable real weight against the unit-modulus exponential is integrable. -/
theorem integrable_smul_exp {μ : Measure ℝ} {g : ℝ → ℝ} (hg : Integrable g μ) (ω : ℝ) :
    Integrable (fun x : ℝ => g x • Complex.exp ((ω : ℂ) * (x : ℂ) * Complex.I)) μ := by
  refine hg.abs.mono' ?_ ?_
  · exact hg.aestronglyMeasurable.smul (by fun_prop)
  · filter_upwards with x
    have hx : ((ω : ℂ) * (x : ℂ)) = ((ω * x : ℝ) : ℂ) := by push_cast; ring
    rw [norm_smul, hx, Complex.norm_exp_ofReal_mul_I]
    simp [Real.norm_eq_abs]

/-- **The transform of the signed measure `x·μ(dx)`**, written as the difference of the
transforms of its Jordan parts: for a symmetric law it is `i` times the sine moment. -/
theorem charFun_jordan_sub {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hsym : IsSymmetric μ) (hmom : Integrable (fun x : ℝ => |x|) μ) (ω : ℝ) :
    charFun (μ.withDensity fun x => ENNReal.ofReal x) ω
        - charFun (μ.withDensity fun x => ENNReal.ofReal (-x)) ω
      = ((∫ x, x * Real.sin (ω * x) ∂μ : ℝ) : ℂ) * Complex.I := by
  have hid : Integrable (fun x : ℝ => x) μ := by
    refine (integrable_norm_iff (f := fun x : ℝ => x) ?_).mp ?_
    · exact aestronglyMeasurable_id
    · simpa [Real.norm_eq_abs] using hmom
  have hpos : Integrable (fun x : ℝ => ((x.toNNReal : ℝ))) μ := by
    refine hmom.mono' (by fun_prop) ?_
    filter_upwards with x
    simp only [Real.norm_eq_abs, Real.coe_toNNReal']
    rcases le_or_gt x 0 with hle | hgt
    · rw [max_eq_right hle]; simp [abs_nonneg]
    · rw [max_eq_left hgt.le, abs_of_pos hgt]
  have hneg : Integrable (fun x : ℝ => (((-x)).toNNReal : ℝ)) μ := by
    refine hmom.mono' (by fun_prop) ?_
    filter_upwards with x
    simp only [Real.norm_eq_abs, Real.coe_toNNReal']
    rcases le_or_gt (-x) 0 with hle | hgt
    · rw [max_eq_right hle]; simp [abs_nonneg]
    · rw [max_eq_left hgt.le]
      rw [abs_of_nonneg (le_of_lt hgt)]
      simp [neg_le_abs]
  have hsplit : ∀ x : ℝ, ((x.toNNReal : ℝ)) - (((-x)).toNNReal : ℝ) = x := by
    intro x
    simp only [Real.coe_toNNReal']
    rcases le_or_gt x 0 with hle | hgt
    · rw [max_eq_right hle, max_eq_left (by linarith)]; ring
    · rw [max_eq_left hgt.le, max_eq_right (by linarith)]; ring
  rw [charFun_withDensity_ofReal (f := fun x : ℝ => x) aemeasurable_id ω,
    charFun_withDensity_ofReal (f := fun x : ℝ => -x) (aemeasurable_id.neg) ω,
    ← integral_sub (integrable_smul_exp hpos ω) (integrable_smul_exp hneg ω)]
  have hcongr : ∫ x, ((((x : ℝ).toNNReal : ℝ)) • Complex.exp ((ω : ℂ) * (x : ℂ) * Complex.I)
        - (((-x : ℝ)).toNNReal : ℝ) • Complex.exp ((ω : ℂ) * (x : ℂ) * Complex.I)) ∂μ
      = ∫ x, (x : ℝ) • Complex.exp ((ω : ℂ) * (x : ℂ) * Complex.I) ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only []
    rw [← sub_smul, hsplit x]
  rw [hcongr, integral_smul_exp_eq hid ω]
  have hc : ∫ x, Real.cos (ω * x) * x ∂μ = 0 := by
    rw [← integral_mul_cos_eq_zero_of_symmetric hsym ω]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  have hs : ∫ x, Real.sin (ω * x) * x ∂μ = ∫ x, x * Real.sin (ω * x) ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  rw [hc, hs]
  simp

/-- **The delay equation as an identity between two finite signed measures**, written in the
Jordan-recombined form that `Measure.ext_of_charFun` accepts: `2·x⁺μ(dx) + ν_τ = 2·x⁻μ(dx) + ν`,
where `ν = μ ∗ delayWindow τ` and `ν_τ` is its translate by `τ`. -/
theorem cin_delay_jordan {τ : ℝ} (hτ : 0 < τ) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hsym : IsSymmetric μ) (hcos : ∀ ω : ℝ, fourierCos μ ω = Real.exp (-cin (τ * ω))) :
    (μ.withDensity fun x => ENNReal.ofReal x) + (μ.withDensity fun x => ENNReal.ofReal x)
        + (μ ∗ delayWindow τ).map (fun z => z - τ)
      = (μ.withDensity fun x => ENNReal.ofReal (-x))
        + (μ.withDensity fun x => ENNReal.ofReal (-x)) + (μ ∗ delayWindow τ) := by
  have hmom : Integrable (fun x : ℝ => |x|) μ := cin_law_integrable_abs hsym hcos
  have hid : Integrable (fun x : ℝ => x) μ := by
    refine (integrable_norm_iff (f := fun x : ℝ => x) ?_).mp ?_
    · exact aestronglyMeasurable_id
    · simpa [Real.norm_eq_abs] using hmom
  haveI hfp : IsFiniteMeasure (μ.withDensity fun x => ENNReal.ofReal x) :=
    isFiniteMeasure_withDensity_ofReal hid
  haveI hfn : IsFiniteMeasure (μ.withDensity fun x => ENNReal.ofReal (-x)) :=
    isFiniteMeasure_withDensity_ofReal hid.neg
  haveI hfm : IsFiniteMeasure ((μ ∗ delayWindow τ).map fun z => z - τ) :=
    Measure.isFiniteMeasure_map _ _
  refine fourier_uniqueness (fun ω => ?_)
  set E : ℝ := Real.exp (-cin (τ * ω)) with hE
  -- the transform of the translate
  have hmap : ((μ ∗ delayWindow τ).map fun z => z - τ) = (μ ∗ delayWindow τ).map
      fun z => z + (-τ) := by simp [sub_eq_add_neg]
  have htrans : charFun ((μ ∗ delayWindow τ).map fun z => z - τ) ω
      = charFun (μ ∗ delayWindow τ) ω * Complex.exp (((-τ * ω : ℝ) : ℂ) * Complex.I) := by
    rw [hmap, charFun_map_add_const]
    congr 1
    norm_num
    ring_nf
  -- the transform of the convolution
  have hconv : charFun (μ ∗ delayWindow τ) ω = (E : ℂ) * charFun (delayWindow τ) ω := by
    rw [charFun_conv, charFun_eq_fourierCos_of_symmetric hsym, hcos ω]
  -- the Jordan difference
  have hdiff : charFun (μ.withDensity fun x => ENNReal.ofReal x) ω
      - charFun (μ.withDensity fun x => ENNReal.ofReal (-x)) ω
      = ((τ * cinIntegrand (τ * ω) * E : ℝ) : ℂ) * Complex.I := by
    rw [charFun_jordan_sub hsym hmom ω, integral_mul_sin_cin hsym hcos ω]
  -- the key identity, an ODE in disguise
  have hkey : ((τ * cinIntegrand (τ * ω) * E : ℝ) : ℂ) * Complex.I * 2
      = charFun (μ ∗ delayWindow τ) ω * (1 - Complex.exp (((-τ * ω : ℝ) : ℂ) * Complex.I)) := by
    rcases eq_or_ne ω 0 with rfl | hω
    · simp [cinIntegrand, hE]
    · rw [hconv, charFun_delayWindow hτ.le hω]
      have hτ0 : (τ : ℝ) ≠ 0 := ne_of_gt hτ
      have hreal : τ * cinIntegrand (τ * ω) = (1 - Real.cos (τ * ω)) / ω := by
        rw [cinIntegrand]
        field_simp
      rw [hreal]
      have ha : Complex.exp ((ω : ℂ) * (τ : ℂ) * Complex.I)
          = (Real.cos (τ * ω) : ℂ) + (Real.sin (τ * ω) : ℂ) * Complex.I := by
        have hx : ((ω : ℂ) * (τ : ℂ)) = ((τ * ω : ℝ) : ℂ) := by push_cast; ring
        rw [hx, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      have hb : Complex.exp (((-τ * ω : ℝ) : ℂ) * Complex.I)
          = (Real.cos (τ * ω) : ℂ) - (Real.sin (τ * ω) : ℂ) * Complex.I := by
        have hneg : ((-τ * ω : ℝ) : ℂ) = ((-(τ * ω) : ℝ) : ℂ) := by norm_num
        rw [hneg, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
          Real.cos_neg, Real.sin_neg]
        push_cast
        ring
      rw [ha, hb]
      have hpyth : (Real.cos (τ * ω) : ℂ) ^ 2 + (Real.sin (τ * ω) : ℂ) ^ 2 = 1 := by
        have hr := Real.sin_sq_add_cos_sq (τ * ω)
        have hc : ((Real.sin (τ * ω) ^ 2 + Real.cos (τ * ω) ^ 2 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
          rw [hr]
        rw [Complex.ofReal_add, Complex.ofReal_pow, Complex.ofReal_pow, Complex.ofReal_one] at hc
        linear_combination hc
      have hωc : (ω : ℂ) ≠ 0 := by exact_mod_cast hω
      field_simp
      rw [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one,
        Complex.I_sq]
      field_simp
      linear_combination (-(E : ℂ) * (Real.sin (τ * ω) : ℂ) ^ 2) * Complex.I_sq
        + (E : ℂ) * hpyth
  rw [charFun_add_measure, charFun_add_measure, charFun_add_measure, charFun_add_measure, htrans]
  have hgoal := hkey
  rw [← hdiff] at hgoal
  linear_combination hgoal

/-! ## The pairing form of the identity -/

/-- A bounded measurable function is integrable against a finite measure. -/
theorem integrable_of_bounded {ν : Measure ℝ} [IsFiniteMeasure ν] {g : ℝ → ℝ}
    (hgm : Measurable g) {C : ℝ} (hgb : ∀ x, |g x| ≤ C) : Integrable g ν := by
  refine (integrable_const C).mono' hgm.aestronglyMeasurable (.of_forall fun x => ?_)
  have h0 : (0 : ℝ) ≤ C := le_trans (abs_nonneg (g x)) (hgb x)
  simpa [Real.norm_eq_abs, abs_of_nonneg h0] using hgb x

/-- **The delay equation, paired against a bounded measurable test function.**

`2∫ x g(x) μ(dx) = ∫ g dν - ∫ g dν_τ` with `ν = μ ∗ delayWindow τ`: the signed-measure identity
of `cin_delay_jordan` with the Jordan parts recombined. -/
theorem cin_delay_pairing {τ : ℝ} (hτ : 0 < τ) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hsym : IsSymmetric μ) (hcos : ∀ ω : ℝ, fourierCos μ ω = Real.exp (-cin (τ * ω)))
    {g : ℝ → ℝ} (hgm : Measurable g) {C : ℝ} (hgb : ∀ x, |g x| ≤ C) :
    2 * ∫ x, x * g x ∂μ
      = (∫ z, g z ∂(μ ∗ delayWindow τ))
        - ∫ z, g z ∂((μ ∗ delayWindow τ).map fun z => z - τ) := by
  have hmom : Integrable (fun x : ℝ => |x|) μ := cin_law_integrable_abs hsym hcos
  have hid : Integrable (fun x : ℝ => x) μ := by
    refine (integrable_norm_iff (f := fun x : ℝ => x) ?_).mp ?_
    · exact aestronglyMeasurable_id
    · simpa [Real.norm_eq_abs] using hmom
  haveI hfp : IsFiniteMeasure (μ.withDensity fun x => ENNReal.ofReal x) :=
    isFiniteMeasure_withDensity_ofReal hid
  haveI hfn : IsFiniteMeasure (μ.withDensity fun x => ENNReal.ofReal (-x)) :=
    isFiniteMeasure_withDensity_ofReal hid.neg
  haveI hfm : IsFiniteMeasure ((μ ∗ delayWindow τ).map fun z => z - τ) :=
    Measure.isFiniteMeasure_map _ _
  have hJ := cin_delay_jordan hτ μ hsym hcos
  have hCnn : (0 : ℝ) ≤ C := le_trans (abs_nonneg (g 0)) (hgb 0)
  have hbound : ∀ (f : ℝ → ℝ), (∀ x, |f x| ≤ |x|) → AEStronglyMeasurable (fun x => f x * g x) μ →
      Integrable (fun x : ℝ => f x * g x) μ := by
    intro f hf hmeas
    refine (hmom.const_mul C).mono' hmeas ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_mul]
    calc |f x| * |g x| ≤ |x| * C :=
          mul_le_mul (hf x) (hgb x) (abs_nonneg _) (abs_nonneg x)
      _ = C * |x| := by ring
  have hposI : Integrable (fun x : ℝ => ((x.toNNReal : ℝ)) * g x) μ := by
    refine hbound _ (fun x => ?_) (by fun_prop)
    simp only [Real.coe_toNNReal']
    rcases le_or_gt x 0 with hle | hgt
    · rw [max_eq_right hle]; simp [abs_nonneg]
    · rw [max_eq_left hgt.le, abs_of_pos hgt]
  have hnegI : Integrable (fun x : ℝ => (((-x)).toNNReal : ℝ)) μ := by
    refine hmom.mono' (by fun_prop) ?_
    filter_upwards with x
    simp only [Real.norm_eq_abs, Real.coe_toNNReal']
    rcases le_or_gt (-x) 0 with hle | hgt
    · rw [max_eq_right hle]; simp [abs_nonneg]
    · rw [max_eq_left hgt.le, abs_of_nonneg (le_of_lt hgt)]; simp [neg_le_abs]
  have hnegI' : Integrable (fun x : ℝ => (((-x)).toNNReal : ℝ) * g x) μ := by
    refine hbound _ (fun x => ?_) (by fun_prop)
    simp only [Real.coe_toNNReal']
    rcases le_or_gt (-x) 0 with hle | hgt
    · rw [max_eq_right hle]; simp [abs_nonneg]
    · rw [max_eq_left hgt.le, abs_of_nonneg (le_of_lt hgt)]; simp [neg_le_abs]
  have hsplit : ∀ x : ℝ, ((x.toNNReal : ℝ)) - (((-x)).toNNReal : ℝ) = x := by
    intro x
    simp only [Real.coe_toNNReal']
    rcases le_or_gt x 0 with hle | hgt
    · rw [max_eq_right hle, max_eq_left (by linarith)]; ring
    · rw [max_eq_left hgt.le, max_eq_right (by linarith)]; ring
  have hrecomb : (∫ x, ((x.toNNReal : ℝ)) * g x ∂μ) - ∫ x, (((-x)).toNNReal : ℝ) * g x ∂μ
      = ∫ x, x * g x ∂μ := by
    rw [← integral_sub hposI hnegI']
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only []
    rw [← sub_mul, hsplit x]
  have h : (∫ z, g z ∂((μ.withDensity fun x => ENNReal.ofReal x)
        + (μ.withDensity fun x => ENNReal.ofReal x) + (μ ∗ delayWindow τ).map fun z => z - τ))
      = ∫ z, g z ∂((μ.withDensity fun x => ENNReal.ofReal (-x))
        + (μ.withDensity fun x => ENNReal.ofReal (-x)) + (μ ∗ delayWindow τ)) := by rw [hJ]
  rw [integral_add_measure ((integrable_of_bounded hgm hgb).add_measure
      (integrable_of_bounded hgm hgb)) (integrable_of_bounded hgm hgb),
    integral_add_measure (integrable_of_bounded hgm hgb) (integrable_of_bounded hgm hgb),
    integral_add_measure ((integrable_of_bounded hgm hgb).add_measure
      (integrable_of_bounded hgm hgb)) (integrable_of_bounded hgm hgb),
    integral_add_measure (integrable_of_bounded hgm hgb) (integrable_of_bounded hgm hgb),
    integral_withDensity_ofReal (f := fun x : ℝ => x) aemeasurable_id,
    integral_withDensity_ofReal (f := fun x : ℝ => -x) aemeasurable_id.neg] at h
  rw [← hrecomb]
  linarith [h]

/-! ## The measure form -/

/-- The window integral of a derivative is the increment of the function: the fundamental
theorem of calculus on `[0,τ)`. -/
theorem integral_delayWindow_deriv {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) {τ : ℝ} (hτ : 0 ≤ τ) (x : ℝ) :
    ∫ u, deriv φ (x + u) ∂(delayWindow τ) = φ (x + τ) - φ x := by
  have hdiff : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hone : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
  have hcont : Continuous (deriv φ) := hφ.continuous_deriv hone
  have hset : delayWindow τ = volume.restrict (Ioc (0 : ℝ) τ) := by
    rw [delayWindow]; exact Measure.restrict_congr_set Ico_ae_eq_Ioc
  rw [hset, ← intervalIntegral.integral_of_le hτ]
  have hd : ∀ u ∈ uIcc (0 : ℝ) τ, HasDerivAt (fun u : ℝ => φ (x + u)) (deriv φ (x + u)) u := by
    intro u _
    have h1 : HasDerivAt (fun u : ℝ => x + u) 1 u := by simpa using (hasDerivAt_id u).const_add x
    simpa [Function.comp_def] using (hdiff (x + u)).hasDerivAt.comp u h1
  have hint : IntervalIntegrable (fun u : ℝ => deriv φ (x + u)) volume 0 τ :=
    (hcont.comp (continuous_const.add continuous_id)).intervalIntegrable 0 τ
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint]
  simp

/-- **`lem:cin-delay-equation`, the measure form.**

The node's derivative form with the density integrated out: an identity between two integrals
against `μ` alone. This is the whole remaining content of the node, the passage back to the
density being `cin_delay_deriv_of_measure_form`. -/
theorem cin_delay_measure_form {τ : ℝ} (hτ : 0 < τ) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hsym : IsSymmetric μ) (hcos : ∀ ω : ℝ, fourierCos μ ω = Real.exp (-cin (τ * ω))) :
    ∀ φ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
      ∫ x, deriv (fun y => y * φ y) x ∂μ
        = ∫ x, (φ (x + τ) + φ (x - τ)) / 2 ∂μ := by
  intro φ hφ hsupp
  have hdiff : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hone : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
  have hcont : Continuous (deriv φ) := hφ.continuous_deriv hone
  have hsupp' : HasCompactSupport (deriv φ) := hsupp.deriv
  obtain ⟨C, hC⟩ := hsupp'.exists_bound_of_continuous hcont
  obtain ⟨C₀, hC₀⟩ := hsupp.exists_bound_of_continuous hφ.continuous
  have hCb : ∀ x, |deriv φ x| ≤ C := fun x => by simpa [Real.norm_eq_abs] using hC x
  have hC₀b : ∀ x, |φ x| ≤ C₀ := fun x => by simpa [Real.norm_eq_abs] using hC₀ x
  -- the pairing identity at `g = φ'`
  have hpair := cin_delay_pairing hτ μ hsym hcos hcont.measurable hCb
  -- the two window integrals
  have hnu : (∫ z, deriv φ z ∂(μ ∗ delayWindow τ)) = ∫ x, (φ (x + τ) - φ x) ∂μ := by
    rw [integral_conv (integrable_of_bounded hcont.measurable hCb)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x =>
      integral_delayWindow_deriv hφ hτ.le x)
  have hnutau : (∫ z, deriv φ z ∂((μ ∗ delayWindow τ).map fun z => z - τ))
      = ∫ x, (φ x - φ (x - τ)) ∂μ := by
    rw [integral_map (by fun_prop) hcont.aestronglyMeasurable,
      integral_conv (f := fun z : ℝ => deriv φ (z - τ)) ?_]
    · refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only []
      have hrw : (fun u : ℝ => deriv φ (x + u - τ)) = fun u : ℝ => deriv φ ((x - τ) + u) := by
        funext u; ring_nf
      rw [hrw, integral_delayWindow_deriv hφ hτ.le (x - τ), sub_add_cancel]
    · exact integrable_of_bounded (hcont.measurable.comp (measurable_id.sub_const τ))
        (fun x => hCb (x - τ))
  -- the elementary integrability facts
  have hφI : Integrable φ μ := integrable_of_bounded hφ.continuous.measurable hC₀b
  have hφplus : Integrable (fun x : ℝ => φ (x + τ)) μ :=
    integrable_of_bounded (hφ.continuous.measurable.comp (measurable_id.add_const τ))
      (fun x => hC₀b (x + τ))
  have hφminus : Integrable (fun x : ℝ => φ (x - τ)) μ :=
    integrable_of_bounded (hφ.continuous.measurable.comp (measurable_id.sub_const τ))
      (fun x => hC₀b (x - τ))
  have hxφ : Integrable (fun x : ℝ => x * deriv φ x) μ := by
    have hmom : Integrable (fun x : ℝ => |x|) μ := cin_law_integrable_abs hsym hcos
    refine (hmom.const_mul C).mono' (by fun_prop) ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_mul]
    have hCnn : (0 : ℝ) ≤ C := le_trans (abs_nonneg (deriv φ 0)) (hCb 0)
    calc |x| * |deriv φ x| ≤ |x| * C :=
          mul_le_mul_of_nonneg_left (hCb x) (abs_nonneg x)
      _ = C * |x| := by ring
  -- the left-hand side
  have hderiv : ∀ x : ℝ, deriv (fun y => y * φ y) x = φ x + x * deriv φ x := by
    intro x
    have h : HasDerivAt (fun y : ℝ => y * φ y) (1 * φ x + x * deriv φ x) x :=
      (hasDerivAt_id x).mul (hdiff x).hasDerivAt
    simpa using h.deriv
  rw [integral_congr_ae (Filter.Eventually.of_forall hderiv), integral_add hφI hxφ]
  rw [hnu, hnutau, integral_sub hφplus hφI, integral_sub hφI hφminus] at hpair
  have hrhs : ∫ x, (φ (x + τ) + φ (x - τ)) / 2 ∂μ
      = ((∫ x, φ (x + τ) ∂μ) + ∫ x, φ (x - τ) ∂μ) / 2 := by
    rw [← integral_add hφplus hφminus, ← integral_div]
  rw [hrhs]
  linarith [hpair]


/-! ## The two forms of the node -/

/-- **`lem:cin-delay-equation`, the derivative form** (`Skeleton.cin_delay_equation_deriv`), with
the measure form of `cin_delay_measure_form` fed into `cin_delay_deriv_of_measure_form`.

CHANGED (proof 2026-09-10): the reviewed statement is carried verbatim except for
`hpmeas : AEMeasurable p volume`, which the passage between the two forms needs and which every
call site supplies (`prop:kernel-regularity` produces the density). -/
theorem cin_delay_equation_deriv {τ : ℝ} (hτ : 0 < τ) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hsym : IsSymmetric μ) (hcos : ∀ ω : ℝ, fourierCos μ ω = Real.exp (-cin (τ * ω)))
    (p : ℝ → ℝ) (hpmeas : AEMeasurable p volume)
    (hp : μ = volume.withDensity fun x => ENNReal.ofReal (p x))
    (hpos : 0 ≤ᵐ[volume] p) :
    ∀ φ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
      -∫ x, p x * deriv (fun y => y * φ y) x
        = -∫ x, (p (x - τ) + p (x + τ)) / 2 * φ x :=
  cin_delay_deriv_of_measure_form μ p hpmeas hpos hp (cin_delay_measure_form hτ μ hsym hcos)

/-! ### The window mass as a density -/

/-- The window mass, as a real-valued function. -/
theorem measurable_windowMassReal (μ : Measure ℝ) [SFinite μ] (τ : ℝ) :
    Measurable fun z : ℝ => (μ (Ioc (z - τ) z)).toReal :=
  (measurable_windowMass μ τ).ennreal_toReal

/-- The window mass is integrable on the line, of total integral `τ`. -/
theorem integrable_windowMassReal (μ : Measure ℝ) [IsFiniteMeasure μ] (τ : ℝ) :
    Integrable (fun z : ℝ => (μ (Ioc (z - τ) z)).toReal) volume := by
  refine integrable_toReal_of_lintegral_ne_top (measurable_windowMass μ τ).aemeasurable ?_
  have h : ∫⁻ z, μ (Ioc (z - τ) z) ∂(volume : Measure ℝ) = (μ ∗ delayWindow τ) univ := by
    rw [conv_delayWindow_eq_withDensity, withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ]
  rw [h]
  exact measure_ne_top _ _

/-- The convolution with the delay window, written with a real density. -/
theorem conv_delayWindow_eq_withDensity_real (μ : Measure ℝ) [IsFiniteMeasure μ] (τ : ℝ) :
    μ ∗ delayWindow τ
      = volume.withDensity fun z => ENNReal.ofReal ((μ (Ioc (z - τ) z)).toReal) := by
  rw [conv_delayWindow_eq_withDensity]
  congr 1
  funext z
  exact (ENNReal.ofReal_toReal (measure_ne_top μ _)).symm

/-- **The delay equation paired against a bounded test function, read at the density.** -/
theorem cin_delay_pairing_density {τ : ℝ} (hτ : 0 < τ) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hsym : IsSymmetric μ) (hcos : ∀ ω : ℝ, fourierCos μ ω = Real.exp (-cin (τ * ω)))
    (p : ℝ → ℝ) (hpmeas : AEMeasurable p volume)
    (hp : μ = volume.withDensity fun x => ENNReal.ofReal (p x)) (hpos : 0 ≤ᵐ[volume] p)
    {g : ℝ → ℝ} (hgm : Measurable g) {C : ℝ} (hgb : ∀ x, |g x| ≤ C) :
    ∫ x, g x * (2 * (x * p x))
      = ∫ x, g x * ((μ (Ioc (x - τ) x)).toReal - (μ (Ioc (x + τ - τ) (x + τ))).toReal) := by
  set A : ℝ → ℝ := fun z => (μ (Ioc (z - τ) z)).toReal with hA
  have hAm : Measurable A := measurable_windowMassReal μ τ
  have hAnn : ∀ z, 0 ≤ A z := fun z => ENNReal.toReal_nonneg
  have hAi : Integrable A volume := integrable_windowMassReal μ τ
  have hCnn : (0 : ℝ) ≤ C := le_trans (abs_nonneg (g 0)) (hgb 0)
  -- integrability of the two products
  have hAg : Integrable (fun z : ℝ => A z * g z) volume := by
    refine (hAi.const_mul C).mono' (by fun_prop) ?_
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hAnn z)]
    calc A z * |g z| ≤ A z * C := mul_le_mul_of_nonneg_left (hgb z) (hAnn z)
      _ = C * A z := by ring
  have hAτi : Integrable (fun z : ℝ => A (z + τ)) volume := by
    simpa [sub_neg_eq_add] using integrable_translate hAi (-τ)
  have hAτg : Integrable (fun z : ℝ => A (z + τ) * g z) volume := by
    refine (hAτi.const_mul C).mono' (by fun_prop) ?_
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hAnn _)]
    calc A (z + τ) * |g z| ≤ A (z + τ) * C := mul_le_mul_of_nonneg_left (hgb z) (hAnn _)
      _ = C * A (z + τ) := by ring
  have hpair := cin_delay_pairing hτ μ hsym hcos hgm hgb
  -- the left-hand side, read at the density
  have hL : 2 * ∫ x, x * g x ∂μ = ∫ x, g x * (2 * (x * p x)) := by
    rw [integral_eq_integral_density hpmeas hpos hp (fun x => x * g x), ← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  -- the two window integrals, read at the density `A`
  have hdens : ∀ h : ℝ → ℝ, ∫ z, h z ∂(μ ∗ delayWindow τ) = ∫ z, A z * h z := by
    intro h
    rw [conv_delayWindow_eq_withDensity_real,
      integral_withDensity_ofReal (f := A) hAm.aemeasurable]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only []
    rw [Real.coe_toNNReal _ (hAnn z)]
  have hR1 : ∫ z, g z ∂(μ ∗ delayWindow τ) = ∫ z, A z * g z := hdens g
  have hR2 : ∫ z, g z ∂((μ ∗ delayWindow τ).map fun z => z - τ) = ∫ z, A (z + τ) * g z := by
    rw [integral_map (by fun_prop) hgm.aestronglyMeasurable, hdens fun z => g (z - τ)]
    have h := integral_add_right_eq_self (μ := (volume : Measure ℝ))
      (fun z : ℝ => A z * g (z - τ)) τ
    simpa using h.symm
  rw [hR1, hR2, ← integral_sub hAg hAτg] at hpair
  rw [← hL, hpair]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [hA]
  ring_nf

/-- **`lem:cin-delay-equation`, the primitive form** (`Skeleton.cin_delay_equation`):
`x p(x) = P(x) - ½[P(x-τ) + P(x+τ)]` almost everywhere.

CHANGED (proof 2026-09-10): the reviewed statement is carried verbatim except for
`hpmeas : AEMeasurable p volume`. Without it the statement is not merely unprovable but false:
`volume.withDensity (ofReal ∘ p)` is unchanged when `p` is raised on a set of inner measure zero
and full outer measure, and the conclusion fails there. Every call site supplies it. -/
theorem cin_delay_equation {τ : ℝ} (hτ : 0 < τ) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hsym : IsSymmetric μ) (hcos : ∀ ω : ℝ, fourierCos μ ω = Real.exp (-cin (τ * ω)))
    (p : ℝ → ℝ) (hpmeas : AEMeasurable p volume)
    (hp : μ = volume.withDensity fun x => ENNReal.ofReal (p x))
    (hpos : 0 ≤ᵐ[volume] p) :
    ∀ᵐ x ∂volume, x * p x
      = (μ (Iic x)).toReal - ((μ (Iic (x - τ))).toReal + (μ (Iic (x + τ))).toReal) / 2 := by
  -- the window mass as a difference of two values of the distribution function
  have hcdf : ∀ y : ℝ, (μ (Ioc (y - τ) y)).toReal
      = (μ (Iic y)).toReal - (μ (Iic (y - τ))).toReal := by
    intro y
    have hle : y - τ ≤ y := by linarith
    have hunion : Iic (y - τ) ∪ Ioc (y - τ) y = Iic y := Iic_union_Ioc_eq_Iic hle
    have hdisj : Disjoint (Iic (y - τ)) (Ioc (y - τ) y) := by
      rw [Set.disjoint_left]
      intro a ha ha'
      exact absurd ha' (by simp only [Set.mem_Ioc, not_and_or, not_lt]; exact Or.inl ha)
    have h := measure_union (μ := μ) hdisj measurableSet_Ioc
    rw [hunion] at h
    rw [h, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
    ring
  -- a measurable representative of the density
  set p₀ : ℝ → ℝ := hpmeas.mk p with hp₀def
  have hp₀m : Measurable p₀ := hpmeas.measurable_mk
  have hpp₀ : p =ᵐ[volume] p₀ := hpmeas.ae_eq_mk
  have hpos₀ : 0 ≤ᵐ[volume] p₀ := by
    filter_upwards [hpos, hpp₀] with x hx hx'
    simpa [← hx'] using hx
  have hμeq : μ = volume.withDensity fun x => ENNReal.ofReal (p₀ x) := by
    rw [hp]
    refine withDensity_congr_ae ?_
    filter_upwards [hpp₀] with x hx
    rw [hx]
  -- the two sides, as integrable measurable functions
  set A : ℝ → ℝ := fun z => (μ (Ioc (z - τ) z)).toReal with hA
  have hAm : Measurable A := measurable_windowMassReal μ τ
  have hAi : Integrable A volume := integrable_windowMassReal μ τ
  have hAτi : Integrable (fun z : ℝ => A (z + τ)) volume := by
    simpa [sub_neg_eq_add] using integrable_translate hAi (-τ)
  have hmom : Integrable (fun x : ℝ => |x|) μ := cin_law_integrable_abs hsym hcos
  have hid : Integrable (fun x : ℝ => x) μ := by
    refine (integrable_norm_iff (f := fun x : ℝ => x) ?_).mp ?_
    · exact aestronglyMeasurable_id
    · simpa [Real.norm_eq_abs] using hmom
  have hxp₀ : Integrable (fun x : ℝ => x * p₀ x) volume := by
    have hlt : ∀ᵐ x ∂(volume : Measure ℝ), ENNReal.ofReal (p₀ x) < ⊤ :=
      .of_forall fun x => ENNReal.ofReal_lt_top
    have hstep := (integrable_withDensity_iff (μ := (volume : Measure ℝ))
      (f := fun x => ENNReal.ofReal (p₀ x)) (by fun_prop) hlt (g := fun x : ℝ => x)).mp
      (by rw [← hμeq]; exact hid)
    refine hstep.congr ?_
    filter_upwards [hpos₀] with x hx
    rw [ENNReal.toReal_ofReal hx]
  set F₁ : ℝ → ℝ := fun x => 2 * (x * p₀ x) with hF₁
  set F₂ : ℝ → ℝ := fun x => A x - A (x + τ) with hF₂
  have hF₁m : Measurable F₁ := by fun_prop
  have hF₂m : Measurable F₂ := by fun_prop
  have hF₁i : Integrable F₁ volume := hxp₀.const_mul 2
  have hF₂i : Integrable F₂ volume := hAi.sub hAτi
  set D : ℝ → ℝ := fun x => F₁ x - F₂ x with hD
  have hDm : Measurable D := hF₁m.sub hF₂m
  have hDi : Integrable D volume := hF₁i.sub hF₂i
  -- the sign of the defect is a legitimate test function
  set g : ℝ → ℝ := fun x => if 0 ≤ D x then (1 : ℝ) else -1 with hg
  have hgm : Measurable g :=
    Measurable.ite (measurableSet_le measurable_const hDm) measurable_const measurable_const
  have hgb : ∀ x, |g x| ≤ 1 := by
    intro x
    by_cases hx : 0 ≤ D x <;> simp [hg, hx]
  have hgF₁ : Integrable (fun x => g x * F₁ x) volume := by
    refine hF₁i.bdd_mul (c := 1) hgm.aestronglyMeasurable (.of_forall fun x => ?_)
    simpa [Real.norm_eq_abs] using hgb x
  have hgF₂ : Integrable (fun x => g x * F₂ x) volume := by
    refine hF₂i.bdd_mul (c := 1) hgm.aestronglyMeasurable (.of_forall fun x => ?_)
    simpa [Real.norm_eq_abs] using hgb x
  have hkey := cin_delay_pairing_density hτ μ hsym hcos p hpmeas hp hpos hgm hgb
  have hkey₁ : ∫ x, g x * F₁ x = ∫ x, g x * (2 * (x * p x)) := by
    refine integral_congr_ae ?_
    filter_upwards [hpp₀] with x hx
    simp only [hF₁, hx]
  have hkey₂ : ∫ x, g x * F₂ x
      = ∫ x, g x * ((μ (Ioc (x - τ) x)).toReal - (μ (Ioc (x + τ - τ) (x + τ))).toReal) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    rw [hF₂, hA]
  have hzero : ∫ x, |D x| = 0 := by
    have hsplit : ∫ x, |D x| = (∫ x, g x * F₁ x) - ∫ x, g x * F₂ x := by
      rw [← integral_sub hgF₁ hgF₂]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only []
      by_cases hx : 0 ≤ D x
      · rw [abs_of_nonneg hx, hD]
        simp only [hg, if_pos hx]
        ring
      · rw [abs_of_neg (lt_of_not_ge hx), hD]
        simp only [hg, if_neg hx]
        ring
    rw [hsplit, hkey₁, hkey₂, hkey]
    ring
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => abs_nonneg (D x)) hDi.abs).mp hzero
  filter_upwards [hae, hpp₀] with x hx hx'
  have hD0 : D x = 0 := by
    have : |D x| = 0 := hx
    exact abs_eq_zero.mp this
  simp only [hD, hF₁, hF₂, hA] at hD0
  have hcdfx := hcdf x
  have hcdfx' := hcdf (x + τ)
  have hxτ : x + τ - τ = x := by ring
  rw [hxτ] at hcdfx' hD0
  rw [hx']
  linarith [hD0, hcdfx, hcdfx']

end SpatialLine
