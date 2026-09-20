/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.GeneratorCommute
import SpatialLine.ExponentContinuity
import SpatialLine.GeneratorFourier
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The signal-side scale evolution

Blueprint: `eq:evolution-signal`, the last clause of `prop:scale-evolution`
(`blueprint/src/parts/11-generator.tex`).
-/

namespace SpatialLine

open MeasureTheory Set Filter
open scoped ENNReal Topology FourierTransform

/-! ## The real pairing with a character -/

/-- The pairing of a function with the character `κ_φ(z) = cos(ωz - φ)`. -/
noncomputable def karPair (h : ℝ → ℝ) (ω φ : ℝ) : ℝ := ∫ z, kar ω φ z * h z

/-- The pairing at the phase `ωx`: `∫h(z)cos(ω(x - z))\,dz`, the real form of the Fourier
integrand at the point `x`. -/
noncomputable def cosPair (h : ℝ → ℝ) (x ω : ℝ) : ℝ := karPair h ω (ω * x)

theorem integrable_kar_mul' {h : ℝ → ℝ} (hint : Integrable h) (ω φ : ℝ) :
    Integrable (fun z => kar ω φ z * h z) volume :=
  hint.bdd_mul (continuous_kar ω φ).aestronglyMeasurable
    (.of_forall fun x => by rw [Real.norm_eq_abs]; exact abs_kar_le ω φ x)

theorem abs_karPair_le {h : ℝ → ℝ} (hint : Integrable h) (ω φ : ℝ) :
    |karPair h ω φ| ≤ ∫ z, |h z| := by
  calc |karPair h ω φ| ≤ ∫ z, |kar ω φ z * h z| := abs_integral_le_integral_abs
    _ ≤ ∫ z, |h z| :=
        integral_mono (integrable_kar_mul' hint ω φ).abs hint.abs (fun z => by
          rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) (abs_kar_le ω φ z))

/-- **The Schwartz decay of the pairing**, uniform in the phase: `|⟨κ_φ, f⟩| ≤ C/(1 + ω²)`.

Proved from the two crude bounds `|⟨κ_φ,f⟩| ≤ ‖f‖₁` and `ω²|⟨κ_φ,f⟩| = |⟨κ_φ,f''⟩| ≤ ‖f''‖₁`,
the second being `integral_kar_mul_iteratedDeriv_two`. That is all the decay this chapter needs,
and it avoids the Schwartz-space Fourier machinery entirely: applied once to `f` and once to
`f''` it gives both the integrability of the frequency integral and the quadratic weight the
differentiation under it wants. -/
theorem exists_bound_karPair (f : SignalClass) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ω φ : ℝ, |karPair (⇑f) ω φ| ≤ C * (1 + ω ^ 2)⁻¹ := by
  set f2 : SignalClass := SchwartzMap.derivCLM ℝ ℝ (SchwartzMap.derivCLM ℝ ℝ f) with hf2
  have hnn1 : (0:ℝ) ≤ ∫ z, |f z| := integral_nonneg fun z => abs_nonneg _
  have hnn2 : (0:ℝ) ≤ ∫ z, |f2 z| := integral_nonneg fun z => abs_nonneg _
  refine ⟨(∫ z, |f z|) + ∫ z, |f2 z|, by positivity, fun ω φ => ?_⟩
  have h1 : |karPair (⇑f) ω φ| ≤ ∫ z, |f z| := abs_karPair_le f.integrable ω φ
  have h2 : ω ^ 2 * |karPair (⇑f) ω φ| ≤ ∫ z, |f2 z| := by
    have hkey : ∫ z, kar ω φ z * iteratedDeriv 2 (⇑f) z = -ω ^ 2 * karPair (⇑f) ω φ :=
      integral_kar_mul_iteratedDeriv_two ω φ f
    have heq : karPair (⇑f2) ω φ = -ω ^ 2 * karPair (⇑f) ω φ := by
      rw [karPair, ← hkey]
      refine integral_congr_ae (.of_forall fun z => ?_)
      exact congrArg (fun r => kar ω φ z * r) (iteratedDeriv_two_schwartz f z).symm
    have hb := abs_karPair_le f2.integrable ω φ
    rw [heq, abs_mul, abs_neg, abs_of_nonneg (sq_nonneg ω)] at hb
    exact hb
  have hpos : (0 : ℝ) < 1 + ω ^ 2 := by positivity
  rw [show ((∫ z, |f z|) + ∫ z, |f2 z|) * (1 + ω ^ 2)⁻¹
      = ((∫ z, |f z|) + ∫ z, |f2 z|) / (1 + ω ^ 2) by ring, le_div_iff₀ hpos]
  nlinarith

/-- The pairing at the phase `ωx`, split into its cosine and sine halves. -/
theorem cosPair_eq {h : ℝ → ℝ} (hint : Integrable h) (x ω : ℝ) :
    cosPair h x ω
      = karPair h ω 0 * Real.cos (ω * x) + karPair h ω (Real.pi / 2) * Real.sin (ω * x) := by
  have hc := integrable_kar_mul' hint ω 0
  have hs := integrable_kar_mul' hint ω (Real.pi / 2)
  rw [cosPair, karPair, karPair, karPair, ← integral_mul_const, ← integral_mul_const,
    ← integral_add (hc.mul_const _) (hs.mul_const _)]
  refine integral_congr_ae (.of_forall fun z => ?_)
  simp only [kar_zero, kar_pi_div_two]
  show Real.cos (ω * z - ω * x) * h z
      = Real.cos (ω * z) * h z * Real.cos (ω * x)
        + Real.sin (ω * z) * h z * Real.sin (ω * x)
  rw [Real.cos_sub]
  ring

theorem abs_cosPair_le {h : ℝ → ℝ} (hint : Integrable h) (x ω : ℝ) :
    |cosPair h x ω| ≤ |karPair h ω 0| + |karPair h ω (Real.pi / 2)| := by
  rw [cosPair_eq hint x ω]
  refine le_trans (abs_add_le _ _) (add_le_add ?_ ?_) <;>
    rw [abs_mul]
  · exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  · exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)

/-- The pairing is continuous in the frequency, by dominated convergence against `|h|`. -/
theorem continuous_karPair {h : ℝ → ℝ} (hint : Integrable h) (φ : ℝ) :
    Continuous (fun ω => karPair h ω φ) := by
  refine continuous_of_dominated (F := fun ω z => kar ω φ z * h z) (bound := fun z => |h z|)
    (fun ω => (integrable_kar_mul' hint ω φ).aestronglyMeasurable) ?_ hint.abs ?_
  · intro ω
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) (abs_kar_le ω φ z)
  · filter_upwards with z
    show Continuous fun ω => Real.cos (ω * z - φ) * h z
    fun_prop

/-! ## The pairing against a symmetric measure -/

/-- The sine transform of a symmetric finite measure vanishes. -/
theorem integral_sin_mul_eq_zero_of_symmetric {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hsym : IsSymmetric ν) (ω : ℝ) : ∫ y, Real.sin (ω * y) ∂ν = 0 := by
  have h2 : ∫ y, Real.sin (ω * y) ∂ν = ∫ y, Real.sin (ω * (-y)) ∂ν := by
    conv_lhs => rw [← hsym]
    rw [integral_map measurable_neg.aemeasurable (by fun_prop)]
  have h3 : ∫ y, Real.sin (ω * (-y)) ∂ν = -∫ y, Real.sin (ω * y) ∂ν := by
    rw [← integral_neg]
    refine integral_congr_ae (.of_forall fun y => ?_)
    simp [mul_neg, Real.sin_neg]
  linarith [h2.trans h3]

/-- **Smoothing acts on the Fourier integrand by the transform**: averaging the pairing over
translations by a symmetric finite measure multiplies it by that measure's cosine transform.

This is where the symmetry of the kernels is spent, and it is the only place. -/
theorem integral_cosPair_translate {h : ℝ → ℝ} (hint : Integrable h) {ν : Measure ℝ}
    [IsFiniteMeasure ν] (hsym : IsSymmetric ν) (x ω : ℝ) :
    ∫ y, cosPair h (x - y) ω ∂ν = fourierCos ν ω * cosPair h x ω := by
  set C := karPair h ω 0 with hC
  set S := karPair h ω (Real.pi / 2) with hS
  have hpt : ∀ y : ℝ, cosPair h (x - y) ω
      = (C * Real.cos (ω * x) + S * Real.sin (ω * x)) * Real.cos (ω * y)
        + (C * Real.sin (ω * x) - S * Real.cos (ω * x)) * Real.sin (ω * y) := by
    intro y
    rw [cosPair_eq hint (x - y) ω, mul_sub, Real.cos_sub, Real.sin_sub]
    ring
  rw [integral_congr_ae (.of_forall hpt),
    integral_add ((integrable_cos_mul ν ω).const_mul _) ((integrable_sin_mul ν ω).const_mul _),
    integral_const_mul, integral_const_mul, integral_sin_mul_eq_zero_of_symmetric hsym ω,
    mul_zero, add_zero, cosPair_eq hint x ω, ← fourierCos_apply]
  ring

/-! ## Fourier inversion in real form

Mathlib's inversion is complex and carries the `2\pi` in the exponent. Rather than convert the
convention, the frequency variable `w` of Mathlib's transform is carried through the whole
clause and the article's frequency `\omega = 2\pi w` appears only inside the integrand; nothing
below ever divides by `2\pi`. -/

/-- The real part of the phase-shifted complex transform is the real pairing at that phase. -/
theorem re_exp_mul_fourier {h : ℝ → ℝ} (hint : Integrable h) (x w : ℝ) :
    (Complex.exp ((2 * Real.pi * (w * x) : ℝ) * Complex.I)
        * 𝓕 (fun z => (h z : ℂ)) w).re
      = cosPair h x (2 * Real.pi * w) := by
  have hg : Integrable (fun z : ℝ =>
      Complex.exp (((-2 * Real.pi * z * w : ℝ) : ℂ) * Complex.I) * (h z : ℂ)) volume :=
    (hint.ofReal (𝕜 := ℂ)).bdd_mul (by fun_prop)
      (.of_forall fun z => le_of_eq (Complex.norm_exp_ofReal_mul_I _))
  have hGint := hg.const_mul (Complex.exp (((2 * Real.pi * (w * x) : ℝ) : ℂ) * Complex.I))
  have hpt : ∀ z : ℝ,
      (Complex.exp (((2 * Real.pi * (w * x) : ℝ) : ℂ) * Complex.I)
        * (Complex.exp (((-2 * Real.pi * z * w : ℝ) : ℂ) * Complex.I) * (h z : ℂ))).re
        = kar (2 * Real.pi * w) (2 * Real.pi * w * x) z * h z := by
    intro z
    rw [← mul_assoc, ← Complex.exp_add, ← add_mul, ← Complex.ofReal_add, Complex.mul_re,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Complex.ofReal_re,
      Complex.ofReal_im]
    have harg : 2 * Real.pi * (w * x) + -2 * Real.pi * z * w
        = -(2 * Real.pi * w * z - 2 * Real.pi * w * x) := by ring
    rw [harg, Real.cos_neg]
    show Real.cos (2 * Real.pi * w * z - 2 * Real.pi * w * x) * h z - _ * 0
      = Real.cos (2 * Real.pi * w * z - 2 * Real.pi * w * x) * h z
    ring
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  rw [← integral_const_mul, ← RCLike.re_to_complex, ← integral_re hGint, cosPair, karPair]
  exact integral_congr_ae (.of_forall hpt)

/-- **Fourier inversion in the article's real form**: an integrable continuous function whose
complex transform is integrable is the frequency integral of its own pairing.

`h(x) = \int (\int h(z)\cos(2\pi w(x - z))\,dz)\,dw`. Machine-checked from Mathlib's
`Integrable.fourierInv_fourier_eq` by taking real parts twice. -/
theorem inversion_cosPair {h : ℝ → ℝ} (hcont : Continuous h) (hint : Integrable h)
    (hFint : Integrable (𝓕 (fun z => (h z : ℂ)))) (x : ℝ) :
    h x = ∫ w, cosPair h x (2 * Real.pi * w) := by
  have hcx : Integrable (fun z => (h z : ℂ)) := hint.ofReal
  have hcont' : ContinuousAt (fun z => ((h z : ℝ) : ℂ)) x :=
    (Complex.continuous_ofReal.comp hcont).continuousAt
  have hinv : 𝓕⁻ (𝓕 (fun z => (h z : ℂ))) x = ((h x : ℝ) : ℂ) :=
    hcx.fourierInv_fourier_eq hFint hcont'
  have hrepr : 𝓕⁻ (𝓕 (fun z => (h z : ℂ))) x
      = ∫ w : ℝ, Complex.exp (((2 * Real.pi * (w * x) : ℝ) : ℂ) * Complex.I)
          * 𝓕 (fun z => (h z : ℂ)) w := by
    rw [Real.fourierInv_eq']
    refine integral_congr_ae (.of_forall fun v => ?_)
    show Complex.exp (((2 * Real.pi * inner ℝ v x : ℝ) : ℂ) * Complex.I) • _ = _
    rw [smul_eq_mul]
    congr 3
    norm_cast
    rw [RCLike.inner_apply]
    simp [mul_comm]
  have hEint : Integrable (fun w : ℝ =>
      Complex.exp (((2 * Real.pi * (w * x) : ℝ) : ℂ) * Complex.I)
        * 𝓕 (fun z => (h z : ℂ)) w) volume :=
    hFint.bdd_mul (by fun_prop) (.of_forall fun w => by
      rw [Complex.norm_exp_ofReal_mul_I])
  have := congrArg Complex.re (hrepr.symm.trans hinv)
  rw [Complex.ofReal_re, ← RCLike.re_to_complex, ← integral_re hEint] at this
  rw [← this]
  refine integral_congr_ae (.of_forall fun w => ?_)
  show RCLike.re (Complex.exp (((2 * Real.pi * (w * x) : ℝ) : ℂ) * Complex.I)
      * 𝓕 (fun z => (h z : ℂ)) w) = cosPair h x (2 * Real.pi * w)
  rw [RCLike.re_to_complex]
  exact re_exp_mul_fourier hint x w


/-! ## Two decay estimates -/

/-- The second derivative of a Schwartz function pairs against a character as `-ω²` times the
function itself. -/
theorem karPair_deriv_two (f : SignalClass) (ω φ : ℝ) :
    karPair (⇑(SchwartzMap.derivCLM ℝ ℝ (SchwartzMap.derivCLM ℝ ℝ f))) ω φ
      = -ω ^ 2 * karPair (⇑f) ω φ := by
  rw [karPair, karPair, ← integral_kar_mul_iteratedDeriv_two ω φ f]
  exact integral_congr_ae (.of_forall fun z =>
    congrArg (fun r => kar ω φ z * r) (iteratedDeriv_two_schwartz f z).symm)

/-- **The quartic decay of the pairing**: `exists_bound_karPair` iterated once. This is the
decay the frequency integral of the generator needs — the symbol grows quadratically, so a
single power of `(1 + ω²)` is exactly cancelled and nothing is left to integrate. -/
theorem exists_bound_karPair_two (f : SignalClass) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ω φ : ℝ, |karPair (⇑f) ω φ| ≤ C * ((1 + ω ^ 2) ^ 2)⁻¹ := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_bound_karPair f
  obtain ⟨C₂, hC₂0, hC₂⟩ :=
    exists_bound_karPair (SchwartzMap.derivCLM ℝ ℝ (SchwartzMap.derivCLM ℝ ℝ f))
  refine ⟨C₁ + C₂, by linarith, fun ω φ => ?_⟩
  have hpos : (0 : ℝ) < 1 + ω ^ 2 := by positivity
  have h1 : (1 + ω ^ 2) * |karPair (⇑f) ω φ| ≤ C₁ := by
    have := hC₁ ω φ
    rw [show C₁ * (1 + ω ^ 2)⁻¹ = C₁ / (1 + ω ^ 2) by ring, le_div_iff₀ hpos] at this
    nlinarith
  have hsq : |karPair (⇑(SchwartzMap.derivCLM ℝ ℝ (SchwartzMap.derivCLM ℝ ℝ f))) ω φ|
      = ω ^ 2 * |karPair (⇑f) ω φ| := by
    rw [karPair_deriv_two f ω φ, abs_mul, abs_neg, abs_of_nonneg (sq_nonneg ω)]
  have h2 : (1 + ω ^ 2) * (ω ^ 2 * |karPair (⇑f) ω φ|) ≤ C₂ := by
    have := hC₂ ω φ
    rw [hsq, show C₂ * (1 + ω ^ 2)⁻¹ = C₂ / (1 + ω ^ 2) by ring, le_div_iff₀ hpos] at this
    nlinarith
  have hpos2 : (0 : ℝ) < (1 + ω ^ 2) ^ 2 := by positivity
  rw [show (C₁ + C₂) * ((1 + ω ^ 2) ^ 2)⁻¹ = (C₁ + C₂) / (1 + ω ^ 2) ^ 2 by ring,
    le_div_iff₀ hpos2]
  nlinarith

/-- `(1 + (2πw)²)⁻¹ ≤ (1 + w²)⁻¹`: the frequency variable of Mathlib's transform is `ω/(2π)`,
and the conversion costs nothing in the majorants because `2π > 1`. -/
theorem inv_one_add_sq_two_pi_le (w : ℝ) :
    (1 + (2 * Real.pi * w) ^ 2)⁻¹ ≤ (1 + w ^ 2)⁻¹ := by
  have hpi : (1 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  have hsq : (1 : ℝ) * (1 : ℝ) ≤ (2 * Real.pi) * (2 * Real.pi) := by nlinarith
  have h : (1 : ℝ) + w ^ 2 ≤ 1 + (2 * Real.pi * w) ^ 2 := by
    have : w ^ 2 ≤ (2 * Real.pi * w) ^ 2 := by nlinarith [sq_nonneg w]
    linarith
  exact inv_anti₀ (by positivity) h

/-! ## The symbol: nonnegative, continuous, of quadratic growth -/

theorem symbol_nonneg (a : ℝ) (ϖ : Measure ℝ) (ω : ℝ) : 0 ≤ symbol a ϖ ω := ENNReal.toReal_nonneg

/-- **`lem:quadratic-growth` at the symbol.** `B(ω) ≤ K(1 + ω²)`, from the truncation
`1 - cos ωv ≤ (2 + ω²)(1 ∧ v²)` and the Lévy condition at the Choquet measure. -/
theorem exists_bound_symbol (P : SDProfile) {ϖ : Measure ℝ} (hϖ : HasProfileTail P.k ϖ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ω : ℝ, symbol P.a ϖ ω ≤ K * (1 + ω ^ 2) := by
  have hne := lintegral_min_one_sq_ne_top hϖ
  set I : ℝ := ∫ v, min 1 (v ^ 2) ∂ϖ with hI
  have hI0 : 0 ≤ I := integral_nonneg fun v => le_min zero_le_one (sq_nonneg v)
  refine ⟨2 * P.a + 2 * I, by nlinarith [P.a_nonneg], fun ω => ?_⟩
  have hjump : (∫ v, (1 - Real.cos (ω * v)) ∂ϖ) ≤ (2 + ω ^ 2) * I := by
    rw [hI, ← integral_const_mul]
    exact integral_mono (integrable_one_sub_cos hne ω)
      ((integrable_min_one_sq hne).const_mul _) (fun v => one_sub_cos_le ω v)
  rw [symbol_eq_add P hϖ ω]
  nlinarith [P.a_nonneg, sq_nonneg ω]

theorem continuous_symbol (P : SDProfile) {ϖ : Measure ℝ} (hϖ : HasProfileTail P.k ϖ) :
    Continuous (symbol P.a ϖ) := by
  have hrw : symbol P.a ϖ = fun ω => 2 * P.a * ω ^ 2 + ∫ v, (1 - Real.cos (ω * v)) ∂ϖ :=
    funext fun ω => symbol_eq_add P hϖ ω
  rw [hrw]
  exact (by fun_prop : Continuous fun ω : ℝ => 2 * P.a * ω ^ 2).add
    (continuous_integral_one_sub_cos (lintegral_min_one_sq_ne_top hϖ))

/-! ## The complex transform in terms of the real pairings -/

/-- The imaginary part of the complex transform is minus the sine pairing. -/
theorem im_fourier_ofReal {h : ℝ → ℝ} (hint : Integrable h) (w : ℝ) :
    (𝓕 (fun z => (h z : ℂ)) w).im = -karPair h (2 * Real.pi * w) (Real.pi / 2) := by
  have hg : Integrable (fun z : ℝ =>
      Complex.exp (((-2 * Real.pi * z * w : ℝ) : ℂ) * Complex.I) * (h z : ℂ)) volume :=
    (hint.ofReal (𝕜 := ℂ)).bdd_mul (by fun_prop)
      (.of_forall fun z => le_of_eq (Complex.norm_exp_ofReal_mul_I _))
  have hpt : ∀ z : ℝ, (Complex.exp (((-2 * Real.pi * z * w : ℝ) : ℂ) * Complex.I)
      * (h z : ℂ)).im = -(kar (2 * Real.pi * w) (Real.pi / 2) z * h z) := by
    intro z
    rw [Complex.mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      Complex.ofReal_re, Complex.ofReal_im, kar_pi_div_two]
    have : -2 * Real.pi * z * w = -(2 * Real.pi * w * z) := by ring
    rw [this, Real.sin_neg]
    ring
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  rw [← RCLike.im_to_complex, ← integral_im hg, karPair, ← integral_neg]
  exact integral_congr_ae (.of_forall hpt)

/-- The real part of the complex transform is the cosine pairing. -/
theorem re_fourier_ofReal {h : ℝ → ℝ} (hint : Integrable h) (w : ℝ) :
    (𝓕 (fun z => (h z : ℂ)) w).re = karPair h (2 * Real.pi * w) 0 := by
  have h0 := re_exp_mul_fourier hint 0 w
  rw [mul_zero, mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul,
    cosPair, mul_zero] at h0
  exact h0

/-- **The complex transform of a real integrable function**, written in the two real pairings.
Everything the clause needs about Mathlib's transform passes through this identity. -/
theorem fourier_ofReal_eq {h : ℝ → ℝ} (hint : Integrable h) (w : ℝ) :
    𝓕 (fun z => (h z : ℂ)) w
      = (karPair h (2 * Real.pi * w) 0 : ℂ)
        - (karPair h (2 * Real.pi * w) (Real.pi / 2) : ℂ) * Complex.I := by
  refine Complex.ext ?_ ?_
  · rw [re_fourier_ofReal hint w]
    simp
  · rw [im_fourier_ofReal hint w]
    simp

theorem continuous_fourier_ofReal {h : ℝ → ℝ} (hint : Integrable h) :
    Continuous (𝓕 (fun z => (h z : ℂ))) := by
  have hrw : 𝓕 (fun z => (h z : ℂ))
      = fun w : ℝ => (karPair h (2 * Real.pi * w) 0 : ℂ)
        - (karPair h (2 * Real.pi * w) (Real.pi / 2) : ℂ) * Complex.I :=
    funext fun w => fourier_ofReal_eq hint w
  rw [hrw]
  have hc0 : Continuous fun w : ℝ => karPair h (2 * Real.pi * w) 0 :=
    (continuous_karPair hint 0).comp (continuous_const.mul continuous_id)
  have hc1 : Continuous fun w : ℝ => karPair h (2 * Real.pi * w) (Real.pi / 2) :=
    (continuous_karPair hint (Real.pi / 2)).comp (continuous_const.mul continuous_id)
  exact (Complex.continuous_ofReal.comp hc0).sub
    ((Complex.continuous_ofReal.comp hc1).mul continuous_const)

/-- The complex transform is integrable as soon as the two real pairings are dominated by an
integrable function of the frequency. -/
theorem integrable_fourier_ofReal_of_bound {h : ℝ → ℝ} (hint : Integrable h) {M : ℝ → ℝ}
    (hM : Integrable M) (hb : ∀ w : ℝ, |karPair h (2 * Real.pi * w) 0|
      + |karPair h (2 * Real.pi * w) (Real.pi / 2)| ≤ M w) :
    Integrable (𝓕 (fun z => (h z : ℂ))) :=
  Integrable.mono' hM (continuous_fourier_ofReal hint).aestronglyMeasurable
    (.of_forall fun w => by
      refine le_trans (Complex.norm_le_abs_re_add_abs_im _) ?_
      rw [re_fourier_ofReal hint w, im_fourier_ofReal hint w, abs_neg]
      exact hb w)

/-! ## The generator of a test signal: continuous, integrable, and its transform -/

/-- The symmetric second difference of a Schwartz function is bounded by `K(1 ∧ v²)`, uniformly
in the base point: the Taylor bound below the truncation and the sup-norm bound above it. -/
theorem exists_bound_secondDifference (f : SignalClass) (t : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x v : ℝ,
      |(f : ℝ → ℝ) x - ((f : ℝ → ℝ) (x - t * v) + (f : ℝ → ℝ) (x + t * v)) / 2|
        ≤ K * min 1 (v ^ 2) := by
  obtain ⟨Cf, hCf⟩ := SignalClass.exists_bound f
  obtain ⟨C₂, hC₂⟩ := SignalClass.exists_bound_iteratedDeriv_two f
  have hCf0 : 0 ≤ Cf := le_trans (abs_nonneg _) (hCf 0)
  have hC₂0 : 0 ≤ C₂ := le_trans (abs_nonneg _) (hC₂ 0)
  refine ⟨max (2 * Cf) (C₂ * t ^ 2), le_trans (by linarith) (le_max_left _ _), fun x v => ?_⟩
  have h1 : |(f : ℝ → ℝ) x - ((f : ℝ → ℝ) (x - t * v) + (f : ℝ → ℝ) (x + t * v)) / 2|
      ≤ C₂ * (t * v) ^ 2 := abs_secondDifference_le (f.smooth 2) hC₂ x (t * v)
  have h2 : |(f : ℝ → ℝ) x - ((f : ℝ → ℝ) (x - t * v) + (f : ℝ → ℝ) (x + t * v)) / 2|
      ≤ 2 * Cf := by
    have e2 := hCf x
    have e3 := hCf (x - t * v)
    have e4 := hCf (x + t * v)
    calc |(f : ℝ → ℝ) x - ((f : ℝ → ℝ) (x - t * v) + (f : ℝ → ℝ) (x + t * v)) / 2|
        ≤ |(f : ℝ → ℝ) x|
          + |((f : ℝ → ℝ) (x - t * v) + (f : ℝ → ℝ) (x + t * v)) / 2| := abs_sub _ _
      _ ≤ Cf + (|(f : ℝ → ℝ) (x - t * v)| + |(f : ℝ → ℝ) (x + t * v)|) / 2 := by
          rw [abs_div, abs_two]
          have := abs_add_le ((f : ℝ → ℝ) (x - t * v)) ((f : ℝ → ℝ) (x + t * v))
          linarith
      _ ≤ 2 * Cf := by linarith
  rcases le_total (v ^ 2) 1 with hv | hv
  · rw [min_eq_right hv]
    nlinarith [le_max_right (2 * Cf) (C₂ * t ^ 2), sq_nonneg v]
  · rw [min_eq_left hv, mul_one]
    exact le_trans h2 (le_max_left _ _)

theorem continuous_iteratedDeriv_two_signal (f : SignalClass) :
    Continuous (iteratedDeriv 2 (⇑f)) := by
  have h : iteratedDeriv 2 (⇑f)
      = ⇑(SchwartzMap.derivCLM ℝ (F := ℝ) (SchwartzMap.derivCLM ℝ (F := ℝ) f)) :=
    funext fun y => iteratedDeriv_two_schwartz f y
  rw [h]
  exact (SchwartzMap.derivCLM ℝ (F := ℝ) (SchwartzMap.derivCLM ℝ (F := ℝ) f)).continuous

/-- The generator of a test signal is continuous, by dominated convergence on the jump term. -/
theorem continuous_scaleGenerator_signal (P : SDProfile) {ϖ : Measure ℝ}
    (hϖ : HasProfileTail P.k ϖ) (t : ℝ) (f : SignalClass) :
    Continuous (scaleGenerator P.a ϖ t (⇑f)) := by
  obtain ⟨K, hK0, hK⟩ := exists_bound_secondDifference f t
  have hfc : Continuous (⇑f) := f.continuous
  have hjump : Continuous fun x : ℝ => ∫ v, ((f : ℝ → ℝ) x
      - ((f : ℝ → ℝ) (x - t * v) + (f : ℝ → ℝ) (x + t * v)) / 2) ∂ϖ := by
    refine continuous_of_dominated
      (F := fun x v : ℝ => (f : ℝ → ℝ) x
        - ((f : ℝ → ℝ) (x - t * v) + (f : ℝ → ℝ) (x + t * v)) / 2)
      (bound := fun v : ℝ => K * min 1 (v ^ 2)) (fun x => ?_) (fun x => ?_)
      ((integrable_min_one_sq (lintegral_min_one_sq_ne_top hϖ)).const_mul K) ?_
    · exact (Continuous.aestronglyMeasurable (by
        exact continuous_const.sub (((hfc.comp (continuous_const.sub
          (continuous_const.mul continuous_id))).add
          (hfc.comp (continuous_const.add (continuous_const.mul continuous_id)))).div_const 2)))
    · filter_upwards with v
      rw [Real.norm_eq_abs]
      exact hK x v
    · filter_upwards with v
      exact hfc.sub (((hfc.comp (by fun_prop : Continuous fun x : ℝ => x - t * v)).add
        (hfc.comp (by fun_prop : Continuous fun x : ℝ => x + t * v))).div_const 2)
  exact ((continuous_iteratedDeriv_two_signal f).const_mul _).sub (hjump.const_mul _)

/-- The generator of a test signal is integrable: the Gaussian term because `f''` is Schwartz,
the jump term as the marginal of the joint integrability the multiplier's Fubini already
established. -/
theorem integrable_scaleGenerator_signal (P : SDProfile) (ϖ : Measure ℝ)
    (hϖ : HasProfileTail P.k ϖ) (t : ℝ) (f : SignalClass) :
    Integrable (scaleGenerator P.a ϖ t (⇑f)) := by
  have h1 : Integrable (fun x : ℝ => 2 * P.a * t * iteratedDeriv 2 (⇑f) x) volume := by
    refine (((SchwartzMap.derivCLM ℝ (F := ℝ) (SchwartzMap.derivCLM ℝ (F := ℝ) f)).integrable
      (μ := (volume : Measure ℝ))).const_mul (2 * P.a * t)).congr (.of_forall fun x => ?_)
    exact congrArg (fun r => 2 * P.a * t * r) (iteratedDeriv_two_schwartz f x).symm
  haveI : SigmaFinite ϖ := sigmaFinite_of_hasProfileTail hϖ
  have hjoint := integrable_uncurry_kar_secondDifference P ϖ hϖ f 0 0 t
  have h2 : Integrable (fun x : ℝ => ∫ v, ((f : ℝ → ℝ) x
      - ((f : ℝ → ℝ) (x - t * v) + (f : ℝ → ℝ) (x + t * v)) / 2) ∂ϖ) volume := by
    refine (hjoint.integral_prod_left).congr (.of_forall fun x => ?_)
    refine integral_congr_ae (.of_forall fun v => ?_)
    show kar 0 0 x * ((f : ℝ → ℝ) x
        - ((f : ℝ → ℝ) (x - t * v) + (f : ℝ → ℝ) (x + t * v)) / 2)
      = (f : ℝ → ℝ) x - ((f : ℝ → ℝ) (x - t * v) + (f : ℝ → ℝ) (x + t * v)) / 2
    rw [kar_zero, zero_mul, Real.cos_zero, one_mul]
  exact h1.sub (h2.const_mul _)

/-! ## The scale space as a frequency integral -/

/-- The Fourier integrand is jointly continuous in the point and the frequency. -/
theorem continuous_cosPair_uncurry {h : ℝ → ℝ} (hint : Integrable h) :
    Continuous (fun p : ℝ × ℝ => cosPair h p.1 p.2) := by
  have hrw : (fun p : ℝ × ℝ => cosPair h p.1 p.2)
      = fun p : ℝ × ℝ => karPair h p.2 0 * Real.cos (p.2 * p.1)
          + karPair h p.2 (Real.pi / 2) * Real.sin (p.2 * p.1) :=
    funext fun p => cosPair_eq hint p.1 p.2
  rw [hrw]
  exact (((continuous_karPair hint 0).comp continuous_snd).mul
      (Real.continuous_cos.comp (continuous_snd.mul continuous_fst))).add
    (((continuous_karPair hint (Real.pi / 2)).comp continuous_snd).mul
      (Real.continuous_sin.comp (continuous_snd.mul continuous_fst)))

/-- **The scale-space representation.** For a symmetric finite `ν` and an `h` to which the
inversion applies, the smoothing `ν * h` is the frequency integral of the transform of `ν`
against the Fourier integrand of `h`.

This is the identity `eq:evolution-signal` is read through: at `h = f` it represents the scale
space, at `h = \mathcal{A}_tf` it represents the generator applied to it. -/
theorem mconv_eq_integral_cosPair {h : ℝ → ℝ} (hcont : Continuous h) (hint : Integrable h)
    (hFint : Integrable (𝓕 (fun z => (h z : ℂ)))) {M : ℝ → ℝ} (hM : Integrable M)
    (hbound : ∀ w : ℝ, |karPair h (2 * Real.pi * w) 0|
      + |karPair h (2 * Real.pi * w) (Real.pi / 2)| ≤ M w)
    {ν : Measure ℝ} [IsFiniteMeasure ν] (hsym : IsSymmetric ν) (x : ℝ) :
    mconv ν h x = ∫ w, fourierCos ν (2 * Real.pi * w) * cosPair h x (2 * Real.pi * w) := by
  have hjoint : Integrable
      (Function.uncurry fun (y w : ℝ) => cosPair h (x - y) (2 * Real.pi * w))
      (ν.prod volume) := by
    refine Integrable.mono' (g := fun p : ℝ × ℝ => M p.2) (hM.comp_snd ν) ?_ ?_
    · exact ((continuous_cosPair_uncurry hint).comp
        ((continuous_const.sub continuous_fst).prodMk
          (continuous_const.mul continuous_snd))).aestronglyMeasurable
    · filter_upwards with p
      rw [Real.norm_eq_abs]
      exact le_trans (abs_cosPair_le hint _ _) (hbound p.2)
  have hpt : ∀ y : ℝ, h (x - y) = ∫ w, cosPair h (x - y) (2 * Real.pi * w) :=
    fun y => inversion_cosPair hcont hint hFint (x - y)
  rw [mconv_apply, integral_congr_ae (.of_forall hpt), integral_integral_swap hjoint]
  refine integral_congr_ae (.of_forall fun w => ?_)
  exact integral_cosPair_translate hint hsym x (2 * Real.pi * w)

/-! ## The two representations, and the differentiation in the scale -/

theorem SDProfile.exponent_nonneg (P : SDProfile) (ω : ℝ) : 0 ≤ P.exponent ω :=
  ENNReal.toReal_nonneg

theorem exp_neg_exponent_le_one (P : SDProfile) (ω : ℝ) :
    Real.exp (-P.exponent ω) ≤ 1 :=
  Real.exp_le_one_iff.mpr (neg_nonpos.mpr (P.exponent_nonneg ω))

/-- **The multiplier identity in the pairing notation**, at every phase and every scale. -/
theorem karPair_scaleGenerator (P : SDProfile) (ϖ : Measure ℝ) (hϖ : HasProfileTail P.k ϖ)
    (f : SignalClass) (ω φ : ℝ) {t : ℝ} (ht : 0 < t) :
    karPair (scaleGenerator P.a ϖ t (⇑f)) ω φ
      = -(t⁻¹ * symbol P.a ϖ (t * ω)) * karPair (⇑f) ω φ :=
  integral_kar_mul_scaleGenerator P ϖ hϖ f ω φ ht

/-- The generator's pairing decays like `(1 + ω²)⁻¹`: the symbol's quadratic growth eats exactly
one of the two powers `exists_bound_karPair_two` supplies. -/
theorem exists_bound_karPair_scaleGenerator (P : SDProfile) (ϖ : Measure ℝ)
    (hϖ : HasProfileTail P.k ϖ) (f : SignalClass) {t : ℝ} (ht : 0 < t) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ ω φ : ℝ,
      |karPair (scaleGenerator P.a ϖ t (⇑f)) ω φ| ≤ D * (1 + ω ^ 2)⁻¹ := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_karPair_two f
  obtain ⟨K, hK0, hK⟩ := exists_bound_symbol P hϖ
  have hti : (0 : ℝ) < t⁻¹ := inv_pos.mpr ht
  refine ⟨t⁻¹ * K * (1 + t ^ 2) * C, by positivity, fun ω φ => ?_⟩
  have hu : (0 : ℝ) < 1 + ω ^ 2 := by positivity
  have hS0 : 0 ≤ symbol P.a ϖ (t * ω) := symbol_nonneg _ _ _
  have hSb : symbol P.a ϖ (t * ω) ≤ K * (1 + t ^ 2) * (1 + ω ^ 2) := by
    have h := hK (t * ω)
    nlinarith [sq_nonneg t, sq_nonneg ω, sq_nonneg (t * ω), hK0]
  have hAb := hC ω φ
  rw [karPair_scaleGenerator P ϖ hϖ f ω φ ht, abs_mul, abs_neg, abs_mul,
    abs_of_nonneg hti.le, abs_of_nonneg hS0]
  have h1 : symbol P.a ϖ (t * ω) * |karPair (⇑f) ω φ|
      ≤ (K * (1 + t ^ 2) * (1 + ω ^ 2)) * (C * ((1 + ω ^ 2) ^ 2)⁻¹) :=
    mul_le_mul hSb hAb (abs_nonneg _) (by positivity)
  calc t⁻¹ * symbol P.a ϖ (t * ω) * |karPair (⇑f) ω φ|
      ≤ t⁻¹ * ((K * (1 + t ^ 2) * (1 + ω ^ 2)) * (C * ((1 + ω ^ 2) ^ 2)⁻¹)) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left h1 hti.le
    _ = t⁻¹ * K * (1 + t ^ 2) * C * (1 + ω ^ 2)⁻¹ := by
        field_simp

set_option maxHeartbeats 1600000 in
/-- **Differentiation under the frequency integral in the scale.** The dominating function is
`(2/t)K(1 + (3t/2)^2 w^2)` times the pairing's own majorant, for `s` in the ball of radius `t/2`
about `t`; it is `lem:quadratic-growth` at the symbol against the quartic decay of the pairing,
and the first summand of the constant is what covers the undifferentiated integrand. -/
theorem hasDerivAt_integral_transfer (P : SDProfile) (ϖ : Measure ℝ)
    (hϖ : HasProfileTail P.k ϖ) (f : SignalClass) (x : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => ∫ w, Real.exp (-P.exponent (s * (2 * Real.pi * w)))
        * cosPair (⇑f) x (2 * Real.pi * w))
      (∫ w, -(t⁻¹ * symbol P.a ϖ (t * (2 * Real.pi * w)))
        * Real.exp (-P.exponent (t * (2 * Real.pi * w)))
        * cosPair (⇑f) x (2 * Real.pi * w)) t := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_karPair_two f
  obtain ⟨K, hK0, hK⟩ := exists_bound_symbol P hϖ
  have ht2 : (0:ℝ) < 2 / t := by positivity
  set E : ℝ := 2 / t * (K * (1 + 9 * t ^ 2 / 4)) * (2 * C) with hE
  have hE0 : 0 ≤ E := by rw [hE]; positivity
  set D : ℝ := 2 * C + E with hD
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  have hcosb : ∀ w : ℝ, |cosPair (⇑f) x (2 * Real.pi * w)|
      ≤ 2 * C * ((1 + (2 * Real.pi * w) ^ 2) ^ 2)⁻¹ := by
    intro w
    refine le_trans (abs_cosPair_le f.integrable x (2 * Real.pi * w)) ?_
    have h1 := hC (2 * Real.pi * w) 0
    have h2 := hC (2 * Real.pi * w) (Real.pi / 2)
    nlinarith
  have hsqle : ∀ w : ℝ, ((1 + (2 * Real.pi * w) ^ 2) ^ 2)⁻¹ ≤ (1 + w ^ 2)⁻¹ := by
    intro w
    refine le_trans ?_ (inv_one_add_sq_two_pi_le w)
    have h1 : (0:ℝ) < 1 + (2 * Real.pi * w) ^ 2 := by positivity
    have h2 : (1:ℝ) + (2 * Real.pi * w) ^ 2 ≤ (1 + (2 * Real.pi * w) ^ 2) ^ 2 := by nlinarith
    exact inv_anti₀ h1 h2
  have hcosb' : ∀ w : ℝ, |cosPair (⇑f) x (2 * Real.pi * w)| ≤ 2 * C * (1 + w ^ 2)⁻¹ := by
    intro w
    refine le_trans (hcosb w) (mul_le_mul_of_nonneg_left (hsqle w) (by positivity))
  have hcontcos : Continuous fun w : ℝ => cosPair (⇑f) x (2 * Real.pi * w) :=
    (continuous_cosPair_uncurry f.integrable).comp
      (continuous_const.prodMk (continuous_const.mul continuous_id))
  have hcontexp : ∀ s : ℝ, Continuous fun w : ℝ =>
      Real.exp (-P.exponent (s * (2 * Real.pi * w))) :=
    fun s => Real.continuous_exp.comp (P.continuous_exponent.neg.comp
      (continuous_const.mul (continuous_const.mul continuous_id)))
  have hbdint : Integrable (fun w : ℝ => D * (1 + w ^ 2)⁻¹) volume :=
    integrable_inv_one_add_sq.const_mul D
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun (s : ℝ) (w : ℝ) => Real.exp (-P.exponent (s * (2 * Real.pi * w)))
      * cosPair (⇑f) x (2 * Real.pi * w))
    (F' := fun (s : ℝ) (w : ℝ) => -(s⁻¹ * symbol P.a ϖ (s * (2 * Real.pi * w)))
      * Real.exp (-P.exponent (s * (2 * Real.pi * w))) * cosPair (⇑f) x (2 * Real.pi * w))
    (bound := fun w : ℝ => D * (1 + w ^ 2)⁻¹)
    (Metric.ball_mem_nhds t (by positivity : (0:ℝ) < t / 2))
    (.of_forall fun s => ((hcontexp s).mul hcontcos).aestronglyMeasurable) ?_
    (((((continuous_symbol P hϖ).comp
        (continuous_const.mul (continuous_const.mul continuous_id))).const_mul
        (t⁻¹)).neg.mul (hcontexp t)).mul hcontcos).aestronglyMeasurable
    ?_ hbdint ?_).2
  · refine Integrable.mono' hbdint ((hcontexp t).mul hcontcos).aestronglyMeasurable
      (.of_forall fun w => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_pos _).le]
    have h3 : (0:ℝ) ≤ (1 + w ^ 2)⁻¹ := by positivity
    have h6 : Real.exp (-P.exponent (t * (2 * Real.pi * w)))
        * |cosPair (⇑f) x (2 * Real.pi * w)| ≤ 1 * (2 * C * (1 + w ^ 2)⁻¹) :=
      mul_le_mul (exp_neg_exponent_le_one P _) (hcosb' w) (abs_nonneg _) zero_le_one
    calc Real.exp (-P.exponent (t * (2 * Real.pi * w)))
          * |cosPair (⇑f) x (2 * Real.pi * w)| ≤ 1 * (2 * C * (1 + w ^ 2)⁻¹) := h6
      _ = (2 * C) * (1 + w ^ 2)⁻¹ := by ring
      _ ≤ D * (1 + w ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_right (by rw [hD]; linarith) h3
  · refine .of_forall fun w => fun s hs => ?_
    have hd : |s - t| < t / 2 := by
      have hb := Metric.mem_ball.mp hs
      rwa [Real.dist_eq] at hb
    have hlt := abs_lt.mp hd
    have hs0 : 0 < s := by linarith [hlt.1]
    have hinv : s⁻¹ ≤ 2 / t := by
      have h1 : t / 2 ≤ s := by linarith [hlt.1]
      have h2 : (0:ℝ) < t / 2 := by positivity
      have h3 := one_div_le_one_div_of_le h2 h1
      rw [one_div, one_div] at h3
      refine le_trans h3 (le_of_eq ?_)
      field_simp
    have hSb : symbol P.a ϖ (s * (2 * Real.pi * w))
        ≤ K * (1 + 9 * t ^ 2 / 4) * (1 + (2 * Real.pi * w) ^ 2) := by
      have h := hK (s * (2 * Real.pi * w))
      have hs2 : s ^ 2 ≤ 9 * t ^ 2 / 4 := by nlinarith [hlt.1, hlt.2]
      have hexp : (s * (2 * Real.pi * w)) ^ 2 = s ^ 2 * (2 * Real.pi * w) ^ 2 := by ring
      have hmono : (1:ℝ) + s ^ 2 * (2 * Real.pi * w) ^ 2
          ≤ (1 + 9 * t ^ 2 / 4) * (1 + (2 * Real.pi * w) ^ 2) := by
        nlinarith [sq_nonneg (2 * Real.pi * w), sq_nonneg t, sq_nonneg s]
      calc symbol P.a ϖ (s * (2 * Real.pi * w)) ≤ K * (1 + (s * (2 * Real.pi * w)) ^ 2) := h
        _ = K * (1 + s ^ 2 * (2 * Real.pi * w) ^ 2) := by rw [hexp]
        _ ≤ K * ((1 + 9 * t ^ 2 / 4) * (1 + (2 * Real.pi * w) ^ 2)) :=
            mul_le_mul_of_nonneg_left hmono hK0
        _ = K * (1 + 9 * t ^ 2 / 4) * (1 + (2 * Real.pi * w) ^ 2) := by ring
    have hS0 : 0 ≤ symbol P.a ϖ (s * (2 * Real.pi * w)) := symbol_nonneg _ _ _
    have hE1 : Real.exp (-P.exponent (s * (2 * Real.pi * w))) ≤ 1 := exp_neg_exponent_le_one P _
    have hE0' : 0 < Real.exp (-P.exponent (s * (2 * Real.pi * w))) := Real.exp_pos _
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_neg, abs_mul,
      abs_of_nonneg (inv_pos.mpr hs0).le, abs_of_nonneg hS0, abs_of_nonneg hE0'.le]
    have hstep1 : s⁻¹ * symbol P.a ϖ (s * (2 * Real.pi * w))
        ≤ 2 / t * (K * (1 + 9 * t ^ 2 / 4) * (1 + (2 * Real.pi * w) ^ 2)) :=
      mul_le_mul hinv hSb hS0 ht2.le
    have hstep2 : Real.exp (-P.exponent (s * (2 * Real.pi * w)))
        * |cosPair (⇑f) x (2 * Real.pi * w)|
        ≤ 1 * (2 * C * ((1 + (2 * Real.pi * w) ^ 2) ^ 2)⁻¹) :=
      mul_le_mul hE1 (hcosb w) (abs_nonneg _) zero_le_one
    have hDw : (0:ℝ) ≤ (1 + (2 * Real.pi * w) ^ 2)⁻¹ := by positivity
    calc s⁻¹ * symbol P.a ϖ (s * (2 * Real.pi * w))
          * Real.exp (-P.exponent (s * (2 * Real.pi * w)))
          * |cosPair (⇑f) x (2 * Real.pi * w)|
        = (s⁻¹ * symbol P.a ϖ (s * (2 * Real.pi * w)))
          * (Real.exp (-P.exponent (s * (2 * Real.pi * w)))
            * |cosPair (⇑f) x (2 * Real.pi * w)|) := by ring
      _ ≤ (2 / t * (K * (1 + 9 * t ^ 2 / 4) * (1 + (2 * Real.pi * w) ^ 2)))
          * (1 * (2 * C * ((1 + (2 * Real.pi * w) ^ 2) ^ 2)⁻¹)) :=
            mul_le_mul hstep1 hstep2 (by positivity) (by positivity)
      _ = E * (1 + (2 * Real.pi * w) ^ 2)⁻¹ := by
            rw [hE]
            field_simp
      _ ≤ D * (1 + (2 * Real.pi * w) ^ 2)⁻¹ :=
            mul_le_mul_of_nonneg_right (by rw [hD]; linarith) hDw
      _ ≤ D * (1 + w ^ 2)⁻¹ :=
            mul_le_mul_of_nonneg_left (inv_one_add_sq_two_pi_le w) hD0
  · refine .of_forall fun w => fun s hs => ?_
    have hd : |s - t| < t / 2 := by
      have hb := Metric.mem_ball.mp hs
      rwa [Real.dist_eq] at hb
    have hlt := abs_lt.mp hd
    have hs0 : 0 < s := by linarith [hlt.1]
    exact (scale_evolution_fourier P ϖ hϖ (2 * Real.pi * w) hs0).mul_const _


/-- `((1 + (2πw)²)²)⁻¹ ≤ (1 + w²)⁻¹`: the majorant conversion used at both arguments. -/
theorem inv_one_add_sq_sq_two_pi_le (w : ℝ) :
    ((1 + (2 * Real.pi * w) ^ 2) ^ 2)⁻¹ ≤ (1 + w ^ 2)⁻¹ := by
  refine le_trans ?_ (inv_one_add_sq_two_pi_le w)
  have h1 : (0:ℝ) < 1 + (2 * Real.pi * w) ^ 2 := by positivity
  have h2 : (1:ℝ) + (2 * Real.pi * w) ^ 2 ≤ (1 + (2 * Real.pi * w) ^ 2) ^ 2 := by nlinarith
  exact inv_anti₀ h1 h2

/-! ## `eq:evolution-signal` -/

/-- **`eq:evolution-signal`**, the last clause of `prop:scale-evolution`: the scale space of a
test signal solves `∂_t u = \mathcal{A}_t u`, pointwise in the scale at a fixed position.

`Skeleton.scale_evolution_signal`'s type verbatim.

The route is the inversion representation read twice. The scale space is
`u(s,x) = \int e^{-F(s\omega)}\langle\kappa_{\omega x}, f\rangle\,dw` with `\omega = 2\pi w`
(`mconv_eq_integral_cosPair`, which is where the symmetry of the kernels is spent);
differentiating under that integral in the scale is `hasDerivAt_integral_transfer` and produces
`-t^{-1}B(t\omega)` in the integrand. The same representation applied to `\mathcal{A}_tf` —
which is legitimate because the generator is continuous and integrable there, and because
`scaleGenerator_mconv` moves the generator off the non-Schwartz `u(t,\cdot)` and onto `f` —
turns the multiplier identity `integral_kar_mul_scaleGenerator` into exactly that integrand. -/
theorem scale_evolution_signal (P : SDProfile) (ϖ : Measure ℝ) (hϖ : HasProfileTail P.k ϖ)
    (μ : ℝ → Measure ℝ) (hprob : ∀ s : ℝ, 0 < s → IsProbabilityMeasure (μ s))
    (hcos : ∀ s ω : ℝ, 0 < s → fourierCos (μ s) ω = Real.exp (-P.exponent (s * ω)))
    (hsym : ∀ s : ℝ, 0 < s → IsSymmetric (μ s))
    (f : SignalClass) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun s : ℝ => scaleSpace μ (⇑f) s x)
      (scaleGenerator P.a ϖ t (scaleSpace μ (⇑f) t) x) t := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_karPair_two f
  have hMfint : Integrable (fun w : ℝ => 2 * C * (1 + w ^ 2)⁻¹) volume :=
    integrable_inv_one_add_sq.const_mul _
  have hMfb : ∀ w : ℝ, |karPair (⇑f) (2 * Real.pi * w) 0|
      + |karPair (⇑f) (2 * Real.pi * w) (Real.pi / 2)| ≤ 2 * C * (1 + w ^ 2)⁻¹ := by
    intro w
    have h1 := hC (2 * Real.pi * w) 0
    have h2 := hC (2 * Real.pi * w) (Real.pi / 2)
    have h3 : C * ((1 + (2 * Real.pi * w) ^ 2) ^ 2)⁻¹ ≤ C * (1 + w ^ 2)⁻¹ :=
      mul_le_mul_of_nonneg_left (inv_one_add_sq_sq_two_pi_le w) hC0
    linarith
  have hFf : Integrable (𝓕 (fun z => ((f : ℝ → ℝ) z : ℂ))) :=
    integrable_fourier_ofReal_of_bound f.integrable hMfint hMfb
  obtain ⟨D, hD0, hD⟩ := exists_bound_karPair_scaleGenerator P ϖ hϖ f ht
  have hgint : Integrable (scaleGenerator P.a ϖ t (⇑f)) :=
    integrable_scaleGenerator_signal P ϖ hϖ t f
  have hgcont : Continuous (scaleGenerator P.a ϖ t (⇑f)) :=
    continuous_scaleGenerator_signal P hϖ t f
  have hMgint : Integrable (fun w : ℝ => 2 * D * (1 + w ^ 2)⁻¹) volume :=
    integrable_inv_one_add_sq.const_mul _
  have hMgb : ∀ w : ℝ, |karPair (scaleGenerator P.a ϖ t (⇑f)) (2 * Real.pi * w) 0|
      + |karPair (scaleGenerator P.a ϖ t (⇑f)) (2 * Real.pi * w) (Real.pi / 2)|
        ≤ 2 * D * (1 + w ^ 2)⁻¹ := by
    intro w
    have h1 := hD (2 * Real.pi * w) 0
    have h2 := hD (2 * Real.pi * w) (Real.pi / 2)
    have h3 : D * (1 + (2 * Real.pi * w) ^ 2)⁻¹ ≤ D * (1 + w ^ 2)⁻¹ :=
      mul_le_mul_of_nonneg_left (inv_one_add_sq_two_pi_le w) hD0
    linarith
  have hFg : Integrable (𝓕 (fun z => ((scaleGenerator P.a ϖ t (⇑f) z : ℝ) : ℂ))) :=
    integrable_fourier_ofReal_of_bound hgint hMgint hMgb
  have hrepr : ∀ s : ℝ, 0 < s → scaleSpace μ (⇑f) s x
      = ∫ w, Real.exp (-P.exponent (s * (2 * Real.pi * w)))
          * cosPair (⇑f) x (2 * Real.pi * w) := by
    intro s hs
    haveI := hprob s hs
    rw [scaleSpace,
      mconv_eq_integral_cosPair f.continuous f.integrable hFf hMfint hMfb (hsym s hs) x]
    refine integral_congr_ae (.of_forall fun w => ?_)
    show fourierCos (μ s) (2 * Real.pi * w) * cosPair (⇑f) x (2 * Real.pi * w) = _
    rw [hcos s (2 * Real.pi * w) hs]
  have heq : (∫ w, -(t⁻¹ * symbol P.a ϖ (t * (2 * Real.pi * w)))
        * Real.exp (-P.exponent (t * (2 * Real.pi * w)))
        * cosPair (⇑f) x (2 * Real.pi * w))
      = scaleGenerator P.a ϖ t (scaleSpace μ (⇑f) t) x := by
    haveI := hprob t ht
    have h1 : scaleSpace μ (⇑f) t = mconv (μ t) (⇑f) := rfl
    rw [h1, scaleGenerator_mconv (μ t) P hϖ t f x,
      mconv_eq_integral_cosPair hgcont hgint hFg hMgint hMgb (hsym t ht) x]
    refine integral_congr_ae (.of_forall fun w => ?_)
    show -(t⁻¹ * symbol P.a ϖ (t * (2 * Real.pi * w)))
        * Real.exp (-P.exponent (t * (2 * Real.pi * w)))
        * cosPair (⇑f) x (2 * Real.pi * w)
      = fourierCos (μ t) (2 * Real.pi * w)
        * cosPair (scaleGenerator P.a ϖ t (⇑f)) x (2 * Real.pi * w)
    rw [hcos t (2 * Real.pi * w) ht, cosPair, cosPair,
      karPair_scaleGenerator P ϖ hϖ f (2 * Real.pi * w) (2 * Real.pi * w * x) ht]
    ring
  rw [← heq]
  refine (hasDerivAt_integral_transfer P ϖ hϖ f x ht).congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds ht] with s hs
  exact hrepr s hs

end SpatialLine
