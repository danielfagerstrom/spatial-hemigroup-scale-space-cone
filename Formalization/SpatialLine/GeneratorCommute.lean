/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.GeneratorMultiplier
import SpatialLine.ConvolutionSmooth

/-!
# The generator commutes with smoothing

Blueprint: `prop:scale-evolution`'s signal clause, `eq:evolution-signal`. Nothing here is a node.

## What this is for

`eq:evolution-signal` asserts `∂_tu = 𝒜_tu(t,\cdot)`, and its right-hand side applies the
generator to the **scale space** `u(t,\cdot) = μ_{0,t} * f`, which is not Schwartz: it inherits
the kernel's tails, and the Student-t and stable kernels have polynomial ones (finding **F13**).
So the multiplier identity, which is stated for a Schwartz argument, cannot be read at
`u(t,\cdot)` directly, and the annotation at the statement records that the clause is "the
multiplier read backwards" without saying through what.

Through this: the generator is translation-invariant, hence **commutes with convolution by a
finite measure**,

  `𝒜_t(ν * f) = ν * (𝒜_tf)`,                                                          (♭)

so `𝒜_tu(t,\cdot) = μ_{0,t} * (𝒜_tf)` with `f` Schwartz, and the transform of the right-hand
side is the transform of `𝒜_tf` — which *is* the multiplier identity, now at an argument it
applies to. The remaining work of the clause is then the Fourier inversion and the
differentiation in the scale, neither of which needs the generator at a non-Schwartz argument.

## What proving it found

**The Gaussian half was already in the library**, and so was the machinery under it.
`SpatialLine/ConvolutionSmooth.lean` — written for chapter 13's `thm:non-enhancement`, whose
second-derivative test needs exactly this — proves `iteratedDeriv_two_mconv`,
`(μ * f)'' = μ * f''`, together with `hasDerivAt_mconv` and `SignalClass.exists_bound`. The
present file was first written with all three reproved from scratch; they were rejected by the
compiler as duplicates, which is the campaign's ninth judgement rule paying for itself.

**The jump half is one Fubini, and the majorant is the pointwise one.** Here, unlike in the
multiplier's exchange, the outer measure is *finite*, so the `x`-uniform Taylor bound
`|Δ_{tv}f(z)| ≤ ‖f''‖_∞t²v²` of `abs_secondDifference_le` — the estimate that was useless for the
transform integral — is exactly what is wanted: it does not depend on the convolution variable
at all, so `K(1 ∧ v²)` composed with the first projection dominates on `ϖ ⊗ ν` and
`lintegral_min_hasProfileTail` closes it. The two exchanges of this chapter want opposite
estimates of the same second difference, which is worth recording as a general lesson about
which bound to reach for.
-/

namespace SpatialLine

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-- A Schwartz function's second derivative is bounded. -/
theorem SignalClass.exists_bound_iteratedDeriv_two (f : SignalClass) :
    ∃ C : ℝ, ∀ x, |iteratedDeriv 2 (⇑f) x| ≤ C := by
  obtain ⟨C, hC⟩ :=
    SignalClass.exists_bound (SchwartzMap.derivCLM ℝ (F := ℝ) (SchwartzMap.derivCLM ℝ (F := ℝ) f))
  refine ⟨C, fun x => ?_⟩
  rw [iteratedDeriv_two_schwartz f x]
  exact hC x

/-- **The joint integrability of the second difference against `ϖ ⊗ ν`.** The bound is the
pointwise Taylor estimate, uniform in the convolution variable, and the outer measure is finite;
`lintegral_min_hasProfileTail` closes it. -/
theorem integrable_prod_secondDifference (ν : Measure ℝ) [IsFiniteMeasure ν] {P : SDProfile}
    {ϖ : Measure ℝ} (hϖ : HasProfileTail P.k ϖ) (t : ℝ) (f : SignalClass) (x : ℝ) :
    Integrable (fun p : ℝ × ℝ => (f : ℝ → ℝ) (x - p.2)
      - ((f : ℝ → ℝ) (x - p.2 - t * p.1) + (f : ℝ → ℝ) (x - p.2 + t * p.1)) / 2) (ϖ.prod ν) := by
  haveI : SigmaFinite ϖ := sigmaFinite_of_hasProfileTail hϖ
  obtain ⟨Cf, hCf⟩ := SignalClass.exists_bound f
  obtain ⟨C₂, hC₂⟩ := SignalClass.exists_bound_iteratedDeriv_two f
  have hCf0 : 0 ≤ Cf := le_trans (abs_nonneg _) (hCf x)
  have hC₂0 : 0 ≤ C₂ := le_trans (abs_nonneg _) (hC₂ x)
  set K : ℝ := max (2 * Cf) (C₂ * t ^ 2) with hK
  have hK0 : 0 ≤ K := le_trans (by linarith) (le_max_left _ _)
  set H : ℝ × ℝ → ℝ := fun p => (f : ℝ → ℝ) (x - p.2)
    - ((f : ℝ → ℝ) (x - p.2 - t * p.1) + (f : ℝ → ℝ) (x - p.2 + t * p.1)) / 2 with hH
  have hfc : Continuous (⇑f) := f.continuous
  have hHcont : Continuous H := by
    have h2 : Continuous fun p : ℝ × ℝ => (f : ℝ → ℝ) (x - p.2) :=
      hfc.comp (continuous_const.sub continuous_snd)
    have h3 : Continuous fun p : ℝ × ℝ => (f : ℝ → ℝ) (x - p.2 - t * p.1) :=
      hfc.comp ((continuous_const.sub continuous_snd).sub (continuous_const.mul continuous_fst))
    have h4 : Continuous fun p : ℝ × ℝ => (f : ℝ → ℝ) (x - p.2 + t * p.1) :=
      hfc.comp ((continuous_const.sub continuous_snd).add (continuous_const.mul continuous_fst))
    exact h2.sub ((h3.add h4).div_const 2)
  have hbound : ∀ p : ℝ × ℝ, ‖H p‖ ≤ K * min 1 (p.1 ^ 2) := by
    rintro ⟨v, y⟩
    have h1 : |H (v, y)| ≤ C₂ * (t * v) ^ 2 :=
      abs_secondDifference_le (f.smooth 2) hC₂ (x - y) (t * v)
    have h2 : |H (v, y)| ≤ 2 * Cf := by
      have e2 := hCf (x - y)
      have e3 := hCf (x - y - t * v)
      have e4 := hCf (x - y + t * v)
      calc |H (v, y)|
          ≤ |(f : ℝ → ℝ) (x - y)|
            + |((f : ℝ → ℝ) (x - y - t * v) + (f : ℝ → ℝ) (x - y + t * v)) / 2| := abs_sub _ _
        _ ≤ Cf + (|(f : ℝ → ℝ) (x - y - t * v)| + |(f : ℝ → ℝ) (x - y + t * v)|) / 2 := by
            rw [abs_div, abs_two]
            have := abs_add_le ((f : ℝ → ℝ) (x - y - t * v)) ((f : ℝ → ℝ) (x - y + t * v))
            linarith
        _ ≤ 2 * Cf := by linarith
    rw [Real.norm_eq_abs]
    rcases le_total (v ^ 2) 1 with hv | hv
    · rw [min_eq_right hv]
      have heq : C₂ * (t * v) ^ 2 = (C₂ * t ^ 2) * v ^ 2 := by ring
      nlinarith [le_max_right (2 * Cf) (C₂ * t ^ 2), sq_nonneg v]
    · rw [min_eq_left hv, mul_one]
      exact le_trans h2 (le_max_left _ _)
  refine Integrable.mono' ?_ hHcont.aestronglyMeasurable (.of_forall hbound)
  exact ((integrable_min_one_sq (lintegral_min_hasProfileTail hϖ)).const_mul K).comp_fst ν

/-- **(♭)'s jump half**: the Choquet integral of the second difference of `ν * f` is the
smoothing of the Choquet integral of the second difference of `f`. -/
theorem integral_secondDifference_mconv (ν : Measure ℝ) [IsFiniteMeasure ν] {P : SDProfile}
    {ϖ : Measure ℝ} (hϖ : HasProfileTail P.k ϖ) (t : ℝ) (f : SignalClass) (x : ℝ) :
    (∫ v, (mconv ν (⇑f) x - (mconv ν (⇑f) (x - t * v) + mconv ν (⇑f) (x + t * v)) / 2) ∂ϖ)
      = mconv ν (fun z => ∫ v, ((f : ℝ → ℝ) z
          - ((f : ℝ → ℝ) (z - t * v) + (f : ℝ → ℝ) (z + t * v)) / 2) ∂ϖ) x := by
  haveI : SigmaFinite ϖ := sigmaFinite_of_hasProfileTail hϖ
  obtain ⟨Cf, hCf⟩ := SignalClass.exists_bound f
  have hfc : Continuous (⇑f) := f.continuous
  have hHint := integrable_prod_secondDifference ν hϖ t f x
  have hi : ∀ c : ℝ, Integrable (fun y : ℝ => (f : ℝ → ℝ) (c - y)) ν := by
    intro c
    refine Integrable.mono' (integrable_const Cf)
      ((hfc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
      (.of_forall fun y => ?_)
    rw [Real.norm_eq_abs]; exact hCf _
  have hLHS : ∀ v : ℝ,
      mconv ν (⇑f) x - (mconv ν (⇑f) (x - t * v) + mconv ν (⇑f) (x + t * v)) / 2
        = ∫ y, ((f : ℝ → ℝ) (x - y)
            - ((f : ℝ → ℝ) (x - y - t * v) + (f : ℝ → ℝ) (x - y + t * v)) / 2) ∂ν := by
    intro v
    have e1 : mconv ν (⇑f) (x - t * v) = ∫ y, (f : ℝ → ℝ) (x - y - t * v) ∂ν := by
      rw [mconv_apply]
      exact integral_congr_ae (.of_forall fun y => by
        show (f : ℝ → ℝ) (x - t * v - y) = (f : ℝ → ℝ) (x - y - t * v)
        congr 1; ring)
    have e2 : mconv ν (⇑f) (x + t * v) = ∫ y, (f : ℝ → ℝ) (x - y + t * v) ∂ν := by
      rw [mconv_apply]
      exact integral_congr_ae (.of_forall fun y => by
        show (f : ℝ → ℝ) (x + t * v - y) = (f : ℝ → ℝ) (x - y + t * v)
        congr 1; ring)
    have i1 : Integrable (fun y : ℝ => (f : ℝ → ℝ) (x - y - t * v)) ν := by
      refine (hi (x - t * v)).congr (.of_forall fun y => ?_)
      show (f : ℝ → ℝ) (x - t * v - y) = (f : ℝ → ℝ) (x - y - t * v)
      congr 1; ring
    have i2 : Integrable (fun y : ℝ => (f : ℝ → ℝ) (x - y + t * v)) ν := by
      refine (hi (x + t * v)).congr (.of_forall fun y => ?_)
      show (f : ℝ → ℝ) (x + t * v - y) = (f : ℝ → ℝ) (x - y + t * v)
      congr 1; ring
    have hdiv : Integrable (fun y : ℝ =>
        ((f : ℝ → ℝ) (x - y - t * v) + (f : ℝ → ℝ) (x - y + t * v)) / 2) ν :=
      (i1.add i2).div_const 2
    rw [mconv_apply, e1, e2, integral_sub (hi x) hdiv, integral_div, integral_add i1 i2]
  rw [integral_congr_ae (.of_forall hLHS), integral_integral_swap hHint, mconv_apply]

/-- The Choquet integral of the second difference, smoothed, is integrable: the right-hand
marginal of the joint integrability above. -/
theorem integrable_mconv_secondDifference (ν : Measure ℝ) [IsFiniteMeasure ν] {P : SDProfile}
    {ϖ : Measure ℝ} (hϖ : HasProfileTail P.k ϖ) (t : ℝ) (f : SignalClass) (x : ℝ) :
    Integrable (fun y : ℝ => ∫ v, ((f : ℝ → ℝ) (x - y)
      - ((f : ℝ → ℝ) (x - y - t * v) + (f : ℝ → ℝ) (x - y + t * v)) / 2) ∂ϖ) ν := by
  haveI : SigmaFinite ϖ := sigmaFinite_of_hasProfileTail hϖ
  exact (integrable_prod_secondDifference ν hϖ t f x).integral_prod_right

/-- **(♭), the commutation**: the generator commutes with convolution by a finite measure.

The Gaussian term is `iteratedDeriv_two_mconv` (chapter 13's), the jump term is the exchange
above, and the two are combined by linearity of the smoothing, for which both terms have to be
`ν`-integrable — the second derivative because it is bounded, the Choquet integral because it is
the marginal of the joint integrability. -/
theorem scaleGenerator_mconv (ν : Measure ℝ) [IsFiniteMeasure ν] (P : SDProfile)
    {ϖ : Measure ℝ} (hϖ : HasProfileTail P.k ϖ) (t : ℝ) (f : SignalClass) (x : ℝ) :
    scaleGenerator P.a ϖ t (mconv ν (⇑f)) x = mconv ν (scaleGenerator P.a ϖ t (⇑f)) x := by
  obtain ⟨C₂, hC₂⟩ := SignalClass.exists_bound_iteratedDeriv_two f
  have hcont2 : Continuous (iteratedDeriv 2 (⇑f)) := by
    have h : iteratedDeriv 2 (⇑f)
        = ⇑(SchwartzMap.derivCLM ℝ (F := ℝ) (SchwartzMap.derivCLM ℝ (F := ℝ) f)) :=
      funext fun y => iteratedDeriv_two_schwartz f y
    rw [h]
    exact (SchwartzMap.derivCLM ℝ (F := ℝ) (SchwartzMap.derivCLM ℝ (F := ℝ) f)).continuous
  have h1 : Integrable (fun y : ℝ => 2 * P.a * t * iteratedDeriv 2 (⇑f) (x - y)) ν := by
    refine (Integrable.mono' (integrable_const C₂)
      ((hcont2.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
      (.of_forall fun y => by rw [Real.norm_eq_abs]; exact hC₂ _)).const_mul _
  have h2 : Integrable (fun y : ℝ => t⁻¹ * ∫ v, ((f : ℝ → ℝ) (x - y)
      - ((f : ℝ → ℝ) (x - y - t * v) + (f : ℝ → ℝ) (x - y + t * v)) / 2) ∂ϖ) ν :=
    (integrable_mconv_secondDifference ν hϖ t f x).const_mul _
  have hlin : mconv ν (scaleGenerator P.a ϖ t (⇑f)) x
      = 2 * P.a * t * mconv ν (iteratedDeriv 2 (⇑f)) x
        - t⁻¹ * mconv ν (fun z => ∫ v, ((f : ℝ → ℝ) z
            - ((f : ℝ → ℝ) (z - t * v) + (f : ℝ → ℝ) (z + t * v)) / 2) ∂ϖ) x := by
    rw [mconv_apply, mconv_apply, mconv_apply, ← integral_const_mul, ← integral_const_mul,
      ← integral_sub h1 h2]
    refine integral_congr_ae (.of_forall fun y => ?_)
    show scaleGenerator P.a ϖ t (⇑f) (x - y)
      = 2 * P.a * t * iteratedDeriv 2 (⇑f) (x - y)
        - t⁻¹ * ∫ v, ((f : ℝ → ℝ) (x - y)
            - ((f : ℝ → ℝ) (x - y - t * v) + (f : ℝ → ℝ) (x - y + t * v)) / 2) ∂ϖ
    rw [scaleGenerator]
  rw [scaleGenerator, congrFun (iteratedDeriv_two_mconv ν f) x,
    integral_secondDifference_mconv ν hϖ t f x, hlin]

end SpatialLine
