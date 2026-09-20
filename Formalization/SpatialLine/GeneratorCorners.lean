/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.Generator

/-!
# The conjugation of the generators, and the two corners that are pure computations

Blueprint: `prop:scale-evolution`'s conjugation clause and `prop:corner-generators`(1) and (5).

## What proving these found

All three are identities of `scaleGenerator` read at a particular `(a, ϖ)`, and none of them
consumes the hypotheses its statement carries beyond `t ≠ 0`.

* The Gaussian corner is the definition at `ϖ = 0`: the jump term is an integral against the
  zero measure. The clause holds for every `t`, the sign of `t` included, and for a `g` with no
  regularity at all — both sides read `iteratedDeriv 2 g x`, which is `0` where `g` is not twice
  differentiable, on the same side of the equation.
* The `Cin` corner is the definition at `a = 0` and `ϖ = δ_τ`, where the Bochner integral is an
  evaluation. Neither `0 < τ` nor `0 < t` is used; the identity is the definition of
  `secondDifference` rearranged.
* The conjugation needs only `t ≠ 0`, and in particular **not** that `g` is twice
  differentiable, which the printed proof's chain rule appears to require. Mathlib's
  `iteratedDeriv_comp_const_mul` does carry a `ContDiff` hypothesis, but the identity
  `(g(t\cdot))'' (z) = t^2g''(tz)` is junk-safe: `deriv_comp_mul_left` and
  `deriv_const_mul_field` are both stated without differentiability, so the two sides degenerate
  to `0` together. `iteratedDeriv_scale_two` below is that fact, and it is worth having
  separately: every scale-covariance computation in the chapter needs it.
-/

namespace SpatialLine

open MeasureTheory Set
open scoped ENNReal

/-! ## The second derivative under a dilation of the argument -/

/-- `(g(t\cdot))''(z) = t^2g''(tz)`, with no differentiability hypothesis.

Mathlib's `iteratedDeriv_comp_const_mul` asks for `ContDiff ℝ n g`; at `n = 2` the hypothesis is
unnecessary, because `deriv_comp_mul_left` and `deriv_const_mul_field` are junk-safe and the two
sides therefore vanish together where `g` fails to be twice differentiable. -/
theorem iteratedDeriv_scale_two (t : ℝ) (g : ℝ → ℝ) (z : ℝ) :
    iteratedDeriv 2 (fun y => g (t * y)) z = t ^ 2 * iteratedDeriv 2 g (t * z) := by
  have h1 : deriv (fun y => g (t * y)) = fun y => t * deriv g (t * y) := by
    funext y
    simpa using deriv_comp_mul_left t g y
  rw [iteratedDeriv_succ, iteratedDeriv_one, h1, deriv_const_mul_field]
  have h2 : deriv (fun y => deriv g (t * y)) z = t * deriv (deriv g) (t * z) := by
    simpa using deriv_comp_mul_left t (deriv g) z
  rw [h2, iteratedDeriv_succ, iteratedDeriv_one]
  ring

/-! ## `prop:scale-evolution`, the conjugation clause -/

/-- **The generators at different scales are conjugate**,
`\mathcal{A}_t = t^{-1}D_t\mathcal{A}_1D_t^{-1}`, and the log-scale clock `\partial_\theta = t\partial_t`.

Both conjuncts are the same identity with the factor `t` moved across, and both sides are the
same integral written twice: the dilation `y \mapsto ty` carries `x/t` to `x` and `x/t \mp v` to
`x \mp tv`, so the jump terms coincide term by term, while the Gaussian terms differ by the
`t^2` of `iteratedDeriv_scale_two` against the `t^{-1}` of the clock. -/
theorem scale_evolution_conjugation (P : SDProfile) (ϖ : Measure ℝ) {t : ℝ} (ht : 0 < t)
    (g : ℝ → ℝ) (x : ℝ) :
    scaleGenerator P.a ϖ t g x
        = t⁻¹ * scaleGenerator P.a ϖ 1 (fun y => g (t * y)) (x / t) ∧
      t * scaleGenerator P.a ϖ t g x
        = scaleGenerator P.a ϖ 1 (fun y => g (t * y)) (x / t) := by
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hd2 : iteratedDeriv 2 (fun y => g (t * y)) (x / t) = t ^ 2 * iteratedDeriv 2 g x := by
    rw [iteratedDeriv_scale_two, mul_div_cancel₀ x ht0]
  have hint : (∫ v, ((fun y => g (t * y)) (x / t)
        - ((fun y => g (t * y)) (x / t - 1 * v) + (fun y => g (t * y)) (x / t + 1 * v)) / 2) ∂ϖ)
      = ∫ v, (g x - (g (x - t * v) + g (x + t * v)) / 2) ∂ϖ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    have e0 : t * (x / t) = x := mul_div_cancel₀ x ht0
    have e1 : t * (x / t - 1 * v) = x - t * v := by field_simp
    have e2 : t * (x / t + 1 * v) = x + t * v := by field_simp
    simp only [e0, e1, e2]
  have hfirst : scaleGenerator P.a ϖ t g x
      = t⁻¹ * scaleGenerator P.a ϖ 1 (fun y => g (t * y)) (x / t) := by
    simp only [scaleGenerator, hd2, hint]
    field_simp
  refine ⟨hfirst, ?_⟩
  rw [hfirst, ← mul_assoc, mul_inv_cancel₀ ht0, one_mul]

/-! ## `prop:corner-generators`(1) and (5) -/

/-- **`prop:corner-generators`(1), the Gaussian corner**: `\mathcal{A}_t = 2at\partial_x^2`.

The jump measure is `0`, so the generator is its Gaussian term alone. -/
theorem corner_generator_gaussian (a : ℝ) (t : ℝ) (g : ℝ → ℝ) (x : ℝ) :
    scaleGenerator a 0 t g x = 2 * a * t * iteratedDeriv 2 g x := by
  simp [scaleGenerator]

/-- **`prop:corner-generators`(5), a `Cin` ray**: `\mathcal{A}_t` is a single symmetric second
difference, `t^{-1}\delta^2_{t\tau}`.

The jump measure is the point mass at `\tau`, so the Bochner integral is an evaluation. -/
theorem corner_generator_cin {τ : ℝ} (hτ : 0 < τ) {t : ℝ} (ht : 0 < t) (g : ℝ → ℝ) (x : ℝ) :
    scaleGenerator 0 (Measure.dirac τ) t g x = t⁻¹ * secondDifference (t * τ) g x := by
  simp only [scaleGenerator, secondDifference, integral_dirac]
  ring

end SpatialLine
