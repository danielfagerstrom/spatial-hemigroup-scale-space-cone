/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.Symbol
import SpatialLine.SelfDecomposable
import SpatialLine.Generator

/-!
# The Fourier-side scale evolution

Blueprint: `eq:evolution-fourier`, the first clause of `prop:scale-evolution`. The statement is
about the **transfer factor** `s ↦ e^{-F(sω)}` rather than about `û(t,ω) = e^{-F(tω)}f̂(ω)`,
`f̂(ω)` being a constant in `s`; that keeps the complex transform out of the chapter's core
identity, and the `û` form is one `HasDerivAt.const_mul` away.

## What proving this found

**Priced M for a reason that turned out not to apply, and paid S.** The annotation's `M` was
"`sd_exponents_symbol` is stated in `ℝ≥0∞` and has to be brought down to a real derivative,
which needs `lem:quadratic-growth` for finiteness". It needs nothing of the sort:
`mul_deriv_exponent_nonneg` is already in the library beside `sd_exponents_symbol`, and
`ENNReal.toReal_ofReal` on a nonnegative real is the whole descent. That is
`symbol_eq_mul_deriv`, three lines.

**The origin is the only case that is not the chain rule, and it is a constant.** The exponent
is differentiable only away from `0` (`hasDerivAt_exponent` is stated at positive frequencies
and transported to negative ones by evenness), so at `ω = 0` there is no derivative to chain
with — but there is nothing to differentiate either: `s ↦ e^{-F(0)}` is constant, and the
asserted derivative `-(t^{-1}B(0))e^{-F(0)}` vanishes because `B(0) = 0·F'(0) = 0` whatever
`deriv` returns at the origin. So the clause holds at every real `ω`, the origin included, with
no puncture in the statement.
-/

namespace SpatialLine

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-! ## The symbol as a real derivative -/
/-- **`eq:symbol` in real form**: the symbol is `ωF'(ω)`. `sd_exponents_symbol` states this in
`ℝ≥0∞`; the descent is `ENNReal.toReal_ofReal` against `mul_deriv_exponent_nonneg`. -/
theorem symbol_eq_mul_deriv (Q : SDProfile) {ϖ : Measure ℝ} (hϖ : HasProfileTail Q.k ϖ) (ω : ℝ) :
    symbol Q.a ϖ ω = ω * deriv Q.exponent ω := by
  rw [symbol_apply, sd_exponents_symbol Q Q.exponent (fun _ => rfl) ϖ hϖ ω,
    ENNReal.toReal_ofReal (mul_deriv_exponent_nonneg Q hϖ ω)]

/-- The exponent is differentiable at every nonzero frequency: `hasDerivAt_exponent` at the
positive ones, and evenness carries it to the negative ones. -/
theorem hasDerivAt_exponent_of_ne (Q : SDProfile) {ϖ : Measure ℝ} (hϖ : HasProfileTail Q.k ϖ)
    {z : ℝ} (hz : z ≠ 0) : HasDerivAt Q.exponent (deriv Q.exponent z) z := by
  rcases lt_or_gt_of_ne hz with hneg | hpos
  · have hd := hasDerivAt_exponent Q hϖ (neg_pos.mpr hneg)
    have hcomp := hd.comp z (hasDerivAt_neg z)
    have hev : Q.exponent ∘ Neg.neg = Q.exponent := funext fun y => Q.exponent_neg y
    rw [hev] at hcomp
    exact hcomp.deriv ▸ hcomp
  · have hd := hasDerivAt_exponent Q hϖ hpos
    exact hd.deriv ▸ hd

/-- **`eq:evolution-fourier`**: `∂_s e^{-F(sω)} = -s^{-1}B(sω)e^{-F(sω)}`, pointwise in `s > 0`
at a fixed frequency.

`Skeleton.scale_evolution_fourier`'s type verbatim. -/
theorem scale_evolution_fourier (P : SDProfile) (ϖ : Measure ℝ) (hϖ : HasProfileTail P.k ϖ)
    (ω : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => Real.exp (-P.exponent (s * ω)))
      (-(t⁻¹ * symbol P.a ϖ (t * ω)) * Real.exp (-P.exponent (t * ω))) t := by
  rcases eq_or_ne ω 0 with rfl | hω
  · have h0 : symbol P.a ϖ (t * 0) = 0 := by
      rw [symbol_eq_mul_deriv P hϖ, mul_zero, zero_mul]
    rw [h0]
    simp only [mul_zero, SDProfile.exponent_zero, neg_zero, mul_zero, zero_mul]
    exact hasDerivAt_const t _
  · have htω : t * ω ≠ 0 := mul_ne_zero ht.ne' hω
    have hlin : HasDerivAt (fun s : ℝ => s * ω) ω t := by
      simpa using (hasDerivAt_id t).mul_const ω
    have hcomp := (hasDerivAt_exponent_of_ne P hϖ htω).comp t hlin
    simp only [Function.comp_def] at hcomp
    have hexp := hcomp.neg.exp
    have hval : Real.exp (-P.exponent (t * ω)) * -(deriv P.exponent (t * ω) * ω)
        = -(t⁻¹ * symbol P.a ϖ (t * ω)) * Real.exp (-P.exponent (t * ω)) := by
      rw [symbol_eq_mul_deriv P hϖ]
      field_simp
    exact hval ▸ hexp

end SpatialLine
