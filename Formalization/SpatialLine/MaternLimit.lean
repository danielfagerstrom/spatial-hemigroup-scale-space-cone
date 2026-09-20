/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.CornerDefs
import SpatialLine.TransformUniqueness
import SpatialLine.TransformBridge
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# `prop:matern-density`, the Gaussian limit

Blueprint: `blueprint/src/parts/10-corners.tex`, `prop:matern-density`, the last sentence: as
`γ → ∞` with `2γt² = v` held fixed, the Matérn kernel converges weakly to the Gaussian of
variance `v`.

## The statement needed a hypothesis, and did not carry it

**CHANGED (proof, wave 2, 2026-09-09).** The skeleton statement quantified over probability
measures `μ n` constrained only by their **cosine** transform, and concluded weak convergence.
That is false, and for the reason the statement review found twice elsewhere (R7, at
`two_members_matern_moments` and `moments_tails_variance`): the cosine transform determines only
the symmetrisation. Writing `μ_n = ν_n + σ_n` with `ν_n` the Matérn law and `σ_n` an odd signed
measure dominated by it leaves the cosine transform unchanged, and `∫ g dμ_n = ∫ g dσ_n` for a
bounded continuous **odd** `g` — take `g = arctan` and `σ_n` of density `½ν_n(x)\,sgn(x)`, whose
integral tends to `½E|arctan N|> 0` while the Gaussian gives `0`. The repair is R7's:
`(hsym : ∀ n, IsSymmetric (μ n))`, which every kernel of this article satisfies by (A3) and
which `two_members_matern` already carries.

## The route

`γ log(1 + c/γ) → c` — `tendsto_mul_log_one_add_div` below, from Mathlib's
`Real.tendsto_one_add_div_rpow_exp` by taking logarithms — gives pointwise convergence of the
transforms, symmetry turns the cosine transform into `charFun`, and `levy_continuity` (chapter
2, proved in wave 1 and *not* an axiom: Mathlib supplies the clause this article consumes) turns
that into weak convergence. **Priced M; paid M.**
-/

namespace SpatialLine

open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal Topology

/-! ## The elementary limit -/

/-- `x log(1 + c/x) → c` as `x → ∞`: the logarithm of Mathlib's `(1 + c/x)^x → e^c`. -/
theorem tendsto_mul_log_one_add_div (c : ℝ) :
    Filter.Tendsto (fun x : ℝ => x * Real.log (1 + c / x)) atTop (𝓝 c) := by
  have hbase : Filter.Tendsto (fun x : ℝ => (1 + c / x) ^ x) atTop (𝓝 (Real.exp c)) :=
    Real.tendsto_one_add_div_rpow_exp c
  have h1 := (Real.continuousAt_log (Real.exp_ne_zero c)).tendsto.comp hbase
  rw [Real.log_exp] at h1
  refine h1.congr' ?_
  filter_upwards [eventually_gt_atTop (max 1 (2 * |c|))] with x hx
  have hx1 : (1:ℝ) < x := lt_of_le_of_lt (le_max_left _ _) hx
  have hx0 : (0:ℝ) < x := lt_trans zero_lt_one hx1
  have hc : |c / x| < 1 / 2 := by
    rw [abs_div, abs_of_pos hx0, div_lt_div_iff₀ hx0 (by norm_num)]
    have : 2 * |c| < x := lt_of_le_of_lt (le_max_right _ _) hx
    linarith
  have hpos : (0:ℝ) < 1 + c / x := by
    have h2 := abs_lt.mp hc
    linarith [h2.1]
  simp only [Function.comp_apply]
  rw [Real.log_rpow hpos]

/-! ## The node's clause -/

/-- **`prop:matern-density`, the Gaussian limit.**

As `γ → ∞` with `2γt² = v` fixed — so that the range is `t = √(v/2γ)` — the Matérn kernels
converge weakly to the Gaussian of variance `v`.

**Changed (proof, wave 2, 2026-09-09): `hsym` added.** See the module docstring: the statement
was false without it, by R7's mechanism. -/
theorem matern_density_gaussian_limit (v : ℝ) (hv : 0 < v) (γ : ℕ → ℝ)
    (hγ : ∀ n, 0 < γ n) (hγtop : Filter.Tendsto γ Filter.atTop Filter.atTop)
    (μ : ℕ → Measure ℝ) (hprob : ∀ n, IsProbabilityMeasure (μ n))
    (hsym : ∀ n, IsSymmetric (μ n))
    (hcos : ∀ n, ∀ ω : ℝ,
      fourierCos (μ n) ω = Real.exp (-maternExponent (γ n) (Real.sqrt (v / (2 * γ n))) ω)) :
    ∀ g : ℝ → ℝ, Continuous g → (∃ C : ℝ, ∀ x, |g x| ≤ C) →
      Filter.Tendsto (fun n => ∫ x, g x ∂(μ n)) Filter.atTop
        (𝓝 (∫ x, g x ∂(ProbabilityTheory.gaussianReal 0 v.toNNReal))) := by
  haveI hp : ∀ n, IsProbabilityMeasure (μ n) := hprob
  have hchar : ∀ ω : ℝ, Filter.Tendsto (fun n => charFun (μ n) ω) Filter.atTop
      (𝓝 (charFun (ProbabilityTheory.gaussianReal 0 v.toNNReal) ω)) := by
    intro ω
    set c : ℝ := v * ω ^ 2 / 2 with hc
    have hgauss : charFun (ProbabilityTheory.gaussianReal 0 v.toNNReal) ω
        = ((Real.exp (-c) : ℝ) : ℂ) := by
      rw [ProbabilityTheory.charFun_gaussianReal, Complex.ofReal_exp]
      congr 1
      rw [Real.coe_toNNReal v hv.le, hc]
      push_cast
      ring
    have hreal : ∀ n, fourierCos (μ n) ω = Real.exp (-(γ n * Real.log (1 + c / γ n))) := by
      intro n
      have hgn : (0:ℝ) < γ n := hγ n
      rw [hcos n ω, maternExponent,
        Real.sq_sqrt (by positivity : (0:ℝ) ≤ v / (2 * γ n))]
      congr 2
      rw [hc]
      field_simp
    have hlim : Filter.Tendsto (fun n => Real.exp (-(γ n * Real.log (1 + c / γ n))))
        Filter.atTop (𝓝 (Real.exp (-c))) :=
      (Real.continuous_exp.tendsto _).comp
        (((tendsto_mul_log_one_add_div c).comp hγtop).neg)
    rw [hgauss]
    refine (Complex.continuous_ofReal.tendsto _).comp (hlim.congr fun n => (hreal n).symm) |>.congr
      fun n => ?_
    rw [Function.comp_apply, charFun_eq_fourierCos_of_symmetric (hsym n)]
  intro g hg ⟨C, hC⟩
  have hbcf : ∀ x : ℝ, ‖g x‖ ≤ C := fun x => by rw [Real.norm_eq_abs]; exact hC x
  have := levy_continuity hchar (BoundedContinuousFunction.ofNormedAddCommGroup g hg C hbcf)
  simpa using this

end SpatialLine
