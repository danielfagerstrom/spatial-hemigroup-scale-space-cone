/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.CornerDefs
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.MeasureTheory.Measure.Restrict

/-!
# Thorin's two-sided exponent at `σ = iω`, and its fold

Blueprint: `lem:thorin-two-sided`, split out of `lem:thorin-ggc` on 2026-09-15 (module B step 2,
ledger row R160).

Ledger **A17** (Bondesson's extended generalized gamma convolutions) states membership in that
class through a *moment generating function* on real `σ`,

`exp{bσ + cσ²/2 + ∫ (log(θ/(θ - σ)) - σθ/(1 + θ²)) V(dθ)}`,   `V ≥ 0` on `ℝ ∖ {0}`,

and says in as many words that it does **not** carry the pairing of `±θ` at `σ = iω` which turns
that formula into the article's `eq:thorin`. This file is that pairing, and it is elementary:

* `thorin_pair_mul` — the two factors at `θ` and `-θ` multiply to the *positive real*
  `(1 + ω²/θ²)⁻¹`, so their logarithms add to a real logarithm and no branch of the complex
  logarithm has to be chosen;
* `neg_log_norm_thorin_factor` — the real part alone already gives `½log(1 + ω²/θ²)` at every
  `θ ≠ 0`, which is why the fold costs a factor `2` and not a case distinction;
* `thorin_pair_compensator` — the compensating terms cancel in pairs at `σ = iω`;
* `thorin_two_sided_fold` — for a symmetric `V` giving no mass to the origin, the two-sided
  exponent read at `σ = iω` is `eq:thorin` at the fold `U = 2V|_{(0,∞)}`.

What is *not* here, and cannot be: that membership in Bondesson's class is the two-sided
representation. That is the reading of a definition at imaginary argument, it is what
`lem:thorin-ggc` retains, and no Lean statement of it is available without a formal definition of
the class — see that node and A17's entry.
-/

namespace SpatialLine

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-- **The pairing of `±θ` at `σ = iω`.** The product of the two Thorin factors is the positive
real `(1 + ω²/θ²)⁻¹`. -/
theorem thorin_pair_mul {θ : ℝ} (hθ : θ ≠ 0) (ω : ℝ) :
    ((θ : ℂ) / ((θ : ℂ) - Complex.I * ω)) * ((-θ : ℂ) / ((-θ : ℂ) - Complex.I * ω))
      = (((1 + ω ^ 2 / θ ^ 2 : ℝ) : ℂ))⁻¹ := by
  have hθC : (θ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hθ
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  have hden : ((θ : ℂ) - Complex.I * ω) * ((-θ : ℂ) - Complex.I * ω)
      = -((θ : ℂ) ^ 2 + (ω : ℂ) ^ 2) := by
    ring_nf
    rw [hI]
    ring
  have hne : ((θ : ℂ) ^ 2 + (ω : ℂ) ^ 2) ≠ 0 := by
    have hpos : (0 : ℝ) < θ ^ 2 + ω ^ 2 := by positivity
    have : ((θ ^ 2 + ω ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpos.ne'
    push_cast at this
    exact this
  rw [div_mul_div_comm, hden]
  have hnum : (θ : ℂ) * (-θ : ℂ) = -((θ : ℂ) ^ 2) := by ring
  rw [hnum]
  have hcast : (((1 + ω ^ 2 / θ ^ 2 : ℝ)) : ℂ) = ((θ : ℂ) ^ 2 + (ω : ℂ) ^ 2) / (θ : ℂ) ^ 2 := by
    push_cast
    field_simp
  rw [hcast]
  field_simp

/-- **The real part of the Thorin factor.** For `θ ≠ 0`,
`-log‖θ/(θ - iω)‖ = ½log(1 + ω²/θ²)`. -/
theorem neg_log_norm_thorin_factor {θ : ℝ} (hθ : θ ≠ 0) (ω : ℝ) :
    -Real.log ‖(θ : ℂ) / ((θ : ℂ) - Complex.I * ω)‖ = 2⁻¹ * Real.log (1 + ω ^ 2 / θ ^ 2) := by
  have hθ2 : (0 : ℝ) < θ ^ 2 := by positivity
  have hnormden : ‖(θ : ℂ) - Complex.I * ω‖ = Real.sqrt (θ ^ 2 + ω ^ 2) := by
    have : (θ : ℂ) - Complex.I * ω = Complex.mk θ (-ω) := by
      apply Complex.ext <;> simp
    rw [this, Complex.norm_def, Complex.normSq_mk]
    congr 1
    ring
  have hnormnum : ‖(θ : ℂ)‖ = |θ| := by simp
  have hpos : (0 : ℝ) < Real.sqrt (θ ^ 2 + ω ^ 2) := Real.sqrt_pos.mpr (by positivity)
  rw [norm_div, hnormnum, hnormden, Real.log_div (abs_ne_zero.mpr hθ) hpos.ne']
  have hlog1 : Real.log (Real.sqrt (θ ^ 2 + ω ^ 2)) = 2⁻¹ * Real.log (θ ^ 2 + ω ^ 2) := by
    rw [Real.log_sqrt (by positivity)]
    ring
  have hlog2 : Real.log |θ| = 2⁻¹ * Real.log (θ ^ 2) := by
    rw [Real.log_pow, Real.log_abs]
    push_cast
    ring
  rw [hlog1, hlog2]
  have hquot : 1 + ω ^ 2 / θ ^ 2 = (θ ^ 2 + ω ^ 2) / θ ^ 2 := by field_simp
  rw [hquot, Real.log_div (by positivity) hθ2.ne']
  ring

/-- **The compensating terms cancel in pairs at `σ = iω`.** -/
theorem thorin_pair_compensator (θ ω : ℝ) :
    Complex.I * ω * (θ : ℂ) / (1 + (θ : ℂ) ^ 2)
        + Complex.I * ω * ((-θ : ℂ)) / (1 + (-θ : ℂ) ^ 2) = 0 := by
  have h : (1 : ℂ) + (-θ : ℂ) ^ 2 = 1 + (θ : ℂ) ^ 2 := by ring
  rw [h]
  ring

/-! ## The fold -/

/-- The two-sided Thorin integrand at `σ = iω`, as a nonnegative real: `½log(1 + ω²/θ²)`, written
through the modulus of the Thorin factor. -/
theorem lintegral_neg_log_norm_eq {V : Measure ℝ} (h0 : V {(0 : ℝ)} = 0) (ω : ℝ) :
    (∫⁻ θ, ENNReal.ofReal (-Real.log ‖(θ : ℂ) / ((θ : ℂ) - Complex.I * ω)‖) ∂V)
      = ∫⁻ θ, ENNReal.ofReal (2⁻¹ * Real.log (1 + ω ^ 2 / θ ^ 2)) ∂V := by
  refine lintegral_congr_ae ?_
  have hae : ∀ᵐ θ ∂V, θ ≠ 0 := by
    rw [ae_iff]
    simpa using h0
  filter_upwards [hae] with θ hθ
  rw [neg_log_norm_thorin_factor hθ ω]

/-- **The fold of a symmetric two-sided measure.** If `V` is invariant under `θ ↦ -θ` and gives
no mass to the origin, then for every nonnegative measurable even integrand the two-sided
integral is twice the integral over `(0,∞)`. -/
theorem lintegral_eq_two_mul_restrict {V : Measure ℝ} (hsym : V.map (fun θ : ℝ => -θ) = V)
    (h0 : V {(0 : ℝ)} = 0) {f : ℝ → ℝ≥0∞} (hf : Measurable f) (heven : ∀ θ : ℝ, f (-θ) = f θ) :
    (∫⁻ θ, f θ ∂V) = 2 * ∫⁻ θ in Ioi (0 : ℝ), f θ ∂V := by
  have hneg : Measurable (fun θ : ℝ => -θ) := measurable_neg
  have hsplit : (∫⁻ θ, f θ ∂V)
      = (∫⁻ θ in Ioi (0 : ℝ), f θ ∂V) + ∫⁻ θ in Iio (0 : ℝ), f θ ∂V := by
    have huniv : (Set.univ : Set ℝ) = Ioi (0 : ℝ) ∪ Iic (0 : ℝ) := by
      ext x; simp
    have hIic : (∫⁻ θ in Iic (0 : ℝ), f θ ∂V) = ∫⁻ θ in Iio (0 : ℝ), f θ ∂V := by
      have hdiff : Iic (0 : ℝ) = Iio (0 : ℝ) ∪ {(0 : ℝ)} := by
        ext x; simp [le_iff_lt_or_eq]
      rw [hdiff, lintegral_union (measurableSet_singleton 0) (by simp [Set.disjoint_singleton_right]),
        setLIntegral_measure_zero _ _ h0, add_zero]
    have hdisj : Disjoint (Ioi (0 : ℝ)) (Iic (0 : ℝ)) := Ioi_disjoint_Iic le_rfl
    rw [← setLIntegral_univ f, huniv, lintegral_union measurableSet_Iic hdisj, hIic]
  have hrefl : (∫⁻ θ in Iio (0 : ℝ), f θ ∂V) = ∫⁻ θ in Ioi (0 : ℝ), f θ ∂V := by
    have h1 : (∫⁻ θ in Iio (0 : ℝ), f θ ∂V)
        = ∫⁻ θ, Set.indicator (Iio (0 : ℝ)) f θ ∂V := by
      rw [lintegral_indicator measurableSet_Iio]
    have h2 : (∫⁻ θ, Set.indicator (Iio (0 : ℝ)) f θ ∂V)
        = ∫⁻ θ, Set.indicator (Iio (0 : ℝ)) f (-θ) ∂V := by
      conv_lhs => rw [← hsym]
      rw [lintegral_map (hf.indicator measurableSet_Iio) hneg]
    have h3 : ∀ θ : ℝ, Set.indicator (Iio (0 : ℝ)) f (-θ) = Set.indicator (Ioi (0 : ℝ)) f θ := by
      intro θ
      by_cases h : (0 : ℝ) < θ
      · rw [Set.indicator_of_mem (show -θ ∈ Iio (0 : ℝ) by simpa using h),
          Set.indicator_of_mem (show θ ∈ Ioi (0 : ℝ) from h), heven]
      · rw [Set.indicator_of_notMem (by simpa using not_lt.mp h),
          Set.indicator_of_notMem (by simpa using not_lt.mp h)]
    rw [h1, h2, lintegral_congr h3, lintegral_indicator measurableSet_Ioi]
  rw [hsplit, hrefl, two_mul]

/-- **`lem:thorin-two-sided`** — Thorin's two-sided exponent read at `σ = iω` is `eq:thorin` at
the fold.

For a symmetric `V` on `ℝ ∖ {0}` and `U = 2V|_{(0,∞)}`, the Gaussian term `aω²` together with
`-∫ log‖θ/(θ - iω)‖ V(dθ)` — the real part of Thorin's integral term at `σ = iω`, the imaginary
parts cancelling in pairs by `thorin_pair_mul` and `thorin_pair_compensator` — is
`thorinExponentL a U ω`.

**Lean core.** -/
theorem thorin_two_sided_fold {V : Measure ℝ} (hsym : V.map (fun θ : ℝ => -θ) = V)
    (h0 : V {(0 : ℝ)} = 0) (a ω : ℝ) :
    ENNReal.ofReal (a * ω ^ 2)
        + ∫⁻ θ, ENNReal.ofReal (-Real.log ‖(θ : ℂ) / ((θ : ℂ) - Complex.I * ω)‖) ∂V
      = thorinExponentL a ((2 : ℝ≥0∞) • V.restrict (Ioi (0 : ℝ))) ω := by
  rw [lintegral_neg_log_norm_eq h0 ω, thorinExponentL]
  congr 1
  have hmeas : Measurable fun θ : ℝ => ENNReal.ofReal (Real.log (1 + ω ^ 2 / θ ^ 2)) := by
    fun_prop
  have heven : ∀ θ : ℝ, ENNReal.ofReal (Real.log (1 + ω ^ 2 / (-θ) ^ 2))
      = ENNReal.ofReal (Real.log (1 + ω ^ 2 / θ ^ 2)) := fun θ => by rw [neg_sq]
  have hhalf : ∀ θ : ℝ, ENNReal.ofReal (2⁻¹ * Real.log (1 + ω ^ 2 / θ ^ 2))
      = ENNReal.ofReal 2⁻¹ * ENNReal.ofReal (Real.log (1 + ω ^ 2 / θ ^ 2)) := fun θ => by
    rw [ENNReal.ofReal_mul (by norm_num)]
  calc (∫⁻ θ, ENNReal.ofReal (2⁻¹ * Real.log (1 + ω ^ 2 / θ ^ 2)) ∂V)
      = ∫⁻ θ, ENNReal.ofReal 2⁻¹ * ENNReal.ofReal (Real.log (1 + ω ^ 2 / θ ^ 2)) ∂V :=
        lintegral_congr hhalf
    _ = ENNReal.ofReal 2⁻¹ * ∫⁻ θ, ENNReal.ofReal (Real.log (1 + ω ^ 2 / θ ^ 2)) ∂V :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal 2⁻¹
          * (2 * ∫⁻ θ in Ioi (0 : ℝ), ENNReal.ofReal (Real.log (1 + ω ^ 2 / θ ^ 2)) ∂V) := by
        rw [lintegral_eq_two_mul_restrict hsym h0 hmeas heven]
    _ = ENNReal.ofReal 2⁻¹ * ∫⁻ θ, ENNReal.ofReal (Real.log (1 + ω ^ 2 / θ ^ 2))
          ∂((2 : ℝ≥0∞) • V.restrict (Ioi (0 : ℝ))) := by
        rw [lintegral_smul_measure, smul_eq_mul]

end SpatialLine
