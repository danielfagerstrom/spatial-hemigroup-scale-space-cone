/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.Thorin
import SpatialLine.StableProfile
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The Thorin density of the symmetric stable corner

Blueprint: `prop:stable-family`, the Thorin density clause.

The stable profile `k(x) = C_α^{-1}x^{-α}` is completely monotone, and its Thorin measure has
density proportional to `θ^{α-1}`: that is the Gamma integral
`∫₀^∞ e^{-θx}θ^{α-1}dθ = Γ(α)x^{-α}`, which Mathlib supplies as
`Real.integral_rpow_mul_exp_neg_mul_Ioi`, followed by `thorin_of_laplace`.

## What the writing found

**The normalising constant is not the blocker here that it is elsewhere.** Wave 2 recorded that
`cor:semigroup-case`'s profile clause and `prop:stable-family`'s moment clause are blocked on
`C_α = ∫₀^∞ (1 - \cos u)u^{-1-α}du`, "an improper integral with no Mathlib support at either
endpoint". That is a statement about its *value*. This clause needs only that `C_α` is a
**positive real number**, which is the integral's convergence together with the positivity of a
nonnegative integrand that is nonzero on `(0,1)` — thirty lines, `stableConst_pos`, of which the
substance is the two comparisons `1 - \cos u \le u^2/2` near the origin and `1 - \cos u \le 2` at
infinity. Reading the obligation rather than the argument is the whole of the difference: nothing
here evaluates `C_α`, and the constant of the Thorin density is left existential by the node for
exactly that reason. Chapter 7 needed the same three facts for `cor:semigroup-case` and wrote
them independently; wave 3's merge kept that copy and this file imports it.
-/

namespace SpatialLine

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-! ## The Gamma measure and its Laplace transform -/

theorem integrableOn_gammaIntegrand {α x : ℝ} (hα : 0 < α) (hx : 0 < x) :
    IntegrableOn (fun θ : ℝ => θ ^ (α - 1) * Real.exp (-(x * θ))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := α - 1) (b := x)
    (by linarith) (by norm_num) hx
  refine h.congr_fun (fun θ hθ => ?_) measurableSet_Ioi
  simp [Real.rpow_one]

/-- The candidate Thorin measure of the stable corner: density `cθ^{α-1}` on `(0,∞)`. -/
noncomputable def gammaThorinMeasure (c α : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi (0 : ℝ))).withDensity fun θ => ENNReal.ofReal (c * θ ^ (α - 1))

theorem isFolded_gammaThorinMeasure (c α : ℝ) : IsFolded (gammaThorinMeasure c α) := by
  refine (withDensity_absolutelyContinuous _ _) ?_
  rw [Measure.restrict_apply measurableSet_Iic]
  convert measure_empty (μ := (volume : Measure ℝ))
  ext x
  simp only [mem_inter_iff, mem_Iic, mem_Ioi, mem_empty_iff_false, iff_false, not_and, not_lt]
  exact fun h => h

instance sFinite_gammaThorinMeasure (c α : ℝ) : SFinite (gammaThorinMeasure c α) := by
  unfold gammaThorinMeasure
  infer_instance

/-- **The Gamma integral.** `∫₀^∞ e^{-θx}cθ^{α-1}d\theta = c\,x^{-α}\Gamma(α)`. -/
theorem laplaceL_gammaThorinMeasure {c α x : ℝ} (hc : 0 ≤ c) (hα : 0 < α) (hx : 0 < x) :
    laplaceL (gammaThorinMeasure c α) x
      = ENNReal.ofReal (c * ((1 / x) ^ α * Real.Gamma α)) := by
  have hdens : AEMeasurable (fun θ : ℝ => ENNReal.ofReal (c * θ ^ (α - 1)))
      (volume.restrict (Ioi (0 : ℝ))) := by fun_prop
  rw [laplaceL, gammaThorinMeasure, lintegral_withDensity_eq_lintegral_mul₀ hdens (by fun_prop)]
  have hstep : (∫⁻ θ in Ioi (0 : ℝ), ENNReal.ofReal (c * θ ^ (α - 1))
        * ENNReal.ofReal (Real.exp (-(x * θ))))
      = ∫⁻ θ in Ioi (0 : ℝ),
          ENNReal.ofReal (c * (θ ^ (α - 1) * Real.exp (-(x * θ)))) := by
    refine setLIntegral_congr_fun measurableSet_Ioi fun θ hθ => ?_
    have hθ0 : (0 : ℝ) < θ := hθ
    have hp : (0 : ℝ) < θ ^ (α - 1) := Real.rpow_pos_of_pos hθ0 _
    rw [← ENNReal.ofReal_mul (by positivity), mul_assoc]
  rw [Pi.mul_def] at *
  rw [hstep]
  have hint : IntegrableOn (fun θ : ℝ => c * (θ ^ (α - 1) * Real.exp (-(x * θ)))) (Ioi 0) :=
    (integrableOn_gammaIntegrand hα hx).const_mul c
  have hnn : ∀ᵐ θ ∂(volume.restrict (Ioi (0 : ℝ))),
      0 ≤ c * (θ ^ (α - 1) * Real.exp (-(x * θ))) := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun θ hθ => ?_)
    have hθ0 : (0 : ℝ) < θ := hθ
    have hp : (0 : ℝ) < θ ^ (α - 1) := Real.rpow_pos_of_pos hθ0 _
    have := Real.exp_pos (-(x * θ))
    positivity
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, integral_const_mul,
    Real.integral_rpow_mul_exp_neg_mul_Ioi hα hx]

/-! ## The node -/

/-- **`prop:stable-family`, the Thorin density.** The symmetric Thorin measure of the stable
exponent has density proportional to `θ^{α-1}` on `(0,∞)`.

The constant is `(C_α\Gamma(α))^{-1}`; the node leaves it existential and says only
"proportional", so it is delivered as the witness of the existential and not fixed in the
statement. Lean core alone — no interface, and in particular not A11: the stable profile is
*exhibited* as a Laplace transform, so Bernstein's theorem is not needed in either direction. -/
theorem stable_family_thorin (α : ℝ) (hα : 0 < α) (hα2 : α < 2) (P : SDProfile)
    (hP : P.a = 0) (hk : P.k = stableProfile α) :
    ∃ c : ℝ, 0 < c ∧
      ∀ ω : ℝ, P.exponent ω
        = thorinExponent 0
            ((volume.restrict (Ioi (0 : ℝ))).withDensity
              fun θ => ENNReal.ofReal (c * θ ^ (α - 1))) ω := by
  have hC : 0 < stableConst α := stableConst_pos hα hα2
  have hG : 0 < Real.Gamma α := Real.Gamma_pos_of_pos hα
  refine ⟨(stableConst α * Real.Gamma α)⁻¹, by positivity, fun ω => ?_⟩
  set c : ℝ := (stableConst α * Real.Gamma α)⁻¹ with hcdef
  have hcnn : (0 : ℝ) ≤ c := by rw [hcdef]; positivity
  have hlap : ∀ x : ℝ, 0 < x → ENNReal.ofReal (P.k x) = laplaceL (gammaThorinMeasure c α) x := by
    intro x hx
    rw [laplaceL_gammaThorinMeasure hcnn hα hx, hk]
    congr 1
    have hpow : (1 / x : ℝ) ^ α = x ^ (-α) := by
      rw [one_div, Real.inv_rpow hx.le, ← Real.rpow_neg hx.le]
    simp only [stableProfile, Set.indicator_of_mem (mem_Ioi.mpr hx), hpow, hcdef]
    field_simp
  have hkey := thorin_of_laplace (isFolded_gammaThorinMeasure c α) hlap ω
  rw [hP] at hkey
  rw [SDProfile.exponent, thorinExponent, hkey]
  rfl


end SpatialLine
