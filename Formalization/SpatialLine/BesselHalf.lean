/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.CornerDefs
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# `K_{1/2}` from the defining integral, and `prop:matern-density`'s two special values

Blueprint: `blueprint/src/parts/10-corners.tex`, `prop:matern-density`, the sentence
"here `γ = 1` gives the Laplace kernel `e^{-|x|/t}/(2t)` and `γ = 1/2` gives `K_0(|x|/t)/(πt)`".

## Mathlib has no Bessel function, so the special value is proved, not looked up

`SpatialLine.besselK` is *defined* by DLMF (10.32.9),
`K_ν(z) = ∫₀^∞ e^{-z cosh u} cosh(νu) du` for `z > 0` (SKELETON.md finding F15, question Q10),
so there is no API behind the name and the `γ = 1` clause — which needs
`K_{1/2}(z) = √(π/2z) e^{-z}` — has to be computed from that integral. It was priced **L** for
that reason.

The computation is one substitution, `w = 2 sinh(u/2)`, which is a diffeomorphism of `(0,∞)`
with `dw = cosh(u/2)du` and — this is the point — `cosh u = 1 + w²/2`, so the whole Bessel
integrand collapses to a Gaussian:

`∫₀^∞ e^{-z cosh u} cosh(u/2) du = ∫₀^∞ e^{-z(1 + w²/2)} dw = e^{-z} ∫₀^∞ e^{-(z/2)w²} dw`,

and Mathlib evaluates the last integral (`integral_exp_neg_mul_rpow` at `p = 2`, which is a
`Γ(3/2)`). The half-integer order is exactly the order at which this happens: `cosh(νu)` is a
polynomial in `sinh(u/2)` only for `ν = ±1/2`, which is why the closed form exists there and
nowhere else — and why the `γ = 1/2` clause of the node, whose Bessel order is `0`, needs no
Bessel fact at all, only `Γ(1/2) = √π`.

**Priced L (the `γ = 1` clause) and S (the `γ = 1/2` clause); paid M and S.** The L was priced
against "no Mathlib API", which is right about the Bessel function; what makes it cheaper than
L in practice is that Mathlib carries the substitution machinery
(`integral_image_eq_integral_abs_deriv_smul`) and the Gaussian moment already in the `Ioi 0`
form, so the only handwork is the image, the injectivity and the derivative of
`u ↦ 2 sinh(u/2)`.
-/

namespace SpatialLine

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-! ## The substitution `w = 2 sinh(u/2)` -/

theorem sinhMap_image : (fun u : ℝ => 2 * Real.sinh (u / 2)) '' (Ioi 0) = Ioi 0 := by
  ext y
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hu2 : (0:ℝ) < u / 2 := by
      have : (0:ℝ) < u := hu
      linarith
    have h : Real.sinh 0 < Real.sinh (u / 2) := Real.sinh_lt_sinh.mpr hu2
    rw [Real.sinh_zero] at h
    simp only [mem_Ioi]
    linarith
  · intro hy
    refine ⟨2 * Real.arsinh (y / 2), ?_, ?_⟩
    · have h : Real.sinh 0 < Real.sinh (Real.arsinh (y / 2)) := by
        rw [Real.sinh_arsinh, Real.sinh_zero]
        simpa using hy
      have := Real.sinh_lt_sinh.mp h
      simp only [mem_Ioi]
      linarith
    · show 2 * Real.sinh (2 * Real.arsinh (y / 2) / 2) = y
      rw [show 2 * Real.arsinh (y / 2) / 2 = Real.arsinh (y / 2) by ring, Real.sinh_arsinh]
      ring

theorem sinhMap_injOn : InjOn (fun u : ℝ => 2 * Real.sinh (u / 2)) (Ioi 0) := by
  intro x _ y _ h
  simp only at h
  have h2 : Real.sinh (x / 2) = Real.sinh (y / 2) := by linarith
  have := Real.sinh_injective h2
  linarith

theorem sinhMap_hasDeriv (u : ℝ) :
    HasDerivAt (fun v : ℝ => 2 * Real.sinh (v / 2)) (Real.cosh (u / 2)) u := by
  have h1 : HasDerivAt (fun v : ℝ => v / 2) (1 / 2 : ℝ) u := by
    simpa using (hasDerivAt_id u).div_const 2
  have h2 : HasDerivAt (fun v : ℝ => Real.sinh (v / 2)) (Real.cosh (u / 2) * (1 / 2)) u := by
    simpa [Function.comp_def] using (Real.hasDerivAt_sinh (u / 2)).comp u h1
  have h3 := h2.const_mul (2 : ℝ)
  rw [show (2:ℝ) * (Real.cosh (u / 2) * (1 / 2)) = Real.cosh (u / 2) by ring] at h3
  exact h3

/-! ## The special value of the Bessel function, and the node's two values -/

/-- **`K_{1/2}(z) = √(π/2z) e^{-z}`**, from the defining integral.

The substitution `w = 2 sinh(u/2)` turns `cosh u` into `1 + w²/2` and `cosh(u/2)du` into `dw`,
so the Bessel integral becomes a Gaussian one. -/
theorem besselK_half {z : ℝ} (hz : 0 < z) :
    besselK (1 / 2) z = Real.sqrt (Real.pi / (2 * z)) * Real.exp (-z) := by
  -- the substitution `w = 2 sinh(u/2)`
  have hsubst := integral_image_eq_integral_abs_deriv_smul (s := Ioi (0:ℝ))
    (f := fun u : ℝ => 2 * Real.sinh (u / 2)) (f' := fun u : ℝ => Real.cosh (u / 2))
    measurableSet_Ioi (fun u _ => (sinhMap_hasDeriv u).hasDerivWithinAt) sinhMap_injOn
    (fun y : ℝ => Real.exp (-(z * (1 + y ^ 2 / 2))))
  rw [sinhMap_image] at hsubst
  have hbess : besselK (1 / 2) z
      = ∫ y in Ioi (0:ℝ), Real.exp (-(z * (1 + y ^ 2 / 2))) := by
    rw [besselK, hsubst]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    have hcosh : Real.cosh u = 1 + (2 * Real.sinh (u / 2)) ^ 2 / 2 := by
      have h := Real.cosh_two_mul (u / 2)
      rw [show 2 * (u / 2) = u by ring] at h
      have hsq := Real.cosh_sq (u / 2)
      rw [h, hsq]
      ring
    rw [smul_eq_mul, abs_of_pos (Real.cosh_pos _), ← hcosh]
    ring
  rw [hbess]
  -- pull out `e^{-z}` and evaluate the Gaussian integral
  have hsplit : ∀ y ∈ Ioi (0:ℝ), Real.exp (-(z * (1 + y ^ 2 / 2)))
      = Real.exp (-z) * Real.exp (-(z / 2) * y ^ (2:ℝ)) := by
    intro y hy
    rw [Real.rpow_two, ← Real.exp_add]
    congr 1
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hsplit, integral_const_mul,
    integral_exp_neg_mul_rpow (by norm_num : (0:ℝ) < 2) (by positivity : (0:ℝ) < z / 2)]
  have hgamma : Real.Gamma (1 / 2 + 1) = Real.sqrt Real.pi / 2 := by
    rw [Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]
    ring
  rw [hgamma]
  have hzh : (0:ℝ) < z / 2 := by positivity
  have hrw : (z / 2) ^ (-1 / 2 : ℝ) = (Real.sqrt (z / 2))⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg_one, ← Real.rpow_mul hzh.le]
    norm_num
  rw [hrw]
  have hs4 : Real.sqrt 4 = 2 := by
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have h2z : 2 * Real.sqrt (z / 2) = Real.sqrt (2 * z) := by
    have hmul : Real.sqrt (2 * z) = Real.sqrt 4 * Real.sqrt (z / 2) := by
      rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]
      congr 1
      ring
    rw [hmul, hs4]
  have hfin : Real.sqrt (Real.pi / (2 * z)) = Real.sqrt Real.pi / Real.sqrt (2 * z) :=
    Real.sqrt_div Real.pi_pos.le _
  rw [hfin, ← h2z]
  have hsz : (0:ℝ) < Real.sqrt (z / 2) := Real.sqrt_pos.mpr hzh
  field_simp

/-- **`prop:matern-density`, the two special values.**

`γ = 1` is the Laplace kernel, on `x ≠ 0` (R11: at the origin the left side carries the factor
`(|0|/2t)^{1/2} = 0` while the right side is `(2t)⁻¹`, so the two densities differ there and
agree off a null set); `γ = 1/2` is `K_0(|x|/t)/(πt)`, with no exclusion, both sides reading
`besselK 0 0/(πt)` at the origin because the exponent is `0`.

**Priced S for the `γ = 1/2` clause and L for the `γ = 1` clause; paid S and M** — see the
module docstring for where the L was over-priced. -/
theorem matern_density_special (t : ℝ) (ht : 0 < t) :
    (∀ x : ℝ, x ≠ 0 → maternDensity 1 t x = laplaceDensity t x) ∧
      ∀ x : ℝ, maternDensity (1 / 2) t x = besselK 0 (|x| / t) / (Real.pi * t) := by
  have hpi : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi :=
    Real.mul_self_sqrt Real.pi_pos.le
  constructor
  · intro x hx
    have hax : (0:ℝ) < |x| := abs_pos.mpr hx
    have hz : (0:ℝ) < |x| / t := by positivity
    rw [maternDensity, laplaceDensity, Real.Gamma_one, mul_one,
      show (1:ℝ) - 1 / 2 = 1 / 2 by norm_num, besselK_half hz, ← Real.sqrt_eq_rpow]
    have harg : Real.pi / (2 * (|x| / t)) = Real.pi * t / (2 * |x|) := by
      field_simp
    rw [harg]
    have hprod : Real.sqrt (|x| / (2 * t)) * Real.sqrt (Real.pi * t / (2 * |x|))
        = Real.sqrt Real.pi / 2 := by
      rw [← Real.sqrt_mul (by positivity)]
      rw [show |x| / (2 * t) * (Real.pi * t / (2 * |x|)) = Real.pi / 4 by field_simp; ring]
      rw [Real.sqrt_div Real.pi_pos.le, show Real.sqrt 4 = 2 by
        rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    have hgoal : (Real.sqrt Real.pi * t)⁻¹ * Real.sqrt (|x| / (2 * t))
        * (Real.sqrt (Real.pi * t / (2 * |x|)) * Real.exp (-(|x| / t)))
        = (Real.sqrt Real.pi * t)⁻¹ * (Real.sqrt (|x| / (2 * t))
          * Real.sqrt (Real.pi * t / (2 * |x|))) * Real.exp (-(|x| / t)) := by ring
    rw [hgoal, hprod]
    have hsp : Real.sqrt Real.pi ≠ 0 := by positivity
    field_simp
  · intro x
    rw [maternDensity, show (1:ℝ) / 2 - 1 / 2 = 0 by norm_num, Real.rpow_zero,
      Real.Gamma_one_half_eq, mul_one]
    rw [show Real.sqrt Real.pi * Real.sqrt Real.pi * t = Real.pi * t by rw [hpi]]
    field_simp

end SpatialLine
