/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.BridgeExponents
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# `prop:bridge-families`(3): the causal Bessel family maps to the Student-t family

Blueprint: `blueprint/src/parts/09-bridge.tex` — clause (3) of `prop:bridge-families`, which is
also where `prop:student-t`(1)'s conditioning computation lives, so the two nodes share this
declaration.

It is a separate file from `SpatialLine/BridgeCorners.lean` because it needs the Brownian
density in closed form, which is `SpatialLine/BridgeExponents.lean`, and `BridgeExponents`
imports `BridgeCorners`.

## The route

The claim is an equality of measures, and it is proved at the densities: the mixture of the
Gaussian laws against the inverse-gamma delay law has, at each `x`, density

  `∫₀^∞ (2πu)^{-1/2}e^{-x²/2u} · u^{-a-1}e^{-1/2u}/(2^aΓ(a)) du`,

and the substitution `w = 1/u` turns that into a Gamma integral. Both halves are in Mathlib:
`integral_comp_rpow_Ioi` at `p = -1` **is** the inversion substitution, and
`Real.integral_rpow_mul_exp_neg_mul_Ioi` evaluates what it produces. The estimate at the
statement said "arithmetic plus one change of variables under an integral", and that is what it
was.

**Integrability is not proved, and does not have to be.** Passing from the Bochner integral,
where the change of variables lives, to the `ℝ≥0∞` integral the measure equality needs would
normally ask for `Integrable`. It is cheaper to observe that
`integral_eq_lintegral_of_nonneg_ae` holds *unconditionally* — both sides are `0` when the
integrand is not integrable — so the computed value being **strictly positive** already forces
the `ℝ≥0∞` integral to be finite. `studentDensity_pos` is the whole of that argument.
-/

namespace SpatialLine

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal

/-! ## The integrand and its integral -/

/-- The mixture integrand of the Bessel corner, in the form the substitution wants:
`C·u^{-a-3/2}e^{-r/u}` with `r = (1+x²)/2`. -/
theorem inverseGamma_brownian_integrand (a x : ℝ) {u : ℝ} (hu : 0 < u) :
    inverseGammaDensity a u * brownianDensity u x
      = (2 ^ a * Real.Gamma a * Real.sqrt (2 * Real.pi))⁻¹
        * u ^ (-a - 3 / 2) * Real.exp (-((1 + x ^ 2) / 2 / u)) := by
  have hsqrt2pi : (0 : ℝ) < Real.sqrt (2 * Real.pi) := by
    apply Real.sqrt_pos.mpr; nlinarith [Real.two_le_pi]
  have hpow : u ^ (-a - 3 / 2 : ℝ) = u ^ (-a - 1 : ℝ) * (u ^ ((1 : ℝ) / 2))⁻¹ := by
    rw [← Real.rpow_neg hu.le, ← Real.rpow_add hu]
    congr 1
    ring
  have hexp : Real.exp (-(2 * u)⁻¹) * Real.exp (-x ^ 2 / (2 * u))
      = Real.exp (-((1 + x ^ 2) / 2 / u)) := by
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  rw [inverseGammaDensity, Set.indicator_of_mem (mem_Ioi.mpr hu), brownianDensity_eq hu,
    Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * Real.pi), ← Real.sqrt_eq_rpow] at *
  rw [hpow, ← hexp]
  have hupos : (0 : ℝ) < Real.sqrt u := Real.sqrt_pos.mpr hu
  field_simp

/-- **The normal variance-mixture computation.** The inverse-gamma mixture of Gaussian
densities is the Student-t density with `2a` degrees of freedom at scale `1`.

The substitution is `integral_comp_rpow_Ioi` at `p = -1`, which is exactly `w = 1/u`, and what
it leaves is `Real.integral_rpow_mul_exp_neg_mul_Ioi` at shape `a + 1/2` and rate
`(1+x²)/2`. -/
theorem integral_inverseGamma_brownian {a : ℝ} (ha : 0 < a) (x : ℝ) :
    (∫ u in Ioi (0 : ℝ), inverseGammaDensity a u * brownianDensity u x)
      = studentDensity a 1 x := by
  set C : ℝ := (2 ^ a * Real.Gamma a * Real.sqrt (2 * Real.pi))⁻¹ with hC
  set r : ℝ := (1 + x ^ 2) / 2 with hr
  have hrpos : (0 : ℝ) < r := by rw [hr]; positivity
  have hstep1 : (∫ u in Ioi (0 : ℝ), inverseGammaDensity a u * brownianDensity u x)
      = ∫ u in Ioi (0 : ℝ), C * u ^ (-a - 3 / 2) * Real.exp (-(r / u)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    exact inverseGamma_brownian_integrand a x hu
  have hsub := integral_comp_rpow_Ioi
    (fun y : ℝ => C * y ^ (-a - 3 / 2) * Real.exp (-(r / y))) (p := -1) (by norm_num)
  have hstep2 : (∫ t in Ioi (0 : ℝ),
        (|(-1 : ℝ)| * t ^ ((-1 : ℝ) - 1)) •
          (C * (t ^ (-1 : ℝ)) ^ (-a - 3 / 2) * Real.exp (-(r / t ^ (-1 : ℝ)))))
      = ∫ t in Ioi (0 : ℝ), C * (t ^ (a + 1 / 2 - 1) * Real.exp (-(r * t))) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : (0 : ℝ) < t := ht
    have hinv : t ^ (-1 : ℝ) = t⁻¹ := Real.rpow_neg_one t
    have hpow : (t ^ (-1 : ℝ)) ^ (-a - 3 / 2 : ℝ) = t ^ (a + 3 / 2 : ℝ) := by
      rw [← Real.rpow_mul ht0.le]
      congr 1
      ring
    have hmul : t ^ ((-1 : ℝ) - 1) * t ^ (a + 3 / 2 : ℝ) = t ^ (a + 1 / 2 - 1 : ℝ) := by
      rw [← Real.rpow_add ht0]
      congr 1
      ring
    rw [hinv] at hpow
    rw [hinv, hpow, smul_eq_mul]
    have hdiv : r / t⁻¹ = r * t := by field_simp
    rw [hdiv]
    have h1 : |(-1 : ℝ)| = 1 := by norm_num
    rw [h1, one_mul, ← hmul]
    ring
  rw [hstep1, ← hsub, hstep2, integral_const_mul,
    Real.integral_rpow_mul_exp_neg_mul_Ioi (by linarith : (0 : ℝ) < a + 1 / 2) hrpos]
  have h2 : (0 : ℝ) < 1 + x ^ 2 := by positivity
  have hGa : (0 : ℝ) < Real.Gamma a := Real.Gamma_pos_of_pos ha
  have hpi : (0 : ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hsqrt2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h2a : (0 : ℝ) < (2 : ℝ) ^ a := Real.rpow_pos_of_pos (by norm_num) a
  have hone : (1 / r : ℝ) = 2 / (1 + x ^ 2) := by rw [hr]; field_simp
  have hsplit : (2 : ℝ) ^ (a + 1 / 2) = 2 ^ a * Real.sqrt 2 := by
    rw [Real.rpow_add (by norm_num), Real.sqrt_eq_rpow]
  have hneg : ((1 + x ^ 2) : ℝ) ^ (-a - 1 / 2) = (((1 + x ^ 2) : ℝ) ^ (a + 1 / 2))⁻¹ := by
    rw [← Real.rpow_neg h2.le]
    congr 1
    ring
  have hsq2pi : Real.sqrt (2 * Real.pi) = Real.sqrt 2 * Real.sqrt Real.pi :=
    Real.sqrt_mul (by norm_num) _
  rw [studentDensity, hone, Real.div_rpow (by norm_num) h2.le, hsplit, hC, hsq2pi]
  simp only [div_one, inv_one]
  rw [hneg]
  have hd : (0 : ℝ) < ((1 + x ^ 2) : ℝ) ^ (a + 1 / 2) := Real.rpow_pos_of_pos h2 _
  field_simp

/-! ## From the density to the measure -/

theorem measurable_inverseGammaDensity (a : ℝ) : Measurable (inverseGammaDensity a) := by
  unfold inverseGammaDensity
  refine Measurable.indicator ?_ measurableSet_Ioi
  fun_prop

theorem inverseGammaDensity_nonneg {a : ℝ} (ha : 0 < a) (u : ℝ) :
    0 ≤ inverseGammaDensity a u := by
  unfold inverseGammaDensity
  refine Set.indicator_nonneg (fun t ht => ?_) u
  have ht0 : (0 : ℝ) < t := ht
  have h1 : (0 : ℝ) < t ^ (-a - 1) := Real.rpow_pos_of_pos ht0 _
  have h2 : (0 : ℝ) < (2 : ℝ) ^ a := Real.rpow_pos_of_pos (by norm_num) a
  have h3 : (0 : ℝ) < Real.Gamma a := Real.Gamma_pos_of_pos ha
  positivity

/-- The Student-t density is strictly positive. This is what makes the `ℝ≥0∞` integral finite
without an integrability proof: `∫⁻` infinite would read as `0` after `toReal`. -/
theorem studentDensity_pos {a : ℝ} (ha : 0 < a) (x : ℝ) : 0 < studentDensity a 1 x := by
  unfold studentDensity
  have h1 : (0 : ℝ) < Real.Gamma (a + 1 / 2) := Real.Gamma_pos_of_pos (by linarith)
  have h2 : (0 : ℝ) < Real.Gamma a := Real.Gamma_pos_of_pos ha
  have h3 : (0 : ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have h4 : (0 : ℝ) < (1 + (x / 1) ^ 2) ^ (-a - 1 / 2) :=
    Real.rpow_pos_of_pos (by positivity) _
  positivity

theorem lintegral_inverseGamma_brownian {a : ℝ} (ha : 0 < a) (x : ℝ) :
    (∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (inverseGammaDensity a u * brownianDensity u x))
      = ENNReal.ofReal (studentDensity a 1 x) := by
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      fun u => inverseGammaDensity a u * brownianDensity u x :=
    .of_forall fun u =>
      mul_nonneg (inverseGammaDensity_nonneg ha u) (brownianDensity_nonneg u x)
  have hmeas : AEStronglyMeasurable
      (fun u => inverseGammaDensity a u * brownianDensity u x)
      (volume.restrict (Ioi (0 : ℝ))) :=
    ((measurable_inverseGammaDensity a).mul
      (measurable_brownianDensity_time x)).aestronglyMeasurable
  have heq := integral_eq_lintegral_of_nonneg_ae hnn hmeas
  rw [integral_inverseGamma_brownian ha x] at heq
  have hpos := studentDensity_pos ha x
  have hne : (∫⁻ u in Ioi (0 : ℝ),
      ENNReal.ofReal (inverseGammaDensity a u * brownianDensity u x)) ≠ ⊤ := by
    intro h
    rw [h] at heq
    simp at heq
    linarith
  rw [heq, ENNReal.ofReal_toReal hne]

/-- **`prop:bridge-families`(3), the causal Bessel family maps to the Student-t family with
`2a` degrees of freedom.**

`Skeleton.bridge_families_bessel`'s statement verbatim. This is also `prop:student-t`(1)'s
conditioning computation, so the two nodes' `\lean` tags share it.

Priced **M**, paid **M**. -/
theorem bridge_families_bessel (a : ℝ) (ha : 0 < a) :
    (inverseGammaLaw a).bind brownianLaw = studentLaw a 1 := by
  refine Measure.ext fun s hs => ?_
  have hdens : Measurable fun u : ℝ => ENNReal.ofReal (inverseGammaDensity a u) :=
    (measurable_inverseGammaDensity a).ennreal_ofReal
  have hcoe : Measurable fun u : ℝ => brownianLaw u s :=
    Measure.measurable_coe hs |>.comp measurable_brownianLaw
  rw [Measure.bind_apply hs measurable_brownianLaw.aemeasurable, inverseGammaLaw,
    lintegral_withDensity_eq_lintegral_mul₀ hdens.aemeasurable hcoe.aemeasurable]
  have hind : ∀ u : ℝ,
      (fun u : ℝ => ENNReal.ofReal (inverseGammaDensity a u)) u * (fun u => brownianLaw u s) u
        = Set.indicator (Ioi (0 : ℝ))
            (fun u => ENNReal.ofReal (inverseGammaDensity a u) * brownianLaw u s) u := by
    intro u
    by_cases h : u ∈ Ioi (0 : ℝ)
    · rw [Set.indicator_of_mem h]
    · rw [Set.indicator_of_notMem h]
      show ENNReal.ofReal (inverseGammaDensity a u) * brownianLaw u s = 0
      rw [inverseGammaDensity, Set.indicator_of_notMem h]
      simp
  simp only [Pi.mul_apply] at *
  rw [lintegral_congr hind, lintegral_indicator measurableSet_Ioi]
  have hstep : (∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (inverseGammaDensity a u) * brownianLaw u s)
      = ∫⁻ u in Ioi (0 : ℝ), ∫⁻ x in s,
          ENNReal.ofReal (inverseGammaDensity a u) * ENNReal.ofReal (brownianDensity u x) := by
    refine setLIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    have hu0 : (0 : ℝ) < u := hu
    rw [brownianLaw_eq_withDensity hu0, withDensity_apply _ hs,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [hstep]
  have huncurry : Measurable (Function.uncurry fun u x : ℝ =>
      ENNReal.ofReal (inverseGammaDensity a u) * ENNReal.ofReal (brownianDensity u x)) := by
    refine Measurable.mul ?_ ?_
    · exact hdens.comp measurable_fst
    · exact measurable_brownianDensity_uncurry.ennreal_ofReal
  rw [lintegral_lintegral_swap huncurry.aemeasurable, studentLaw, withDensity_apply _ hs]
  refine setLIntegral_congr_fun hs fun x _ => ?_
  rw [← lintegral_inverseGamma_brownian ha x]
  refine setLIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
  rw [← ENNReal.ofReal_mul (inverseGammaDensity_nonneg ha u)]

end SpatialLine
