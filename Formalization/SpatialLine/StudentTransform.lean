/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.FirstPassage
import SpatialLine.BridgeBessel
import SpatialLine.StudentCorner

/-!
# `prop:student-t`(2), the transform

Blueprint: `blueprint/src/parts/10-corners.tex`, `prop:student-t`(2).
-/

namespace SpatialLine

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-- **The Bessel–Laplace integral, in `ℝ≥0∞` and down to the defining integral of `K_p`.**

`∫_0^∞ u^{p-1}e^{-A/u - Bu}\,du = 2c^pK_p(2s)` for `A, B > 0`, every real `p`, and
`c = \sqrt A/\sqrt B`, `s = \sqrt A\sqrt B` — here with the right-hand side left as the integral
that *defines* `besselK`, and with the constants written in the coordinates
`SpatialLine/FirstPassage.lean` records as the ones that keep fourth roots out.

This is `lintegral_Ioi_firstPassage`'s computation at a general order, and it is cheaper than
that one: at `p = -3/2` the value has to be read off `besselK_half`, while at a general `p` the
cosh-integral **is** the definition of `K_p` and nothing has to be evaluated. -/
theorem lintegral_Ioi_rpow_exp_besselKernel {p A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    (∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (u ^ (p - 1) * Real.exp (-(A / u + B * u))))
      = ENNReal.ofReal ((Real.sqrt A / Real.sqrt B) ^ p) * (2 * ∫⁻ v in Ioi (0 : ℝ),
          ENNReal.ofReal (Real.cosh (p * v)
            * Real.exp (-(2 * (Real.sqrt A * Real.sqrt B) * Real.cosh v)))) := by
  have hsA : (0 : ℝ) < Real.sqrt A := Real.sqrt_pos.mpr hA
  have hsB : (0 : ℝ) < Real.sqrt B := Real.sqrt_pos.mpr hB
  set c : ℝ := Real.sqrt A / Real.sqrt B with hcdef
  set s : ℝ := Real.sqrt A * Real.sqrt B with hsdef
  have hc : (0 : ℝ) < c := by rw [hcdef]; positivity
  have hs : (0 : ℝ) < s := by rw [hsdef]; positivity
  have hcp : (0 : ℝ) < c ^ p := Real.rpow_pos_of_pos hc p
  have hAA : A / Real.sqrt A = Real.sqrt A := by
    rw [eq_comm, eq_div_iff hsA.ne']
    exact Real.mul_self_sqrt hA.le
  have hBB : B / Real.sqrt B = Real.sqrt B := by
    rw [eq_comm, eq_div_iff hsB.ne']
    exact Real.mul_self_sqrt hB.le
  have hAc : A / c = s := by
    rw [hcdef, hsdef, div_div_eq_mul_div,
      show A * Real.sqrt B / Real.sqrt A = (A / Real.sqrt A) * Real.sqrt B by ring, hAA]
  have hBc : B * c = s := by
    rw [hcdef, hsdef,
      show B * (Real.sqrt A / Real.sqrt B) = (B / Real.sqrt B) * Real.sqrt A by ring, hBB]
    ring
  have hpt : ∀ v : ℝ, ENNReal.ofReal (c * Real.exp v)
        * ENNReal.ofReal ((c * Real.exp v) ^ (p - 1)
            * Real.exp (-(A / (c * Real.exp v) + B * (c * Real.exp v))))
      = ENNReal.ofReal (Real.exp (p * v)
          * (c ^ p * Real.exp (-(2 * s * Real.cosh v)))) := by
    intro v
    have hev : (0 : ℝ) < Real.exp v := Real.exp_pos v
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [Real.mul_rpow hc.le hev.le, exp_rpow]
    have harg : A / (c * Real.exp v) + B * (c * Real.exp v) = 2 * s * Real.cosh v := by
      rw [show A / (c * Real.exp v) = (A / c) * Real.exp (-v) by
            rw [Real.exp_neg]; field_simp,
        show B * (c * Real.exp v) = (B * c) * Real.exp v by ring, hAc, hBc, Real.cosh_eq]
      ring
    rw [harg]
    have hcpow : c * c ^ (p - 1) = c ^ p := by
      nth_rewrite 1 [← Real.rpow_one c]
      rw [← Real.rpow_add hc]
      norm_num
    calc c * Real.exp v * (c ^ (p - 1) * Real.exp (v * (p - 1))
            * Real.exp (-(2 * s * Real.cosh v)))
        = (c * c ^ (p - 1)) * (Real.exp v * Real.exp (v * (p - 1)))
            * Real.exp (-(2 * s * Real.cosh v)) := by ring
      _ = c ^ p * Real.exp (p * v) * Real.exp (-(2 * s * Real.cosh v)) := by
          rw [hcpow, ← Real.exp_add, show v + v * (p - 1) = p * v by ring]
      _ = Real.exp (p * v) * (c ^ p * Real.exp (-(2 * s * Real.cosh v))) := by ring
  rw [lintegral_Ioi_comp_exp hc, funext hpt,
    lintegral_exp_mul_of_even (G := fun v => c ^ p * Real.exp (-(2 * s * Real.cosh v)))
      (by fun_prop) (fun v => by positivity) (fun v => by rw [Real.cosh_neg])]
  have hconst : ∀ v : ℝ, ENNReal.ofReal (Real.cosh (p * v)
        * (c ^ p * Real.exp (-(2 * s * Real.cosh v))))
      = ENNReal.ofReal (c ^ p)
        * ENNReal.ofReal (Real.cosh (p * v) * Real.exp (-(2 * s * Real.cosh v))) := by
    intro v
    rw [← ENNReal.ofReal_mul hcp.le]
    congr 1
    ring
  simp only [hconst]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc, ← mul_assoc,
    mul_comm (2 : ℝ≥0∞) (ENNReal.ofReal (c ^ p)), mul_assoc]

/-- **The cosh-integral is `K_p`**, once it is known to be finite.

`besselK` is a Bochner integral and returns junk when its integrand is not integrable, so the
identification is stated with finiteness as a hypothesis; every consumer here gets it by
comparison with a convergent integral. This is `lintegral_besselK_half`'s positivity trick in
the direction that needs no value. -/
theorem lintegral_cosh_exp_eq_besselK (p : ℝ) {z : ℝ}
    (hfin : (∫⁻ v in Ioi (0 : ℝ),
      ENNReal.ofReal (Real.cosh (p * v) * Real.exp (-(z * Real.cosh v)))) ≠ ⊤) :
    (∫⁻ v in Ioi (0 : ℝ), ENNReal.ofReal (Real.cosh (p * v) * Real.exp (-(z * Real.cosh v))))
      = ENNReal.ofReal (besselK p z) := by
  have hb : besselK p z
      = (∫⁻ v in Ioi (0 : ℝ),
          ENNReal.ofReal (Real.cosh (p * v) * Real.exp (-(z * Real.cosh v)))).toReal := by
    rw [besselK]
    have hcongr : (∫ u in Ioi (0 : ℝ), Real.exp (-(z * Real.cosh u)) * Real.cosh (p * u))
        = ∫ u in Ioi (0 : ℝ), Real.cosh (p * u) * Real.exp (-(z * Real.cosh u)) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
      ring
    rw [hcongr]
    refine integral_eq_lintegral_of_nonneg_ae ?_ (by fun_prop)
    exact .of_forall fun u => by positivity
  rw [hb, ENNReal.ofReal_toReal hfin]

/-- **The mass of the inverse-gamma law.** `∫_0^∞ u^{-a-1}e^{-1/(2u)}\,du = 2^a\Gamma(a)`.

Two exponential substitutions and one reflection: `u = e^v` turns the integral into
`∫_ℝ e^{-av}e^{-e^{-v}/2}dv`, the reflection `v \mapsto -v` into `∫_ℝ e^{av}e^{-e^v/2}dv`, and
`u = e^v` read backwards into the Gamma integral at rate `1/2`. Mathlib's
`integral_rpow_mul_exp_neg_mul_Ioi` evaluates that one, and the positivity trick carries the
value back into `ℝ≥0∞`. -/
theorem lintegral_Ioi_inverseGammaKernel {a : ℝ} (ha : 0 < a) :
    (∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (u ^ (-a - 1) * Real.exp (-(2 * u)⁻¹)))
      = ENNReal.ofReal (2 ^ a * Real.Gamma a) := by
  have hemb : MeasurableEmbedding (fun x : ℝ => -x) :=
    (Homeomorph.neg ℝ).toMeasurableEquiv.measurableEmbedding
  have hmp : MeasurePreserving (fun x : ℝ => -x) volume volume :=
    Measure.measurePreserving_neg volume
  -- the two sides, each pushed onto the line
  have hleft : (∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (u ^ (-a - 1) * Real.exp (-(2 * u)⁻¹)))
      = ∫⁻ v, ENNReal.ofReal (Real.exp (-(a * v)) * Real.exp (-(Real.exp (-v) / 2))) := by
    rw [lintegral_Ioi_comp_exp (c := 1) one_pos]
    refine lintegral_congr fun v => ?_
    have hev : (0 : ℝ) < Real.exp v := Real.exp_pos v
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [one_mul, exp_rpow,
      show ((2 : ℝ) * Real.exp v)⁻¹ = Real.exp (-v) / 2 from by
        rw [Real.exp_neg]; field_simp,
      ← mul_assoc, ← Real.exp_add]
    congr 1
    congr 1
    ring
  have hright : (∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (u ^ (a - 1) * Real.exp (-(2⁻¹ * u))))
      = ∫⁻ v, ENNReal.ofReal (Real.exp (a * v) * Real.exp (-(Real.exp v / 2))) := by
    rw [lintegral_Ioi_comp_exp (c := 1) one_pos]
    refine lintegral_congr fun v => ?_
    have hev : (0 : ℝ) < Real.exp v := Real.exp_pos v
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [one_mul, exp_rpow,
      show -((2 : ℝ)⁻¹ * Real.exp v) = -(Real.exp v / 2) from by ring,
      ← mul_assoc, ← Real.exp_add]
    congr 1
    congr 1
    ring
  have hrefl : (∫⁻ v, ENNReal.ofReal (Real.exp (-(a * v)) * Real.exp (-(Real.exp (-v) / 2))))
      = ∫⁻ v, ENNReal.ofReal (Real.exp (a * v) * Real.exp (-(Real.exp v / 2))) := by
    have hkey := hmp.lintegral_comp_emb hemb
      (fun v => ENNReal.ofReal (Real.exp (a * v) * Real.exp (-(Real.exp v / 2))))
    rw [← hkey]
    refine lintegral_congr fun v => ?_
    congr 1
    congr 1
    congr 1
    ring
  -- and the Gamma evaluation
  have hgamma : (∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (u ^ (a - 1) * Real.exp (-(2⁻¹ * u))))
      = ENNReal.ofReal (2 ^ a * Real.Gamma a) := by
    have hval := Real.integral_rpow_mul_exp_neg_mul_Ioi ha (by norm_num : (0:ℝ) < 2⁻¹)
    have hpos : (0 : ℝ) < 2 ^ a * Real.Gamma a := by
      have := Real.Gamma_pos_of_pos ha
      positivity
    have hcoe : ((1 : ℝ) / 2⁻¹) ^ a * Real.Gamma a = 2 ^ a * Real.Gamma a := by
      norm_num
    rw [hcoe] at hval
    have hb : (∫ u in Ioi (0 : ℝ), u ^ (a - 1) * Real.exp (-(2⁻¹ * u)))
        = (∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (u ^ (a - 1) * Real.exp (-(2⁻¹ * u)))).toReal := by
      refine integral_eq_lintegral_of_nonneg_ae ?_ (by fun_prop)
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
      have : (0 : ℝ) < u := hu
      positivity
    rw [hb] at hval
    set X := ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (u ^ (a - 1) * Real.exp (-(2⁻¹ * u))) with hX
    have hXne : X ≠ ⊤ := by
      intro h
      rw [h, ENNReal.toReal_top] at hval
      linarith
    rw [← ENNReal.ofReal_toReal hXne, hval]
  rw [hleft, hrefl, ← hright, hgamma]

/-! ## The inverse-gamma law is a probability law carried by the half-line -/

theorem inverseGammaDensity_eq_indicator (a : ℝ) :
    (fun u : ℝ => ENNReal.ofReal (inverseGammaDensity a u))
      = Set.indicator (Ioi (0 : ℝ))
          (fun u => ENNReal.ofReal (u ^ (-a - 1) * Real.exp (-(2 * u)⁻¹)
            * (2 ^ a * Real.Gamma a)⁻¹)) := by
  funext u
  by_cases h : u ∈ Ioi (0 : ℝ)
  · rw [Set.indicator_of_mem h, inverseGammaDensity, Set.indicator_of_mem h]
    congr 1
  · rw [Set.indicator_of_notMem h, inverseGammaDensity, Set.indicator_of_notMem h]
    simp

theorem inverseGammaLaw_Iio_zero (a : ℝ) : inverseGammaLaw a (Iio 0) = 0 := by
  rw [inverseGammaLaw, withDensity_apply _ measurableSet_Iio,
    inverseGammaDensity_eq_indicator]
  rw [setLIntegral_congr_fun measurableSet_Iio (g := fun _ => (0 : ℝ≥0∞)) ?_]
  · simp
  · intro u hu
    exact Set.indicator_of_notMem (by simpa using le_of_lt hu) _

theorem isProbabilityMeasure_inverseGammaLaw {a : ℝ} (ha : 0 < a) :
    IsProbabilityMeasure (inverseGammaLaw a) := by
  have hpos : (0 : ℝ) < 2 ^ a * Real.Gamma a := by
    have := Real.Gamma_pos_of_pos ha
    positivity
  constructor
  rw [inverseGammaLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    inverseGammaDensity_eq_indicator, lintegral_indicator measurableSet_Ioi]
  have hstep : ∀ u : ℝ, ENNReal.ofReal (u ^ (-a - 1) * Real.exp (-(2 * u)⁻¹)
        * (2 ^ a * Real.Gamma a)⁻¹)
      = ENNReal.ofReal ((2 ^ a * Real.Gamma a)⁻¹)
        * ENNReal.ofReal (u ^ (-a - 1) * Real.exp (-(2 * u)⁻¹)) := by
    intro u
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  simp only [hstep]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_Ioi_inverseGammaKernel ha,
    ← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ hpos.ne', ENNReal.ofReal_one]

/-! ## `prop:student-t`(2) -/

/-- `K_{-p} = K_p`: the defining integral is even in the order. -/
theorem besselK_neg (p z : ℝ) : besselK (-p) z = besselK p z := by
  rw [besselK, besselK]
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
  rw [show -p * u = -(p * u) by ring, Real.cosh_neg]

/-- **The Laplace transform of the inverse-gamma law at `\sigma = \omega^2/2`.**

This is `prop:student-t`(2) before the conditioning is undone: the causal Bessel family's delay
law has Laplace transform `2^{1-a}\Gamma(a)^{-1}\sigma^{a/2}K_a(\sqrt{2\sigma})`, written here at
`\sigma = \omega^2/2`, where `\sqrt{2\sigma} = |\omega|`. -/
theorem lintegral_exp_neg_inverseGammaLaw {a ω : ℝ} (ha : 0 < a) (hω : ω ≠ 0) :
    (∫⁻ u, ENNReal.ofReal (Real.exp (-(ω ^ 2 / 2 * u))) ∂(inverseGammaLaw a))
      = ENNReal.ofReal (2 ^ (1 - a) / Real.Gamma a * |ω| ^ a * besselK a |ω|) := by
  have hΓ : (0 : ℝ) < Real.Gamma a := Real.Gamma_pos_of_pos ha
  have hK : (0 : ℝ) < 2 ^ a * Real.Gamma a := by positivity
  have habs : (0 : ℝ) < |ω| := abs_pos.mpr hω
  have hB : (0 : ℝ) < ω ^ 2 / 2 := by positivity
  have hprob := isProbabilityMeasure_inverseGammaLaw ha
  -- the substitution constants
  have hsqrtinv : (0 : ℝ) < Real.sqrt 2⁻¹ := Real.sqrt_pos.mpr (by norm_num)
  have hsq : Real.sqrt (ω ^ 2 / 2) = |ω| * Real.sqrt 2⁻¹ := by
    rw [show ω ^ 2 / 2 = ω ^ 2 * 2⁻¹ by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_sq_eq_abs]
  have hc : Real.sqrt 2⁻¹ / Real.sqrt (ω ^ 2 / 2) = |ω|⁻¹ := by
    rw [hsq]
    field_simp
  have hs : 2 * (Real.sqrt 2⁻¹ * Real.sqrt (ω ^ 2 / 2)) = |ω| := by
    rw [hsq, show Real.sqrt 2⁻¹ * (|ω| * Real.sqrt 2⁻¹)
        = |ω| * (Real.sqrt 2⁻¹ * Real.sqrt 2⁻¹) by ring,
      Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2⁻¹)]
    ring
  have hcpow : (|ω|⁻¹ : ℝ) ^ (-a) = |ω| ^ a := by
    rw [Real.inv_rpow habs.le, Real.rpow_neg habs.le, inv_inv]
  -- the integral, rewritten against Lebesgue measure
  have hdens : Measurable fun u : ℝ => ENNReal.ofReal (inverseGammaDensity a u) :=
    (measurable_inverseGammaDensity a).ennreal_ofReal
  have hstep : (∫⁻ u, ENNReal.ofReal (Real.exp (-(ω ^ 2 / 2 * u))) ∂(inverseGammaLaw a))
      = ENNReal.ofReal (2 ^ a * Real.Gamma a)⁻¹
        * ∫⁻ u in Ioi (0 : ℝ),
            ENNReal.ofReal (u ^ (-a - 1) * Real.exp (-(2⁻¹ / u + ω ^ 2 / 2 * u))) := by
    rw [inverseGammaLaw, lintegral_withDensity_eq_lintegral_mul₀ hdens.aemeasurable (by fun_prop),
      inverseGammaDensity_eq_indicator]
    have hind : ∀ u : ℝ,
        (Set.indicator (Ioi (0 : ℝ))
          (fun u => ENNReal.ofReal (u ^ (-a - 1) * Real.exp (-(2 * u)⁻¹)
            * (2 ^ a * Real.Gamma a)⁻¹)) * fun u => ENNReal.ofReal
              (Real.exp (-(ω ^ 2 / 2 * u)))) u
        = Set.indicator (Ioi (0 : ℝ))
            (fun u => ENNReal.ofReal (2 ^ a * Real.Gamma a)⁻¹
              * ENNReal.ofReal (u ^ (-a - 1)
                  * Real.exp (-(2⁻¹ / u + ω ^ 2 / 2 * u)))) u := by
      intro u
      by_cases h : u ∈ Ioi (0 : ℝ)
      · have hu : (0 : ℝ) < u := h
        rw [Pi.mul_apply, Set.indicator_of_mem h, Set.indicator_of_mem h,
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [show -(2⁻¹ / u + ω ^ 2 / 2 * u) = -(2 * u)⁻¹ + -(ω ^ 2 / 2 * u) by
          field_simp; ring, Real.exp_add]
        ring
      · rw [Pi.mul_apply, Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_mul]
    simp only [hind]
    rw [lintegral_indicator measurableSet_Ioi,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  -- the substituted form, and the comparison that makes it finite
  have hsub := lintegral_Ioi_rpow_exp_besselKernel (p := -a) (A := 2⁻¹) (B := ω ^ 2 / 2)
    (by norm_num) hB
  rw [hc, hs, hcpow] at hsub
  have hYle : (∫⁻ u in Ioi (0 : ℝ),
        ENNReal.ofReal (u ^ (-a - 1) * Real.exp (-(2⁻¹ / u + ω ^ 2 / 2 * u))))
      ≤ ENNReal.ofReal (2 ^ a * Real.Gamma a) := by
    rw [← lintegral_Ioi_inverseGammaKernel ha]
    refine setLIntegral_mono_ae (by fun_prop) (.of_forall fun u hu => ?_)
    have hu0 : (0 : ℝ) < u := hu
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (by positivity))
    refine Real.exp_le_exp.mpr ?_
    have hhalf : ((2 : ℝ) * u)⁻¹ = 2⁻¹ / u := by field_simp
    rw [hhalf]
    have : (0 : ℝ) ≤ ω ^ 2 / 2 * u := by positivity
    linarith
  have hXne : (∫⁻ v in Ioi (0 : ℝ),
      ENNReal.ofReal (Real.cosh (-a * v) * Real.exp (-(|ω| * Real.cosh v)))) ≠ ⊤ := by
    intro h
    rw [h, ENNReal.mul_top (by norm_num : (2 : ℝ≥0∞) ≠ 0),
      ENNReal.mul_top (by
        simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
        positivity)] at hsub
    rw [hsub] at hYle
    exact absurd (top_le_iff.mp hYle) (by simp)
  rw [hstep, hsub, lintegral_cosh_exp_eq_besselK (-a) hXne, besselK_neg,
    show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
    ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
    ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ |ω| ^ a),
    ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (2 ^ a * Real.Gamma a)⁻¹)]
  congr 1
  rw [Real.rpow_sub (by norm_num), Real.rpow_one]
  field_simp

theorem besselK_nonneg (p z : ℝ) : 0 ≤ besselK p z := by
  rw [besselK]
  refine setIntegral_nonneg measurableSet_Ioi fun u _ => ?_
  positivity

/-- The Student-t law at canonical scale is a symmetric probability law: it *is* the Brownian
mixture over the inverse-gamma delay (`bridge_families_bessel`). -/
theorem isProbabilityMeasure_studentLaw_one {a : ℝ} (ha : 0 < a) :
    IsProbabilityMeasure (studentLaw a 1) := by
  have := isProbabilityMeasure_inverseGammaLaw ha
  rw [← bridge_families_bessel a ha]
  exact isProbabilityMeasure_bind_brownianLaw _

theorem isSymmetric_studentLaw_one {a : ℝ} (ha : 0 < a) : IsSymmetric (studentLaw a 1) := by
  rw [← bridge_families_bessel a ha]
  exact isSymmetric_bind_brownianLaw _

/-- **`prop:student-t`(2), the transform.** `\hat\phi_1(\omega) =
\frac{2^{1-a}}{\Gamma(a)}|\omega|^aK_a(|\omega|)` for `\omega \ne 0`.

`Skeleton.student_transform`'s conclusion, and the reviewed `\omega \ne 0` quantifier (review
**R10**): at the origin the identity is false, `|0|^a` being `0` while the transform of a
probability law is `1`.

**The vestigial hypotheses are dropped.** The skeleton's statement carries a causally admissible
`F` with its Laplace-transform specification, which the *conclusion does not mention*: that
hypothesis is the route the node's proof takes and not the obligation, and the causal exponent
is never formed here. What the checked proof consumes is the conditioning identity
`bridge_families_bessel` — the law *is* the Brownian mixture over the inverse-gamma delay — and
the Laplace transform of that delay law, which is the Bessel–Laplace integral above at
`\sigma = \omega^2/2`. Ledger **A18**, the causal admissibility of the Bessel family, is not on
this path; neither is any Bessel asymptotic (ledger **A16**), because `besselK` is *defined*
here by the integral that the substitution produces. -/
theorem student_transform {a : ℝ} (ha : 0 < a) :
    ∀ ω : ℝ, ω ≠ 0 → fourierCos (studentLaw a 1) ω
      = 2 ^ (1 - a) / Real.Gamma a * |ω| ^ a * besselK a |ω| := by
  intro ω hω
  have hprob := isProbabilityMeasure_inverseGammaLaw ha
  have hval : (0 : ℝ) ≤ 2 ^ (1 - a) / Real.Gamma a * |ω| ^ a * besselK a |ω| := by
    have hΓ : (0 : ℝ) < Real.Gamma a := Real.Gamma_pos_of_pos ha
    have := besselK_nonneg a |ω|
    positivity
  rw [← bridge_families_bessel a ha,
    fourierCos_bind_brownianLaw (inverseGammaLaw_Iio_zero a) ω]
  have hb : (∫ u, Real.exp (-(ω ^ 2 / 2 * u)) ∂(inverseGammaLaw a))
      = (∫⁻ u, ENNReal.ofReal (Real.exp (-(ω ^ 2 / 2 * u))) ∂(inverseGammaLaw a)).toReal := by
    refine integral_eq_lintegral_of_nonneg_ae (.of_forall fun u => (Real.exp_pos _).le)
      (by fun_prop)
  rw [hb, lintegral_exp_neg_inverseGammaLaw ha hω, ENNReal.toReal_ofReal hval]

end SpatialLine
