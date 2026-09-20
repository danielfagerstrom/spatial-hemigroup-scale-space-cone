/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.Moments
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

import SpatialLine.BesselHalf

/-!
# The first-passage Laplace transform

Blueprint: the profile clause of `prop:bridge-families`(2), and `prop:thorin-subclass`(4), both
of which run on the classical identity

  `\int_0^\infty u^{-3/2} e^{-A/u - Bu}\,du = \sqrt{\pi/A}\,e^{-2\sqrt{AB}}`  (A, B > 0),

which at `A = x^2/2`, `B = \sigma` is the Laplace transform of the first-passage law of Brownian
motion at level `x`.

## What proving this found

**The exponential change of variables is available in the `\mathbb{R}_{\ge 0}^\infty` form, and
that is what makes the identity cheap.** The skeleton priced this `M-L` on the ground that the
substitution `u = \sqrt{A/B}e^v`, from the line onto `(0,\infty)`, "is not
`integral_comp_rpow_Ioi` and this development has not needed it before". It is
`lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn`, which asks only for measurability of the
domain, the derivative and *monotonicity* --- no injectivity argument, no integrability side
condition. Working in `\mathbb{R}_{\ge 0}^\infty` also makes the folding of the line onto the
half-line free, where a Bochner split would first have to prove the integrand integrable.

**The Bochner value comes back for free by the positivity trick.** `besselK_half` is a Bochner
statement; `integral_eq_lintegral_of_nonneg_ae` holds unconditionally, so a *strictly positive*
computed value forces the `\mathbb{R}_{\ge 0}^\infty` integral to be finite and equal to
`ENNReal.ofReal` of it. That is the two-line step `SpatialLine/BridgeBessel.lean` recorded in
wave 4, used here in the other direction.

**No fourth roots appear if the constants stay under `Real.sqrt`.** Written with
`c = \sqrt A/\sqrt B` and `s = \sqrt A\sqrt B`, the final algebra is
`\sqrt c\,\sqrt s = \sqrt{cs} = \sqrt A`; written with `(A/B)^{1/4}` and `(AB)^{1/4}` it is a
page of `rpow` arithmetic. The choice of coordinates is the whole difference.
-/

namespace SpatialLine

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-- The exponential change of variables `v ↦ c e^v`, from the line onto `(0,∞)`. -/
theorem expMap_image {c : ℝ} (hc : 0 < c) :
    (fun v : ℝ => c * Real.exp v) '' univ = Ioi (0 : ℝ) := by
  ext y
  constructor
  · rintro ⟨v, -, rfl⟩
    exact mul_pos hc (Real.exp_pos v)
  · intro hy
    refine ⟨Real.log (y / c), mem_univ _, ?_⟩
    show c * Real.exp (Real.log (y / c)) = y
    rw [Real.exp_log (div_pos hy hc)]
    field_simp

theorem expMap_monotone {c : ℝ} (hc : 0 < c) :
    MonotoneOn (fun v : ℝ => c * Real.exp v) univ := by
  intro x _ y _ hxy
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hxy) hc.le

theorem expMap_hasDeriv (c v : ℝ) :
    HasDerivAt (fun w : ℝ => c * Real.exp w) (c * Real.exp v) v :=
  (Real.hasDerivAt_exp v).const_mul c

/-- The change of variables in `ℝ≥0∞` form. -/
theorem lintegral_Ioi_comp_exp {c : ℝ} (hc : 0 < c) (g : ℝ → ℝ≥0∞) :
    (∫⁻ u in Ioi (0 : ℝ), g u)
      = ∫⁻ v, ENNReal.ofReal (c * Real.exp v) * g (c * Real.exp v) := by
  have h := lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn
    (s := (univ : Set ℝ)) (f := fun v : ℝ => c * Real.exp v)
    (f' := fun v : ℝ => c * Real.exp v) MeasurableSet.univ
    (fun v _ => (expMap_hasDeriv c v).hasDerivWithinAt) (expMap_monotone hc) g
  rw [expMap_image hc] at h
  rw [h, setLIntegral_univ]


/-- **The reflection fold at a general exponential weight.** For an even nonnegative `G`,
`∫_ℝ e^{pv}G(v)\,dv = 2∫_0^∞ \cosh(pv)G(v)\,dv`.

Written at a general `p` in wave 7 for `student_transform`; it lives here, one file below its
second consumer, because the `p = -1/2` instance below it was written first (wave 5, for the
first-passage transform) and is used in this file. The two were the same reflection argument
twice, and the merge of 2026-09-10 kept this one. -/
theorem lintegral_exp_mul_of_even {p : ℝ} {G : ℝ → ℝ} (hGm : Measurable G)
    (hGnn : ∀ v, 0 ≤ G v) (hGeven : ∀ v, G (-v) = G v) :
    (∫⁻ v, ENNReal.ofReal (Real.exp (p * v) * G v))
      = 2 * ∫⁻ v in Ioi (0 : ℝ), ENNReal.ofReal (Real.cosh (p * v) * G v) := by
  have hemb : MeasurableEmbedding (fun x : ℝ => -x) :=
    (Homeomorph.neg ℝ).toMeasurableEquiv.measurableEmbedding
  have hmp : MeasurePreserving (fun x : ℝ => -x) volume volume :=
    Measure.measurePreserving_neg volume
  have hpre : (fun x : ℝ => -x) ⁻¹' (Ioi (0 : ℝ)) = Iio (0 : ℝ) := by ext x; simp
  set g : ℝ → ℝ≥0∞ := fun v => ENNReal.ofReal (Real.exp (-(p * v)) * G v) with hgdef
  have hgm : Measurable g := by rw [hgdef]; fun_prop
  have hIio : (∫⁻ v in Iio (0 : ℝ), ENNReal.ofReal (Real.exp (p * v) * G v))
      = ∫⁻ v in Ioi (0 : ℝ), g v := by
    have hkey := hmp.setLIntegral_comp_preimage_emb hemb g (Ioi (0 : ℝ))
    rw [hpre] at hkey
    rw [← hkey]
    refine setLIntegral_congr_fun measurableSet_Iio fun v _ => ?_
    rw [hgdef]
    simp only
    rw [hGeven v, show -(p * -v) = p * v by ring]
  have hsplit := lintegral_add_compl (μ := (volume : Measure ℝ))
    (fun v => ENNReal.ofReal (Real.exp (p * v) * G v)) (measurableSet_Iio (a := (0 : ℝ)))
  rw [compl_Iio] at hsplit
  have hIci : (∫⁻ v in Ici (0 : ℝ), ENNReal.ofReal (Real.exp (p * v) * G v))
      = ∫⁻ v in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (p * v) * G v) :=
    setLIntegral_congr Ioi_ae_eq_Ici.symm
  rw [hIio, hIci] at hsplit
  rw [← hsplit, ← lintegral_add_left' (hgm.aemeasurable.restrict)]
  have hpt : ∀ v : ℝ, g v + ENNReal.ofReal (Real.exp (p * v) * G v)
      = 2 * ENNReal.ofReal (Real.cosh (p * v) * G v) := by
    intro v
    rw [hgdef]
    simp only
    rw [← ENNReal.ofReal_add (mul_nonneg (Real.exp_pos _).le (hGnn v))
        (mul_nonneg (Real.exp_pos _).le (hGnn v)),
      show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
      ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    rw [Real.cosh_eq]
    ring
  simp only [hpt]
  rw [lintegral_const_mul' _ _ (by norm_num)]

/-- **The even-part folding of an exponentially weighted integral**, the `p = -1/2` instance of
`lintegral_exp_mul_of_even` in the coordinates the first-passage transform uses. -/
theorem lintegral_exp_neg_half_of_even {G : ℝ → ℝ} (hGm : Measurable G)
    (hGnn : ∀ v, 0 ≤ G v) (hGeven : ∀ v, G (-v) = G v) :
    (∫⁻ v, ENNReal.ofReal (Real.exp (-(v / 2)) * G v))
      = 2 * ∫⁻ v in Ioi (0 : ℝ), ENNReal.ofReal (Real.cosh (v / 2) * G v) := by
  have hp : ∀ v : ℝ, -(1 / 2 : ℝ) * v = -(v / 2) := fun v => by ring
  simpa only [hp, Real.cosh_neg] using
    lintegral_exp_mul_of_even (p := -(1 / 2 : ℝ)) hGm hGnn hGeven


theorem exp_rpow (v y : ℝ) : (Real.exp v) ^ y = Real.exp (v * y) := by
  rw [Real.rpow_def_of_pos (Real.exp_pos v), Real.log_exp]

/-- `K_{1/2}` in `ℝ≥0∞` form. The value is strictly positive, which is what forces the
`ℝ≥0∞` integral to be finite and lets it be read off from the Bochner one. -/
theorem lintegral_besselK_half {z : ℝ} (hz : 0 < z) :
    (∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (Real.cosh (u / 2) * Real.exp (-(z * Real.cosh u))))
      = ENNReal.ofReal (Real.sqrt (Real.pi / (2 * z)) * Real.exp (-z)) := by
  have hval := besselK_half hz
  have hpos : (0 : ℝ) < Real.sqrt (Real.pi / (2 * z)) * Real.exp (-z) := by
    have : (0 : ℝ) < Real.pi / (2 * z) := by positivity
    have := Real.sqrt_pos.mpr this
    positivity
  have hcongr : (∫ u in Ioi (0 : ℝ), Real.exp (-(z * Real.cosh u)) * Real.cosh (1 / 2 * u))
      = ∫ u in Ioi (0 : ℝ), Real.cosh (u / 2) * Real.exp (-(z * Real.cosh u)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    rw [show (1 : ℝ) / 2 * u = u / 2 by ring]
    ring
  have hb : besselK (1 / 2) z
      = (∫⁻ u in Ioi (0 : ℝ),
          ENNReal.ofReal (Real.cosh (u / 2) * Real.exp (-(z * Real.cosh u)))).toReal := by
    rw [besselK, hcongr]
    refine integral_eq_lintegral_of_nonneg_ae ?_ (by fun_prop)
    exact .of_forall fun u => by positivity
  set X := ∫⁻ u in Ioi (0 : ℝ),
    ENNReal.ofReal (Real.cosh (u / 2) * Real.exp (-(z * Real.cosh u))) with hX
  have hXne : X ≠ ⊤ := by
    intro h
    rw [h, ENNReal.toReal_top] at hb
    rw [hval] at hb
    linarith
  rw [← ENNReal.ofReal_toReal hXne, ← hb, hval]


/-- **The first-passage Laplace transform**, as the integral it is:
`∫₀^∞ u^{-3/2} e^{-A/u - Bu} du = √(π/A) e^{-2√(AB)}` for `A, B > 0`. -/
theorem lintegral_Ioi_firstPassage {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    (∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (u ^ (-(3 : ℝ) / 2) * Real.exp (-(A / u + B * u))))
      = ENNReal.ofReal (Real.sqrt (Real.pi / A) * Real.exp (-(2 * Real.sqrt (A * B)))) := by
  have hsA : (0 : ℝ) < Real.sqrt A := Real.sqrt_pos.mpr hA
  have hsB : (0 : ℝ) < Real.sqrt B := Real.sqrt_pos.mpr hB
  set c : ℝ := Real.sqrt A / Real.sqrt B with hcdef
  set s : ℝ := Real.sqrt A * Real.sqrt B with hsdef
  have hc : (0 : ℝ) < c := by rw [hcdef]; positivity
  have hs : (0 : ℝ) < s := by rw [hsdef]; positivity
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
  -- the pointwise identity after the substitution
  have hpt : ∀ v : ℝ, ENNReal.ofReal (c * Real.exp v)
        * ENNReal.ofReal ((c * Real.exp v) ^ (-(3 : ℝ) / 2)
            * Real.exp (-(A / (c * Real.exp v) + B * (c * Real.exp v))))
      = ENNReal.ofReal (Real.exp (-(v / 2))
          * (c ^ (-(1 : ℝ) / 2) * Real.exp (-(2 * s * Real.cosh v)))) := by
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
    have hcpow : c * (c ^ (-(3 : ℝ) / 2)) = c ^ (-(1 : ℝ) / 2) := by
      rw [show (-(1 : ℝ) / 2) = 1 + (-(3 : ℝ) / 2) by norm_num, Real.rpow_add hc,
        Real.rpow_one]
    calc c * Real.exp v * (c ^ (-(3 : ℝ) / 2) * Real.exp (v * (-(3 : ℝ) / 2))
            * Real.exp (-(2 * s * Real.cosh v)))
        = (c * c ^ (-(3 : ℝ) / 2)) * (Real.exp v * Real.exp (v * (-(3 : ℝ) / 2)))
            * Real.exp (-(2 * s * Real.cosh v)) := by ring
      _ = c ^ (-(1 : ℝ) / 2) * Real.exp (-(v / 2)) * Real.exp (-(2 * s * Real.cosh v)) := by
          rw [hcpow, ← Real.exp_add]
          congr 2
          ring
      _ = Real.exp (-(v / 2)) * (c ^ (-(1 : ℝ) / 2) * Real.exp (-(2 * s * Real.cosh v))) := by
          ring
  rw [lintegral_Ioi_comp_exp hc, funext hpt]
  have hcp : (0 : ℝ) < c ^ (-(1 : ℝ) / 2) := Real.rpow_pos_of_pos hc _
  rw [lintegral_exp_neg_half_of_even (G := fun v => c ^ (-(1 : ℝ) / 2)
      * Real.exp (-(2 * s * Real.cosh v))) (by fun_prop)
    (fun v => by positivity) (fun v => by rw [Real.cosh_neg])]
  have hconst : ∀ v : ℝ, ENNReal.ofReal (Real.cosh (v / 2)
        * (c ^ (-(1 : ℝ) / 2) * Real.exp (-(2 * s * Real.cosh v))))
      = ENNReal.ofReal (c ^ (-(1 : ℝ) / 2))
        * ENNReal.ofReal (Real.cosh (v / 2) * Real.exp (-(2 * s * Real.cosh v))) := by
    intro v
    rw [← ENNReal.ofReal_mul hcp.le]
    congr 1
    ring
  simp only [hconst]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_besselK_half (by positivity : (0 : ℝ) < 2 * s),
    ← ENNReal.ofReal_mul hcp.le, ← ENNReal.ofReal_ofNat 2,
    ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  have hcs : c * s = A := by
    rw [hcdef, hsdef,
      show Real.sqrt A / Real.sqrt B * (Real.sqrt A * Real.sqrt B)
        = (Real.sqrt A * Real.sqrt A) * (Real.sqrt B / Real.sqrt B) by ring,
      div_self hsB.ne', mul_one, Real.mul_self_sqrt hA.le]
  have hcinv : c ^ (-(1 : ℝ) / 2) = (Real.sqrt c)⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg_one, ← Real.rpow_mul hc.le]
    norm_num
  have h4s : Real.sqrt (2 * (2 * s)) = 2 * Real.sqrt s := by
    rw [show 2 * (2 * s) = 4 * s by ring, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4),
      show Real.sqrt 4 = 2 by
        rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  have hsq : Real.sqrt c * Real.sqrt s = Real.sqrt A := by
    rw [← Real.sqrt_mul hc.le, hcs]
  have hAB : Real.sqrt (A * B) = s := by rw [hsdef, Real.sqrt_mul hA.le]
  have hsc : (0 : ℝ) < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hss : (0 : ℝ) < Real.sqrt s := Real.sqrt_pos.mpr hs
  rw [hcinv, hAB, Real.sqrt_div Real.pi_pos.le, Real.sqrt_div Real.pi_pos.le, h4s]
  field_simp
  rw [← hsq]


end SpatialLine
