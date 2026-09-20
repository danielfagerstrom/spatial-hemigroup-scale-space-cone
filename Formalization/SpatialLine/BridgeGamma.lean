/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.Moments
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

import SpatialLine.FirstPassage
import SpatialLine.BridgeExponents
import SpatialLine.MaternCorner

/-!
# The Gamma corner of the subordination bridge

Blueprint: `prop:bridge-families`(2) --- the causal Gamma family maps to the Matern family at
range `1/\sqrt 2`, at the exponent, at the range and at the profile.

## What proving this found

**The exponent clause is a corollary of the profile clause, and needs no second integral.** The
skeleton priced this node as two classical integrals: the first-passage Laplace transform for
the profile, and the *exponential Frullani* `\int_0^\infty(1 - e^{-\sigma u})e^{-u}du/u =
\log(1+\sigma)` for the exponent, `M` on its own. The second is not needed. Wave 4's
`CausalAdmissible.bridgeDatum_exponent` already says that `F_I(\omega^2/2)` is the exponent of
the `SDProfile` whose folded profile is `eq:bridge-profile`; once the profile clause identifies
that profile with `maternProfile \gamma (1/\sqrt 2)`, `lintegral_maternProfile` --- the spatial
Frullani, wave 2's --- evaluates the exponent. So the causal Frullani integral is an upper bound
on what the statement needs, and the two chapters' machinery meets in the middle.

**The profile clause is one substitution once the first-passage identity is in hand.** With
`k_I(u) = \gamma e^{-u}` the integrand of `eq:bridge-profile` is
`\gamma(2\pi)^{-1/2}u^{-3/2}e^{-(x^2/2)/u - u}`, and `SpatialLine/FirstPassage.lean` evaluates
it. The rest is `\sqrt{\pi/(x^2/2)} = \sqrt{2\pi}/x` and `2\sqrt{x^2/2} = \sqrt 2 x`.
-/

namespace SpatialLine

open MeasureTheory Set Filter
open scoped ENNReal Topology

theorem rpow_neg_three_half {u : ℝ} (hu : 0 < u) :
    u ^ (-(3 : ℝ) / 2) = (Real.sqrt u * u)⁻¹ := by
  rw [show -(3 : ℝ) / 2 = -(3 / 2) by ring, Real.rpow_neg hu.le,
    show (3 : ℝ) / 2 = 1 / 2 + 1 by norm_num, Real.rpow_add hu, Real.rpow_one,
    ← Real.sqrt_eq_rpow]

/-- The Bochner form of the first-passage identity. -/
theorem integral_Ioi_firstPassage {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    (∫ u in Ioi (0 : ℝ), u ^ (-(3 : ℝ) / 2) * Real.exp (-(A / u + B * u)))
      = Real.sqrt (Real.pi / A) * Real.exp (-(2 * Real.sqrt (A * B))) := by
  rw [integral_eq_lintegral_of_nonneg_ae
      ((ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun u hu => by
        have hu0 : (0 : ℝ) < u := hu; positivity))
      (by fun_prop),
    lintegral_Ioi_firstPassage hA hB, ENNReal.toReal_ofReal (by positivity)]

/-- **The Gamma corner's folded profile.** With `k_I(u) = γe^{-u}`, `eq:bridge-profile` is the
Matérn profile of shape `γ` at range `1/√2`. -/
theorem bridgeProfile_of_exp {γ : ℝ} (hγ : 0 < γ) (F : CausalAdmissible)
    (hk : ∀ u : ℝ, 0 < u → F.k u = γ * Real.exp (-u)) {x : ℝ} (hx : 0 < x) :
    F.bridgeProfile x = maternProfile γ (Real.sqrt 2)⁻¹ x := by
  have hA : (0 : ℝ) < x ^ 2 / 2 := by positivity
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hstep : (∫ u in Ioi (0 : ℝ), brownianDensity u x * F.k u / u)
      = γ * (Real.sqrt (2 * Real.pi))⁻¹
        * ∫ u in Ioi (0 : ℝ), u ^ (-(3 : ℝ) / 2) * Real.exp (-(x ^ 2 / 2 / u + 1 * u)) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    have hu0 : (0 : ℝ) < u := hu
    have hsu : (0 : ℝ) < Real.sqrt u := Real.sqrt_pos.mpr hu0
    rw [brownianDensity_eq hu0, hk u hu0, rpow_neg_three_half hu0,
      show 2 * Real.pi * u = (2 * Real.pi) * u by ring,
      Real.sqrt_mul h2pi.le,
      show -(x ^ 2 / 2 / u + 1 * u) = -x ^ 2 / (2 * u) + -u by field_simp; ring,
      Real.exp_add]
    have hsp : (0 : ℝ) < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr h2pi
    field_simp
  rw [ScaleSpace.CausalAdmissible.bridgeProfile, hstep, integral_Ioi_firstPassage hA one_pos]
  have hsA : Real.sqrt (Real.pi / (x ^ 2 / 2)) = Real.sqrt (2 * Real.pi) / x := by
    rw [show Real.pi / (x ^ 2 / 2) = (2 * Real.pi) / x ^ 2 by field_simp,
      Real.sqrt_div h2pi.le, Real.sqrt_sq hx.le]
  have hmm : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hsB : 2 * Real.sqrt (x ^ 2 / 2 * 1) = Real.sqrt 2 * x := by
    have hval : Real.sqrt (x ^ 2 / 2 * 1) = x / Real.sqrt 2 := by
      rw [mul_one, show x ^ 2 / 2 = (x / Real.sqrt 2) ^ 2 by
        rw [div_pow, show (Real.sqrt 2) ^ 2 = 2 from by rw [sq, hmm]]]
      exact Real.sqrt_sq (by positivity)
    rw [hval, mul_div_assoc', eq_comm, eq_div_iff hs2.ne']
    nlinarith [hmm]
  rw [hsA, hsB, maternProfile_eq_exp (by positivity) hx]
  have hsp : (0 : ℝ) < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr h2pi
  rw [show (Real.sqrt 2)⁻¹⁻¹ = Real.sqrt 2 by rw [inv_inv]]
  field_simp


theorem bridge_families_gamma (γ : ℝ) (hγ : 0 < γ) (F : CausalAdmissible)
    (hk : ∀ u : ℝ, 0 < u → F.k u = γ * Real.exp (-u)) (hb : F.b₀ = 0) :
    (∀ ω : ℝ, F.exponent (ω ^ 2 / 2) = maternExponent γ (Real.sqrt 2)⁻¹ ω) ∧
      ∀ x : ℝ, 0 < x →
        2 * x * (∫ u in Ioi (0 : ℝ), brownianDensity u x * F.k u / u)
          = maternProfile γ (Real.sqrt 2)⁻¹ x := by
  have hθ : (0 : ℝ) < (Real.sqrt 2)⁻¹ := by positivity
  have heq : Set.EqOn F.bridgeProfile (maternProfile γ (Real.sqrt 2)⁻¹) (Ioi (0 : ℝ)) :=
    fun x hx => bridgeProfile_of_exp hγ F hk hx
  refine ⟨fun ω => ?_, fun x hx => bridgeProfile_of_exp hγ F hk hx⟩
  have hnn : 0 ≤ maternExponent γ (Real.sqrt 2)⁻¹ ω := by
    have hlog : 0 ≤ Real.log (1 + ((Real.sqrt 2)⁻¹) ^ 2 * ω ^ 2) :=
      Real.log_nonneg (by nlinarith [sq_nonneg ((Real.sqrt 2)⁻¹ * ω)])
    rw [maternExponent]
    positivity
  rw [← F.bridgeDatum_exponent ω, SDProfile.exponent, SDProfile.exponentL,
    ScaleSpace.CausalAdmissible.bridgeDatum_a, ScaleSpace.CausalAdmissible.bridgeDatum_k, hb,
    lintegral_maternProfile hγ hθ heq ω]
  simp [ENNReal.toReal_ofReal hnn]


end SpatialLine
