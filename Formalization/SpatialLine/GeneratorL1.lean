/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.Generator
import SpatialLine.GeneratorDomain

/-!
# The `L¹` estimates for the symmetric second difference

Blueprint: the Fubini step inside `prop:scale-evolution`'s multiplier clause
(`scale_evolution_multiplier`), and nothing else. Nothing here is a node.

## Why an `L¹` estimate and not the pointwise one

The multiplier identity exchanges the `ϖ`-integral of the generator with the `x`-integral of the
transform, and Fubini for that exchange needs the second difference to be jointly integrable in
`x` and `v`. The library's `abs_secondDifference_le` is the wrong estimate for it: it is
`x`-uniform, `|Δ_v g(x)| ≤ ‖g''‖_∞v²`, and a uniform bound is not integrable over the line.
`scale_evolution_absconv` is absolute convergence of the `ϖ`-integral at a *fixed* `x` and does
not help either.

What does work is the same quadratic bound taken in `L¹` rather than in `L^∞`, and the route is
the factorisation `Δ_v = ½(T_v - I)(I - T_{-v})`: each factor costs one translation estimate

  `‖T_hg - g‖₁ ≤ |h|·‖g'‖₁`,                                                         (★)

and the two together give `‖Δ_vf‖₁ ≤ ½v²‖f''‖₁`, which is `ϖ`-integrable against
`∫(1 ∧ v²)ϖ < ∞` exactly as the pointwise bound is. (★) is the piece Mathlib does not carry in
this form; it is the fundamental theorem of calculus in the *shift* variable — writing
`g(x - h) - g(x) = -∫₀^h g'(x - s)\,ds` keeps the domain of integration independent of `x` — and
then one Tonelli turn and the translation invariance of Lebesgue measure. Everything is stated
in `ℝ≥0∞`, so no integrability side condition is carried anywhere; the constants are deliberately
generous, since only the shape `C·(1 ∧ v²)` is consumed.
-/

namespace SpatialLine

open MeasureTheory Set
open scoped ENNReal

/-- The length of the interval of shifts between `0` and `h`. -/
theorem volume_uIoc_zero (h : ℝ) : volume (uIoc (0 : ℝ) h) = ENNReal.ofReal |h| := by
  rw [Set.uIoc, Real.volume_Ioc]
  rcases le_total 0 h with hh | hh
  · rw [min_eq_left hh, max_eq_right hh, abs_of_nonneg hh, sub_zero]
  · rw [min_eq_right hh, max_eq_left hh, abs_of_nonpos hh, zero_sub]

/-- **The fundamental theorem of calculus in the shift variable.** The increment of a `C¹`
function over a translation is the integral of its derivative over a *fixed* interval of shifts,
which is what makes the Tonelli turn below available. -/
theorem sub_translate_eq_intervalIntegral {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) (h x : ℝ) :
    g (x - h) - g x = -∫ s in (0 : ℝ)..h, deriv g (x - s) := by
  have hd : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hc : Continuous (deriv g) := (contDiff_one_iff_deriv.mp hg).2
  have hderiv : ∀ s ∈ uIcc (0 : ℝ) h,
      HasDerivAt (fun r : ℝ => -g (x - r)) (deriv g (x - s)) s := by
    intro s _
    have h1 : HasDerivAt (fun r : ℝ => g (x - r)) (-deriv g (x - s)) s :=
      HasDerivAt.comp_const_sub x s ((hd (x - s)).hasDerivAt)
    exact h1.neg.congr_deriv (by ring)
  have hint : IntervalIntegrable (fun s => deriv g (x - s)) volume 0 h :=
    (hc.comp (continuous_const.sub continuous_id)).intervalIntegrable 0 h
  have hres := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [hres]
  simp
  ring

/-- **(★), the `L¹` translation estimate**: `‖T_hg - g‖₁ ≤ |h|·‖g'‖₁`, in `ℝ≥0∞` and with no
integrability hypothesis on either side.

The proof is the fundamental theorem of calculus in the shift variable, `‖∫‖ ≤ ∫‖·‖`, one
Tonelli turn and the translation invariance of Lebesgue measure. -/
theorem lintegral_enorm_translate_sub_le {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) (h : ℝ) :
    ∫⁻ x, ‖g (x - h) - g x‖ₑ ≤ ENNReal.ofReal |h| * ∫⁻ x, ‖deriv g x‖ₑ := by
  have hc : Continuous (deriv g) := (contDiff_one_iff_deriv.mp hg).2
  have hpt : ∀ x : ℝ, ‖g (x - h) - g x‖ₑ ≤ ∫⁻ s in uIoc (0 : ℝ) h, ‖deriv g (x - s)‖ₑ := by
    intro x
    rw [sub_translate_eq_intervalIntegral hg h x, enorm_neg,
      intervalIntegral.intervalIntegral_eq_integral_uIoc]
    rcases le_total (0 : ℝ) h with hh | hh
    · rw [if_pos hh, one_smul]
      exact enorm_integral_le_lintegral_enorm _
    · rcases eq_or_lt_of_le hh with rfl | hlt
      · simp
      · rw [if_neg (by linarith), neg_smul, one_smul, enorm_neg]
        exact enorm_integral_le_lintegral_enorm _
  have hmeas : AEMeasurable (Function.uncurry fun x s : ℝ => ‖deriv g (x - s)‖ₑ)
      (volume.prod (volume.restrict (uIoc (0 : ℝ) h))) :=
    Measurable.aemeasurable ((hc.comp (continuous_fst.sub continuous_snd)).enorm).measurable
  calc ∫⁻ x, ‖g (x - h) - g x‖ₑ
      ≤ ∫⁻ x, ∫⁻ s in uIoc (0 : ℝ) h, ‖deriv g (x - s)‖ₑ := lintegral_mono hpt
    _ = ∫⁻ s in uIoc (0 : ℝ) h, ∫⁻ x, ‖deriv g (x - s)‖ₑ := lintegral_lintegral_swap hmeas
    _ = ∫⁻ _ in uIoc (0 : ℝ) h, ∫⁻ x, ‖deriv g x‖ₑ :=
        lintegral_congr fun s => lintegral_sub_right_eq_self (fun x => ‖deriv g x‖ₑ) s
    _ = ENNReal.ofReal |h| * ∫⁻ x, ‖deriv g x‖ₑ := by
        rw [setLIntegral_const, volume_uIoc_zero, mul_comm]

theorem contDiff_one_of_two {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) : ContDiff ℝ 1 g :=
  hg.of_le (by norm_num)

theorem contDiff_deriv_of_two {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) : ContDiff ℝ 1 (deriv g) :=
  ((contDiff_succ_iff_deriv (n := 1) (f := g)).mp (by exact_mod_cast hg)).2.2

/-- **The `L¹` bound on the symmetric second difference**, quadratic in the displacement:
`‖Δ_vg‖₁ ≤ v²‖g''‖₁`.

The factorisation `Δ_v = ½(T_v - I)(I - T_{-v})` is carried out on the function
`G = g - T_{-v}g`, whose own translation increment is twice the second difference and whose
derivative is the corresponding increment of `g'`; each factor spends one application of (★).
The constant `1` in place of the sharp `½` is deliberate: only the shape `C·v²` is consumed. -/
theorem lintegral_enorm_secondDifference_le {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (v : ℝ) :
    ∫⁻ x, ‖g x - (g (x - v) + g (x + v)) / 2‖ₑ
      ≤ ENNReal.ofReal (v ^ 2) * ∫⁻ x, ‖iteratedDeriv 2 g x‖ₑ := by
  have hg1 : ContDiff ℝ 1 g := contDiff_one_of_two hg
  have hd1 : Differentiable ℝ g := hg1.differentiable (by norm_num)
  have hg' : ContDiff ℝ 1 (deriv g) := contDiff_deriv_of_two hg
  have hdd : ∀ y, iteratedDeriv 2 g y = deriv (deriv g) y := fun y => by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  set G : ℝ → ℝ := fun x => g x - g (x + v) with hG
  have hGc : ContDiff ℝ 1 G := hg1.sub (hg1.comp (contDiff_id.add contDiff_const))
  have hGd : ∀ x, deriv G x = deriv g x - deriv g (x + v) := by
    intro x
    have h1 : HasDerivAt (fun y : ℝ => g (y + v)) (deriv g (x + v)) x :=
      HasDerivAt.comp_add_const x v ((hd1 (x + v)).hasDerivAt)
    exact ((hd1 x).hasDerivAt.sub h1).deriv
  have hstep : ∀ x : ℝ, ‖G (x - v) - G x‖ₑ = 2 * ‖g x - (g (x - v) + g (x + v)) / 2‖ₑ := by
    intro x
    have he : G (x - v) - G x = -(2 * (g x - (g (x - v) + g (x + v)) / 2)) := by
      simp only [hG]
      ring_nf
    rw [he, enorm_neg, enorm_mul, Real.enorm_eq_ofReal (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hbase := lintegral_enorm_translate_sub_le hGc v
  rw [lintegral_congr hstep, lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)] at hbase
  have hderiv : ∫⁻ x, ‖deriv G x‖ₑ ≤ ENNReal.ofReal |v| * ∫⁻ x, ‖iteratedDeriv 2 g x‖ₑ := by
    have h := lintegral_enorm_translate_sub_le hg' (-v)
    have he : ∀ x : ℝ, ‖deriv g (x - -v) - deriv g x‖ₑ = ‖deriv G x‖ₑ := by
      intro x
      rw [hGd x, sub_neg_eq_add,
        show deriv g (x + v) - deriv g x = -(deriv g x - deriv g (x + v)) by ring, enorm_neg]
    rw [lintegral_congr he, abs_neg] at h
    refine h.trans (le_of_eq ?_)
    congr 1
    exact (lintegral_congr fun x => by rw [hdd x]).symm
  have hchain : (2 : ℝ≥0∞) * ∫⁻ x, ‖g x - (g (x - v) + g (x + v)) / 2‖ₑ
      ≤ ENNReal.ofReal |v| * (ENNReal.ofReal |v| * ∫⁻ x, ‖iteratedDeriv 2 g x‖ₑ) :=
    hbase.trans (by gcongr)
  have hfinal : ENNReal.ofReal |v| * (ENNReal.ofReal |v| * ∫⁻ x, ‖iteratedDeriv 2 g x‖ₑ)
      = ENNReal.ofReal (v ^ 2) * ∫⁻ x, ‖iteratedDeriv 2 g x‖ₑ := by
    rw [← mul_assoc, ← ENNReal.ofReal_mul (abs_nonneg v)]
    congr 2
    rw [abs_mul_abs_self]
    ring
  rw [hfinal] at hchain
  exact le_trans (le_mul_of_one_le_left' (by norm_num)) hchain

/-- **The crude `L¹` bound**, for displacements the Choquet measure sees as large: the second
difference is bounded by three copies of the function itself. -/
theorem lintegral_enorm_secondDifference_le_three {g : ℝ → ℝ} (hg : Continuous g) (v : ℝ) :
    ∫⁻ x, ‖g x - (g (x - v) + g (x + v)) / 2‖ₑ ≤ 3 * ∫⁻ x, ‖g x‖ₑ := by
  have hpt : ∀ x : ℝ, ‖g x - (g (x - v) + g (x + v)) / 2‖ₑ
      ≤ ‖g x‖ₑ + ‖g (x - v)‖ₑ + ‖g (x + v)‖ₑ := by
    intro x
    rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs,
      Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _),
      ← ENNReal.ofReal_add (by positivity) (abs_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : |g x - (g (x - v) + g (x + v)) / 2| ≤ |g x| + |(g (x - v) + g (x + v)) / 2| :=
      abs_sub _ _
    have h2 : |(g (x - v) + g (x + v)) / 2| ≤ (|g (x - v)| + |g (x + v)|) / 2 := by
      rw [abs_div, abs_two]
      have := abs_add_le (g (x - v)) (g (x + v))
      linarith
    have := abs_nonneg (g (x - v))
    have := abs_nonneg (g (x + v))
    linarith
  have hm : Measurable fun x : ℝ => ‖g x‖ₑ := hg.enorm.measurable
  calc ∫⁻ x, ‖g x - (g (x - v) + g (x + v)) / 2‖ₑ
      ≤ ∫⁻ x, (‖g x‖ₑ + ‖g (x - v)‖ₑ + ‖g (x + v)‖ₑ) := lintegral_mono hpt
    _ = (∫⁻ x, ‖g x‖ₑ) + (∫⁻ x, ‖g (x - v)‖ₑ) + ∫⁻ x, ‖g (x + v)‖ₑ := by
        rw [lintegral_add_left (by fun_prop), lintegral_add_left (by fun_prop)]
    _ = 3 * ∫⁻ x, ‖g x‖ₑ := by
        rw [lintegral_sub_right_eq_self (fun x => ‖g x‖ₑ) v,
          lintegral_add_right_eq_self (fun x => ‖g x‖ₑ) v]
        ring

/-- The two `L¹` regimes of the second difference, collected against the Lévy truncation. -/
theorem lintegral_enorm_secondDifference_le_min {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) {M : ℝ≥0∞}
    (hM1 : (∫⁻ x, ‖g x‖ₑ) ≤ M) (hM2 : (∫⁻ x, ‖iteratedDeriv 2 g x‖ₑ) ≤ M) (v : ℝ) :
    ∫⁻ x, ‖g x - (g (x - v) + g (x + v)) / 2‖ₑ ≤ 3 * M * ENNReal.ofReal (min 1 (v ^ 2)) := by
  rcases le_total (v ^ 2) 1 with hv | hv
  · rw [min_eq_right hv]
    refine (lintegral_enorm_secondDifference_le hg v).trans ?_
    calc ENNReal.ofReal (v ^ 2) * ∫⁻ x, ‖iteratedDeriv 2 g x‖ₑ
        ≤ ENNReal.ofReal (v ^ 2) * M := by gcongr
      _ ≤ 3 * M * ENNReal.ofReal (v ^ 2) := by
          rw [mul_comm]
          gcongr
          exact le_mul_of_one_le_left' (by norm_num)
  · rw [min_eq_left hv, ENNReal.ofReal_one, mul_one]
    refine (lintegral_enorm_secondDifference_le_three
      ((contDiff_one_of_two hg).continuous) v).trans ?_
    gcongr

end SpatialLine
