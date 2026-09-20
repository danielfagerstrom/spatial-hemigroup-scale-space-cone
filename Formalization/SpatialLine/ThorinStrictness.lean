/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.ThorinBridge
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Strictness the other way: the image of the `Cin` ray is not Thorin

Blueprint: `prop:thorin-subclass`(5) — the subordinated slice `S` of `prop:bridge-strictness` is
strictly larger than the symmetric Thorin subclass, because the image of the causal ray with
profile `1_{(0,τ)}` has the explicit folded profile `2 erfc(x/√(2τ))`, which is not completely
monotone.

## What proving this found

**`erfc` needs four elementary facts and this file proves all four**, Mathlib having no `erfc`:
that `e^{-v²}` is integrable, that `erfc` is continuous (needed for the a.e.-to-pointwise
passage, exactly as in `ThorinBridge.lean`), that it is strictly positive, and the Gaussian upper
bound. The bound the estimate proposed — `∫_y^∞ e^{-v²}dv ≤ ∫_y^∞ ve^{-v²}dv = e^{-y²}/2` — is
*not* the cheapest one available here: it costs the integrability of `ve^{-v²}` on a half-line,
which Mathlib does not carry either. The comparison `e^{-v²} ≤ e^{-yv}` on `(y,∞)` costs nothing
beyond `exp_neg_integrableOn_Ioi`, which Mathlib does carry, and gives `erfc y ≤ 2e^{-y²}` for
`y ≥ 1` after one improper fundamental theorem of calculus. Both bounds are Gaussian and the node
only needs *some* Gaussian bound.

**The change of variables is antitone, and Mathlib has the antitone form.** The estimate proposed
`v = x²/2u`, which is decreasing, and `SpatialLine/FirstPassage.lean`'s exponential substitution
is stated for monotone maps only. There is no need to reverse the interval by hand:
`lintegral_image_eq_lintegral_deriv_mul_of_antitoneOn` is the same lemma for a decreasing map,
and `v ↦ A/v²` carries `(y,∞)` onto `(0, A/y²)` in one step.

**The non-complete-monotonicity half is a bound, not an asymptotic.** The printed proof compares
`erfc(x/√(2τ)) ∼ √(2τ/π)x^{-1}e^{-x²/2τ}` against the exponential floor of a completely monotone
function. No asymptotic is needed: what the contradiction consumes is one *upper* bound of
Gaussian type at one sufficiently large `x`, chosen explicitly, and the floor `c e^{-nx}` comes
from a single window `U(-∞, n]` of positive mass rather than from Bernstein's measure as a whole.
-/

namespace SpatialLine

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-! ## The complementary error function -/

/-- `e^{-v²}` is integrable on the line. -/
theorem integrable_expNegSq : Integrable fun v : ℝ => Real.exp (-v ^ 2) := by
  simpa using integrable_exp_neg_mul_sq (b := 1) one_pos

/-- **`erfc` is continuous.** Written as `erfc 0`'s integral minus a primitive of an integrable
function, which is `Integrable.continuous_primitive`. -/
theorem continuous_erfc : Continuous erfc := by
  have hI : Integrable fun v : ℝ => Real.exp (-v ^ 2) := integrable_expNegSq
  have hrw : ∀ y : ℝ, (∫ v in Ioi y, Real.exp (-v ^ 2))
      = (∫ v in Ici (0 : ℝ), Real.exp (-v ^ 2)) - ∫ v in (0 : ℝ)..y, Real.exp (-v ^ 2) := by
    intro y
    rw [← integral_Ici_eq_integral_Ioi,
      ← intervalIntegral.integral_Ici_sub_Ici' hI.integrableOn hI.integrableOn]
    ring
  unfold erfc
  refine Continuous.mul continuous_const ?_
  simp only [hrw]
  exact continuous_const.sub (hI.continuous_primitive 0)

/-- **`erfc` is strictly positive.** -/
theorem erfc_pos (y : ℝ) : 0 < erfc y := by
  have hI : IntegrableOn (fun v : ℝ => Real.exp (-v ^ 2)) (Ioi y) :=
    integrable_expNegSq.integrableOn
  have hpos : 0 < ∫ v in Ioi y, Real.exp (-v ^ 2) := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae
      (.of_forall fun v => (Real.exp_pos _).le) hI]
    have hsupp : (Function.support fun v : ℝ => Real.exp (-v ^ 2)) = univ := by
      ext v; simp [Function.mem_support, Real.exp_ne_zero]
    rw [hsupp, univ_inter, Real.volume_Ioi]
    simp
  unfold erfc
  have : (0 : ℝ) < 2 / Real.sqrt Real.pi := by positivity
  positivity

theorem erfc_nonneg (y : ℝ) : 0 ≤ erfc y := (erfc_pos y).le

theorem integrableOn_exp_neg_mul_Ioi {y : ℝ} (hy : 0 < y) (a : ℝ) :
    IntegrableOn (fun v : ℝ => Real.exp (-(y * v))) (Ioi a) := by
  refine (exp_neg_integrableOn_Ioi a hy).congr_fun (fun v _ => ?_) measurableSet_Ioi
  simp only [neg_mul]

/-- `∫_y^∞ e^{-yv}dv = e^{-y²}/y`, the comparison integral for the Gaussian bound. -/
theorem integral_Ioi_exp_neg_mul_const {y : ℝ} (hy : 0 < y) :
    (∫ v in Ioi y, Real.exp (-(y * v))) = Real.exp (-(y ^ 2)) / y := by
  have hfun : (fun w : ℝ => -(y * w)) = fun w : ℝ => (-y) * w := by funext w; ring
  have hderiv : ∀ v ∈ Ioi y,
      HasDerivAt (fun w : ℝ => -Real.exp (-(y * w)) / y) (Real.exp (-(y * v))) v := by
    intro v _
    have h1 : HasDerivAt (fun w : ℝ => -(y * w)) (-y) v := by
      rw [hfun]; simpa using (hasDerivAt_id v).const_mul (-y)
    have h2 : HasDerivAt (fun w : ℝ => -Real.exp (-(y * w)) / y)
        (-(Real.exp (-(y * v)) * -y) / y) v := (h1.exp.neg).div_const y
    have hval : Real.exp (-(y * v)) = -(Real.exp (-(y * v)) * -y) / y := by field_simp
    rw [hval]
    exact h2
  have hb : Tendsto (fun w : ℝ => -(y * w)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp (Filter.Tendsto.const_mul_atTop hy tendsto_id)
  have hlim : Tendsto (fun w : ℝ => -Real.exp (-(y * w)) / y) atTop (𝓝 0) := by
    have h0 : Tendsto (fun w : ℝ => Real.exp (-(y * w))) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp hb
    simpa using h0.neg.div_const y
  have hcont : ContinuousWithinAt (fun w : ℝ => -Real.exp (-(y * w)) / y) (Ici y) y := by
    fun_prop
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv (integrableOn_exp_neg_mul_Ioi hy y) hlim,
    show -(y * y) = -(y ^ 2) by ring]
  ring

/-- **A Gaussian upper bound on `erfc`.** For `y ≥ 1`, `erfc y ≤ 2e^{-y²}`.

The comparison is `e^{-v²} ≤ e^{-yv}` on `(y,∞)`, whose integral is `e^{-y²}/y ≤ e^{-y²}`; the
constant `2/√π ≤ 2` is discarded rather than tracked, the node needing only a bound of Gaussian
*type*. -/
theorem erfc_le_two_mul_exp {y : ℝ} (hy : 1 ≤ y) : erfc y ≤ 2 * Real.exp (-(y ^ 2)) := by
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le one_pos hy
  have hI1 : IntegrableOn (fun v : ℝ => Real.exp (-v ^ 2)) (Ioi y) :=
    integrable_expNegSq.integrableOn
  have hmono : (∫ v in Ioi y, Real.exp (-v ^ 2)) ≤ ∫ v in Ioi y, Real.exp (-(y * v)) := by
    refine setIntegral_mono_on hI1 (integrableOn_exp_neg_mul_Ioi hy0 y) measurableSet_Ioi
      fun v hv => ?_
    have hv0 : y < v := hv
    exact Real.exp_le_exp.mpr (by nlinarith)
  rw [integral_Ioi_exp_neg_mul_const hy0] at hmono
  have hspi : (1 : ℝ) < Real.sqrt Real.pi := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by linarith [Real.two_le_pi])
  have hle : Real.exp (-(y ^ 2)) / y ≤ Real.exp (-(y ^ 2)) := by
    rw [div_le_iff₀ hy0]
    nlinarith [Real.exp_pos (-(y ^ 2))]
  have hfac : 2 / Real.sqrt Real.pi ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hnn : 0 ≤ ∫ v in Ioi y, Real.exp (-v ^ 2) :=
    setIntegral_nonneg measurableSet_Ioi fun v _ => (Real.exp_pos _).le
  unfold erfc
  calc 2 / Real.sqrt Real.pi * ∫ v in Ioi y, Real.exp (-v ^ 2)
      ≤ 2 * ∫ v in Ioi y, Real.exp (-v ^ 2) := mul_le_mul_of_nonneg_right hfac hnn
    _ ≤ 2 * Real.exp (-(y ^ 2)) := mul_le_mul_of_nonneg_left (le_trans hmono hle) (by norm_num)

/-! ## The change of variables `u = A/v²` -/

theorem hasDerivAt_inv_sq {A v : ℝ} (hv : v ≠ 0) :
    HasDerivAt (fun w : ℝ => A * (w ^ 2)⁻¹) (-(2 * A / v ^ 3)) v := by
  have h1 : HasDerivAt (fun w : ℝ => w ^ 2) (2 * v) v := by
    simpa using hasDerivAt_pow 2 v
  have h2 : HasDerivAt (fun w : ℝ => A * (w ^ 2)⁻¹) (A * (-(2 * v) / (v ^ 2) ^ 2)) v :=
    (h1.inv (by positivity : v ^ 2 ≠ 0)).const_mul A
  have hval : -(2 * A / v ^ 3) = A * (-(2 * v) / (v ^ 2) ^ 2) := by
    field_simp
  rw [hval]
  exact h2

theorem antitoneOn_inv_sq {A y : ℝ} (hA : 0 < A) (hy : 0 < y) :
    AntitoneOn (fun v : ℝ => A * (v ^ 2)⁻¹) (Ioi y) := by
  intro a ha b hb hab
  have ha0 : (0 : ℝ) < a := lt_trans hy ha
  have hb0 : (0 : ℝ) < b := lt_trans hy hb
  have h1 : a ^ 2 ≤ b ^ 2 := by nlinarith
  have h2 : (b ^ 2)⁻¹ ≤ (a ^ 2)⁻¹ := by
    rw [inv_le_inv₀ (by positivity) (by positivity)]; exact h1
  exact mul_le_mul_of_nonneg_left h2 hA.le

theorem image_inv_sq {A y : ℝ} (hA : 0 < A) (hy : 0 < y) :
    (fun v : ℝ => A * (v ^ 2)⁻¹) '' Ioi y = Ioo (0 : ℝ) (A * (y ^ 2)⁻¹) := by
  have hyp : (0 : ℝ) < y ^ 2 := by positivity
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    have hv0 : y < v := hv
    have hvp : (0 : ℝ) < v := lt_trans hy hv0
    have hvsq : (0 : ℝ) < v ^ 2 := by positivity
    refine ⟨by positivity, ?_⟩
    show A * (v ^ 2)⁻¹ < A * (y ^ 2)⁻¹
    have h1 : y ^ 2 < v ^ 2 := by nlinarith
    have h2 : (v ^ 2)⁻¹ < (y ^ 2)⁻¹ := by
      rw [inv_lt_inv₀ hvsq hyp]; exact h1
    exact mul_lt_mul_of_pos_left h2 hA
  · rintro ⟨hw0, hwt⟩
    have hAw : y ^ 2 < A / w := by
      rw [lt_div_iff₀ hw0]
      have h : w * y ^ 2 < A * (y ^ 2)⁻¹ * y ^ 2 := by nlinarith
      calc y ^ 2 * w = w * y ^ 2 := by ring
        _ < A * (y ^ 2)⁻¹ * y ^ 2 := h
        _ = A := by field_simp
    refine ⟨Real.sqrt (A / w), ?_, ?_⟩
    · show y < Real.sqrt (A / w)
      exact (Real.lt_sqrt hy.le).mpr hAw
    · show A * (Real.sqrt (A / w) ^ 2)⁻¹ = w
      rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ A / w)]
      field_simp

/-- **The change of variables `u = A/v²`**, in `ℝ≥0∞`: it carries `(y,∞)` onto `(0, A/y²)` and
leaves the factor `2A/v³`. -/
theorem lintegral_Ioo_comp_inv_sq {A y : ℝ} (hA : 0 < A) (hy : 0 < y) (u : ℝ → ℝ≥0∞) :
    (∫⁻ w in Ioo (0 : ℝ) (A * (y ^ 2)⁻¹), u w)
      = ∫⁻ v in Ioi y, ENNReal.ofReal (2 * A / v ^ 3) * u (A * (v ^ 2)⁻¹) := by
  have h := lintegral_image_eq_lintegral_deriv_mul_of_antitoneOn (s := Ioi y)
    (f := fun v : ℝ => A * (v ^ 2)⁻¹) (f' := fun v : ℝ => -(2 * A / v ^ 3))
    measurableSet_Ioi
    (fun v hv => (hasDerivAt_inv_sq (A := A) (by
      have hvy : y < v := hv; linarith)).hasDerivWithinAt)
    (antitoneOn_inv_sq hA hy) u
  rw [image_inv_sq hA hy] at h
  rw [h]
  refine setLIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
  rw [neg_neg]

/-! ## The folded profile of the subordinated `Cin` ray -/

end SpatialLine

namespace ScaleSpace.CausalAdmissible

open SpatialLine
open MeasureTheory Set Filter
open scoped ENNReal Topology

/-- **The `Cin` corner's folded profile.** With `k_I = 1_{(0,τ)}`, `eq:bridge-profile` is
`2 erfc(x/√(2τ))`. -/
theorem bridgeProfile_of_cin {τ : ℝ} (hτ : 0 < τ) (F : CausalAdmissible)
    (hkF : F.k = cinProfile τ) {x : ℝ} (hx : 0 < x) :
    F.bridgeProfile x = 2 * erfc (x / Real.sqrt (2 * τ)) := by
  have hsp : (0 : ℝ) < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hmm : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs2τ : (0 : ℝ) < Real.sqrt (2 * τ) := Real.sqrt_pos.mpr (by positivity)
  set C : ℝ := x * (Real.sqrt (2 * Real.pi))⁻¹ with hCdef
  have hC : 0 < C := by rw [hCdef]; positivity
  set y : ℝ := x / Real.sqrt (2 * τ) with hydef
  have hy : 0 < y := by rw [hydef]; positivity
  set A : ℝ := x ^ 2 / 2 with hAdef
  have hA : 0 < A := by rw [hAdef]; positivity
  -- the window
  have hwin : ENNReal.ofReal x * F.mixDensityL x
      = ∫⁻ u in Ioo (0 : ℝ) τ,
          ENNReal.ofReal (C * (u ^ (-(3 : ℝ) / 2) * Real.exp (-(x ^ 2 / 2 / u)))) := by
    rw [mixDensityL, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    have hpt : ∀ u ∈ Ioi (0 : ℝ),
        ENNReal.ofReal x * ENNReal.ofReal (brownianDensity u x * F.k u / u)
          = (Ioo (0 : ℝ) τ).indicator
              (fun u => ENNReal.ofReal
                (C * (u ^ (-(3 : ℝ) / 2) * Real.exp (-(x ^ 2 / 2 / u))))) u := by
      intro u hu
      have hu0 : (0 : ℝ) < u := hu
      have hsu : (0 : ℝ) < Real.sqrt u := Real.sqrt_pos.mpr hu0
      have halg : ENNReal.ofReal x * ENNReal.ofReal (brownianDensity u x * F.k u / u)
          = ENNReal.ofReal (C * (u ^ (-(3 : ℝ) / 2) * Real.exp (-(x ^ 2 / 2 / u))))
              * ENNReal.ofReal (F.k u) := by
        rw [← ENNReal.ofReal_mul hx.le, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [brownianDensity_eq hu0, rpow_neg_three_half hu0,
          show 2 * Real.pi * u = (2 * Real.pi) * u by ring, Real.sqrt_mul (by positivity),
          show -x ^ 2 / (2 * u) = -(x ^ 2 / 2 / u) by ring, hCdef]
        field_simp
      rw [halg, hkF]
      by_cases hcase : u ∈ Ioo (0 : ℝ) τ
      · rw [cinProfile_eq_one hcase, indicator_of_mem hcase]
        simp
      · rw [cinProfile_eq_zero hcase, indicator_of_notMem hcase]
        simp
    rw [setLIntegral_congr_fun measurableSet_Ioi hpt,
      lintegral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo]
    congr 1
    exact congrArg volume.restrict (inter_eq_left.mpr fun u hu => hu.1)
  -- the window is `(0, A/y²)`
  have hAy : A * (y ^ 2)⁻¹ = τ := by
    rw [hAdef, hydef, div_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * τ)]
    field_simp
  -- the substitution
  have hsub : ENNReal.ofReal x * F.mixDensityL x
      = ENNReal.ofReal (2 / Real.sqrt Real.pi)
        * ∫⁻ v in Ioi y, ENNReal.ofReal (Real.exp (-v ^ 2)) := by
    rw [hwin, ← hAy, lintegral_Ioo_comp_inv_sq hA hy,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_congr_fun measurableSet_Ioi fun v hv => ?_
    have hv0 : (0 : ℝ) < v := lt_trans hy hv
    have hw0 : (0 : ℝ) < A * (v ^ 2)⁻¹ := by positivity
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have hwval : A * (v ^ 2)⁻¹ = x ^ 2 / (2 * v ^ 2) := by rw [hAdef]; field_simp
    have hsqrtw : Real.sqrt (x ^ 2 / (2 * v ^ 2)) = x / (Real.sqrt 2 * v) := by
      rw [show x ^ 2 / (2 * v ^ 2) = (x / (Real.sqrt 2 * v)) ^ 2 by
        rw [div_pow, mul_pow, sq (Real.sqrt 2), hmm]]
      exact Real.sqrt_sq (by positivity)
    have hexpo : x ^ 2 / 2 / (A * (v ^ 2)⁻¹) = v ^ 2 := by
      rw [hwval]; field_simp
    rw [rpow_neg_three_half hw0, hexpo, hwval, hsqrtw, hAdef, hCdef,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    field_simp
  -- back to the real profile
  have hint : (∫⁻ v in Ioi y, ENNReal.ofReal (Real.exp (-v ^ 2)))
      = ENNReal.ofReal (∫ v in Ioi y, Real.exp (-v ^ 2)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal integrable_expNegSq.integrableOn
      (.of_forall fun v => (Real.exp_pos _).le)]
  have hfin : ENNReal.ofReal x * F.mixDensityL x ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (F.mixDensityL_ne_top hx.ne')
  rw [F.bridgeProfile_eq hx.le, hsub, hint, ← ENNReal.ofReal_mul (by positivity),
    ENNReal.toReal_ofReal (by
      have := (erfc_pos y).le
      unfold erfc at this
      positivity)]
  rfl

end ScaleSpace.CausalAdmissible

namespace SpatialLine

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-! ## The exponential floor under a completely monotone profile -/

/-- **A nonzero measure with a finite Laplace transform has an exponential floor.**

`U(-∞, n]` has positive finite mass for some `n`, and on that window `e^{-xθ} ≥ e^{-xn}`. This is
what the printed proof calls "a completely monotone function decays no faster than exponentially",
stated at the one window the argument uses rather than at Bernstein's measure as a whole. -/
theorem exists_laplaceL_lower_bound {U : Measure ℝ} (hne : U ≠ 0)
    (hfin : ∀ x : ℝ, 0 < x → laplaceL U x ≠ ⊤) :
    ∃ (n : ℕ) (c : ℝ), 0 < c ∧ ∀ x : ℝ, 0 < x →
      ENNReal.ofReal (c * Real.exp (-(x * n))) ≤ laplaceL U x := by
  have hex : ∃ n : ℕ, U (Iic (n : ℝ)) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    refine hne ?_
    have huniv : U univ = 0 := by
      have hcov : (⋃ n : ℕ, Iic (n : ℝ)) = univ :=
        eq_univ_of_forall fun t => mem_iUnion.mpr ⟨⌈t⌉₊, Nat.le_ceil t⟩
      rw [← hcov]
      exact measure_iUnion_null hcon
    exact Measure.measure_univ_eq_zero.mp huniv
  obtain ⟨n, hn⟩ := hex
  have hbound : ∀ x : ℝ, 0 < x →
      ENNReal.ofReal (Real.exp (-(x * n))) * U (Iic (n : ℝ)) ≤ laplaceL U x := by
    intro x hx
    have hle : ENNReal.ofReal (Real.exp (-(x * n))) * U (Iic (n : ℝ))
        ≤ ∫⁻ θ in Iic (n : ℝ), ENNReal.ofReal (Real.exp (-(x * θ))) ∂U := by
      have hconst : (∫⁻ _θ in Iic (n : ℝ), ENNReal.ofReal (Real.exp (-(x * n))) ∂U)
          = ENNReal.ofReal (Real.exp (-(x * n))) * U (Iic (n : ℝ)) := by
        rw [lintegral_const, Measure.restrict_apply_univ]
      rw [← hconst]
      refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_Iic).mpr
        (.of_forall fun θ hθ => ?_))
      have hθn : θ ≤ (n : ℝ) := hθ
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by nlinarith))
    exact le_trans hle (setLIntegral_le_lintegral _ _)
  have hnetop : U (Iic (n : ℝ)) ≠ ⊤ := by
    intro hcon
    have hb := hbound 1 one_pos
    have hne0 : ENNReal.ofReal (Real.exp (-(1 * (n : ℝ)))) ≠ 0 := by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      positivity
    rw [hcon, ENNReal.mul_top hne0] at hb
    exact hfin 1 one_pos (top_le_iff.mp hb)
  refine ⟨n, (U (Iic (n : ℝ))).toReal, ENNReal.toReal_pos hn hnetop, fun x hx => ?_⟩
  refine le_trans (le_of_eq ?_) (hbound x hx)
  rw [mul_comm ((U (Iic (n : ℝ))).toReal), ENNReal.ofReal_mul (Real.exp_pos _).le,
    ENNReal.ofReal_toReal hnetop]

/-! ## The node -/

/-- **`prop:thorin-subclass`(5), strictness the other way.**

`Skeleton.thorin_strictness`'s statement verbatim: the image of the causal `Cin` ray has the
explicit profile `2 erfc(x/√(2τ))`, and that profile is not completely monotone.

**Spends ledger A3** (`fourier_toolbox_levy_unique`, through `sdProfile_unique`) and ledger
**A11** (`bernstein_completely_monotone`, at its *forward* direction — a completely monotone
function is a Laplace transform). Both names were already on the trust boundary.

The route: the density clause is the change of variables above followed by the same
a.e.-to-pointwise passage as `thorin_bridge`, `erfc` being continuous and `Q.k` antitone; the
strictness clause assumes complete monotonicity, extracts the representing measure, bounds the
profile below by `ce^{-nx}` on one window of positive mass, and contradicts that at a single
explicitly chosen `x` with the Gaussian bound `erfc y ≤ 2e^{-y²}`. -/
theorem thorin_strictness {τ : ℝ} (hτ : 0 < τ) (F : CausalAdmissible)
    (hk : F.k = cinProfile τ) (Q : SDProfile)
    (hQ : ∀ ω : ℝ, Q.exponent ω = F.exponent (ω ^ 2 / 2)) :
    (∀ x : ℝ, 0 < x → Q.k x = 2 * erfc (x / Real.sqrt (2 * τ))) ∧
      ¬ IsCompletelyMonotone Q.k := by
  have hs2τ : (0 : ℝ) < Real.sqrt (2 * τ) := Real.sqrt_pos.mpr (by positivity)
  set g : ℝ → ℝ := fun x => 2 * erfc (x / Real.sqrt (2 * τ)) with hgdef
  have hgcont : Continuous g := by
    rw [hgdef]
    exact continuous_const.mul (continuous_erfc.comp (continuous_id.div_const _))
  have hgnonneg : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ g x := fun x _ => by
    rw [hgdef]; have := erfc_nonneg (x / Real.sqrt (2 * τ)); linarith
  -- the density clause
  have hexp : ∀ ω, Q.exponent ω = F.bridgeDatum.exponent ω := fun ω => by
    rw [F.bridgeDatum_exponent ω]; exact hQ ω
  obtain ⟨-, hQprof⟩ := sdProfile_unique hexp
  have hprof : profileMeasure Q.k = profileMeasure g := by
    rw [hQprof, ScaleSpace.CausalAdmissible.bridgeDatum_k, profileMeasure, profileMeasure]
    refine withDensity_congr_ae ?_
    filter_upwards [self_mem_ae_restrict (measurableSet_Ioi (a := (0 : ℝ)))] with x hx
    rw [F.bridgeProfile_of_cin hτ hk (hx : (0 : ℝ) < x)]
  have hdens : Set.EqOn Q.k g (Ioi 0) :=
    eqOn_of_profileMeasure_eq Q.k_antitone Q.k_nonneg
      (hgcont.continuousOn.aemeasurable measurableSet_Ioi) hgnonneg hgcont.continuousOn hprof
  refine ⟨fun x hx => hdens hx, ?_⟩
  -- the strictness clause
  intro hcm
  obtain ⟨U, hUneg, hUlap⟩ := (bernstein_completely_monotone Q.k).mp hcm
  have hLfin : ∀ x : ℝ, 0 < x → laplaceL U x ≠ ⊤ := fun x hx => (hUlap x hx).1
  have hUne : U ≠ 0 := by
    intro hU0
    have h1 : Q.k 1 = (laplaceL U 1).toReal := (hUlap 1 one_pos).2
    rw [hU0] at h1
    simp only [laplaceL, lintegral_zero_measure, ENNReal.toReal_zero] at h1
    have h2 : Q.k 1 = g 1 := hdens (by norm_num)
    rw [h1, hgdef] at h2
    have := erfc_pos (1 / Real.sqrt (2 * τ))
    simp only at h2
    linarith
  obtain ⟨n, c, hc, hlow⟩ := exists_laplaceL_lower_bound hUne hLfin
  -- an explicit `x` at which the Gaussian bound beats the exponential floor
  set x : ℝ := max (max (Real.sqrt (2 * τ)) (2 * τ * ((n : ℝ) + 1))) (4 / c + 1) with hxdef
  have hx1 : Real.sqrt (2 * τ) ≤ x := le_trans (le_max_left _ _) (le_max_left _ _)
  have hx2 : 2 * τ * ((n : ℝ) + 1) ≤ x := le_trans (le_max_right _ _) (le_max_left _ _)
  have hx3 : 4 / c + 1 ≤ x := le_max_right _ _
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le hs2τ hx1
  set y : ℝ := x / Real.sqrt (2 * τ) with hydef
  have hy1 : (1 : ℝ) ≤ y := by
    rw [hydef, le_div_iff₀ hs2τ]; linarith
  have hysq : y ^ 2 = x ^ 2 / (2 * τ) := by
    rw [hydef, div_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * τ)]
  -- the floor
  have hfloor : c * Real.exp (-(x * n)) ≤ Q.k x := by
    have h := ENNReal.toReal_mono (hLfin x hx0) (hlow x hx0)
    rwa [ENNReal.toReal_ofReal (by positivity), ← (hUlap x hx0).2] at h
  -- the ceiling
  have hceil : Q.k x ≤ 4 * Real.exp (-(y ^ 2)) := by
    have h := hdens (hx0 : x ∈ Ioi (0 : ℝ))
    rw [h, hgdef]
    simp only
    rw [← hydef]
    linarith [erfc_le_two_mul_exp hy1]
  -- and the comparison
  have hgap : 4 * Real.exp (-(y ^ 2)) < c * Real.exp (-(x * n)) := by
    have hstep : ((n : ℝ) + 1) * x ≤ y ^ 2 := by
      rw [hysq, le_div_iff₀ (by positivity : (0 : ℝ) < 2 * τ)]
      nlinarith [hx2, hx0]
    have hexpmono : Real.exp (-(y ^ 2)) ≤ Real.exp (-(((n : ℝ) + 1) * x)) :=
      Real.exp_le_exp.mpr (by linarith)
    have hsplit : Real.exp (-(((n : ℝ) + 1) * x))
        = Real.exp (-x) * Real.exp (-(x * n)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hcx : 4 < c * x := by
      have h4 : 4 / c < x := by linarith
      rwa [div_lt_iff₀ hc, mul_comm] at h4
    have hexpx : Real.exp (-x) ≤ 1 / x := by
      have hxe : x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
      rw [Real.exp_neg, inv_eq_one_div]
      exact one_div_le_one_div_of_le hx0 hxe
    have h4x : 4 * Real.exp (-x) < c := by
      have : 4 * Real.exp (-x) ≤ 4 / x := by
        rw [show (4 : ℝ) / x = 4 * (1 / x) by ring]
        linarith
      have h4c : 4 / x < c := by rw [div_lt_iff₀ hx0]; linarith
      linarith
    calc 4 * Real.exp (-(y ^ 2)) ≤ 4 * Real.exp (-(((n : ℝ) + 1) * x)) := by linarith
      _ = (4 * Real.exp (-x)) * Real.exp (-(x * n)) := by rw [hsplit]; ring
      _ < c * Real.exp (-(x * n)) := by
          exact mul_lt_mul_of_pos_right h4x (Real.exp_pos _)
  linarith

end SpatialLine
