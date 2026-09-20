/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.Tightness
import SpatialLine.Cin

/-!
# The first absolute moment of a law with a quadratically flat transform

Blueprint: `lem:cin-delay-equation` (`blueprint/src/parts/08-cone.tex`), the hypothesis its
printed proof needs and does not have.

## What this file is for, and what it corrects

Wave 2 re-priced `lem:cin-delay-equation` at **L** on the ground that its printed route "closes
with Fourier uniqueness applied to `x p`, which presupposes a first absolute moment --- true
here, but a theorem in its own right that neither this development nor Mathlib carries;
deriving it is more work than the rest of the node." That estimate was made from the paper
proof. Read at the statement the obligation is much smaller, and it is discharged here.

Finiteness of the first moment of a symmetric probability law follows from a **quadratic bound
on its exponent near the origin and nothing else**, through the truncation inequality this
development already owns. The chain is

* `integral_one_sub_sinc_le` (`Tightness.lean`, `thm:increments-levy`'s second step): the sinc
  defect at scale `r` is at most the mean of the exponent over `[-r,r]`;
* `one_sub_sinc_ge` (`Truncation.lean`): the sinc defect dominates `min 1 (r x)^2` up to the
  constant `2/(3 pi^2)`;
* so `mu {|x| > R}` is at most a constant times the mean of the exponent over `[-1/R, 1/R]`,
  and a quadratic bound on the exponent makes that `O(R^{-2})`;
* and a tail of order `R^{-2}` is integrable against `dR`, which is the first moment by the
  layer cake.

For a `Cin` law the quadratic bound is `cin_le_sq`, already proved: `Cin(z) <= z^2/4`. So the
whole of the "theorem nobody carries" is one application of two lemmas written for another
chapter and one elementary integral. This is the shape of mis-estimate the campaign's own rule
about pricing at the Lean statement rather than from the paper exists to catch.

## What this does *not* do

It does not prove `lem:cin-delay-equation`. With the moment in hand the primitive form still
needs the derivative of the transform under the integral sign, the transform of the signed
measure `y nu_2`, and uniqueness for *signed* finite measures through their Jordan parts; and
the derivative form still needs a multiplication formula pairing a finite measure against a
Schwartz function, which Mathlib does not carry in that form (`Measure.ext_of_charFun` goes
through a Stone-Weierstrass argument, not through Parseval). Both remain **L**. What has
changed is that the blocker the node's annotation named is no longer one.

Proving campaign, wave 3, chapter 8 (2026-09-09).
-/

namespace SpatialLine

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-! ## The tail bound -/

/-- **A quadratically flat exponent gives a quadratically decaying tail.**

If the exponent of a symmetric probability law is at most `c omega^2`, then
`mu {|x| > R} <= (3 pi^2 / 4) c / R^2`. The constant is the product of the two the development
already carries and is not optimised: only the order matters. -/
theorem measureReal_abs_gt_le_of_exponent_le {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hsym : IsSymmetric μ) (hpos : ∀ ω, 0 < fourierCos μ ω) {c : ℝ}
    (hb : ∀ ω : ℝ, exponent μ ω ≤ c * ω ^ 2) {R : ℝ} (hR : 0 < R) :
    μ.real {x : ℝ | R < |x|} ≤ Real.pi ^ 2 * c / (2 * R ^ 2) := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  set r : ℝ := R⁻¹ with hr
  have hr0 : 0 < r := by positivity
  -- the sinc defect at scale `r` dominates the mass beyond `R`
  have hmin : ∀ x : ℝ, R < |x| → (1 : ℝ) ≤ min 1 ((r * x) ^ 2) := by
    intro x hx
    have h1 : (1 : ℝ) < |r * x| := by
      rw [abs_mul, abs_of_pos hr0, hr]
      rw [inv_mul_eq_div, lt_div_iff₀ hR]
      linarith
    have : (1 : ℝ) ≤ (r * x) ^ 2 := by nlinarith [abs_nonneg (r * x), sq_abs (r * x)]
    exact le_min le_rfl this
  have hmeas : MeasurableSet {x : ℝ | R < |x|} :=
    measurableSet_lt measurable_const (measurable_id.abs)
  have hintmin : Integrable (fun x : ℝ => min 1 ((r * x) ^ 2)) μ := by
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min zero_le_one (by positivity))]
    exact min_le_left _ _
  have hmass : μ.real {x : ℝ | R < |x|} ≤ ∫ x, min 1 ((r * x) ^ 2) ∂μ := by
    have hind : ∀ x : ℝ, Set.indicator {x : ℝ | R < |x|} (fun _ => (1 : ℝ)) x
        ≤ min 1 ((r * x) ^ 2) := by
      intro x
      by_cases hx : x ∈ {x : ℝ | R < |x|}
      · rw [Set.indicator_of_mem hx]
        exact hmin x hx
      · rw [Set.indicator_of_notMem hx]
        exact le_min zero_le_one (by positivity)
    calc μ.real {x : ℝ | R < |x|}
        = ∫ x, Set.indicator {x : ℝ | R < |x|} (fun _ => (1 : ℝ)) x ∂μ := by
          rw [integral_indicator hmeas]
          simp [measureReal_def]
      _ ≤ ∫ x, min 1 ((r * x) ^ 2) ∂μ :=
          integral_mono ((integrable_const (1 : ℝ)).indicator hmeas) hintmin hind
  -- the sinc defect is bounded by the mean of the exponent
  have hsinc : 2 / (3 * Real.pi ^ 2) * ∫ x, min 1 ((r * x) ^ 2) ∂μ
      ≤ ∫ x, (1 - Real.sinc (r * x)) ∂μ := by
    rw [← integral_const_mul]
    refine integral_mono (hintmin.const_mul _)
      ((integrable_const (1 : ℝ)).sub (integrable_sinc_mul μ r)) fun x => ?_
    exact one_sub_sinc_ge (r * x)
  have htrunc := integral_one_sub_sinc_le μ hsym hpos hr0
  -- the mean of the exponent is at most `c r^2 / 3`
  have hmean : (2 * r)⁻¹ * ∫ ω in (-r)..r, exponent μ ω ≤ c * r ^ 2 / 3 := by
    have hle : ∫ ω in (-r)..r, exponent μ ω ≤ ∫ ω in (-r)..r, c * ω ^ 2 := by
      refine intervalIntegral.integral_mono_on (by linarith) ?_ ?_ fun ω _ => hb ω
      · exact ((continuous_fourierCos μ).log fun ω => (hpos ω).ne').neg.intervalIntegrable _ _
      · exact (continuous_const.mul (continuous_pow 2)).intervalIntegrable _ _
    have hval : ∫ ω in (-r)..r, c * ω ^ 2 = c * (2 * r ^ 3 / 3) := by
      rw [intervalIntegral.integral_const_mul, integral_pow]
      ring
    have h2r : (0 : ℝ) < 2 * r := by linarith
    rw [hval] at hle
    calc (2 * r)⁻¹ * ∫ ω in (-r)..r, exponent μ ω
        ≤ (2 * r)⁻¹ * (c * (2 * r ^ 3 / 3)) := by
          exact mul_le_mul_of_nonneg_left hle (by positivity)
      _ = c * r ^ 2 / 3 := by field_simp
  -- assemble
  have hstep : 2 / (3 * Real.pi ^ 2) * μ.real {x : ℝ | R < |x|} ≤ c * r ^ 2 / 3 := by
    have hcpos : (0 : ℝ) < 2 / (3 * Real.pi ^ 2) := by positivity
    calc 2 / (3 * Real.pi ^ 2) * μ.real {x : ℝ | R < |x|}
        ≤ 2 / (3 * Real.pi ^ 2) * ∫ x, min 1 ((r * x) ^ 2) ∂μ :=
          mul_le_mul_of_nonneg_left hmass hcpos.le
      _ ≤ ∫ x, (1 - Real.sinc (r * x)) ∂μ := hsinc
      _ ≤ (2 * r)⁻¹ * ∫ ω in (-r)..r, exponent μ ω := htrunc
      _ ≤ c * r ^ 2 / 3 := hmean
  have hR2 : r ^ 2 = 1 / R ^ 2 := by
    rw [hr]
    field_simp
  rw [hR2] at hstep
  have hmulpos : (0 : ℝ) < 3 * Real.pi ^ 2 / 2 := by positivity
  have h := mul_le_mul_of_nonneg_left hstep hmulpos.le
  have hRne : (R : ℝ) ≠ 0 := ne_of_gt hR
  have hL : 3 * Real.pi ^ 2 / 2 * (2 / (3 * Real.pi ^ 2) * μ.real {x : ℝ | R < |x|})
      = μ.real {x : ℝ | R < |x|} := by field_simp
  have hRR : 3 * Real.pi ^ 2 / 2 * (c * (1 / R ^ 2) / 3) = Real.pi ^ 2 * c / (2 * R ^ 2) := by
    field_simp
  rw [hL, hRR] at h
  exact h

/-! ## The first moment -/

/-- **A quadratically flat exponent gives a finite first absolute moment.**

The layer cake turns the tail bound into the moment: the mass beyond `R` is at most `1`
below `R = 1` and `O(R^{-2})` above it, and `R^{-2}` is integrable on the ray. Nothing here
is about this article: it is the standard truncation route, run on the two inequalities
chapters 5 wrote for the null-array step. -/
theorem integrable_abs_of_exponent_le {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hsym : IsSymmetric μ) (hpos : ∀ ω, 0 < fourierCos μ ω) {c : ℝ} (hc : 0 ≤ c)
    (hb : ∀ ω : ℝ, exponent μ ω ≤ c * ω ^ 2) :
    Integrable (fun x : ℝ => |x|) μ := by
  have hnn : 0 ≤ᵐ[μ] fun x : ℝ => |x| := Filter.Eventually.of_forall fun x => abs_nonneg x
  refine ⟨measurable_id.abs.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal hnn]
  rw [lintegral_eq_lintegral_meas_lt μ hnn measurable_id.abs.aemeasurable]
  have hsplit : Ioi (0 : ℝ) = Ioc (0 : ℝ) 1 ∪ Ioi 1 := (Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  have hdisj : Disjoint (Ioc (0 : ℝ) 1) (Ioi 1) := Ioc_disjoint_Ioi le_rfl
  rw [hsplit, lintegral_union measurableSet_Ioi hdisj]
  refine ENNReal.add_lt_top.mpr ⟨?_, ?_⟩
  · refine lt_of_le_of_lt (lintegral_mono fun R => prob_le_one) ?_
    rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioc]
    exact ENNReal.mul_lt_top ENNReal.one_lt_top ENNReal.ofReal_lt_top
  · have hgnn : ∀ R : ℝ, 1 < R → 0 ≤ Real.pi ^ 2 * c / (2 * R ^ 2) := by
      intro R hR
      have : (0 : ℝ) < R := lt_trans zero_lt_one hR
      positivity
    have hg : IntegrableOn (fun R : ℝ => Real.pi ^ 2 * c / (2 * R ^ 2)) (Ioi 1) := by
      have hrp : IntegrableOn (fun R : ℝ => R ^ (-2 : ℝ)) (Ioi (1 : ℝ)) :=
        integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one
      have hcm : IntegrableOn (fun R : ℝ => Real.pi ^ 2 * c / 2 * R ^ (-2 : ℝ)) (Ioi 1) :=
        hrp.const_mul (Real.pi ^ 2 * c / 2)
      refine hcm.congr_fun (fun R hR => ?_) measurableSet_Ioi
      have hR0 : (0 : ℝ) < R := lt_trans zero_lt_one hR
      change Real.pi ^ 2 * c / 2 * R ^ (-2 : ℝ) = Real.pi ^ 2 * c / (2 * R ^ 2)
      rw [rpow_neg_two hR0]
      field_simp
    have hle : (∫⁻ R in Ioi (1 : ℝ), μ {x : ℝ | R < |x|})
        ≤ ∫⁻ R in Ioi (1 : ℝ), ENNReal.ofReal (Real.pi ^ 2 * c / (2 * R ^ 2)) := by
      refine lintegral_mono_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with R hR
      have hR1 : (1 : ℝ) < R := hR
      have hR0 : (0 : ℝ) < R := lt_trans zero_lt_one hR1
      have hb' := measureReal_abs_gt_le_of_exponent_le hsym hpos hb hR0
      have hfin : μ {x : ℝ | R < |x|} ≠ ⊤ := measure_ne_top _ _
      rw [← ENNReal.ofReal_toReal hfin]
      exact ENNReal.ofReal_le_ofReal hb'
    refine lt_of_le_of_lt hle ?_
    rw [← ofReal_integral_eq_lintegral_ofReal hg
      ((ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun R hR => hgnn R hR))]
    exact ENNReal.ofReal_lt_top

/-- **The first absolute moment of a `Cin` law is finite.**

The specialisation of `integrable_abs_of_exponent_le` at `c = tau^2/4`, the constant of
`cin_le_sq`. This is the hypothesis `lem:cin-delay-equation`'s printed proof assumes and
the wave-2 annotation called "a theorem in its own right that neither this development nor
Mathlib carries". It is neither: it is four lines on top of a lemma written for another
chapter. The node is still open, but not for this reason. -/
theorem cin_law_integrable_abs {τ : ℝ} {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hsym : IsSymmetric μ) (hcos : ∀ ω : ℝ, fourierCos μ ω = Real.exp (-cin (τ * ω))) :
    Integrable (fun x : ℝ => |x|) μ := by
  have hpos : ∀ ω, 0 < fourierCos μ ω := fun ω => by rw [hcos ω]; exact Real.exp_pos _
  have hexp : ∀ ω, exponent μ ω = cin (τ * ω) := by
    intro ω
    rw [exponent_apply, hcos ω, Real.log_exp, neg_neg]
  refine integrable_abs_of_exponent_le hsym hpos (c := τ ^ 2 / 4) (by positivity) fun ω => ?_
  rw [hexp ω]
  calc cin (τ * ω) ≤ (τ * ω) ^ 2 / 4 := cin_le_sq _
    _ = τ ^ 2 / 4 * ω ^ 2 := by ring

end SpatialLine
