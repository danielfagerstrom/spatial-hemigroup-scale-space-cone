/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.Generator
import SpatialLine.ChoquetCone

/-!
# The domain of the scale generator

Blueprint: `prop:scale-evolution`'s convergence clause, "the integral converging absolutely for
`g` in the signal class".

## What the writing found

**The clause is priced against the wrong half of the work.** The estimate called it **S**, "the
integrand is bounded by `min(2‖g‖_∞, (t²v²/2)‖g''‖_∞)`, and `∫(1 ∧ v²)ϖ < ∞` is the profile's
integrability read at the Choquet measure". The second half is indeed short — three steps through
`cin_superposition`, `SDProfile.exponentL_ne_top` and `lintegral_cin_ne_top_iff`, all of them
already in the library (`lintegral_min_hasProfileTail`). The first half is the whole cost: the
quadratic bound on the symmetric second difference is a Taylor estimate that Mathlib does not
carry in this form, and it has to be assembled by hand from two mean-value inequalities on
`phi(s) = (g(x+s) + g(x-s))/2 - g(x)` and its derivative. That is
`abs_secondDifference_le`, and it is the reason the clause paid **M**.

**`0 < t` is not consumed.** Neither is the sign of `t`. The bound
`min(2‖g‖_∞, ‖g''‖_∞t²v²)` holds for every `t`, so the convergence clause is a statement about
the class of `g` and about the Choquet measure, and not about a scale — which is the shape the
node's own reading (F13) already predicted, one step further than it went.

`abs_secondDifference_le` is stated separately because `prop:corner-generators`(3) and (4) need
the same estimate, and `lintegral_min_hasProfileTail` because every later statement about the
generator's domain does.
-/

namespace SpatialLine

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-- The Lévy condition at the Choquet measure. -/
theorem lintegral_min_hasProfileTail {P : SDProfile} {ϖ : Measure ℝ}
    (hϖ : HasProfileTail P.k ϖ) :
    (∫⁻ v, ENNReal.ofReal (min 1 (v ^ 2)) ∂ϖ) ≠ ⊤ := by
  have hfold : IsFolded ϖ := hϖ.1
  have hcin : (∫⁻ τ, ENNReal.ofReal (cin (τ * 1)) ∂ϖ) ≠ ⊤ := by
    have h := cin_superposition P ϖ hϖ 1
    have hne := P.exponentL_ne_top 1
    rw [h, cinSuperpositionL] at hne
    intro hcon
    rw [hcon] at hne
    simp at hne
  have hdom : (∫⁻ τ, ENNReal.ofReal (domainIntegrand τ) ∂ϖ) ≠ ⊤ :=
    (lintegral_cin_ne_top_iff ϖ hfold one_ne_zero).mp hcin
  have hpos : ∀ᵐ τ ∂ϖ, 0 < τ := by
    rw [ae_iff]
    refine measure_mono_null (fun t ht => ?_) hfold
    simp only [not_lt, mem_setOf_eq] at ht
    exact mem_Iic.mpr ht
  refine ne_top_of_le_ne_top hdom (lintegral_mono_ae ?_)
  filter_upwards [hpos] with τ hτ
  refine ENNReal.ofReal_le_ofReal ?_
  rw [domainIntegrand]
  rcases le_or_gt τ 1 with h | h
  · rw [max_eq_left h, Real.log_one]
    exact le_min (min_le_right _ _) (by nlinarith [min_le_left (1:ℝ) (τ ^ 2)])
  · rw [max_eq_right h.le, min_eq_left (by nlinarith : (1:ℝ) ≤ τ ^ 2)]
    have hlog : 0 ≤ Real.log τ := Real.log_nonneg h.le
    exact le_min (by nlinarith) (by linarith)

theorem abs_secondDifference_le {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) {C₂ : ℝ}
    (hb2 : ∀ y, |iteratedDeriv 2 g y| ≤ C₂) (x h : ℝ) :
    |g x - (g (x - h) + g (x + h)) / 2| ≤ C₂ * h ^ 2 := by
  have hd1 : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hd2 : Differentiable ℝ (deriv g) := by
    have h1 : ContDiff ℝ 1 (deriv g) :=
      ((contDiff_succ_iff_deriv (n := 1) (f := g)).mp (by exact_mod_cast hg)).2.2
    exact h1.differentiable (by norm_num)
  have hdd : ∀ y, iteratedDeriv 2 g y = deriv (deriv g) y := by
    intro y
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  set φ : ℝ → ℝ := fun s => (g (x + s) + g (x - s)) / 2 - g x with hφ
  set ψ : ℝ → ℝ := fun s => (deriv g (x + s) - deriv g (x - s)) / 2 with hψ
  have hplus : ∀ (f : ℝ → ℝ), Differentiable ℝ f → ∀ s : ℝ,
      HasDerivAt (fun r => f (x + r)) (deriv f (x + s)) s := by
    intro f hf s
    exact HasDerivAt.comp_const_add x s ((hf (x + s)).hasDerivAt)
  have hminus : ∀ (f : ℝ → ℝ), Differentiable ℝ f → ∀ s : ℝ,
      HasDerivAt (fun r => f (x - r)) (-deriv f (x - s)) s := by
    intro f hf s
    exact HasDerivAt.comp_const_sub x s ((hf (x - s)).hasDerivAt)
  have hφd : ∀ s : ℝ, HasDerivAt φ (ψ s) s := by
    intro s
    have h := (((hplus g hd1 s).add (hminus g hd1 s)).div_const 2).sub_const (g x)
    simpa [hφ, hψ, sub_eq_add_neg] using h
  have hψd : ∀ s : ℝ,
      HasDerivAt ψ ((deriv (deriv g) (x + s) + deriv (deriv g) (x - s)) / 2) s := by
    intro s
    have h := ((hplus (deriv g) hd2 s).sub (hminus (deriv g) hd2 s)).div_const 2
    simpa [hψ, sub_neg_eq_add] using h
  have hψ0 : ψ 0 = 0 := by simp [hψ]
  have hφ0 : φ 0 = 0 := by simp [hφ]
  -- `|ψ s| ≤ C₂ |s|`
  have hψbound : ∀ s : ℝ, |ψ s| ≤ C₂ * |s| := by
    intro s
    have hb : ∀ r ∈ (uIcc 0 s : Set ℝ),
        ‖(deriv (deriv g) (x + r) + deriv (deriv g) (x - r)) / 2‖ ≤ C₂ := by
      intro r _
      have h1 : |deriv (deriv g) (x + r)| ≤ C₂ := by rw [← hdd]; exact hb2 _
      have h2 : |deriv (deriv g) (x - r)| ≤ C₂ := by rw [← hdd]; exact hb2 _
      rw [Real.norm_eq_abs, abs_div, abs_two]
      have := abs_add_le (deriv (deriv g) (x + r)) (deriv (deriv g) (x - r))
      linarith
    have := (convex_uIcc (0:ℝ) s).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun r _ => (hψd r).hasDerivWithinAt) hb left_mem_uIcc right_mem_uIcc
    simpa [hψ0] using this
  -- `|φ h| ≤ C₂ h²`
  have hb : ∀ r ∈ (uIcc 0 h : Set ℝ), ‖ψ r‖ ≤ C₂ * |h| := by
    intro r hr
    have hrle : |r| ≤ |h| := by
      rcases le_total (0:ℝ) h with hh | hh
      · rw [uIcc_of_le hh] at hr
        rw [abs_of_nonneg hr.1, abs_of_nonneg hh]
        exact hr.2
      · rw [uIcc_of_ge hh] at hr
        rw [abs_of_nonpos hr.2, abs_of_nonpos hh]
        linarith [hr.1]
    have hC₂ : 0 ≤ C₂ := le_trans (abs_nonneg _) (hb2 x)
    exact le_trans (by simpa using hψbound r) (by nlinarith)
  have hmain := (convex_uIcc (0:ℝ) h).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun r _ => (hφd r).hasDerivWithinAt) hb left_mem_uIcc right_mem_uIcc
  rw [hφ0] at hmain
  simp only [Real.norm_eq_abs, sub_zero] at hmain
  have hgoal : g x - (g (x - h) + g (x + h)) / 2 = -φ h := by
    simp [hφ]; ring
  rw [hgoal, abs_neg]
  calc |φ h| ≤ C₂ * |h| * |h| := hmain
    _ = C₂ * h ^ 2 := by rw [mul_assoc, abs_mul_abs_self]; ring



/-- **`prop:scale-evolution`'s convergence clause.** The generator's integral converges
absolutely for a bounded function with bounded second derivative.

The integrand is bounded by `min(2‖g‖_∞, ‖g''‖_∞t²v²)`, which is at most
`max(2‖g‖_∞, ‖g''‖_∞t²)(1 ∧ v²)`, and `∫(1 ∧ v²)varpi < ∞` is the profile's integrability read
at the Choquet measure (`lintegral_min_hasProfileTail`).

**`0 < t` is not consumed**, and neither is `HasProfileTail`'s tail identity beyond what
`lintegral_min_hasProfileTail` extracts from it: the clause is a statement about the class of
`g`, not about a scale. -/
theorem scale_evolution_absconv (P : SDProfile) (ϖ : Measure ℝ) (hϖ : HasProfileTail P.k ϖ)
    {t : ℝ} (ht : 0 < t) (g : ℝ → ℝ) (hg : ContDiff ℝ 2 g)
    (hb : ∃ C : ℝ, ∀ x, |g x| ≤ C) (hb2 : ∃ C : ℝ, ∀ x, |iteratedDeriv 2 g x| ≤ C) (x : ℝ) :
    Integrable (fun v : ℝ => g x - (g (x - t * v) + g (x + t * v)) / 2) ϖ := by
  obtain ⟨C, hC⟩ := hb
  obtain ⟨C₂, hC₂⟩ := hb2
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC x)
  have hC₂0 : 0 ≤ C₂ := le_trans (abs_nonneg _) (hC₂ x)
  set K : ℝ := max (2 * C) (C₂ * t ^ 2) with hK
  have hK0 : 0 ≤ K := le_trans (by linarith) (le_max_left _ _)
  have hfin := lintegral_min_hasProfileTail hϖ
  have hbint : Integrable (fun v : ℝ => K * min 1 (v ^ 2)) ϖ := by
    refine ⟨(by fun_prop : Continuous fun v : ℝ => K * min 1 (v ^ 2)).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (.of_forall fun v => by
      have : (0:ℝ) ≤ min 1 (v ^ 2) := le_min zero_le_one (sq_nonneg v)
      positivity)]
    have heq : ∀ v : ℝ, ENNReal.ofReal (K * min 1 (v ^ 2))
        = ENNReal.ofReal K * ENNReal.ofReal (min 1 (v ^ 2)) := fun v =>
      ENNReal.ofReal_mul hK0
    rw [lintegral_congr heq, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin)
  refine Integrable.mono' hbint ?_ (.of_forall fun v => ?_)
  · have hgc : Continuous g := hg.continuous
    fun_prop
  · have h1 : |g x - (g (x - t * v) + g (x + t * v)) / 2| ≤ C₂ * (t * v) ^ 2 :=
      abs_secondDifference_le hg hC₂ x (t * v)
    have h2 : |g x - (g (x - t * v) + g (x + t * v)) / 2| ≤ 2 * C := by
      have e1 := hC x
      have e2 := hC (x - t * v)
      have e3 := hC (x + t * v)
      have := abs_sub (g x) ((g (x - t * v) + g (x + t * v)) / 2)
      calc |g x - (g (x - t * v) + g (x + t * v)) / 2|
          ≤ |g x| + |(g (x - t * v) + g (x + t * v)) / 2| := abs_sub _ _
        _ ≤ C + (|g (x - t * v)| + |g (x + t * v)|) / 2 := by
            rw [abs_div, abs_two]
            have := abs_add_le (g (x - t * v)) (g (x + t * v))
            linarith
        _ ≤ 2 * C := by linarith
    rw [Real.norm_eq_abs]
    rcases le_total (v ^ 2) 1 with hv | hv
    · rw [min_eq_right hv]
      have : C₂ * (t * v) ^ 2 = (C₂ * t ^ 2) * v ^ 2 := by ring
      nlinarith [le_max_right (2 * C) (C₂ * t ^ 2), sq_nonneg v]
    · rw [min_eq_left hv, mul_one]
      exact le_trans h2 (le_max_left _ _)

end SpatialLine
