/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.Interfaces
import SpatialLine.VarianceFormula
import SpatialLine.StableProfile
import SpatialLine.MaternCorner

/-!
# The moments of the corners

Blueprint: `prop:stable-family`'s moment clause and `prop:matern-exponent`(3), both of which run
`prop:moments-tails`(1) — ledger **A13**, admitted in `SpatialLine/Interfaces.lean` as
`moments_tails_criterion` — on an explicit profile.

The finiteness bridge `lintegral_ofReal_ne_top_iff_integrableOn` stood here until 2026-09-14 and
is now in `SpatialLine/VarianceFormula.lean`, which is imported above: the variance formula is
the `[T]` half of the same node, it spends no interface, and turning the import around is what
lets a Chapter 3 node reach the variance without reaching the criterion (ADR-0005).

## What proving these found

**The criterion is consumed as a black box and the work is entirely in the profile.** Once the
witness `SDProfile` is in hand — `stableDatum` for the pure power, `maternDatum` for the
exponential — the moment question is the convergence of `∫₁^∞ x^{n-1}k(x)dx`, and the two
profiles answer it in opposite ways: the pure power converges exactly when `n < α`, and the
exponential converges for every `n`. Nothing else of the criterion is used, and in particular
its left-hand side is never unfolded.

**The `ℕ`-subtraction in the criterion's exponent is load-bearing and harmless.** `x ^ (n - 1)`
is truncated subtraction, so the statement at `n = 0` would read `x ^ 0`; the hypothesis `1 ≤ n`
is what makes `((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1`, and that cast is the only place the hypothesis
is spent on the profile side. The stable clause's conclusion `(n : ℝ) < α` is therefore an
assertion about `n ≥ 1` only, as the node's own range is.
-/

namespace SpatialLine

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-! ## `prop:stable-family`, the moments -/

/-- **`prop:stable-family`, the moment clause.** For the symmetric stable family of index
`0 < α < 2`, `E|X_t|^n < ∞` exactly when `n < α`.

The criterion (ledger **A13**) turns the question into the convergence of
`∫₁^∞ x^{n-1}C_α^{-1}x^{-α}dx`, which is `integrableOn_Ioi_rpow_iff` at the exponent
`n - 1 - α`: finite exactly when `n - 1 - α < -1`. The normalising constant enters only through
its positivity (`stableConst_pos`), never through its value. -/
theorem stable_family_moments (α : ℝ) (hα : 0 < α) (hα2 : α < 2) (μ : ℝ → Measure ℝ)
    (hprob : ∀ t : ℝ, 0 < t → IsProbabilityMeasure (μ t))
    (hcos : ∀ t ω : ℝ, 0 < t → fourierCos (μ t) ω = Real.exp (-|t * ω| ^ α))
    {t : ℝ} (ht : 0 < t) :
    ∀ n : ℕ, 1 ≤ n → (Integrable (fun x : ℝ => |x| ^ n) (μ t) ↔ (n : ℝ) < α) := by
  intro n hn
  have hCpos : 0 < stableConst α := stableConst_pos hα hα2
  have hcos' : ∀ s ω : ℝ, 0 < s →
      fourierCos (μ s) ω = Real.exp (-(stableDatum α hα hα2).exponent (s * ω)) := by
    intro s ω hs
    rw [stableDatum_exponent hα hα2]
    exact hcos s ω hs
  rw [moments_tails_criterion (stableDatum α hα hα2) μ hprob hcos' ht hn]
  set s : ℝ := (n : ℝ) - 1 - α with hs
  have hpt : ∀ x ∈ Ioi (1 : ℝ),
      ENNReal.ofReal (x ^ (n - 1) * (stableDatum α hα hα2).k x)
        = ENNReal.ofReal ((stableConst α)⁻¹ * x ^ s) := by
    intro x hx
    have hx1 : (1 : ℝ) < x := hx
    have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx1
    congr 1
    rw [stableDatum_k, stableProfile_of_pos hx0, ← Real.rpow_natCast x (n - 1),
      Nat.cast_sub hn, Nat.cast_one, hs, show (n : ℝ) - 1 - α = ((n : ℝ) - 1) + -α by ring,
      Real.rpow_add hx0]
    ring
  rw [setLIntegral_congr_fun measurableSet_Ioi hpt]
  have hmeas : AEStronglyMeasurable (fun x : ℝ => (stableConst α)⁻¹ * x ^ s)
      (volume.restrict (Ioi (1 : ℝ))) := by fun_prop
  have hnn : ∀ᵐ x ∂(volume.restrict (Ioi (1 : ℝ))), 0 ≤ (stableConst α)⁻¹ * x ^ s := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun x hx => ?_)
    have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
    positivity
  rw [lintegral_ofReal_ne_top_iff_integrableOn hmeas hnn]
  constructor
  · intro h
    have h2 : IntegrableOn (fun x : ℝ => stableConst α * ((stableConst α)⁻¹ * x ^ s))
        (Ioi (1 : ℝ)) := h.const_mul _
    have h' : IntegrableOn (fun x : ℝ => x ^ s) (Ioi (1 : ℝ)) := by
      refine h2.congr_fun (fun x _ => ?_) measurableSet_Ioi
      field_simp
    have := (integrableOn_Ioi_rpow_iff (t := (1 : ℝ)) zero_lt_one).mp h'
    rw [hs] at this; linarith
  · intro h
    have hlt : s < -1 := by rw [hs]; linarith
    exact (integrableOn_Ioi_rpow_of_lt hlt zero_lt_one).const_mul _

/-! ## `prop:matern-exponent`(3), the finiteness clause -/

/-- **`prop:matern-exponent`(3), finiteness of every moment.** For the Matern family of shape
`γ` at unit range, every absolute moment of the kernel at canonical scale `t` is finite.

This is the first conjunct of `Skeleton.matern_moments`; the even-moment identity and the
variance are its other two and are not proved here.

The route is the second of the two the node's proof offers — the criterion (ledger **A13**) on
an exponentially decaying profile — and not the Gamma-mixture route through
`prop:bridge-families`(2). At `n = 0` the moment is the total mass and the criterion says
nothing, so that case is discharged separately from `hprob`; for `n ≥ 1` the tail integral is
`∫₁^∞ 2γ x^{n-1}e^{-x}dx`, which Mathlib's `integrableOn_rpow_mul_exp_neg_mul_rpow` gives at
`p = 1`, `b = 1`.

**Not a node declaration since 2026-09-10** (author's decision). This is a corollary of the
library, kept for its own sake and consumed by `two_members_matern_moments`; it is no longer
named in `prop:matern-exponent`'s `\lean` tag. The node is `[T]` and its four tagged
declarations print Lean core, while this one spends A13 — a second, independent part-proof of
the same conjunct, which the tag was reading as part of the node's grounding. -/
theorem matern_moments_integrable (γ : ℝ) (hγ : 0 < γ) (μ : ℝ → Measure ℝ)
    (hprob : ∀ t : ℝ, 0 < t → IsProbabilityMeasure (μ t))
    (hcos : ∀ t ω : ℝ, 0 < t → fourierCos (μ t) ω = Real.exp (-maternExponent γ 1 (t * ω)))
    {t : ℝ} (ht : 0 < t) :
    ∀ n : ℕ, Integrable (fun x : ℝ => |x| ^ n) (μ t) := by
  have hpm := hprob t ht
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hcos' : ∀ s ω : ℝ, 0 < s →
      fourierCos (μ s) ω = Real.exp (-(maternDatum γ 1 hγ one_pos).exponent (s * ω)) := by
    intro s ω hs
    rw [maternDatum_exponent]
    exact hcos s ω hs
  rw [moments_tails_criterion (maternDatum γ 1 hγ one_pos) μ hprob hcos' ht hn]
  have hpt : ∀ x ∈ Ioi (1 : ℝ),
      ENNReal.ofReal (x ^ (n - 1) * (maternDatum γ 1 hγ one_pos).k x)
        = ENNReal.ofReal (2 * γ * (x ^ ((n : ℝ) - 1) * Real.exp (-1 * x ^ (1 : ℝ)))) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
    congr 1
    rw [maternDatum_k, maternProfile_eq_exp one_pos hx0, ← Real.rpow_natCast x (n - 1),
      Nat.cast_sub hn, Nat.cast_one, Real.rpow_one]
    ring_nf
  rw [setLIntegral_congr_fun measurableSet_Ioi hpt]
  refine lintegral_ofReal_ne_top_of_integrableOn ?_ ?_
  · refine IntegrableOn.mono_set ?_ (Ioi_subset_Ioi zero_le_one)
    exact (integrableOn_rpow_mul_exp_neg_mul_rpow (s := (n : ℝ) - 1) (p := 1) (b := 1)
      (by simp only [neg_lt_sub_iff_lt_add, lt_add_iff_pos_right, Nat.cast_pos]; exact hn)
      le_rfl one_pos).const_mul _
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun x hx => ?_)
    have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
    positivity

end SpatialLine
