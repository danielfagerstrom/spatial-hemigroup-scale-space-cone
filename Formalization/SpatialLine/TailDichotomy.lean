/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.Interfaces
import SpatialLine.SelfDecomposable

/-!
# The tail dichotomy, the `[T]` half

Blueprint: the last sentence of `prop:moments-tails`(2) — a completely monotone profile that is
not identically zero vanishes beyond no `τ`, so the whole Thorin subclass is on the heavy side;
and a nonzero catalogue makes every Gaussian moment infinite, so no kernel other than the
Gaussians has a Gaussian or lighter tail.

The cited half is ledger **A14**, admitted in `SpatialLine/Interfaces.lean` as
`moments_tails_divergence` and **narrowed**, the skeleton's `moments_tails_bounded` having been
false as typed; the docstring there says what happened and the node carries the
`% CHANGED (proof 2026-09-10)` marker.

## What proving this found

**The Gaussian comparison is a square-root trick and nothing more.** The step the blueprint
calls "the comparison of the two regimes" is: `α'|x|log|x| ≤ αx²` once `|x|` is large. It is
`log y = 2 log √y ≤ 2(√y - 1) ≤ 2√y`, which turns the claim into `2α' ≤ α√y`, true beyond
`(2α'/α)²`. The passage from the pointwise comparison to the integrals is a split at that
radius: the law is a probability measure, so the inner piece is bounded by one constant times
one, and the divergence therefore lives on the outer piece, where the comparison holds. No
asymptotics and no truncation argument.

**One `τ` suffices, and the case split the node's proof makes is avoidable.** The printed proof
distinguishes a bounded catalogue (where A14's floor `exp(-|x|log|x|/(τt))` supplies the
divergence) from an unbounded one (where the heavy branch does). Read at the Lean statement
there is no distinction to make: the narrowed axiom takes *any* `τ` at or beyond which the
profile is nonzero, and the hypothesis `∃ x, 0 < x ∧ P.k x ≠ 0` hands one over directly. The
bounded/unbounded split is a fact about which thresholds are available, not about which argument
is used.

**The first clause is Bernstein's theorem and the strict positivity of an exponential.** A
completely monotone `k` is `∫e^{-θx}U(dθ)` (ledger **A11**); if `k` vanished at one positive
point the transform would vanish there, and the integrand being strictly positive that forces
`U = 0`, hence `k ≡ 0` on the half-line. So a nonzero completely monotone profile is nonzero at
*every* positive point, which is more than the clause asks for.
-/

namespace SpatialLine

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-! ## Two elementary comparisons -/

/-- `y ↦ y log y` is dominated by its value at the right endpoint on `[0,R]`, for `R ≥ 1`: below
`1` the product is nonpositive, above it both factors are nondecreasing. -/
theorem abs_mul_log_le {R x : ℝ} (hR : 1 ≤ R) (hx : |x| ≤ R) :
    |x| * Real.log |x| ≤ R * Real.log R := by
  have hR0 : (0:ℝ) < R := lt_of_lt_of_le zero_lt_one hR
  have hRlog : 0 ≤ Real.log R := Real.log_nonneg hR
  rcases le_or_gt |x| 1 with h1 | h1
  · have : |x| * Real.log |x| ≤ 0 := by
      rcases eq_or_lt_of_le (abs_nonneg x) with h0 | h0
      · rw [← h0]; simp
      · exact mul_nonpos_of_nonneg_of_nonpos (abs_nonneg x) (Real.log_nonpos (abs_nonneg x) h1)
    exact this.trans (by positivity)
  · have hlog : Real.log |x| ≤ Real.log R := Real.log_le_log (by linarith) hx
    have hlognn : 0 ≤ Real.log |x| := Real.log_nonneg h1.le
    exact mul_le_mul hx hlog hlognn hR0.le

/-- **The Gaussian comparison.** `b|x|log|x| ≤ ax²` once `|x| ≥ (2b/a)²`, by
`log y = 2 log √y ≤ 2(√y - 1) ≤ 2√y`. -/
theorem mul_log_le_sq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {x : ℝ}
    (hx1 : 1 ≤ |x|) (hx : (2 * b / a) ^ 2 ≤ |x|) :
    b * (|x| * Real.log |x|) ≤ a * x ^ 2 := by
  set y : ℝ := |x| with hy
  have hy0 : (0:ℝ) < y := lt_of_lt_of_le zero_lt_one hx1
  have hs : Real.sqrt y * Real.sqrt y = y := Real.mul_self_sqrt hy0.le
  have hsq : 2 * b / a ≤ Real.sqrt y := by
    have hnn : (0:ℝ) ≤ 2 * b / a := by positivity
    exact (Real.le_sqrt hnn hy0.le).mpr hx
  have hlog : Real.log y ≤ 2 * Real.sqrt y := by
    have h1 : Real.log (Real.sqrt y) ≤ Real.sqrt y - 1 :=
      Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hy0)
    have h2 : Real.log (Real.sqrt y) = Real.log y / 2 := Real.log_sqrt hy0.le
    rw [h2] at h1
    have : Real.sqrt y ≥ 0 := Real.sqrt_nonneg y
    linarith
  have hstep : b * (y * Real.log y) ≤ b * (y * (2 * Real.sqrt y)) := by
    have := mul_le_mul_of_nonneg_left hlog hy0.le
    exact mul_le_mul_of_nonneg_left this hb.le
  refine hstep.trans ?_
  have hxy : x ^ 2 = y * y := by rw [hy, ← sq_abs]; ring
  rw [hxy]
  have key : 2 * b ≤ a * Real.sqrt y := by
    have h := mul_le_mul_of_nonneg_left hsq ha.le
    have he : a * (2 * b / a) = 2 * b := by field_simp
    rw [he] at h
    exact h
  calc b * (y * (2 * Real.sqrt y)) = (2 * b) * (y * Real.sqrt y) := by ring
    _ ≤ (a * Real.sqrt y) * (y * Real.sqrt y) := by
        exact mul_le_mul_of_nonneg_right key (by positivity)
    _ = a * (y * (Real.sqrt y * Real.sqrt y)) := by ring
    _ = a * (y * y) := by rw [hs]

/-- **From a divergent `exp(b|x|log|x|)` moment to a divergent Gaussian moment.** The law being
a probability measure, the contribution of `{|x| < R}` is finite for every `R`, so the
divergence lives beyond `R`; choosing `R` past `(2b/a)²` the comparison applies there. -/
theorem lintegral_exp_sq_eq_top {μ : Measure ℝ} [IsProbabilityMeasure μ] {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (h : ∫⁻ x, ENNReal.ofReal (Real.exp (b * |x| * Real.log |x|)) ∂μ = ⊤) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (a * x ^ 2)) ∂μ = ⊤ := by
  set R : ℝ := max 1 ((2 * b / a) ^ 2) with hR
  have hR1 : (1:ℝ) ≤ R := le_max_left _ _
  have hR2 : (2 * b / a) ^ 2 ≤ R := le_max_right _ _
  set f : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (Real.exp (b * |x| * Real.log |x|)) with hf
  set A : Set ℝ := {x : ℝ | R ≤ |x|} with hA
  have hAm : MeasurableSet A := measurableSet_le measurable_const measurable_id.abs
  have hsplit : (∫⁻ x in A, f x ∂μ) + ∫⁻ x in Aᶜ, f x ∂μ = ∫⁻ x, f x ∂μ :=
    lintegral_add_compl f hAm
  set M : ℝ := Real.exp (b * (R * Real.log R)) with hM
  have hcompl : (∫⁻ x in Aᶜ, f x ∂μ) ≤ ENNReal.ofReal M := by
    have hbd : ∀ x ∈ Aᶜ, f x ≤ ENNReal.ofReal M := by
      intro x hx
      have hxlt : |x| ≤ R := le_of_lt (by simpa [hA, not_le] using hx)
      refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (abs_mul_log_le hR1 hxlt) hb.le
    calc (∫⁻ x in Aᶜ, f x ∂μ) ≤ ∫⁻ _ in Aᶜ, ENNReal.ofReal M ∂μ :=
          setLIntegral_mono' hAm.compl hbd
      _ = ENNReal.ofReal M * μ Aᶜ := by rw [setLIntegral_const]
      _ ≤ ENNReal.ofReal M * 1 := by
          gcongr
          exact le_trans (measure_mono (subset_univ _)) (le_of_eq measure_univ)
      _ = ENNReal.ofReal M := mul_one _
  have hAtop : (∫⁻ x in A, f x ∂μ) = ⊤ := by
    by_contra hcon
    rw [h] at hsplit
    exact (ENNReal.add_ne_top.mpr ⟨hcon, ne_top_of_le_ne_top ENNReal.ofReal_ne_top hcompl⟩) hsplit
  refine eq_top_iff.mpr ?_
  calc (⊤ : ℝ≥0∞) = ∫⁻ x in A, f x ∂μ := hAtop.symm
    _ ≤ ∫⁻ x in A, ENNReal.ofReal (Real.exp (a * x ^ 2)) ∂μ := by
        refine setLIntegral_mono' hAm (fun x hx => ?_)
        have hx1 : (1:ℝ) ≤ |x| := le_trans hR1 hx
        have hx2 : (2 * b / a) ^ 2 ≤ |x| := le_trans hR2 hx
        refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
        rw [mul_assoc]
        exact mul_log_le_sq ha hb hx1 hx2
    _ ≤ ∫⁻ x, ENNReal.ofReal (Real.exp (a * x ^ 2)) ∂μ :=
        setLIntegral_le_lintegral _ _

/-- **`prop:moments-tails`(2), the first claim.** A completely monotone profile that is nonzero
somewhere on the half-line is nonzero at *every* positive point, so it vanishes beyond no `τ`.
Ledger **A11**. -/
theorem completely_monotone_support_unbounded {k : ℝ → ℝ} (hcm : IsCompletelyMonotone k)
    (hne : ∃ x : ℝ, 0 < x ∧ k x ≠ 0) : ∀ τ : ℝ, 0 < τ → ∃ x : ℝ, τ ≤ x ∧ k x ≠ 0 := by
  obtain ⟨x₀, hx₀, hkx₀⟩ := hne
  obtain ⟨U, _, hUx⟩ := (bernstein_completely_monotone k).mp hcm
  intro τ hτ
  refine ⟨τ, le_rfl, fun hkτ => ?_⟩
  have h1 := hUx τ hτ
  have hzero : laplaceL U τ = 0 := by
    have h2 := h1.2
    rw [hkτ] at h2
    exact ((ENNReal.toReal_eq_zero_iff _).mp h2.symm).resolve_right h1.1
  have huniv : U Set.univ = 0 := by
    rw [laplaceL_apply, lintegral_eq_zero_iff (by fun_prop)] at hzero
    rw [Filter.EventuallyEq, ae_iff] at hzero
    refine measure_mono_null (fun u _ => ?_) hzero
    simp [ENNReal.ofReal_eq_zero, not_le, Real.exp_pos]
  have hU0 : U = 0 := Measure.measure_univ_eq_zero.mp huniv
  have hk0 := (hUx x₀ hx₀).2
  rw [hU0] at hk0
  rw [laplaceL_apply, lintegral_zero_measure, ENNReal.toReal_zero] at hk0
  exact hkx₀ hk0

/-- **`prop:moments-tails`(2), the last sentence.** `Skeleton.moments_tails_completely_monotone`'s
type verbatim.

The first clause is ledger **A11**, the second ledger **A14** at its divergence branch; the
comparison of the two regimes is `[T]` and is `lintegral_exp_sq_eq_top`. -/
theorem moments_tails_completely_monotone (P : SDProfile) (μ : ℝ → Measure ℝ)
    (hprob : ∀ t : ℝ, 0 < t → IsProbabilityMeasure (μ t))
    (hcos : ∀ t ω : ℝ, 0 < t → fourierCos (μ t) ω = Real.exp (-P.exponent (t * ω))) :
    (IsCompletelyMonotone P.k → (∃ x : ℝ, 0 < x ∧ P.k x ≠ 0) →
        ∀ τ : ℝ, 0 < τ → ∃ x : ℝ, τ ≤ x ∧ P.k x ≠ 0) ∧
      ((∃ x : ℝ, 0 < x ∧ P.k x ≠ 0) → ∀ t : ℝ, 0 < t → ∀ α : ℝ, 0 < α →
        ∫⁻ x, ENNReal.ofReal (Real.exp (α * x ^ 2)) ∂(μ t) = ⊤) := by
  refine ⟨fun hcm hne => completely_monotone_support_unbounded hcm hne, ?_⟩
  rintro ⟨x₀, hx₀, hkx₀⟩ t ht α hα
  haveI := hprob t ht
  have hbpos : 0 < (x₀ * t)⁻¹ + 1 := by positivity
  have hlt : (x₀ * t)⁻¹ < (x₀ * t)⁻¹ + 1 := by linarith
  exact lintegral_exp_sq_eq_top hα hbpos
    (moments_tails_divergence P μ hprob hcos ht hx₀ ⟨x₀, le_rfl, hkx₀⟩ hlt)

end SpatialLine
