/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.Symbol
import SpatialLine.StableProfile
import SpatialLine.ChoquetExtreme

/-!
# The stable corner of the generator

Blueprint: `prop:corner-generators`(2). The clause reads `𝒜_t = -αt^{α-1}(-∂_x²)^{α/2}` and
Mathlib has no fractional Laplacian, so what is proved is the pair the clause is about and that
its own proof computes: the symbol `B(ω) = α|ω|^α` and the jump measure
`ϖ(dv) = C_α^{-1}α v^{-α-1}dv`. Together with the multiplier identity of `prop:scale-evolution`
those determine the operator; the operator name is what is missing, not the mathematics.

## What proving this found

**The symbol half is one differentiation, and the pure power is differentiable at every
frequency except the origin, where the identity still holds.** `mul_deriv_abs_rpow` is
`ω·(|·|^α)'(ω) = α|ω|^α` for every real `ω`, the three cases being the two half-lines, where
`Real.hasDerivAt_rpow_const` applies after a local rewrite of `|z|` to `±z`, and the origin,
where both sides are `0` — the left because of the factor `ω`, the right because `α > 0` makes
`0^α = 0`. So no puncture is needed in the statement, although the printed proof works off the
origin.

**The jump-measure half is not a computation of `-dk` but an identification of two measures by
their tails.** The clause's `ϖ` is quantified over `HasProfileTail (stableProfile α)`, which
pins the tails only almost everywhere on the half-line, so the route is chapter 8's pair
`tail_eq_of_ae_tail_eq` and `measure_eq_of_tail_eq` rather than any differentiation: the
candidate `stableJump α` is exhibited, its tail is evaluated by
`integral_Ioi_rpow_of_lt` — the exponent `-α-1 < -1` is where `α > 0` is spent — and the two
folded measures with equal tails on `(0,∞)`, one finite on every `Ioi x` with `x > 0`, are
equal. This is the same reading `prop:choquet-cone`'s injectivity clause needed and is why
those two lemmas were stated for arbitrary measures.
-/

namespace SpatialLine

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-! ## The symbol of the pure power -/
/-- `ω·(|·|^α)'(ω) = α|ω|^α` for every real `ω` and every `α > 0`, the origin included: both
sides vanish there, the left because of the factor `ω` and the right because `0^α = 0`. -/
theorem mul_deriv_abs_rpow {α : ℝ} (hα : 0 < α) (ω : ℝ) :
    ω * deriv (fun z : ℝ => |z| ^ α) ω = α * |ω| ^ α := by
  rcases lt_trichotomy ω 0 with hneg | rfl | hpos
  · have hev : (fun z : ℝ => |z| ^ α) =ᶠ[𝓝 ω] fun z : ℝ => (-z) ^ α := by
      filter_upwards [Iio_mem_nhds hneg] with z hz
      rw [abs_of_neg hz]
    have hd : HasDerivAt (fun z : ℝ => (-z) ^ α) (α * (-ω) ^ (α - 1) * (-1)) ω :=
      (Real.hasDerivAt_rpow_const (x := -ω) (p := α) (Or.inl (by linarith))).comp ω
        (hasDerivAt_neg ω)
    rw [hev.deriv_eq, hd.deriv, abs_of_neg hneg]
    have hpos' : (0:ℝ) < -ω := by linarith
    rw [show α * (-ω) ^ (α - 1) * (-1) = -(α * (-ω) ^ (α - 1)) by ring]
    have hstep : (-ω) ^ (α - 1) * (-ω) = (-ω) ^ α := by
      nth_rewrite 2 [← Real.rpow_one (-ω)]
      rw [← Real.rpow_add hpos']
      congr 1
      ring
    rw [← hstep]; ring
  · simp [Real.zero_rpow hα.ne']
  · have hev : (fun z : ℝ => |z| ^ α) =ᶠ[𝓝 ω] fun z : ℝ => z ^ α := by
      filter_upwards [Ioi_mem_nhds hpos] with z hz
      rw [abs_of_pos hz]
    have hd : HasDerivAt (fun z : ℝ => z ^ α) (α * ω ^ (α - 1)) ω :=
      Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hpos))
    rw [hev.deriv_eq, hd.deriv, abs_of_pos hpos]
    have hstep : ω ^ (α - 1) * ω = ω ^ α := by
      nth_rewrite 2 [← Real.rpow_one ω]
      rw [← Real.rpow_add hpos]
      congr 1
      ring
    rw [← hstep]; ring

/-- **`prop:corner-generators`(2), the symbol.** For the pure-power profile the symbol
`B(ω) = ωF'(ω)` of `eq:symbol` is `α|ω|^α`. -/
theorem corner_generator_stable_symbol (α : ℝ) (hα : 0 < α) (hα2 : α < 2) (ϖ : Measure ℝ)
    (hϖ : HasProfileTail (stableProfile α) ϖ) (ω : ℝ) :
    symbol 0 ϖ ω = α * |ω| ^ α := by
  have hQ : (stableDatum α hα hα2).k = stableProfile α := rfl
  have hϖ' : HasProfileTail (stableDatum α hα hα2).k ϖ := hϖ
  have hexp : (stableDatum α hα hα2).exponent = fun z : ℝ => |z| ^ α :=
    funext (stableDatum_exponent hα hα2)
  have h := sd_exponents_symbol (stableDatum α hα hα2) (stableDatum α hα hα2).exponent
    (fun _ => rfl) ϖ hϖ' ω
  rw [stableDatum_a] at h
  rw [symbol_apply, h, hexp, mul_deriv_abs_rpow hα ω]
  exact ENNReal.toReal_ofReal (by positivity)

/-! ## The jump measure -/
/-- The candidate jump measure of the stable corner, `C_α^{-1}α v^{-α-1}dv` on `(0,∞)`. -/
noncomputable def stableJump (α : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi (0 : ℝ))).withDensity
    fun v => ENNReal.ofReal ((stableConst α)⁻¹ * α * v ^ (-α - 1))

/-- `stableJump` is carried by the positive half-line. -/
theorem isFolded_stableJump (α : ℝ) : IsFolded (stableJump α) := by
  rw [IsFolded, stableJump, withDensity_apply _ measurableSet_Iic,
    Measure.restrict_restrict measurableSet_Iic]
  convert lintegral_zero_measure _
  rw [Measure.restrict_eq_zero]
  convert measure_empty (μ := (volume : Measure ℝ))
  ext z
  simp only [mem_inter_iff, mem_Iic, mem_Ioi, mem_empty_iff_false, iff_false, not_and, not_lt]
  exact fun h => h

/-- The tail of `stableJump α` at a positive point is the stable profile there. The exponent
`-α-1` is below `-1` exactly because `α > 0`, which is what makes the ray integrable. -/
theorem stableJump_tail {α : ℝ} (hα : 0 < α) (hα2 : α < 2) {y : ℝ} (hy : 0 < y) :
    stableJump α (Ioi y) = ENNReal.ofReal (stableProfile α y) := by
  have hlt : -α - 1 < -1 := by linarith
  have hC : 0 < stableConst α := stableConst_pos hα hα2
  rw [stableJump, withDensity_apply _ measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi]
  have hset : Ioi y ∩ Ioi (0 : ℝ) = Ioi y := by
    ext z; simp only [mem_inter_iff, mem_Ioi]; exact ⟨fun h => h.1, fun h => ⟨h, lt_trans hy h⟩⟩
  rw [hset]
  have hint : IntegrableOn (fun v : ℝ => (stableConst α)⁻¹ * α * v ^ (-α - 1)) (Ioi y) :=
    (integrableOn_Ioi_rpow_of_lt hlt hy).const_mul _
  have hnn : ∀ᵐ v ∂(volume.restrict (Ioi y)),
      0 ≤ (stableConst α)⁻¹ * α * v ^ (-α - 1) := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun v hv => ?_)
    have hv0 : (0 : ℝ) < v := lt_trans hy hv
    positivity
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
  congr 1
  rw [integral_const_mul, integral_Ioi_rpow_of_lt hlt hy, stableProfile_of_pos hy]
  have : -α - 1 + 1 = -α := by ring
  rw [this]
  field_simp

/-- **`prop:corner-generators`(2), the jump measure.** A folded measure whose tails are the
stable profile almost everywhere on `(0,∞)` *is* `stableJump α`. The identification runs on
`tail_eq_of_ae_tail_eq` and `measure_eq_of_tail_eq`, not on a differentiation of `k`. -/
theorem stable_jump_measure {α : ℝ} (hα : 0 < α) (hα2 : α < 2) (ϖ : Measure ℝ)
    (hϖ : HasProfileTail (stableProfile α) ϖ) : ϖ = stableJump α := by
  refine measure_eq_of_tail_eq hϖ.1 (isFolded_stableJump α)
    (fun x hx => measure_Ioi_ne_top hϖ hx) (fun x hx => ?_)
  refine tail_eq_of_ae_tail_eq ?_ hx
  have hpos : ∀ᵐ y ∂(volume.restrict (Ioi (0 : ℝ))), (0 : ℝ) < y :=
    (ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun y hy => hy)
  filter_upwards [hϖ.2, hpos] with y hy hy0
  rw [hy, stableJump_tail hα hα2 hy0]

/-! ## The node's clause -/

/-- **`prop:corner-generators`(2), symmetric stable.** The symbol is `α|ω|^α` and the jump
measure is `C_α^{-1}α v^{-α-1}dv` on the positive half-line.

`Skeleton.corner_generator_stable`'s type verbatim; the two conjuncts are
`corner_generator_stable_symbol` and `stable_jump_measure`, and the second is stated there
against the abbreviation `stableJump`, which unfolds to the density written here. -/
theorem corner_generator_stable (α : ℝ) (hα : 0 < α) (hα2 : α < 2) (ϖ : Measure ℝ)
    (hϖ : HasProfileTail (stableProfile α) ϖ) :
    (∀ ω : ℝ, symbol 0 ϖ ω = α * |ω| ^ α) ∧
      ϖ = (volume.restrict (Ioi (0 : ℝ))).withDensity
        fun v => ENNReal.ofReal ((stableConst α)⁻¹ * α * v ^ (-α - 1)) :=
  ⟨corner_generator_stable_symbol α hα hα2 ϖ hϖ, stable_jump_measure hα hα2 ϖ hϖ⟩

end SpatialLine
