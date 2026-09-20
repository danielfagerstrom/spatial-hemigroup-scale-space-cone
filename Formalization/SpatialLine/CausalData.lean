/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.Strictness
import SpatialLine.BridgeGamma
import SpatialLine.BridgeCorners
import ScaleSpaceCore.CausalData
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Three causally admissible data, and `lem:subordinated-members`

Blueprint: `blueprint/src/parts/09-bridge.tex` — `lem:subordinated-members` (row R121). The
constructions here are not blueprint nodes; they are the witnesses that node's proof needs.

`IsSubordinated` is an existential over `CausalAdmissible`, and the data that witness it
are `ScaleSpaceCore/CausalData.lean`'s, one generator per family:

* `driftDatum b₀`, the data `(b₀, 0)`, with exponent `σ ↦ b₀σ` on `[0,∞)`;
* `gammaCausalDatum γ`, the data `(0, γe^{-u})`, whose image `bridge_families_gamma`
  computes;
* `stableCausalDatum α`, `0 < α < 1`, the data `(0, c_α u^{-α})` with `c_α = α/Γ(1-α)`,
  with exponent `σ ↦ σ^α` on `[0,∞)`.

All three were Paper V's until the causal cone moved to `ScaleSpaceCore` (2026-09-12);
what stays here is the node they were built for.

## What proving this found

**The families close at general parameters under the cone clauses, as the printed proof
says.** The Matérn range `θ` is a spatial dilation by `√2θ` of the range `1/√2` that the
Gamma datum produces, and the stable index `α ∈ (0,2)` is the causal index `α/2 ∈ (0,1)`
times the constant `2^{α/2}`, both through `bridge_strictness_cone`.
-/

namespace SpatialLine

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-! ## `lem:subordinated-members` -/

open ScaleSpace.CausalAdmissible in
/-- **`lem:subordinated-members`** — the subordinated slice `S` of `prop:bridge-strictness`
contains the Gaussian ray (`a ≥ 0`), the Matérn family (`γ, θ > 0`) and the symmetric stable
family (`0 < α < 2`).

`Skeleton.subordinated_members`'s first, second and fourth conjuncts, verbatim; the Student-t
conjunct was split out (R121) as `lem:student-subordinated`, and is proved in
`SpatialLine/StudentThorin.lean` since 2026-09-15 (R160), with the causally admissible datum of
the inverse-gamma delay law — what ledger A18 grounds — as a hypothesis rather than an admitted
interface.

The Gaussian member is the drift datum `(2a, 0)` directly. The Matérn member at range `θ` is the
spatial dilation by `√2θ` of the image of the Gamma datum, which `bridge_families_gamma`
identifies as the Matérn exponent at range `1/√2`. The stable member of index `α` is `2^{α/2}`
times the image of the causal stable datum of index `α/2`, which `bridge_families_stable`
identifies as `2^{-α/2}|ω|^α`. Dilation and multiple are clauses of `bridge_strictness_cone`. -/
theorem subordinated_members :
    (∀ a : ℝ, 0 ≤ a → IsSubordinated fun ω => a * ω ^ 2) ∧
      (∀ γ θ : ℝ, 0 < γ → 0 < θ → IsSubordinated (maternExponent γ θ)) ∧
        (∀ α : ℝ, 0 < α → α < 2 → IsSubordinated fun ω => |ω| ^ α) := by
  refine ⟨fun a ha => ?_, fun γ θ hγ hθ => ?_, fun α hα hα2 => ?_⟩
  · refine ⟨driftDatum (2 * a) (by positivity), fun ω => ?_⟩
    rw [driftDatum_exponent _ (by positivity)]
    ring
  · have hG : IsSubordinated (maternExponent γ (Real.sqrt 2)⁻¹) :=
      ⟨gammaCausalDatum γ hγ.le, fun ω =>
        ((bridge_families_gamma γ hγ _ (fun u hu => gammaCausalDatum_k hγ.le hu) rfl).1 ω).symm⟩
    have hD := bridge_strictness_cone.2.2.1 _ (Real.sqrt 2 * θ) (by positivity) hG
    convert hD using 1
    funext ω
    have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hs : Real.sqrt 2 ≠ 0 := by positivity
    simp only [maternExponent]
    congr 3
    rw [mul_pow, mul_pow, inv_pow, h2]
    field_simp
  · have hβ : 0 < α / 2 := by linarith
    have hβ1 : α / 2 < 1 := by linarith
    have hS : IsSubordinated fun ω => (2 : ℝ) ^ (-(α / 2)) * |ω| ^ (2 * (α / 2)) :=
      ⟨stableCausalDatum (α / 2) hβ hβ1, fun ω => by
        rw [stableCausalDatum_exponent hβ hβ1 (by positivity),
          bridge_families_stable (α / 2) hβ hβ1.le ω]⟩
    have hM := bridge_strictness_cone.2.1 _ ((2 : ℝ) ^ (α / 2)) (by positivity) hS
    convert hM using 1
    funext ω
    rw [← mul_assoc, ← Real.rpow_add two_pos, add_neg_cancel, Real.rpow_zero, one_mul,
      show 2 * (α / 2) = α by ring]

end SpatialLine
