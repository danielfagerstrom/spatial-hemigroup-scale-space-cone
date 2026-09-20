/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.Bridge
import SpatialLine.SemigroupCase
import SpatialLine.Corners

/-!
# `prop:bridge-families`, the corners

Blueprint: `blueprint/src/parts/09-bridge.tex` — clauses (1)–(4) of `prop:bridge-families`, the
four causal families and their images. The family clause itself is in
`Skeleton/Chapter9.lean`; what is here is the identification of the images, which the blueprint
does as four computations on exponents and densities.

## `brownianLaw` is a measurable family

Every clause that mixes Gaussian laws against a delay law is a `Measure.bind`, and every
`Measure.bind` lemma in Mathlib asks for the kernel to be measurable. `measurable_brownianLaw`
is that fact once: `brownianLaw` is `gaussianReal 0 (·).toNNReal`, and Mathlib's
`ProbabilityTheory.measurable_gaussianReal` gives the uncurried Gaussian family. It stood here
until 2026-09-14, on the ground that this file was its first consumer; it is now in
`SpatialLine/BrownianDensity.lean` beside the wrappers, the Matérn corner's Gamma mixture
having become a second consumer that must not import the causal bridge (ADR-0005).
-/

namespace SpatialLine

open MeasureTheory Set
open scoped ENNReal

/-! ## `prop:bridge-families`(1), the pure delay -/

/-- **`prop:bridge-families`(1), the pure delay maps to the Gaussian family.**

`Skeleton.bridge_families_delay`'s statement verbatim.

The kernel clause is `Measure.dirac_bind` at the measurable family `brownianLaw`: mixing the
Gaussian laws against the point mass at `v` returns `g_v`. The ray clause exhibits the
`SDProfile` with zero profile, `gaussianDatum (b₀/2)`, whose exponent is `(b₀/2)ω²`.

The kernel clause does not consume `0 ≤ v`. `brownianLaw` is total, `g_u` being `δ₀` for
`u ≤ 0` by the `toNNReal` in its definition, so `Measure.dirac_bind` applies at every real `v`;
the hypothesis is the node's range and is carried because the statement is the node's. -/
theorem bridge_families_delay :
    (∀ v : ℝ, 0 ≤ v → (Measure.dirac v).bind brownianLaw = brownianLaw v) ∧
      ∀ b₀ : ℝ, 0 ≤ b₀ → ∃ Q : SDProfile, Q.a = b₀ / 2 ∧ Q.k = 0 ∧
        ∀ ω : ℝ, Q.exponent ω = b₀ * ω ^ 2 / 2 := by
  refine ⟨fun v _ => Measure.dirac_bind measurable_brownianLaw v, fun b₀ hb => ?_⟩
  refine ⟨gaussianDatum (b₀ / 2) (by linarith), rfl, rfl, fun ω => ?_⟩
  rw [gaussianDatum_exponent]
  ring

/-! ## `prop:bridge-families`(4), the stable index doubles -/

set_option linter.unusedVariables false in
/-- **`prop:bridge-families`(4), the causal stable family maps to the symmetric stable family
of twice the index.**

`Skeleton.bridge_families_stable`'s statement verbatim. `(ω²/2)^α = 2^{-α}|ω|^{2α}`, the whole
of the clause at the level of exponents.

**The two hypotheses are carried unused, and that is the finding.** The identity is an `rpow`
computation valid for every real `α`: `ω² = |ω|²`, the quotient rule for `rpow` on a
nonnegative base, and `(|ω|²)^α = |ω|^{2α}`. Neither `0 < α` nor `α ≤ 1` enters. They belong to
the *node*, where they cut out the range in which `σ ↦ σ^α` is causally admissible and in which
the image index `2α` lands in `(0,2]`; the arithmetic of the substitution knows nothing about
either. The statement is the node's and is left as it is; the linter is silenced, as at
`representation_symmetric`. -/
theorem bridge_families_stable (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ∀ ω : ℝ, ((ω ^ 2 / 2) ^ α : ℝ) = 2 ^ (-α) * |ω| ^ (2 * α) := by
  intro ω
  have h0 : (0 : ℝ) ≤ |ω| := abs_nonneg ω
  have hω : ω ^ 2 = |ω| ^ (2 : ℕ) := (sq_abs ω).symm
  rw [hω, Real.div_rpow (by positivity) (by norm_num : (0 : ℝ) ≤ 2),
    ← Real.rpow_natCast |ω| 2, ← Real.rpow_mul h0,
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  push_cast
  ring

end SpatialLine
