/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.Frullani
import SpatialLine.SemigroupCase

/-!
# `prop:stable-family`: the bridge image and the Gaussian endpoint

Blueprint: `blueprint/src/parts/10-corners.tex`, `prop:stable-family`, the closing clauses.

twin: Paper I's `prop:stable-family` (`Hemigroup.SelfDecomposableExponent.stableExponent`), at
index `α/2` where this one has `α` — the bridge halves the index.

## The Gaussian datum

`gaussianDatum a` -- the `SDProfile` with Gaussian coefficient `a` and zero profile, whose
exponent is `aω²` -- is the witness of the `α = 2` endpoint here **and** of
`cor:semigroup-case`'s Gaussian clause in chapter 7. The two chapters wrote it twice, and wave
2's merge (2026-09-09) kept the copy in `SpatialLine/SemigroupCase.lean`, the file of the node
it belongs to, on wave 1's deduplication rule; this file imports it. It is not in
`Corners.lean` for the reason recorded there: a corner's admissibility is the *content* of a
node, so the witness belongs in the file that proves one (SKELETON.md, F12).
-/

namespace SpatialLine

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-- **`prop:stable-family`, the bridge image and the Gaussian endpoint.**

The first clause is the arithmetic of the bridge: the causal stable exponent of index `α/2`,
read at `σ = ω²/2`, is `2^{-α/2}|ω|^α`. The second exhibits the Gaussian ray as the `α = 2`
endpoint, with `k ≡ 0` and `a = 1`. -/
theorem stable_family_bridge (α : ℝ) (hα : 0 < α) (hα2 : α < 2) :
    (∀ ω : ℝ, ((ω ^ 2 / 2) ^ (α / 2) : ℝ) = 2 ^ (-α / 2) * |ω| ^ α) ∧
      ∃ Q : SDProfile, Q.a = 1 ∧ Q.k = 0 ∧ ∀ ω : ℝ, Q.exponent ω = ω ^ 2 := by
  refine ⟨fun ω => ?_, ⟨gaussianDatum 1 zero_le_one, rfl, rfl, fun ω => ?_⟩⟩
  · rw [show ω ^ 2 = |ω| ^ (2:ℕ) from (sq_abs ω).symm,
      Real.div_rpow (by positivity) (by norm_num),
      ← Real.rpow_natCast |ω| 2, ← Real.rpow_mul (abs_nonneg ω)]
    norm_num
    rw [show (2:ℝ) * (α / 2) = α by ring, show (-α / 2 : ℝ) = -(α / 2) by ring,
      Real.rpow_neg (by norm_num)]
    ring
  · rw [gaussianDatum_exponent, one_mul]

end SpatialLine
