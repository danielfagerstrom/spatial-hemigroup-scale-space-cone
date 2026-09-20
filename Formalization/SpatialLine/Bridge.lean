/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.ConeDefs
import SpatialLine.BrownianDensity
import ScaleSpaceCore.CausalCone
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Measure.GiryMonad

/-!
# The causal side of the bridge: `def:causal-admissible` and the Brownian laws

Blueprint: `blueprint/src/parts/09-bridge.tex` — `def:causal-admissible` is the one blueprint
node in this file, and it is a definition.

## `CausalAdmissible` is imported, not restated

**The import happened** (2026-09-12). The causal admissible cone is
`ScaleSpace.CausalAdmissible` in `ScaleSpaceCore/CausalCone.lean`, together with its
exponent, the cone constructions and the causal data; `TWINS.md` marks
`def:causal-admissible` class **(a)** with the instruction *import, do not restate* — "the
one place where the two developments must share a *type*, not just a theorem". Until the
shared type existed this file carried a local mirror of Paper I's
`Hemigroup.SelfDecomposableExponent`; what stands here now is the `export` that keeps the
spatial names reading as before, and the Brownian laws.

The field layout is Paper I's — `b₀`, `k`, `b₀_nonneg`, `k_nonneg`, `k_antitone`, `k_zero`
— and the last field is the blueprint's **two integrability conditions**
`∫₀¹ k_I(u)\,du < ∞` and `∫₁^∞ k_I(u)\,u^{-1}du < ∞`, which are what
`def:causal-admissible` says, rather than Paper I's equivalent single `ne_top`. The core
carries that equivalence as `ne_top_iff_windows`, with `ofNeTop` as the constructor from
Paper I's side. Note the weight: the causal condition is `∫₀¹ k_I`, where the spatial
`SDProfile.integrable_near_zero` is `∫₀¹ x\,k(x)\,dx`, because the Fourier weight
`1 ∧ x²` replaces the Laplace weight `1 ∧ x`. That difference is exactly what
`lem:bridge-exponents` has to absorb.

With that layout `lem:bridge-exponents` is a function between two structures with parallel
fields: `a = b₀/2` and the profile of `eq:bridge-profile`, with no reshaping.

## The Brownian laws

`brownianLaw` and `brownianDensity` stood here until 2026-09-14 and are now in
`SpatialLine/BrownianDensity.lean`, together with the elementary facts about them, so that the
Matérn corner's Gamma mixture can read them without importing the causal cone (ADR-0005). The
import above re-exports them, so every consumer of this file reads them as before.
-/

namespace SpatialLine

open MeasureTheory Set
open scoped ENNReal

/-! ## `def:causal-admissible`

The node's type is `ScaleSpace.CausalAdmissible` (`ScaleSpaceCore/CausalCone.lean`), with
the causal exponent `exponentL` in `ℝ≥0∞` and its real form `exponent`. The exports below
let the spatial development read all three unqualified, and make
`SpatialLine.CausalAdmissible` and `SpatialLine.CausalAdmissible.exponent` resolve by
elaboration, which is what the blueprint's `\lean{}` tags still name.

twin: `exponentL` is `Hemigroup.levyExponentD F.b₀ F.k`, verbatim.
-/

export ScaleSpace (CausalAdmissible)

namespace CausalAdmissible

export ScaleSpace.CausalAdmissible (exponent exponentL)

end CausalAdmissible

/-- **`prop:bridge-strictness`'s subordinated exponents**: those of the form
`F(ω) = F_I(ω²/2)` for a causally admissible `F_I`.

A predicate on the exponent, not on the family, which is how clauses (1), (3) and (4) of that
node read it. -/
def IsSubordinated (F : ℝ → ℝ) : Prop :=
  ∃ FI : CausalAdmissible, ∀ ω : ℝ, F ω = FI.exponent (ω ^ 2 / 2)

end SpatialLine
