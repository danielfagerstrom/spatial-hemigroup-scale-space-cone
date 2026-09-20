/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.Transform
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# The two-sided profile, and ledger A10 at Sato's letter: the definitions

Blueprint: `blueprint/src/parts/08-cone.tex` — `lem:folding-translation`,
`prop:cin-origin-singularity`, `cor:origin-boundedness`.

**This file holds the vocabulary the axioms are stated over** — the definitions and one `rfl`
lemma unfolding `satoK` — and it exists for one reason: `SpatialLine/Interfaces.lean`
is the only file of the library that declares axioms, and the three axioms of ledger **A10**
(admitted 2026-09-15, the author's decision) are stated over the vocabulary below. Putting that
vocabulary in `SpatialLine/TwoSidedProfile.lean`, where it was written on 2026-09-15, would make
`Interfaces` import a chapter 8 *theorem* module and so pull chapter 8 into the release closure of
the line paper, whose modules are chapters 2–7. Splitting the definitions out keeps the closure a
closure of definitions, which is the arrangement R158 settled for `CornerDefs`, `VariationDefs`
and `ConeDefs` (`Formalization/SKELETON.md` § 22).

`TwoSidedProfile` is the source's datum — the `k`-function of a self-decomposable law on the
punctured line, in the two-sided convention every probabilistic source states its results in —
and `SatoOriginSingular`, `SatoOriginSmooth`, `SatoOriginThreshold` are ledger A10's three regimes
typed at that letter. The translation into this article's folded convention is
`lem:folding-translation`, proved beside the interface in `SpatialLine/TwoSidedProfile.lean` and
*not* carried by the axioms; the three theorems that carry the axioms across it are
`SpatialLine/OriginSingularity.lean`.
-/

namespace SpatialLine

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-! ## The source's datum -/

/-- **Sato's `k`-function datum**: the two-sided profile of a self-decomposable law with no
Gaussian part, whose Lévy measure is `k(x)|x|⁻¹dx` on `ℝ \ {0}`.

The fields are the source's hypotheses: `k ≥ 0`, nonincreasing on `(0,∞)`, nondecreasing on
`(−∞,0)`, and the Lévy condition `∫(1 ∧ x²)k(x)|x|⁻¹dx < ∞`. The last is load-bearing and not
decoration: without it the exponent can be infinite at some frequency, where the real-valued
`exponent` returns `0`, and a specification stated through the exponent would then be met by laws
the source says nothing about. -/
structure TwoSidedProfile where
  /-- The two-sided profile, a density against `dx/|x|` on `ℝ \ {0}`. -/
  k : ℝ → ℝ
  k_nonneg : ∀ x, 0 ≤ k x
  k_antitoneOn : AntitoneOn k (Ioi (0 : ℝ))
  k_monotoneOn : MonotoneOn k (Iio (0 : ℝ))
  /-- Sato's Lévy condition on `k(x)|x|⁻¹dx`. -/
  levy_condition : (∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2) * k x / |x|)) ≠ ⊤

namespace TwoSidedProfile

/-- The two-sided exponent `∫_ℝ(1 − cos ωx)k(x)|x|⁻¹dx`, `ℝ≥0∞`-valued. -/
noncomputable def exponentL (K : TwoSidedProfile) (ω : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal ((1 - Real.cos (ω * x)) * K.k x / |x|)

/-- The real-valued two-sided exponent. -/
noncomputable def exponent (K : TwoSidedProfile) (ω : ℝ) : ℝ := (K.exponentL ω).toReal

end TwoSidedProfile

/-! ## The source's slowly varying factor

Sato's (53.25) is `K(x) = exp[∫_{|x|}^1 (c − k(y) − k(−y)) dy/y]`, and it enters **both** of
Thm. 53.8's comparison functions: (53.28)'s `x^{c−1}K(x)` below the threshold and, through
(53.26)'s `L(x) = ∫_{|x|}^1 K(y) dy/y`, the threshold's own. Until 2026-09-19 it was written out
inline in `SatoOriginThreshold` and **omitted altogether** from `SatoOriginSingular`, which made
that axiom false (R171; the referee's profile `k(x) = ½ − 1/log(1/x)` on `(0,e^{-4})` has
`c = ½` and kernel of order `|x|^{-1/2}log(1/|x|)`, which no multiple of `|x|^{-1/2}` dominates).
It is one definition now, used by both regimes. -/

/-- **Sato's slowly varying factor `K`** ((53.25), @sato1999levy p. 410), with its lower limit
given directly rather than as `|x|`: `satoK c y = exp[∫_y^1 (c − k(u) − k(−u)) du/u]`. The
consumers apply it at `y = |x|`, which is the source's reading.

The integral is a genuine one and not `integral`'s junk value on a non-integrable integrand:
`TwoSidedProfile.integrableOn_satoIntegrand` (`SpatialLine/TwoSidedProfile.lean`) proves the
integrand integrable on `Ioo y 1` for every `y > 0`, from the monotone pieces of the profile.
That matters because a junk `0` would give `satoK = 1` identically and return the singular regime
to the false comparison it had before R171. -/
noncomputable def TwoSidedProfile.satoK (K : TwoSidedProfile) (c y : ℝ) : ℝ :=
  Real.exp (∫ u in Ioo y 1, (c - (K.k u + K.k (-u))) / u)

theorem TwoSidedProfile.satoK_apply (K : TwoSidedProfile) (c y : ℝ) :
    K.satoK c y = Real.exp (∫ u in Ioo y 1, (c - (K.k u + K.k (-u))) / u) := rfl

/-! ## Ledger A10 at the source's letter, as specifications

The three `Prop`s below are the *types* of the three axioms admitted in
`SpatialLine/Interfaces.lean`. They are written here rather than there so that the statements and
the admission can be read apart: what is on the trust boundary is a name of `Interfaces`, and what
is here is the sentence of Sato it names. Each is quantified over a `TwoSidedProfile`, with the
source's constant `c = k(0+) + k(0−)` appearing as the sum of the two one-sided limits, with the
source's hypothesis that **both** one-sided limits are positive, and with the comparison functions
written in `k₂(u) + k₂(−u)` as the source writes them. -/

/-- **A10's singular regime, at Sato's letter** (@sato1999levy Thm. 53.8 with (53.28),
pp. 410–411). A self-decomposable law with no Gaussian part, given through its two-sided profile,
whose one-sided limits `k(0+)`, `k(0−)` are positive and whose constant `c = k(0+) + k(0−)` is
below `1`, has a density comparable to `|x|^{c−1}K(x)` on a punctured neighbourhood of the origin,
with `K` the slowly varying factor (53.25).

**Restated 2026-09-19 (R171), the previous form having been false.** It concluded
`c₁|x|^{c−1} ≤ p x ≤ c₂|x|^{c−1}`, dropping `K`; `K` is slowly varying at the origin but need not
be bounded, and the referee's admissible profile `k(x) = ½ − 1/log(1/x)` on `(0,e^{-4})`, folded,
has `c = ½` and `K(x) ≍ log(1/x)`, so no constant multiple of `|x|^{-1/2}` dominates its density.
The hypothesis `0 < k(0+) ∧ 0 < k(0−)` is (53.24)'s and was missing too. -/
def SatoOriginSingular : Prop :=
  ∀ (K : TwoSidedProfile) (cp cm : ℝ), Tendsto K.k (𝓝[>] (0 : ℝ)) (𝓝 cp) →
    Tendsto K.k (𝓝[<] (0 : ℝ)) (𝓝 cm) → 0 < cp → 0 < cm → cp + cm < 1 →
      ∀ μ : Measure ℝ, IsProbabilityMeasure μ → IsSymmetric μ →
        (∀ ω : ℝ, fourierCos μ ω = Real.exp (-K.exponent ω)) →
          ∃ p : ℝ → ℝ, μ = volume.withDensity (fun x => ENNReal.ofReal (p x)) ∧
            ∃ c₁ c₂ δ : ℝ, 0 < c₁ ∧ c₁ ≤ c₂ ∧ 0 < δ ∧
              ∀ x : ℝ, 0 < |x| → |x| < δ →
                c₁ * (|x| ^ (cp + cm - 1) * K.satoK (cp + cm) |x|) ≤ p x ∧
                  p x ≤ c₂ * (|x| ^ (cp + cm - 1) * K.satoK (cp + cm) |x|)

/-- **A10's smooth regime, at Sato's letter** (@sato1999levy Thm. 28.4, p. 191). -/
def SatoOriginSmooth : Prop :=
  ∀ (K : TwoSidedProfile) (cp cm : ℝ) (N : ℕ), Tendsto K.k (𝓝[>] (0 : ℝ)) (𝓝 cp) →
    Tendsto K.k (𝓝[<] (0 : ℝ)) (𝓝 cm) → 1 ≤ N → (N : ℝ) < cp + cm → cp + cm ≤ N + 1 →
      ∀ μ : Measure ℝ, IsProbabilityMeasure μ → IsSymmetric μ →
        (∀ ω : ℝ, fourierCos μ ω = Real.exp (-K.exponent ω)) →
          ∃ p : ℝ → ℝ, μ = volume.withDensity (fun x => ENNReal.ofReal (p x)) ∧
            ContDiff ℝ (((N - 1 : ℕ) : ℕ∞) : WithTop ℕ∞) p

/-- **A10's threshold regime, at Sato's letter** (@sato1999levy Thm. 53.8 with (53.30),
pp. 410–411). The comparison function is the source's `L(x) = ∫_{|x|}^1 K(y) dy/y` of (53.26),
written in the two-sided profile through `satoK`: the inner integrand is `(c − k(u) − k(−u))u⁻¹`,
which the folding translation turns into the article's `(c − k(u))u⁻¹`.

**2026-09-19 (R171):** `K` is now the shared `satoK` rather than an inline `exp` of the same
integral — the singular regime needs the same factor — and the source's (53.24) hypothesis that
both one-sided limits are positive is added. Neither changes what the axiom says at `c = 1`. -/
def SatoOriginThreshold : Prop :=
  ∀ (K : TwoSidedProfile) (cp cm : ℝ), Tendsto K.k (𝓝[>] (0 : ℝ)) (𝓝 cp) →
    Tendsto K.k (𝓝[<] (0 : ℝ)) (𝓝 cm) → 0 < cp → 0 < cm → cp + cm = 1 →
      ∀ μ : Measure ℝ, IsProbabilityMeasure μ → IsSymmetric μ →
        (∀ ω : ℝ, fourierCos μ ω = Real.exp (-K.exponent ω)) →
          ∃ p : ℝ → ℝ, μ = volume.withDensity (fun x => ENNReal.ofReal (p x)) ∧
            ∃ c₁ c₂ δ : ℝ, 0 < c₁ ∧ c₁ ≤ c₂ ∧ 0 < δ ∧
              ∀ x : ℝ, 0 < |x| → |x| < δ →
                c₁ * (∫ y in Ioo |x| 1, K.satoK 1 y / y) ≤ p x ∧
                  p x ≤ c₂ * ∫ y in Ioo |x| 1, K.satoK 1 y / y

end SpatialLine
