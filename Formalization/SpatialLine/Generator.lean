/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.Corners
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# The scale evolution and the two localities

Blueprint: `blueprint/src/parts/11-generator.tex` — `def:signal-class` is a node and is
`SignalClass` below — and `blueprint/src/parts/12-locality.tex`, `def:localities`.

## The generator acts on functions, not on the signal class

`eq:evolution-signal` reads `∂_t u = \mathcal{A}_t u`, and `\mathcal{A}_t` is introduced with
"the integral converging absolutely for `g ∈ \mathcal{D}`". Typing `\mathcal{A}_t` as an
operator *on* `\mathcal{D} = SchwartzMap ℝ ℝ` makes that equation ill-typed, because **the scale
space is not Schwartz**: `u(t,\cdot) = μ_{0,t} * f` inherits the kernel's tails, and the
Student-t and stable corners have polynomial tails, so `μ * f` decays like `|x|^{-2a-1}` however
fast `f` decays. Chapter 10 constructs exactly those corners, so this is not a hypothetical.

`scaleGenerator` is therefore total on `ℝ → ℝ`, junk where the integral diverges — the phase A
convention for `exponent` and `laplaceL`. What the convergence clause is really about is the
bound `|g(x) - \tfrac12(g(x-h) + g(x+h))| \le \min(2\|g\|_∞, \tfrac12h^2\|g''\|_∞)`, which needs
`g` bounded with bounded second derivative and not Schwartz decay; `u(t,\cdot)` satisfies it
because convolution with a probability measure contracts both sup-norms. See SKELETON.md,
finding F13.

## The two localities, and one contrast with Paper I

`IsScaleLocallyGenerated` is polynomiality of the symbol, which `def:localities` says in so many
words is the notion consumed ("the definition is stated as polynomiality because that is what
the proof of `thm:scale-locality` uses, and the support formulation is left to `rem:peetre`").
Peetre's theorem is neither used nor a ledger entry.

`IsJointlyLocalOfOrder` is an **existential `Prop`**, where Paper I's
`Hemigroup.SelfDecomposableExponent.IsLocalOfOrderCore` is a structure carrying the
coefficients. The reason is the shape of the theorem each serves: Paper I's
`lem:local-polynomial-symbol` concludes something *about* the coefficients (`c_j(x) = γ_jx^{j-1}`),
which an existential cannot state, while `thm:joint-locality` concludes only which families are
local. The classification of the coefficients happens inside that theorem's proof, not in its
statement.

One clause of `def:localities` is transcribed by an added hypothesis rather than by a display:
"satisfies a linear partial differential equation" is read as *satisfies it classically*, so the
predicate demands that the scale space of a test signal be `C^m` on the open half-plane. The
demand is not decoration — without it the predicate is satisfied by every family whose scale
space is nowhere twice differentiable in `t`, `iteratedDeriv` returning `0` there; see the
declaration's own docstring and SKELETON.md § 5 (R3).

Two further clauses are read rather than transcribed, both harmlessly.
"Translation invariant, so that the coefficients do not depend on `x`" is carried by the type
`c : ℕ → ℕ → ℝ → ℝ`, whose only argument is `t`. And "satisfied by constants, which is unit
mass read on the equation" is `c_{00} = 0`: for a constant `u` every term with `j + k > 0`
vanishes, so the equation reduces to `c_{00}(t)u = 0`.

Paper I's causal `def:locality-pmp` bundles a positive maximum principle into the notion.
`def:localities` deliberately does not, and neither does this file: here the principle is
automatic (`thm:non-enhancement`(2)), so bundling it would silently narrow the class.
-/

namespace SpatialLine

open MeasureTheory Set
open scoped ENNReal

/-! ## `def:signal-class` -/

/-- **`def:signal-class`**: `\mathcal{D} = \mathcal{S}(ℝ)`, the Schwartz class on the line.

Literally Mathlib's `SchwartzMap ℝ ℝ`; the abbreviation exists so that the blueprint node has a
declaration in this repository to name. The node's three ancillary properties — contained in
`L¹`, stable under convolution with a finite measure and under differentiation, Fourier image
itself — are Mathlib's (`SchwartzMap.integrable`, `SchwartzMap.derivCLM`,
`SchwartzMap.fourierTransformCLE`) and carry no declaration of their own here; see SKELETON.md,
question Q9. -/
abbrev SignalClass := SchwartzMap ℝ ℝ

/-! ## The scale space and its generator -/

/-- The scale space of `f` under the kernels from the origin: `u(t,x) = (μ_t * f)(x)`.

The argument is `t ↦ μ_{0,t}`, the canonical-gauge kernel at scale `t`. -/
noncomputable def scaleSpace (μ : ℝ → Measure ℝ) (f : ℝ → ℝ) (t x : ℝ) : ℝ :=
  mconv (μ t) f x

/-- **`eq:evolution-signal`'s generator**,
`\mathcal{A}_tg(x) = 2at\,g''(x) - t^{-1}∫[g(x) - \tfrac12(g(x-tv) + g(x+tv))]\,\varpi(dv)`.

Total on `ℝ → ℝ`; see the module docstring for why it is not typed on `SignalClass`.

twin: `Hemigroup.SelfDecomposableExponent.phillipsGenerator`, with the one-sided delay
`g - T_rg` replaced by the symmetric second difference and the drift by the Laplacian. The
causal generator is `X`-valued (a Bochner integral in `L¹`) because its blueprint states it as
an operator identity in `L¹`; `eq:evolution-signal` is a pointwise identity, so this one is
scalar-valued and needs no vector-valued integral at all. -/
noncomputable def scaleGenerator (a : ℝ) (ϖ : Measure ℝ) (t : ℝ) (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  2 * a * t * iteratedDeriv 2 g x
    - t⁻¹ * ∫ v, (g x - (g (x - t * v) + g (x + t * v)) / 2) ∂ϖ

/-- The symmetric second difference `δ^2_hg = \tfrac12(g(\cdot-h) + g(\cdot+h)) - g`, the
generator of a `Cin` ray (`prop:corner-generators`(5)). -/
noncomputable def secondDifference (h : ℝ) (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  (g (x - h) + g (x + h)) / 2 - g x

/-! ## `def:localities` -/

/-- **`def:localities`, the first notion**: the family is *scale-locally generated* when its
symbol `B` is a polynomial.

Stated in `ℝ≥0∞` through `symbolL` (review 2026-09-09, R23). Through the real `symbol`, which is
a `toReal`, the pair `a = 0`, `ϖ = volume.restrict (Ioi 0)` would count as scale-locally
generated: its symbol is `⊤` at every `ω ≠ 0`, hence `0` after `toReal`, hence the zero
polynomial. That is harmless where the notion is *consumed* — under `scale_locality`'s
hypotheses the symbol is finite by `lem:quadratic-growth` — but it is a property of the
definition, and a definition is what the other modules reuse. -/
def IsScaleLocallyGenerated (a : ℝ) (ϖ : Measure ℝ) : Prop :=
  ∃ p : Polynomial ℝ, ∀ ω : ℝ, symbolL a ϖ ω = ENNReal.ofReal (p.eval ω)

/-- The mixed partial derivative `∂_t^j∂_x^ku` of a function of scale and position. -/
noncomputable def mixedDeriv (j k : ℕ) (u : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  iteratedDeriv j (fun s => iteratedDeriv k (u s) x) t

/-- **`def:localities`, the second notion**: the family is *jointly local of order `m`* when its
scale space satisfies a linear partial differential equation of order at most `m` in `(t,x)`,
with continuous coefficients not all zero, that is compatible with the axioms.

The five conjuncts after the coefficients are the node's four compatibility clauses and its
nondegeneracy clause: continuity; some coefficient nonzero; no odd `x`-derivative, which is
reflection symmetry; dilation covariance up to a factor `ρ(λ)`; and `c_{00} = 0`, which is
"satisfied by constants". Translation invariance is carried by the type of `c`.

**The regularity conjunct** (added by the review of 2026-09-09, R3) comes first, before the
coefficients, and says that the scale space of a test signal is `C^m` on the open half-plane.
Without it the definition is **spuriously satisfiable** and `thm:joint-locality` is false as a
consequence: `mixedDeriv` is built from `iteratedDeriv`, which returns `0` where the function is
not differentiable, and an admissible `F` is known to be `C¹` off the origin only
(`lem:selfdecomposable-exponents`(2)), so `∂_t^2u` need not exist. Where it does not, the
coefficients `c_{20} = 1` and all others zero, with `ρ(λ) = λ^{-2}`, satisfy every other
conjunct and the equation reads `1 · 0 = 0`; every family whose scale space is nowhere twice
differentiable in `t` would then be "jointly local of order 2", and no proof of the forward
direction could exclude it. The blueprint's "satisfies a linear partial differential equation"
presupposes classical derivatives, so the conjunct is a transcription of the node and not a
narrowing of it; both the Gaussian and the Student-t families, the two the theorem classifies,
have real-analytic scale spaces on `t > 0`. -/
def IsJointlyLocalOfOrder (μ : ℝ → Measure ℝ) (m : ℕ) : Prop :=
  ∃ (c : ℕ → ℕ → ℝ → ℝ) (ρ : ℝ → ℝ),
    (∀ f : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f → HasCompactSupport f →
      ContDiffOn ℝ (m : WithTop ℕ∞) (Function.uncurry (scaleSpace μ f))
        (Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ))) ∧
    (∀ j k, ContinuousOn (c j k) (Ioi 0)) ∧
    (∃ j k t, j + k ≤ m ∧ 0 < t ∧ c j k t ≠ 0) ∧
    (∀ j k, Odd k → ∀ t, c j k t = 0) ∧
    (∀ lam, 0 < lam → ∀ j k t, 0 < t → c j k (lam * t) = ρ lam * lam ^ (j + k) * c j k t) ∧
    (∀ t, c 0 0 t = 0) ∧
    ∀ f : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f → HasCompactSupport f → ∀ t : ℝ, 0 < t →
      ∀ x : ℝ, ∑ j ∈ Finset.range (m + 1), ∑ k ∈ Finset.range (m + 1 - j),
        c j k t * mixedDeriv j k (scaleSpace μ f) t x = 0

end SpatialLine
