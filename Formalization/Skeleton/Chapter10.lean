/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Skeleton.Chapter9

/-!
# The target types of Chapter 10 — the corners

**This file carries `sorry`s and is not part of the `SpatialLine` library.**

## What writing this chapter down found

**1. Mathlib has no modified Bessel function, and three nodes are stated through one.**
`prop:matern-density`'s closed form, `prop:student-t`(2)'s transform and
`thm:joint-locality`(2)'s transform all name `K_ν`. Mathlib (v4.31.0) has none, and no error
function either. Rather than leave three nodes untypable, `SpatialLine.besselK` is defined by
the integral representation DLMF (10.32.9) — which is what the ledger's own sources define it
by — and the nodes are stated against it. The consequence to keep in view is that A16 and A19
then become statements about *that* integral, and a prover discharging them proves properties of
it from scratch; there is no Mathlib API behind the name. Question **Q10** asks the review
whether that is the right primitive.

**2. The corners are stated existentially over `SDProfile`, and the profiles are plain
functions.** Building `maternProfile` as an `SDProfile` *value* would prove
`lem:profile-integrability` for it inside the `sorry`-free library, which is precisely the
content of `prop:matern-exponent`(1); the node would then assert something already proved
elsewhere and its `\lean` tag would name a restatement. Phase A settled this shape at
`semigroup_case_profile`, and this chapter follows it. See SKELETON.md, finding **F12**.

**3. `thm:matern`'s consequence clause reaches a chapter with no Lean.** The theorem's four-way
equivalence is typed below; its closing sentence — "the Matérn family is the unique admissible
family with every moment finite, exponential tails, and an exact realization by first-order
forward–backward sections at every knot ladder" — rests on `prop:matern-cascade`, a Chapter 14
node for which no Lean is scheduled. The uniqueness *among the equivalence's terms* is the
equivalence itself; the realization clause is not typed, and the node's `\lean` tag is
accordingly incomplete by design rather than by omission. Recorded as question **Q11**.

**4. `prop:two-members`(2)'s density sentence lands here.** Phase A's question **Q1** asked
whether the Matérn kernel's identification, stated inside the Chapter 3 node, should be added to
that node's tag or moved to its annotation. Answer taken: `matern_density` is added to
`prop:two-members`'s `\lean` tag, since it is the declaration that discharges the sentence, and
the blueprint sentence is left alone. That is the more faithful tag and costs nothing, the
forward `\uses` edges being already in place.
-/

namespace Skeleton

open MeasureTheory Set Filter SpatialLine
open scoped ENNReal Topology

/-! ## `prop:moments-tails` (draft Proposition 10.1) — ledger A13, A14

Class (b) for clause (1) — twin `prop:moment-criterion`, causal ledger A7; class (c) for clause
(2), which the causal article states in a remark.

**What the entries carry**: **A13** the moment criterion for infinitely divisible laws in the
submultiplicative-weight form (Sato Thm. 25.3, p. 159), used with the weight `|x|^n`; **A14** the
two-sided tail statement for a Lévy law whose jump measure has bounded support (Sato Thm. 26.1,
p. 168, whose clauses (i) and (ii) are the two directions). **What they do not carry**: the
translation into the folded profile, and the variance formula, both `[T]` and written out in the
blueprint's own proof.
-/

/-- **`prop:moments-tails`(1), the moment criterion** — interface, ledger **A13**.

Reading: the law is the kernel at canonical scale `t`, quantified over by its transform as
everywhere in this development; the moment is `∫|x|^n` against it, and the criterion is an
integrability statement about the profile. `n ≥ 1` is the node's range.

Cost **L (interface)**: no infinite-divisibility development in Mathlib. -/
theorem moments_tails_criterion (P : SDProfile) (μ : ℝ → Measure ℝ)
    (hprob : ∀ t : ℝ, 0 < t → IsProbabilityMeasure (μ t))
    (hcos : ∀ t ω : ℝ, 0 < t → fourierCos (μ t) ω = Real.exp (-P.exponent (t * ω)))
    {t : ℝ} (ht : 0 < t) {n : ℕ} (hn : 1 ≤ n) :
    Integrable (fun x : ℝ => |x| ^ n) (μ t) ↔
      ∫⁻ x in Ioi (1 : ℝ), ENNReal.ofReal (x ^ (n - 1) * P.k x) ≠ ⊤ := by
  sorry

/-! ### `prop:moments-tails`(1), the variance — **PROVED AND MOVED (wave 5, 2026-09-10)**

`SpatialLine.moments_tails_variance`, in `SpatialLine/Variance.lean`, with the statement
verbatim (including the review's R7 hypothesis `hsym`, without which the mean-zero clause is
false — a cosine transform pins only the symmetrisation of `μ t`). Priced **M** and paid **M**.
**Lean core**, and that is the finding: ledger **A13** is *not* spent, though the natural route
spends it.

**The obligation is a second difference, not a second derivative.** The printed proof reads
`E X_t² = -∂²_ω e^{-F(tω)}|_{ω=0} = t²F''(0)` and differentiates `eq:levy-khintchine` twice
under the integral sign. The statement asks for neither derivative. Both of its sides are
pinned by

  `lim_{ω → 0} (1 - μ̂_t(ω))·2/ω²`,

evaluated once on the measure side and once on the exponent side, so two differentiations under
the integral sign — each needing its own dominating function — collapse to one dominated
convergence. The blueprint proof of record is rewritten to this route.

**One identity does the work three times.** For `ω ≠ 0`,
`(1 - cos(cω))·2/ω² = c² sinc(cω/2)²` (`SpatialLine.one_sub_cos_mul_two_div`), the half-angle
formula divided by `ω²`. Being an *equality* it supplies the pointwise limit (`Real.sinc` is
continuous with `sinc 0 = 1`), the dominating function (`|sinc| ≤ 1`, so the bound is `c²`) and
the inequality `1 - cos u ≤ u²/2` that the integrability steps need. Mathlib's `Real.sinc` is
what makes this cheap.

**The second moment is finite for free.** The apparent circularity — dominated convergence on
the measure side wants `x²` integrable, which is clause (1)'s criterion at `n = 2` — does not
arise. Fatou's lemma applied to the same integrands bounds `∫ x² dμ_t` by `t²(2a + ∫ xk)`
before any integrability is known, and the domination then upgrades the bound to an equality.
So finiteness of the second moment is a *conclusion* of this declaration, not a hypothesis of
it, and the `[T]` label the blueprint gives the variance formula is honest at the axiom line.

**The exponential is squeezed, not expanded.** `y e^{-y} ≤ 1 - e^{-y} ≤ y` for `y ≥ 0` is
`Real.add_one_le_exp` read at `y` and at `-y`; no Taylor remainder is needed, the two bounds
having the same limit because `F(tω) → 0`.
-/

/-- **`prop:moments-tails`(2), the tail dichotomy for a bounded catalogue** — interface, ledger
**A14**.

Reading: both directions, which is what the chapter's conclusion rests on and what the ledger's
verification pass confirmed is at the anchor (Sato Thm. 26.1's clauses (i) and (ii) on the same
page). The threshold is `1/(τt)`, the dilation by `t` moving it; the statement says nothing at
`α = 1/(τt)`, as the source says nothing there.

Range: the Lévy measure is carried by `{|x| ≤ τ}`, a Gaussian part being allowed, which is the
hypothesis `k` vanishes beyond `τ`.

**Changed (proof 2026-09-10, wave 4): the divergence conjunct was FALSE as typed and is
repaired.** It read: for every `α > (τt)⁻¹`, the moment is infinite. The ledger entry's own
parenthesis says that Sato's radius `c` is an *infimum* and that the blueprint's `τ` is that
number; the hypothesis `hvan` does not say so, and without it the conjunct fails twice.

* At `k ≡ 0` — the pure Gaussian — every `τ` satisfies `hvan`, while `α|x|log|x|` grows more
  slowly than `x²` and the Gaussian moment is finite at every `α`. Sato's Remark 26.3 treats
  `ν = 0` separately for exactly this reason.
* At any `τ` strictly larger than the radius, and `hvan` admits every such `τ`, the true
  threshold `1/(ct)` is larger than `(τt)⁻¹`, so the conjunct asserted divergence on a range
  where clause (i) of the same theorem — the *first* conjunct here — asserts convergence.

The repair quantifies the divergence over a radius the profile actually reaches: for every
`τ' > 0` at or beyond which `P.k` is nonzero, and every `α > (τ't)⁻¹`. That is clause (ii) read
at a lower bound for `c`, it is satisfiable, and it is what the two consumers need. The
finiteness conjunct is untouched: it is true for every `τ` with `hvan`, a larger `τ` making a
weaker claim. `moments_tails_heavy` is untouched and is this conjunct along `τ' → ∞`.

The narrowed Lean interface `SpatialLine.moments_tails_divergence` is the repaired conjunct
alone, and is what wave 4 admitted; see `SpatialLine/Interfaces.lean`.

Cost **L (interface)**. -/
theorem moments_tails_bounded (P : SDProfile) (μ : ℝ → Measure ℝ)
    (hprob : ∀ t : ℝ, 0 < t → IsProbabilityMeasure (μ t))
    (hcos : ∀ t ω : ℝ, 0 < t → fourierCos (μ t) ω = Real.exp (-P.exponent (t * ω)))
    {τ t : ℝ} (hτ : 0 < τ) (ht : 0 < t) (hvan : ∀ x : ℝ, τ ≤ x → P.k x = 0) :
    (∀ α : ℝ, 0 < α → α < (τ * t)⁻¹ →
        ∫⁻ x, ENNReal.ofReal (Real.exp (α * |x| * Real.log |x|)) ∂(μ t) ≠ ⊤) ∧
      ∀ τ' : ℝ, 0 < τ' → (∃ x : ℝ, τ' ≤ x ∧ P.k x ≠ 0) → ∀ α : ℝ, (τ' * t)⁻¹ < α →
        ∫⁻ x, ENNReal.ofReal (Real.exp (α * |x| * Real.log |x|)) ∂(μ t) = ⊤ := by
  sorry

/-- **`prop:moments-tails`(2), the heavy branch** — interface, ledger **A14**.

Reading: if the catalogue is unbounded then no rate of the previous form is achieved, at any
`α > 0`.

**Ledger coverage** (review 2026-09-09, R21, settled the same day). A14's "Statement as used"
originally recorded only the bounded-support dichotomy of Sato Thm. 26.1; the unbounded branch
is now recorded there too, from a librarian read of the page image: Sato defines `c` as the
infimum of the supporting radii, sets `c = ∞` for unbounded support and `1/∞ = 0` in the
statement itself, so clause (ii) at `c = ∞` gives an infinite moment for every `α > 0` and the
tail ratio `P[|X| > r]/e^{-αr log r} → ∞`, a Gaussian part allowed. This declaration is exactly
that instance and is within its citation.

Cost **L (interface)**. -/
theorem moments_tails_heavy (P : SDProfile) (μ : ℝ → Measure ℝ)
    (hprob : ∀ t : ℝ, 0 < t → IsProbabilityMeasure (μ t))
    (hcos : ∀ t ω : ℝ, 0 < t → fourierCos (μ t) ω = Real.exp (-P.exponent (t * ω)))
    {t : ℝ} (ht : 0 < t) (hunb : ∀ τ : ℝ, 0 < τ → ∃ x : ℝ, τ ≤ x ∧ P.k x ≠ 0) :
    ∀ α : ℝ, 0 < α →
      ∫⁻ x, ENNReal.ofReal (Real.exp (α * |x| * Real.log |x|)) ∂(μ t) = ⊤ := by
  sorry

/-! ### `prop:moments-tails`(2), the last sentence — **PROVED AND MOVED (wave 4, 2026-09-10)**

`SpatialLine.moments_tails_completely_monotone`, in `SpatialLine/TailDichotomy.lean`, with the
statement verbatim. Priced **M** and paid **M**. It spends **A11** at its first clause, through
`bernstein_completely_monotone`, and **A14** at its second, through the narrowed
`moments_tails_divergence`; the comparison of the two regimes is `[T]` and is
`lintegral_exp_sq_eq_top`.

**Admitting A14 forced a repair, because the reviewed `moments_tails_bounded` is false.** The
defect and the repair are written out at that declaration above and in
`SpatialLine/Interfaces.lean`; in one line, its divergence conjunct did not carry the ledger's
own reading of Sato's `c` as an *infimum*, and it therefore claimed divergence at `k ≡ 0` and on
a range where the entry's finiteness clause claims convergence.

**Two things proving it found.** The case split the node's printed proof makes — bounded
catalogue through A14's floor, unbounded through the heavy branch — is not needed: the narrowed
axiom takes any radius the profile reaches, and the clause's own hypothesis
`∃ x, 0 < x ∧ P.k x ≠ 0` hands one over. And "the comparison of the two regimes", which the
annotation priced as the content, is a square root: `log y = 2 log √y ≤ 2√y` turns
`α'|x|log|x| ≤ αx²` into `2α' ≤ α√|x|`, true beyond `(2α'/α)²`, and the passage to the integrals
is one split at that radius, the law being a probability measure. The first clause gives more
than it is asked for — a nonzero completely monotone profile is nonzero at *every* positive
point, not merely beyond every `τ`.
-/

/-! ## `prop:matern-exponent` (draft Proposition 10.2, clauses (1), (2), (4)) — [T]

Class (b) — three causal nodes collapse into one here (`prop:gamma-family`, `prop:gamma-kernels`,
`prop:gamma-moments`); the profile is `2γe^{-x}` where the causal one is `γe^{-u}`, the factor
being the folding.
-/

/-! ### `prop:matern-exponent`(1) and (2) — **PROVED AND MOVED (wave 2, 2026-09-09)**

Both went to `SpatialLine/MaternCorner.lean`, as `SpatialLine.matern_exponent` and
`SpatialLine.matern_transforms`, together with the witness `SpatialLine.maternDatum` — the
`SDProfile` clause (1) asserts to exist — and the elementary integral behind it,
`SpatialLine.integral_frullani` in `SpatialLine/Frullani.lean`. Lean core alone.

Clause (1) was priced **M** and cost **M**, and the price paid for exactly the differentiation
under the integral sign the annotation named. The route is the spatial twin of Paper I's
`ClosedForms.lean`, and one thing about it is worth recording: differentiating the integrand in
`ω` cancels the `x⁻¹` exactly, leaving `sin(ωx)e^{-px}`, whose modulus is bounded by `e^{-px}`
**uniformly in `ω`**. So the domination that
`hasDerivAt_integral_of_dominated_loc_of_deriv_le` asks for is global — no local ball, no
`ε`-neighbourhood — and `is_const_of_deriv_eq_zero` then finishes against the common value `0`
at the origin. The evaluated derivative `∫₀^∞ sin(ωx)e^{-px}dx = ω/(p²+ω²)` is the imaginary
part of Mathlib's `integral_exp_mul_complex_Ioi`, the only complex number in the chapter.

The two integrability conditions cost nothing beyond the dominating functions of that same
proof, read on `(0,1)` and `(1,∞)`. Note that `lem:profile-integrability` is **not** invoked:
`SDProfile` bundles the two conditions as fields, so the witness discharges them directly, and
the node's dependency edge to that lemma records where the conditions come from rather than a
step of the Lean proof.

Clause (2) was priced **S** and cost **S**.
-/


/-! ### `prop:matern-exponent`(3), the moments — **PROVED AND MOVED (wave 5, 2026-09-10)**

`SpatialLine.matern_moments`, in `SpatialLine/MaternMixture.lean`, with the statement verbatim,
and the node is `\leanok`: its other three declarations landed in waves 2 and 4. Priced **M**
and paid **M–L**, most of it in two special-function evaluations that had no counterpart in this
development.

**The route is the printed one, but the Gamma mixture is built here rather than imported.** The
wave-4 note called this conjunct blocked, on `prop:bridge-families`(2) for the mixture route and
on `moments_tails_variance` for the variance route. Neither block was real. The variance route
never gave the general even moment, only `n = 1`; and the mixture route does not need chapter 9,
because what it needs is a Gamma law with a known Laplace transform, and that is
`ProbabilityTheory.gammaMeasure` — Mathlib's, with its normalisation already proved. The delay
law is `SpatialLine.maternDelay γ t = gammaMeasure γ (2t²)⁻¹`, and the identification of
`μ t` with `(maternDelay γ t).bind brownianLaw` is one appeal to `prop:fourier-uniqueness`. This
is judgement point 1 of the charter in its usual form — what a proof cites is an upper bound on
what a statement needs — and judgement point 9 beside it: the mixing law was upstream all along.

**Three things the target type made visible.**

1. *The node has no symmetry hypothesis and needs none, but the proof needs the symmetrisation
   named.* Every conclusion here — integrability of `|x|^n`, the even moments, the variance — is
   an integral of an **even** function, hence a function of the symmetrisation of `μ t` alone,
   which is exactly what a cosine transform pins. So the absence of `hsym` is not the R7 defect
   it is elsewhere in this chapter. The proof cannot shrug, though: it identifies a *measure*
   with the Gaussian mixture, and only the symmetrisation is identifiable.
   `SpatialLine.symmetrise` with `lintegral_symmetrise_of_even` is the four-line bridge.
2. *The Gaussian even moment is one Gamma value, not an induction.* `E B_v^{2n} = (2n-1)‼ v^n`
   falls out of `integral_rpow_mul_exp_neg_mul_rpow` at `p = 2`, `q = 2n`, `b = (2v)⁻¹` together
   with `Real.Gamma_nat_add_half`, which is the half-integer special value already in
   double-factorial form. Mathlib has no moment formula for `gaussianReal`, but it has the two
   halves that meet.
3. *One Gamma-law lemma serves both uses.* The mixing law is wanted for its Laplace transform
   (to identify the mixture) and for its `n`-th moment (to evaluate the answer), and both are
   `∫ u^q e^{-su}` against the Gamma density: `lintegral_gammaMeasure_rpow_mul_exp` states it
   once, read at `q = 0` and at `s = 0`.

**Ledger A13 is not on this declaration's path.** The first conjunct follows from the even
moments by `|x|^n ≤ 1 + x^{2n}`, so `matern_moments` prints Lean core.
`SpatialLine.matern_moments_integrable` — wave 4's, by the moment criterion — remains the A13
consumer, and the two routes to finiteness are independent, as the blueprint's own proof says.
The author's decision of 2026-09-10 **dropped that declaration from the node's `\lean` tag**:
the node is `[T]`, its four tagged declarations print Lean core, and a `[T]` tag naming an
axiom-spending declaration reads as a grounding it is not. The declaration keeps its place in
the library, and since 2026-09-14 (R156) it has **no consumer**: `two_members_matern_moments`,
its last one, was re-routed to `matern_moments` when `prop:two-members`(2) was narrowed, and
moved into `MaternMixture.lean` to be able to read it. `matern_moments_integrable` stays as the
independent A13 part-proof of the same conjunct, and ledger A13 now grounds only
`prop:moments-tails` and the stable family's moments.
-/

/-! ## `prop:matern-density` (draft Proposition 10.2, clauses (3), (5), (6)) — ledger A15, A16

Class (b) — twin `prop:gamma-density` (causal ledger A17): a different Fourier pair in the same
role, the closed form of the kernel.

**What the entries carry**: **A15** the Fourier pair — that the displayed density has transform
`(1+t²ω²)^{-γ}` — together with the identification of the family as the symmetric variance-gamma
laws (Fischer et al., density (1.1) p. 1, characteristic function (2.12) p. 5); **A16** the
asymptotics of `K_ν` at infinity that give the tail (Abramowitz–Stegun 9.7.2 p. 378). **What
they do not carry**: the two special values, which are the displayed formula evaluated; that the
kernel is a density at all, which is `prop:kernel-regularity`; and the Gaussian limit, which is
`[T]` from `prop:levy-continuity`.
-/

/-- **`prop:matern-density`, the closed form** — interface, ledger **A15**.

Reading: the kernel at canonical scale `t` *is* `volume.withDensity` of `maternDensity γ t`,
which is the strongest of the three ways to state a density identification and the one Chapter 8
and Chapter 13 use. `maternDensity` is written through `SpatialLine.besselK`, the integral
representation; see the module docstring, finding 1.

This declaration also discharges the density sentence of `prop:two-members`(2), which phase A's
question **Q1** left open, and is named in that node's `\lean` tag as well.

Cost **L (interface)**. -/
theorem matern_density (γ : ℝ) (hγ : 0 < γ) (μ : ℝ → Measure ℝ)
    (hprob : ∀ t : ℝ, 0 < t → IsProbabilityMeasure (μ t))
    (hcos : ∀ t ω : ℝ, 0 < t → fourierCos (μ t) ω = Real.exp (-maternExponent γ 1 (t * ω)))
    {t : ℝ} (ht : 0 < t) :
    μ t = volume.withDensity fun x => ENNReal.ofReal (maternDensity γ t x) := by
  sorry

/-! ### `prop:matern-density`, the two special values —
**PROVED AND MOVED (wave 2, 2026-09-09)**

`SpatialLine.matern_density_special`, in `SpatialLine/BesselHalf.lean`, with the Bessel fact it
needs, `SpatialLine.besselK_half`. Lean core alone — no interface is spent, and in particular
neither A15 nor A16: the two special values are computations on the *definition* of `besselK`,
which is what the node's own assignment clause says ("the two special values, which are the
displayed formula at `γ = 1` and `γ = 1/2`" are among what A15 and A16 do not carry).

**Priced S (the `γ = 1/2` clause) and L (the `γ = 1` clause); paid S and M.** The finding is
where the L was over-priced. It was priced against "no Mathlib API behind `besselK`", which is
true, but the missing value is reachable in one substitution: `w = 2 sinh(u/2)` is a
diffeomorphism of `(0,∞)` under which `cosh u = 1 + w²/2` and `cosh(u/2)du = dw`, so
`∫₀^∞ e^{-z cosh u} cosh(u/2)du` collapses to `e^{-z}∫₀^∞ e^{-(z/2)w²}dw`, and Mathlib has both
halves of that — the substitution (`integral_image_eq_integral_abs_deriv_smul`) and the Gaussian
moment on `Ioi 0` (`integral_exp_neg_mul_rpow`). What is left is the image, the injectivity and
the derivative of the substitution, about thirty lines.

The order matters and is worth recording for the other three nodes stated through `besselK`:
`cosh(νu)` is a polynomial in `sinh(u/2)` **only at `ν = ±1/2`**, so this route closes the
half-integer orders and no others. `prop:student-t`(2) and `thm:joint-locality`(2) are at
general order and get nothing from it.
-/

/-- **`prop:matern-density`, the tail** — interface, ledger **A16**.

Reading: an asymptotic equivalence at `|x| → ∞`, with the constant `c_γ` existential and
positive, since the node writes `c_γ` without fixing it. Stated through `cocompact`, as
`quadratic_growth_isBigO` states its own two-sided limit.

**Changed (review 2026-09-09, R20), twice, and the blueprint with it.** The power of `t` was
wrong in the text of record: the blueprint and the draft write `t^{-γ-1/2}`, and the correct
exponent is `t^{-γ}`. From the scaling `φ_t = t^{-1}φ_1(\cdot/t)` and `φ_1(y) ∼ c|y|^{γ-1}e^{-|y|}`
one gets `φ_t(x) ∼ c\,t^{-1}(|x|/t)^{γ-1}e^{-|x|/t} = c\,t^{-γ}|x|^{γ-1}e^{-|x|/t}`; the same
follows from `K_ν(z) ∼ \sqrt{π/2z}e^{-z}` substituted into `maternDensity`, and the check at
`γ = 1` settles it — the Laplace kernel is `e^{-|x|/t}/(2t)`, whose `t`-power is `-1` and not
`-3/2`. Second, `∃ c` was written *inside* the scope of `t`, so the constant could absorb any
power of `t` and the statement said nothing about the scale at all; it is now quantified before
`t`, as `student_moments` does it. Only in that order is the corrected exponent an assertion.

Cost **L (interface)**, unchanged: the asymptotics of `K_ν` are A16, and there is no Mathlib
route to them. -/
theorem matern_density_tail (γ : ℝ) (hγ : 0 < γ) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, 0 < t →
      Filter.Tendsto
        (fun x : ℝ => maternDensity γ t x
          / (c * t ^ (-γ) * |x| ^ (γ - 1) * Real.exp (-(|x| / t))))
        (Filter.cocompact ℝ) (𝓝 1) := by
  sorry

/-! ### `prop:matern-density`, the Gaussian limit —
**PROVED AND MOVED (wave 2, 2026-09-09), WITH A STATEMENT CHANGE**

`SpatialLine.matern_density_gaussian_limit`, in `SpatialLine/MaternLimit.lean`. Lean core alone
— `levy_continuity` is chapter 2's proved theorem, not an axiom.

**The statement changed: `(hsym : ∀ n, IsSymmetric (μ n))` was added, because the declaration
was FALSE without it.** It is R7's defect at a third site. The hypotheses constrained the `μ n`
only through their **cosine** transform, which determines a measure's symmetrisation and nothing
else, while the conclusion is weak convergence — a statement about the whole measure. A
counterexample: let `ν n` be the Matérn law of the statement and put `μ n = ν n + σ n` with
`σ n` the signed measure of density `½ ν n(x) sgn(x)`. Then `σ n` is odd, so `μ n` is a
probability measure with the same cosine transform as `ν n`; but for `g = arctan`, bounded,
continuous and odd, `∫ g d(μ n) = ∫ g d(σ n) = ½∫|arctan| dν n → ½ E|arctan N| > 0`, while the
Gaussian limit gives `0`. The repair is R7's own: symmetry of the kernels, which (A3) gives for
every family in this article and which `two_members_matern` already assumes.

The review caught this reading at `two_members_matern_moments` and at `moments_tails_variance`
and said "the `|x|^n`-integrability and second-moment clauses are unaffected"; what it did not
do was sweep the chapter for the *third* clause with the same shape. Every remaining declaration
of this chapter that quantifies over `μ` by `hcos` alone and concludes something not determined
by the symmetrisation should be re-read against this: `matern_moments`'s odd-moment-free
statement is safe, and so are `moments_tails_criterion`, `_bounded` and `_heavy`, whose
conclusions are about `|x|`; `matern_density` concludes an identity of measures and is **not**
safe by inspection, but it is an `[A]` interface whose citation supplies the symmetric law, so
the reading to fix there is the hypothesis, not the ledger.

**Priced M; paid M.** The obligation is `γ log(1 + c/γ) → c`, which is Mathlib's
`Real.tendsto_one_add_div_rpow_exp` read through the logarithm.
-/

/-! ## `thm:matern` (draft Theorem 10.3) — [T]

Class (c) — the causal article has no single Gamma theorem; this is a collation node and the
chapter's headline. Its consequence clause is not typed; see the module docstring, finding 3.
-/

/-! ### `thm:matern`, clauses (1) ⟺ (2) and (1) ⟺ (3) —
**PROVED AND MOVED (wave 2, 2026-09-09)**

`SpatialLine.matern_thorin_atom` and `SpatialLine.matern_kernels`, in
`SpatialLine/MaternTheorem.lean`. With `matern_rational` and `matern_gauge` this completes
`thm:matern`'s tag, and the node is `\leanok`.

Both priced **M** and both cost **M**, but not where the annotations expected. The forward
directions are arithmetic on the exponent — `integral_frullani` on one side, `lintegral_dirac`
on the other — and cost almost nothing. The two backward directions are one lemma applied
twice, `SpatialLine.eqOn_maternProfile_of_exponent`, and it has two steps of which only the
first was priced:

1. Uniqueness of the Lévy pair (**A3**, admitted as `SpatialLine.fourier_toolbox_levy_unique`)
   gives equality of the profile **measures** `k(x)x⁻¹dx`.
2. A measure determines its density only **almost everywhere**, and the reviewed statement
   asserts a *pointwise* `Set.EqOn` on `(0,∞)`. R9's annotation named the reason this is
   nevertheless true — one side is antitone, the other continuous — but no Mathlib lemma says
   it. `SpatialLine.eqOn_of_ae_eq_of_antitoneOn` in `SpatialLine/ProfileUniqueness.lean` is
   that step, and it is the larger half of the cost. Strict monotonicity of the continuous side
   is **not** needed, although the annotation's wording suggested it might be: continuity on
   one side and monotonicity on the other are enough, because the co-null good set meets every
   subinterval and the antitone function is squeezed between the continuous one's two
   one-sided limits.

The lemma is stated for a general pair of profiles, since every corner theorem's backward
direction and `prop:choquet-cone`'s injectivity have the same obligation.

`matern_kernels`'s backward direction reads the transform at the canonical scale `t = 1` only;
the hypothesis at the other scales is not used, and the `s → 0` limit the printed proof takes
is not needed either, the increment formula being stated at `s = 0`.
-/

/-! ### `thm:matern`, clause (3) ⟺ (4) and the gauge — **PROVED AND MOVED (wave 2, 2026-09-09)**

`SpatialLine.matern_rational` and `SpatialLine.matern_gauge`, both in
`SpatialLine/MaternCorner.lean`. Lean core alone. Priced **S** and **S**; cost **S** and **S**.

One step of `matern_rational` is not algebra and is worth recording, because the reviewed
statement made it necessary and the annotation did not name it. R8 added the cascade relation as
a hypothesis, and the hypothesis quantifies over `0 ≤ s ≤ t` — so the conclusion has to be proved
at the **collapsed pair** `(0,0)` as well, where the left-hand hypothesis (`0 < t`) says nothing.
It is not a gap: the cascade relation at `(s,t) = (0,1)` reads
`Φ̂_{0,1} = Φ̂_{0,1} · Φ̂_{0,0}`, and the left factor is a positive rpow, so `Φ̂_{0,0} = 1`,
which is the conclusion there. No continuity of the transform in `ω` is needed for it — the
first route tried, and the more expensive one.
-/

/-! ## `prop:thorin-subclass` (draft Proposition 10.4) — ledger A11, A17

Class (b) for clauses (1)–(3), (c) for (4)–(5), which are new.

**What the entries carry**: **A11** Bernstein's theorem, which is (1) ⟺ (2) — a completely
monotone `k` is `∫ exp(-θx) U(dθ)` for a unique positive `U`; **A17** the identification of
clause (3), the definition of the extended generalized gamma convolutions and of their symmetric
members (Bondesson Ch. 7, Def. and (7.1.1)–(7.1.2) p. 105; the GGC class Thm. 3.1.1 p. 30).
**What they do not carry**: the elementary integral and the Tonelli that turn the mixture into
`eq:thorin`, the integrability correspondence, the exclusion of an atom at `θ = 0`, and clauses
(4) and (5) entirely — all `[T]`.
-/

/-! ### `prop:thorin-subclass`, (1) implies (2) and back — **PROVED AND MOVED (wave 3, 2026-09-09)**

`SpatialLine.thorin_subclass_representation`, in `SpatialLine/Thorin.lean`, with the statement
verbatim. Priced **L (interface)** for the Bernstein step plus **M** for the surrounding
computation; paid **L (interface)** plus **L**. The `M` estimate was made from the printed proof
and read the obligation too narrowly: the Tonelli itself is `M`, but the σ-finiteness of `U`, the
finiteness of the transform, the integrability correspondence, the continuity of the
reconstructed profile and the Lévy condition it needs are five further steps, none of them
visible in the printed argument.

Three things the writing found, recorded here so that the next round does not rediscover them.

**The uniqueness clause spends no interface.** It was expected to be where A11's own uniqueness
is spent — the ledger entry says so in as many words. It is not: two folded measures whose
Laplace transforms agree and are finite on a ray are equal by
`prop:laplace-uniqueness-locally-finite`, which this development *proves*. So the admitted axiom
`SpatialLine.bernstein_completely_monotone` is the **existence equivalence only**, and A11 is
charged for less than its citation carries, exactly as wave 2 narrowed A1.

**The integrability conjunct is a consequence, not a hypothesis.** Finiteness of the Thorin
integral at the single frequency `ω = 1` — which `SDProfile.exponentL_ne_top` gives for free
whenever `U` represents an admissible exponent — already yields σ-finiteness of `U`, finiteness
of `U` on `(0,1]`, and both halves of the condition. The converse direction discards the conjunct
outright. It is stated because `eq:thorin` states it, not because a proof consumes it.

**The Lévy condition for the reconstructed profile is a Gaussian average away.** The step that
looked expensive was showing that `k'(x) = ∫e^{-θx}U(dθ)` is the profile of a symmetric Lévy pair
at all. Integrating the identity `profileJumpL k ω = profileJumpL k' ω` over `ω` against a
standard Gaussian replaces the weight `1 - cos ωx` by `1 - e^{-x²/2}`, which is trapped between
`(1 ∧ x²)/3` and `1 ∧ x²` by two applications of `Real.add_one_le_exp`. The uniform average,
whose weight is `1 - sin x/x`, would have needed a fourth-order estimate on the sine that Mathlib
does not carry.
-/

/-! ### `prop:thorin-subclass`, (2) ⟺ (3) — **withdrawn, review 2026-09-09 (R19)**

The declaration `thorin_subclass_ggc` stood here and has been removed; clause (3) of the node is
now **untyped**, and the part file records it as a `% SKELETON NOTE`.

What it said: the class of symmetric extended generalized gamma convolutions was a *parameter*
`IsSymEGGC : Measure ℝ → Prop` whose only hypothesis, `hclass`, defined it as "the laws with a
completely monotone folded profile". That is clause (1)'s own form, so the declaration was
provable in `[T]` from `fourier_toolbox_levy_unique` and carried none of A17's content. An `[A]`
clause discharged by a tautology is worse than an untyped one.

Why the repair the review proposed is not available either. Defining the class in
`SpatialLine/Corners.lean` by A17's own form would mean transcribing the ledger's "statement as
used": the moment generating function `exp{bσ + cσ²/2 + ∫(\log(θ/(θ-σ)) - σθ/(1+θ²))U(dθ)}` on
**real** `σ`. The laws this node is about have no such transform — the Student-t law has no
exponential moment at any `σ ≠ 0`, and the Matérn law only in a strip — so a definition by that
formula would be empty at exactly the members the clause classifies. The reading that does apply
to them is the formula at `σ = iω`, where the pairing of `±θ` turns the integrand into
`-\log(1 + ω²/θ²)`; but the ledger says in as many words that the entry does **not** carry that
pairing (it is `[T]`, and it is the content of clauses (1)–(2)). Defining the class post-pairing
would restore the tautology in a new place.

So clause (3) is left as prose with a page-cited interface behind it and no Lean, which is the
honest state: nothing downstream consumes it — clauses (4) and (5), `thorin_bridge` and
`thorin_strictness`, run on complete monotonicity and on the Thorin measure, not on the class
name. Should the clause ever need a declaration, the missing step is a formal statement of
Bondesson's definition at imaginary argument, and that is a librarian read of §7.1 followed by a
new ledger entry, not a Lean exercise.
-/

/-! ### `prop:thorin-subclass`(4), the bridge on Thorin subclasses — **PROVED AND MOVED
(wave 6, 2026-09-10)**

`SpatialLine.thorin_bridge`, in `SpatialLine/ThorinBridge.lean`, with the statement verbatim.
Spends ledger **A3** (uniqueness, through `sdProfile_unique`) and ledger **A11**
(`bernstein_completely_monotone`, at its easy direction); both names were already on the trust
boundary. **Re-priced L by wave 5; paid M.**

Three things the writing found.

**The a.e.-to-pointwise antitone lemma wave 5 said was missing already existed.** The wave-5
re-price named, as the step no estimate contained, "the general fact that two antitone functions
agreeing a.e., one of them continuous, agree everywhere", and recorded that "this development has
no such lemma yet; it belongs beside `SpatialLine/AntitoneDensity.lean`". It has had one since
wave 2, one file away: `eqOn_of_ae_eq_of_antitoneOn` in `SpatialLine/ProfileUniqueness.lean`,
with the composed form `eqOn_of_profileMeasure_eq` that goes from equal profile measures straight
to a pointwise identity on `(0,∞)` — and `thorin_subclass_representation`, in the same node, runs
on it. Both consumers here cost one application. This is judgement point 9 in its exact form: the
claim "this development lacks X" was published without grepping the development for X, and it
cost the wave-5 branch nothing only because neither node was attempted.

**σ-finiteness of `U_I` is a consequence of `hk`, not a missing hypothesis.** The Tonelli needs
`U_I` s-finite and the reviewed statement does not assume it. It does not have to: `hk` at
`u = 1` says a *real* number equals the transform, so the transform is finite there, and
`sigmaFinite_of_lintegral_ne_top` applies with the weight `e^{-θ}`, whose zero set is empty. The
same two lines give σ-finiteness of the image measure from finiteness of *its* transform, which
is what `thorin_of_laplace` needs. Recorded because the alternative — adding `[SFinite UI]` to
the statement — would have been a statement change made for want of two lines.

**The exponent clause needs no Tonelli of its own.** Once `x ν₂(x)` is exhibited as the Laplace
transform of the image measure, `thorin_of_laplace` (wave 3's) turns that into `eq:thorin`. The
change of variables `θ' = √(2θ)` is performed once, in the image measure, and the Frullani
computation is quoted rather than repeated. The only integral written here is the mixture
identity `x∫₀^∞ g_u(x)k_I(u)du/u = ∫e^{-x√(2θ)}U_I(dθ)`, which is one Tonelli over
`lintegral_Ioi_firstPassage` at `A = x²/2`, `B = θ`, with `IsFolded U_I` supplying `B > 0`
exactly as wave 5 predicted.
-/

/-! ### `prop:thorin-subclass`(5), strictness the other way — **PROVED AND MOVED
(wave 6, 2026-09-10)**

`SpatialLine.thorin_strictness`, in `SpatialLine/ThorinStrictness.lean`, with the statement
verbatim. Spends ledger **A3** and ledger **A11** (here at its *forward* direction). **Re-priced
M–L by wave 5; paid M–L**, and the three parts came out in the proportions the re-price named,
with two of the three cheaper by a different route.

**The change of variables is antitone, and Mathlib has the antitone form.** The estimate proposed
`v = x²/2u` and this development's only change-of-variables tool
(`lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn`, `SpatialLine/FirstPassage.lean`) is
stated for monotone maps, so the interval looked as though it would have to be reversed by hand.
`lintegral_image_eq_lintegral_deriv_mul_of_antitoneOn` is the same lemma for a decreasing map;
`v ↦ A/v²` carries `(y,∞)` onto `(0,A/y²)` in one step, and the substitution is four lines plus
the image computation.

**The Gaussian bound the estimate proposed is not the cheapest one.**
`∫_y^∞e^{-v²}dv ≤ ∫_y^∞ve^{-v²}dv = e^{-y²}/2` needs the integrability of `ve^{-v²}` on a
half-line, which Mathlib does not carry. `e^{-v²} ≤ e^{-yv}` on `(y,∞)` needs only
`exp_neg_integrableOn_Ioi`, which it does, and gives `erfc y ≤ 2e^{-y²}` for `y ≥ 1` after one
improper FTC. The node needs a bound of Gaussian *type* and not a particular constant.

**The strictness half is a bound at one point, not an asymptotic.** The printed proof compares
`erfc(x/√(2τ)) ∼ √(2τ/π)x^{-1}e^{-x²/2τ}` against the exponential floor. No asymptotic is
needed: the floor comes from a single window `U(-∞,n]` of positive mass
(`exists_laplaceL_lower_bound`), and the contradiction is evaluated at one explicitly chosen
`x = max(max(√(2τ), 2τ(n+1)), 4/c + 1)`. What `erfc` did cost is four elementary facts Mathlib
does not have — integrability of `e^{-v²}`, continuity, strict positivity, the bound — of which
*continuity* is the load-bearing one, being the a.e.-to-pointwise passage's continuous side.
-/

/-! ## `prop:student-t` (draft Proposition 10.5) — ledger A18

Class (b) — twin `prop:bessel-family`, causal ledger A8; the spatial statement adds the density
and doubles the moment count.

**What A18 carries**: that the generalized inverse Gaussian laws, and the inverse-gamma laws
among them, are generalized gamma convolutions and hence self-decomposable, so that the causal
Bessel family is causally admissible (Halgreen §2, pp. 14–15, an unnumbered prose section).
**What it does not carry**: everything spatial — the density, the transform, the bridge image
and the moment count are all `[T]`.
-/

/-! ### `prop:student-t`, the causal input — **WITHDRAWN (2026-09-15, module B step 2, R160)**

`student_causal` said: there is a `CausalAdmissible` whose exponent has the inverse-gamma
Laplace transform. It was the declaration ledger **A18** would have carried, and nothing was
ever proved from it.

**It could not have discharged the clause it was recorded against.** Its conclusion is
self-decomposability of the delay law and no more, while `prop:student-t`(3) concludes that the
*spatial* profile is completely monotone — membership in the Thorin subclass — which needs the
*causal* profile to be a Laplace transform, i.e. the generalized-gamma-convolution half of
Halgreen's theorem. The interface as typed dropped exactly what its consumer consumes; there was
no route from `student_causal` to `student_thorin`, with or without an admission.

Both nodes are restated with the representation as a hypothesis and proved:
`SpatialLine.student_subordinated` (chapter 9, Lean core) quantifies over a causally admissible
datum, and `SpatialLine.student_thorin` (below) over the Thorin measure at Halgreen's own letter.
A18 is cited at `rem:student-ggc` and admitted nowhere.
-/

/-! ### `prop:student-t`(1), the scaling — **PROVED AND MOVED (wave 2, 2026-09-09)**

`SpatialLine.student_density`, in `SpatialLine/StudentCorner.lean`. Lean core alone.

**Priced M "given `bridge_families_bessel`"; paid S, and it consumes no Chapter 9 node at
all.** The finding is the annotation's, and it is the standard one: what a proof cites is an
upper bound on what a statement needs. The node obtains clause (1) by conditioning the Brownian
kernel on the inverse-gamma delay law, so both halves of the clause read as consequences of
`prop:bridge-families`; but `studentLaw` is *defined* here by the explicit density, so the
scaling half is the change of variables for a density under a dilation and nothing else —
`studentDensity a t (tx) = t⁻¹ studentDensity a 1 x` is arithmetic, and
`Real.map_volume_mul_left` with `setLIntegral_map` does the rest.

What does rest on the conditioning is the *other* half of clause (1), the identification of
`φ_1` with the law of `B_{T_1}`; that is `bridge_families_bessel`, R25 put it in this node's tag
for exactly that reason, and it stays there.
-/

/-! ### `prop:student-t`(2), the transform — **proved and moved** (wave 7, 2026-09-10)

`Skeleton.student_transform` is withdrawn. The clause is `SpatialLine.student_transform`, in
`SpatialLine/StudentTransform.lean`, on Lean core, and the node's `\lean` tag names it there.

**The proved declaration's type is not the withdrawn one, and the difference is a
strengthening.** The skeleton statement carried a causally admissible `F` with the specification
`∀ σ ≥ 0, ∫ e^{-σu} d(inverseGammaLaw a) = e^{-F.exponent σ}`, because the node's printed proof
reads clause (2) as the *causal* transform evaluated at `σ = ω²/2`. The conclusion mentions
neither `F` nor its exponent, and the checked proof forms neither: it takes the conditioning
identity `bridge_families_bessel` — the law is the Brownian mixture over the inverse-gamma delay
— and computes that delay law's Laplace transform directly. Both hypotheses are therefore
dropped, which removes hypotheses from a `[T]` clause and so weakens nothing downstream.

**The cost estimate was wrong at the top of its range, and the reason is worth keeping.** It read
**L**, "with no Bessel API this is the Fourier pair proved from scratch", and named a Bessel
asymptotic (ledger **A16**, finding F15) as what the development lacked. There is no asymptotic
in the obligation: `besselK` is *defined* here by its DLMF integral, and the exponential change
of variables `u = c e^v` that wave 5 already wrote for the first-passage transform carries the
delay integral onto that definition. Paid **M**, and cheaper at a general order `a` than at the
half-integer one, where the cosh-integral additionally has to be evaluated. The R10 reading is
unchanged: the identity is quantified over `ω ≠ 0`, being false at the origin where `|0|^a = 0`
and the transform of a probability law is `1`.
-/

/-! ### `prop:student-t`(3), self-decomposability and the Thorin subclass — **PROVED AND MOVED
(2026-09-15, module B step 2, R160)**

`SpatialLine.student_thorin`, in `SpatialLine/StudentThorin.lean`. **The hypothesis is not the
skeleton's**: it is the Thorin representation of the delay law at Halgreen's letter — a folded
`U` with `∫ log(1 + 1/θ) U(dθ) < ∞` and `E e^{-σT₁} = exp{-∫ log(1 + σ/θ) U(dθ)}` — where the
skeleton carried a `CausalAdmissible` with the same Laplace transform. That is a *strengthening
of the hypothesis*, so the statement is weaker and nothing that cited the clause is strengthened
by it; it is also the only hypothesis under which the conclusion is reachable, because complete
monotonicity of the spatial profile needs the causal profile to be a Laplace transform and
`CausalAdmissible` only makes it antitone (the withdrawn `student_causal` above).

The conclusion gains two conjuncts the skeleton did not have, both free on the checked route:
`Q.a = 0` and the spatial Thorin representation at twice the image of `U` under `θ ↦ √(2θ)`.

**Priced M given `bridge_exponents` and `thorin_bridge`; paid M**, and all of the cost was in a
step neither the estimate nor the printed proof named: the passage from a Thorin measure to a
causally admissible datum. `thorin_bridge_onto` performs it inside its own proof from *spatial*
finiteness data; `causalThorinDatum` is that block stated on the causal side alone, and what it
needed beyond the block is one elementary bound, `e^{-θu} ≤ C(u) log(1 + 1/θ)` on `(0,∞)`,
which gives the Laplace transform's finiteness where the spatial route read it off `eq:thorin`.
-/

/-- **`prop:student-t`(4), the moments and the tail** — the `[T]` half.

Reading: `E|X_t|^n < ∞` exactly when `n < 2a`, with `n` a natural number as everywhere in this
chapter; the tail is polynomial of order `|x|^{-2a-1}`, with the constant existential.

Cost **M**: the tail of the explicit density in clause (1), or `moments_tails_criterion` on the
profile, the two routes the node's proof gives. -/
theorem student_moments (a : ℝ) (ha : 0 < a) :
    (∀ (t : ℝ) (n : ℕ), 0 < t →
        (Integrable (fun x : ℝ => |x| ^ n) (studentLaw a t) ↔ (n : ℝ) < 2 * a)) ∧
      ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, 0 < t →
        Filter.Tendsto (fun x : ℝ => studentDensity a t x / (c * t ^ (2 * a) * |x| ^ (-2 * a - 1)))
          (Filter.cocompact ℝ) (𝓝 1) := by
  sorry

/-! ## `prop:stable-family` (draft Proposition 10.6) — [T]

Class (b) — twin `prop:stable-family` + `prop:stable-moments`; index `α` here is index `α/2`
there, by the bridge.
-/

/-! ### `prop:stable-family`, the moments — **PROVED AND MOVED (wave 4, 2026-09-10)**

`SpatialLine.stable_family_moments`, in `SpatialLine/Moments.lean`, with the statement verbatim.
Priced **S** given `moments_tails_criterion`; cost **S**, forty lines. The criterion is ledger
**A13** and is now admitted in `SpatialLine/Interfaces.lean` at the reviewed type verbatim, this
declaration being its first consumer; it is the only axiom the theorem's `#print axioms` shows
beside Lean core.

The reading the statement commits to is unchanged: the admissibility clause is
`semigroup_case_profile`, phase A, which this declaration does **not** restate, and the node's
sentence "the kernels are the symmetric α-stable densities" is nomenclature, not a clause.

**What proving it found.** The criterion is consumed as a black box — its left-hand side is
never unfolded — and the whole cost is on the profile side, where `stableDatum` (chapter 7) is
already the witness. Two small things are worth recording. The `ℕ`-subtraction in the criterion's
exponent is load-bearing: `x ^ (n - 1)` is truncated subtraction, and the hypothesis `1 ≤ n` is
spent exactly once, to turn `((n - 1 : ℕ) : ℝ)` into `(n : ℝ) - 1`, after which
`integrableOn_Ioi_rpow_iff` reads the convergence off `n - 1 - α < -1`. And the normalising
constant `C_α` enters only through `stableConst_pos`: the equivalence is invariant under a
positive factor, so the value is not needed here either.
-/

/-! ### `prop:stable-family`, the Thorin density — **PROVED AND MOVED (wave 3, 2026-09-09)**

`SpatialLine.stable_family_thorin`, in `SpatialLine/StableThorin.lean`, with the statement
verbatim. Priced **M**, paid **M**, and by neither of the two routes the annotation named: not
the image of the causal Thorin density under the bridge, and not a complete-monotonicity
argument. The profile is simply *exhibited* as a Laplace transform — Mathlib's
`Real.integral_rpow_mul_exp_neg_mul_Ioi` is the Gamma integral `∫₀^∞ e^{-θx}θ^{α-1}dθ =
Γ(α)x^{-α}` — and `SpatialLine.thorin_of_laplace` turns that into `eq:thorin`. So the clause
spends **no interface at all**, A11 included: Bernstein's theorem is what one needs when the
representing measure has to be *produced*, and here it is written down.

**The normalising constant is not the blocker here that it is elsewhere.** Wave 2 recorded
`C_α = ∫₀^∞ (1 − cos u)u^{-1-α}du` as blocking `semigroup_case_profile` and
`stable_family_moments`, "an improper integral with no Mathlib support at either endpoint" —
which is a statement about its *value*. This clause needs only that `C_α` is a **positive real
number**, and that is thirty lines (`SpatialLine.stableConst_pos`): convergence from
`1 − cos u ≤ u²/2` near the origin and `1 − cos u ≤ 2` beyond `1`, positivity because the
integrand is nonzero on `(0,1)`. The same reading unblocks more than this clause, and that was
**checked, not surveyed**: the substitution `u = ωx` inside the defining integral *produces*
`C_α` rather than evaluating it, so `∫₀^∞(1 − cos ωx)x^{-1-α}dx = C_α|ω|^α` is one application
of `setLIntegral_Ioi_comp_mul`. `SpatialLine.stableDatum` and
`SpatialLine.stableDatum_exponent` are the resulting `SDProfile` and its exponent clause, both
proved, and `Skeleton.semigroup_case_profile` — chapter 7's declaration, and another worktree's
this wave, so not discharged here — follows from them in one line. `stable_family_moments` then
waits only on `moments_tails_criterion`, ledger A13, which no proof of wave 3 consumed and which
is therefore not admitted.
-/

/-! ### `prop:stable-family`, the bridge image and the Gaussian endpoint —
**PROVED AND MOVED (wave 2, 2026-09-09)**

`SpatialLine.stable_family_bridge` in `SpatialLine/StableCorner.lean`, with the witness
`SpatialLine.gaussianDatum`. Lean core alone. Priced **S**; cost **S**.

`gaussianDatum a` — Gaussian coefficient `a`, zero profile, exponent `aω²` — is the same object
`Skeleton.semigroup_case_gaussian` (Chapter 7) asserts to exist. The two copies should be
deduplicated when the chapters merge; the survivor belongs with `cor:semigroup-case`, which is
the node that asserts it.
-/


end Skeleton
