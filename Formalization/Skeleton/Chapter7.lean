/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Skeleton.Chapter6
import SpatialLine.ConeDefs

/-!
# The target types of Chapter 7 — self-decomposability and the characterization theorem

**This file carries `sorry`s and is not part of the `SpatialLine` library.** The scaffold's
placeholder `SpatialLine.skeleton_scaffolded` is gone; this is the real chapter.

## What writing this chapter down found

**1. `thm:main-characterization` asserted an `[A]` fact inside a `[T]` node.** The statement read
"In the canonical gauge the scale-space kernels are `φ_t = 𝓕⁻¹[e^{-F(t·)}]`, **symmetric
probability densities** for `t > 0`". Absolute continuity of `μ_{0,t}` is not available to this
theorem: it is `prop:kernel-regularity`, an `[A]` node grounded in ledger **A8**, which the
main theorem does not (and cannot) `\uses` — the reverse edge already exists and adding this
one would make the graph cyclic. A proof of the statement as written would therefore have spent
A8 and put it in the *headline theorem's* `#print axioms`, contradicting the node's own `[T]`
grade. **Narrowed** to "the kernel at scale `t` is the symmetric probability measure with
transform `e^{-F(t·)}`", which is exactly what the construction proves; the density and its
unimodality stay where they belong, in `prop:kernel-regularity`. Recorded in the part file as
`% CHANGED (skeleton 2026-09-08)`.

**2. The analysis direction lands in the right type.** It produces an `SDProfile` — the
admissible-exponent structure — and not a bare pair `(a, k)`, so the next theorem
(`lem:admissible-cone`, and Chapter 8's cone) starts from the type this one ends in. That is the
fidelity rule the causal article's review named, and it is cheap to get right at statement time
and expensive later.

**3. `lem:selfdecomposable-exponents` splits four ways, not three.** The three conditions are not
equally deep and the node's own annotation says so: (3) ⟹ (1) is a change of variables and is all
the constructive direction consumes; (1) ⟹ (3) spends the uniqueness clause of
`prop:fourier-toolbox`(3) once and then runs a convex-tail argument; (3) ⟹ (2) is the `Cin`
superposition with differentiation under the integral sign; (2) ⟹ (3) is a Tonelli. Four
declarations, four different prices. The trailing `ϖ` material is a fifth and a sixth.

**4. The symbol is a total function without a case split.** `B(ω) = ω F'(ω)` is stated as
`fun ω => ω * deriv F ω` on all of `ℝ`: `F` is `C¹` on `(0,∞)` by clause (2) and on `(-∞,0)` by
evenness, `ω * deriv F ω` is then even, and at `ω = 0` the factor `ω` kills whatever `deriv`
returns. So no junk-value hypothesis is needed and `IsSymLevyExponent B` is meaningful as
written.
-/

namespace Skeleton

open MeasureTheory Set Filter SpatialLine
open scoped ENNReal Topology

/-! ## `lem:selfdecomposable-exponents` (draft Lemma 7.1') — [T]

The analytic heart. Its (1) ⟹ (3) leg is proved **directly**, which is why
`prop:sd-exponents` (ledger A7) is cited for orientation and never consumed, and why this
article's trust base is narrower than the causal one's at exactly this point.
-/

/-! ### (3) ⟹ (1) — **proved and moved** (2026-09-09, wave 2)

`SpatialLine.sd_exponents_three_implies_one`, in `SpatialLine/SelfDecomposable.lean`, with the
statement verbatim. Priced **M**, paid **M**: the port of Paper I's `levyExponentD_increment` is
mechanical, and the trap its docstring names — that the increment density is not antitone, so
measurability has to come from the two dilated pieces separately — is real and is handled by
`aemeasurable_incrementProfile`.

**What the estimate did not price, and it is the file's one piece of new mathematics.** Paper
I's exponent structure carries a single finiteness field, so its increment is a Lévy exponent as
soon as the increment's *exponent* is finite. `SymLevyPair` carries the Lévy condition
`∫ (1 ∧ x²) ν < ∞`, a statement about the **measure**, and the increment measure inherits it from
the *dilated* profile measure, not from the original. Transferring it is
`SpatialLine.lintegral_min_profileMeasure_comp_div_ne_top`, and it rests on the truncation
comparison `1 ∧ (cx)² ≤ (1 ∨ c²)(1 ∧ x²)` (`SpatialLine.min_one_sq_mul_le`) — the two regimes of
the truncation, which is exactly what the blueprint's "which is finite because `F(t·) ∈ LEₛ`"
was assuming rather than proving. The proof of record was rewritten to the checked route.

**A second finding, cheap and worth carrying to the next round.** The direction spends
`prop:fourier-toolbox` **not at all**, though the printed proof closed by citing clause (3).
`IsSymLevyExponent` is defined by the representation, and the increment is exhibited in that
form, so the whole implication reduces to Lean core. The blueprint's closing sentence now says
so.

The reusable pieces, all in `SpatialLine/SelfDecomposable.lean`:
`setLIntegral_Ioi_comp_mul` (the change of variables `u = cx` on `(0,∞)` for an arbitrary
`ℝ≥0∞` integrand — no measurability needed, the map being a measurable embedding),
`profileJumpL` and `profileJumpL_comp_div` (dilation acts on the density alone),
`lintegral_profileMeasure`, `lintegral_one_sub_cos_profileMeasure`, and `sd_increment_pair`,
which is the additive form `F(sω) + G(ω) = F(tω)` with `G` the exponent of the pair
`(a(t² - s²), ϖ_increment)` — the form `main_construction` needs, since a cascade adds.
-/

/-! ### (1) ⟹ (3), the analysis direction — **proved and moved** (2026-09-09, wave 3)

`SpatialLine.sd_exponents_one_implies_three`, in `SpatialLine/AnalysisDirection.lean`, with the
statement verbatim. Priced **L**, paid **L**, in three files and about five hundred lines. It
spends `fourier_toolbox_levy_unique` (ledger **A3**) and nothing else — the prediction phase A
made at this statement, confirmed by `#print axioms`.

**The direction splits in two at a clean seam, and the seam is worth recording.**
`SpatialLine/DilationDecrease.lean` carries the first half, from the hypothesis to
`eq:dilation-decrease`, `D_c ν ≤ ν`; that is where the axiom is spent, at **one** pair of scales
`(s,t) = (c,1)` — the quantifier over all `0 < s ≤ t` is not consumed. After it **no property of
`F` remains**: the rest is a statement about measures, which
`SpatialLine/AntitoneDensity.lean` proves in the generality it has:

  *a measure on `ℝ`, finite on every ray and decreasing under every right translation, is
  `volume.withDensity f` for a nonincreasing `f`.*

`SpatialLine/AnalysisDirection.lean` is the passage between the two coordinates.

**The convexity route is not the one that was taken, and the reason is a Mathlib gap.** The
blueprint's proof calls `M(θ) := ν̃((θ,∞))` convex and takes `f = -M'`. Everything *after* the
word "convex" is in Mathlib and would have been three lines —
`ConvexOn.monotoneOn_rightDeriv`, `ConvexOn.hasDerivWithinAt_rightDeriv_of_mem_interior`, and
`intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le`, whose hypotheses (continuity on
`[a,b]`, a right derivative on the interior) are exactly a convex function's. The word itself is
not: the shift property gives `M(θ) + M(θ+2δ) ≥ 2M(θ+δ)`, **midpoint** convexity, and Mathlib
has no "midpoint convex plus continuous implies convex" — `convexOn_of_slope_mono_adjacent`
wants the adjacent-slope inequality at arbitrary triples. Supplying it is the classical dyadic
induction plus a continuity passage, and the continuity of `M` is a further argument of its own
(an atom of mass `α` forces uncountably many atoms of mass `α` to its left, hence `M = ∞`).

The route taken defines `f(θ) := ⨆ₙ 2ⁿ ν̃((θ, θ+2⁻ⁿ])`, which is **antitone by construction**:
each term is antitone by the shift property, and the sequence is nondecreasing in `n` because
`ν̃((θ,θ+2δ]) ≤ 2ν̃((θ,θ+δ])`, the shift property again. No convexity, no modification, no
almost-everywhere reasoning and no Radon–Nikodym derivative; and what comes out is the
nonincreasing function `SDProfile.k_antitone` asks for rather than a representative of it. That
`ν̃((a,b]) = ∫_a^b f` is monotone convergence and one Tonelli, the `n`-th term squeezed between
`ν̃((a+εₙ,b])` and `ν̃((a,b+εₙ])`. The proof of record was rewritten to this route.

**What writing it down found, and it decided the shape of the construction.** The profile has to
be a *real* function, so `f` must be finite — and finite at **every** point, not almost every
point: `(⊤ : ℝ≥0∞).toReal` is `0`, so a single infinite value of the antitone `f` would make `k`
vanish exactly where the profile is largest and destroy `k_antitone` while leaving
`profileMeasure k` unchanged. It is finite everywhere and not by assumption:
`f(θ) = ∞` would force `f = ∞` on `(θ-1,θ]` by antitonicity, hence `ν̃((θ-1,θ]) = ∞`, which the
finiteness of the rays forbids. This is the kind of defect a `sorry`-free build does not catch,
because the statement would still be provable with a weaker `k` — and false.

The reusable pieces: `SpatialLine.dilate_le_of_increments`, `symLevyPair_dilate`,
`symLevyPair_add` (`DilationDecrease.lean`); `exists_antitone_density` with `dyadicDensity`,
`tonelli_window` and the two sandwich bounds (`AntitoneDensity.lean`);
`SymLevyPair.measure_Ioi_ne_top`, `map_log_Ioi`, `map_log_shift`, `map_exp_withDensity` (the
one-dimensional change of variables at `exp`), `dyadicDensity_ne_top` and
`exists_profile_of_dilate_le` (`AnalysisDirection.lean`). `map_exp_withDensity` and
`exists_antitone_density` are general enough to belong to `ScaleSpaceCore` if a second article
wants them.
-/

/-! ### (3) ⟹ (2) — **proved and moved** (2026-09-09, wave 3)

`SpatialLine.sd_exponents_three_implies_two`, in `SpatialLine/Symbol.lean`, with the statement
verbatim. Priced **L**, paid **M**.

**F6's ordering claim was right, and the ordering is cheap.** The direction is downstream of a
Choquet measure, as F6 said; what F6 got wrong is what producing one costs. It is
`cin_superposition_exists`, proved in chapter 8 in wave 2, so this direction opens with one
`obtain` and never mentions a modification, a Stieltjes function or a right-continuous profile:
`HasProfileTail`'s almost-everywhere identity is all the superposition needs, and the everywhere
form `sd_exponents_profile_measure` produces is not used here at all.

**The whole direction spends nothing** — `#print axioms` is Lean core, and in particular
`prop:fourier-toolbox` is not consumed. The printed proof's closing sentence, "which is of the
form `eq:levy-khintchine` with pair `(2a,ϖ)`, hence in `LEₛ`", is literal in this development:
`IsSymLevyExponent` is defined by the representation, so exhibiting the pair *is* the conclusion.
That is the same observation `sd_exponents_three_implies_one` made in wave 2, at the other
elementary direction.

**What the estimate missed, and it is the file's new mathematics.** The obligation was priced as
"differentiation under the integral sign with a dominated derivative", and that part went exactly
as priced: `hasDerivAt_integral_of_dominated_loc_of_deriv_le` on `(ω/2, 2ω)` with the bound
`(4/ω + 2ω)(1 ∧ u²)`, whose two regimes are the blueprint's own "at most `2/ω`, and at most
`ωu²/2`". What was not priced is that **`Cin` had no calculus**: chapter 8 built it for the
expansions at `0` and at `∞` and never differentiated it. `Cin' = (1 - cos v)/v` needs the
integrand to be *continuous at the origin*, where it is `0/0`; Lean's division convention makes
the value `0` and the limit is also `0`, the two agreeing because `|(1-\cos v)/v| ≤ |v|/2`, which
is `cinIntegrand_le_half` read on both signs. With that, the fundamental theorem of calculus
gives `hasDerivAt_cin` at every real point and `Cin` is continuous — three lemmas, and the
article's `Cin` is `C¹` on all of `ℝ` rather than only off the origin.

**One design decision, made at the statement.** The real identity `mul_deriv_exponent`,
`ωF'(ω) = 2aω² + ∫(1 - cos ωv)ϖ(dv)`, is proved first and `eq:symbol` is read off it, not the
other way round: `ENNReal.ofReal` is not injective, so an identity between `ofReal`s does not by
itself deliver the real value, and clause (2)'s Lévy pair needs the real value. The trichotomy
lives in the real lemma: positive frequencies by differentiation, negative ones because the
exponent is even so its derivative is odd, and `ω = 0` because the factor `ω` kills whatever
`deriv` returns there — which is finding 4 of this chapter's docstring, confirmed at the proof.

`ContDiffOn ℝ 1 F (Ioi 0)` is the differentiability above plus continuity of `F'`, and the
latter is a second dominated-convergence argument (`continuous_integral_one_sub_cos`) with the
bound `(2 + (|ω₀|+1)²)(1 ∧ v²)` on a unit ball. The blueprint's proof asserted `F ∈ C¹((0,∞))`
without separating the two; the proof of record now does.

The reusable pieces. In `SpatialLine/Cin.lean`, moved there by the wave-6 merge because chapter
8 came to need them too: `abs_cinIntegrand_le`, `continuous_cinIntegrand`, `hasDerivAt_cin`,
`continuous_cin`. In `SpatialLine/Symbol.lean`:
`one_sub_cos_le`, `integrable_min_one_sq`, `integrable_one_sub_cos`,
`integrable_cin_dilate`, `continuous_integral_one_sub_cos`; `exponent_eq_integral_cin`,
`hasDerivAt_exponent`, `mul_deriv_exponent`, `mul_deriv_exponent_nonneg`, `symbolL_eq_ofReal`;
and `SDProfile.exponentL_neg`/`exponent_neg`, the evenness of the exponent, which chapter 11's
symbol calculus will want too.
-/

/-! ### (2) implies (3) — **proved and moved** (2026-09-10, wave 5)

`SpatialLine.sd_exponents_two_implies_three`, in `SpatialLine/SymbolInverse.lean`, with the
statement verbatim. Priced **L**, paid **L** — and the five-step ordering the wave-3 note
worked out is the load-bearing part of that estimate, because it is right about *why* the node
is hard: the second integrability condition of `SDProfile` cannot come from the Lévy condition
on the symbol's measure, so the profile data does not exist until the finiteness of `F` has
been spent. Three corrections to the note, all in the cheap direction:

* **Step (i) was already in the library.** "`F` is continuous at the origin with `F(0) = 0`,
  priced S" is `SymLevyPair.continuous_exponent` (wave 3) with a two-line
  `SymLevyPair.exponent_zero`. Nothing was written for it.
* **Step (ii) is needed only as an inequality**, and that changes what it costs. The assembly
  wants `∫ Cin dϖ < ∞`, not its value, so the improper endpoint never becomes an improper
  integral: the fundamental theorem of calculus on `[ε,1]` gives `F(1) - F(ε) ≤ F(1)`, and
  `(0,1] = ⋃ₙ (1/(n+1), 1]` turns the limit into one `lintegral_iSup` over indicators.
* **Step (iii) is not stated at all.** The note makes the representation
  `F(ω) = ½a_Bω² + ∫ Cin(ωu)ϖ(du)` a step and prices it M. It is not needed: once the profile
  exists, `mul_deriv_exponent` gives its exponent the same derivative as `F` on `(0,∞)`, the
  two agree at the origin and both are continuous and even, so they are equal. What survives of
  the Tonelli is the *inequality* `∫ Cin dϖ ≤ ∫₀¹ F'`, over `(0,1) × (0,∞)` with a nonnegative
  integrand and no window.

So the wave-3 alternative recorded above — averaging the identity over `ω ∈ (0,1)` and using
`1 - sin t/t ≥ c(1 ∧ t²)` — was **not needed**, and neither was the trap it was proposed to
avoid: the layer cake at the weight `Cin'` oscillates, but the route above never takes a layer
cake at `Cin'`. It integrates `F'` over `(0,1)` and lets Tonelli produce `Cin` on the other
side, which is the same computation read in the direction that has a monotone bound.

Two general facts came out of it and are stated for an arbitrary pair:
`SpatialLine.SymLevyPair.sigmaFinite_nu`, σ-finiteness of a Lévy measure (needed for the
Tonelli, and not a field of the structure), and
`SpatialLine.eq_zero_of_hasDerivAt_zero_of_continuous`, the half-line identity theorem above.

`#print axioms` is Lean core plus `fourier_toolbox_levy_unique` (ledger **A3**, uniqueness),
spent once at the last step — which makes A3's uniqueness clause the only axiom this node
spends, in this direction and in the analysis direction. With this, all six declarations of
`lem:selfdecomposable-exponents` are proved and the node is `\leanok`. -/

/-! ### The Choquet measure `ϖ` — **proved and moved** (2026-09-09, wave 3)

`SpatialLine.sd_exponents_profile_measure`, in `SpatialLine/ProfileTail.lean`, with the statement
verbatim. Priced **M**, paid **S**.

**Finding F6 is answered, and answered in the negative.** The estimate read the node as
downstream of a Stieltjes construction, and re-read Paper I's `Subordinator.lean` warning that
"the Stieltjes route fails for a reason the work order did not anticipate" as a warning about
this construction. It is not one — that note is about forming `∫₀^∞ μ_t dt` as a measure, a
different obligation on the causal side — and no Stieltjes function is needed here at all. The
measure this node asks for is `lem:cin-rays`'s Choquet measure, which chapter 8 already built by
the quantile transform (`SpatialLine.exists_tailMeasure`, `cin_superposition_exists`), so the
node is a corollary of a node proved in wave 2 and the ordering F6 recorded does not exist.

**What the modification is.** Take `ϖ` from `cin_superposition_exists` and set
`k'(x) := ϖ((x,∞)).toReal`. Then the everywhere tail identity is `ENNReal.ofReal_toReal` at a
finite tail, right continuity is continuity of `ϖ` from below along `(x,∞) = ⋃ₙ (x+(n+1)⁻¹,∞)`,
antitonicity is monotonicity of a measure, `k' = k` almost everywhere is the specification
`HasProfileTail` itself, and `k'(∞) = 0` comes from `SDProfile.tendsto_k_atTop` through one point
of the a.e. identity beyond each threshold. Finiteness of every positive tail — what makes
`toReal` faithful — is not a hypothesis either: a point of the a.e. identity below `x` bounds
`ϖ((x,∞))` by a value of the profile (`SpatialLine.measure_Ioi_ne_top`).

**The two integrability conditions changed weight, and the change is a simplification.** The
blueprint reads them off the profile by Tonelli with the weights `(u ∧ 1)²` and `log₊ u`, whose
densities `2t·1_{t<1}` and `t⁻¹1_{t>1}` are discontinuous; Mathlib's layer cake
(`lintegral_comp_eq_lintegral_meas_lt_mul`) wants an interval-integrable density, and carrying
two indicators is avoidable. The proof integrates `u²/(1+u²)` and `½log(1+u²)` instead — the
primitives of the *continuous* densities `2t(1+t²)⁻²` and `t(1+t²)⁻¹` — each of which dominates
the blueprint's weight up to a factor of `2` and is dominated by the same two conditions on `k`.
Both conditions are finiteness assertions, so nothing is lost. The proof of record now runs this
way (`% CHANGED (proof of record 2026-09-09)`).

The reusable pieces, all in `SpatialLine/ProfileTail.lean`:
`lintegral_intervalIntegral_of_hasProfileTail` (the layer cake against a Choquet measure, with
the weight left free — the form `prop:choquet-cone`'s domain clause also wants),
`lintegral_min_one_sq_ne_top` and `lintegral_log_max_one_ne_top` (the two conditions, for **any**
`ϖ` with `HasProfileTail`, not only the constructed one), `exists_tail_eq_mem_Ioo`,
`measure_Ioi_ne_top` and `tendsto_measure_Ioi_nhdsGT`.
-/

/-! ### `eq:symbol` — **proved and moved** (2026-09-09, wave 3)

`SpatialLine.sd_exponents_symbol`, in `SpatialLine/Symbol.lean`, with the statement verbatim.
Priced **S** given (3) ⟹ (2), paid **S**: it is `symbolL_eq_ofReal` composed with
`mul_deriv_exponent`, two lines, both of which that direction had to prove anyway.

The review's substitution (R2) is what makes it two lines rather than a case analysis:
`HasProfileTail` is finiteness-forcing, so the `ℝ≥0∞` identity never has to rule out a tail of
`⊤`, and the hypothesis is met by the measure `cin_superposition_exists` produces for *any*
admissible profile.
-/

/-! ## `thm:main-characterization` (draft Theorem 7.3') — [T]

The headline, split three ways as TWINS.md says the causal development's split is the model:
construction, analysis, uniqueness. The `\lean` tag on the node names all three.
-/

/-! ### The construction direction — **proved and moved** (2026-09-09, wave 2)

`SpatialLine.main_construction`, in `SpatialLine/MainConstruction.lean`, with the statement
verbatim. Priced **L**, paid **L**. It spends exactly two axioms, `fourier_toolbox_levy_converse`
(ledger A3, already on the boundary) and `fourier_toolbox_bochner_symm` (ledger **A1**, admitted
in `SpatialLine/Interfaces.lean` — see the trust-boundary note for why A3's *second* name did
not appear here).

**What the estimate got right.** (A7) is the expensive clause, and R30's re-estimate after wave 1
was the accurate one: `SpatialLine.norm_mconvL1_sub_le` reduces it to weak convergence of the
collapsing increments to `δ₀`, so no compact set, no density argument and no `ε/3` appear. The
blueprint's proof of record was rewritten to that route.

**Three findings.**

1. **(A7)'s block is not Matérn's — it is everybody's.** `Matern.lean`'s
   `tendsto_integral_transDiff`, `norm_sub_left`, `norm_sub_right` and `continuousOn_mconvL1` use
   only that the kernels are symmetric probability measures with `κ t t = δ₀`, the cascade law at
   the level of measures, and a transform continuous in the pair of scales. They are rewritten
   generically as `SpatialLine.CascadeData` in `SpatialLine/Construction.lean`, which delivers
   `PreCascadeCore`, `IsPositive`, `IsKernelFamily`, `IsNondegenerate` and `IsScaleCovariant` from
   those five properties. `Matern.lean` and `Gaussian.lean` are chapter 3's files and were left
   alone; at the merge they should be rebuilt on `CascadeData` and their copies deleted, on wave
   1's deduplication pattern. `MaternData.charFun_map_const_mul` is a general fact stranded in a
   concrete namespace and should move with them.

2. **(ND) does not need `prop:strict-positivity`.** The blueprint's proof cites clause (2) of that
   node; the clause the construction needs is only that *some* frequency is moved. At `s = 0` that
   is `F ≢ 0`; for `s > 0`, a vanishing increment gives `F(ω) = F(cω)` with `c = χ(s)/χ(t) ∈ (0,1)`
   and `lem:dilation-invariance` finishes. So this direction of the headline theorem is
   independent of an unproved node — the "read the obligation, not the argument" test paying off
   at a node where the argument named something much heavier.

3. **The gauge's continuity is a theorem of the hypotheses, not a hypothesis.** (A7) needs `χ`
   continuous, and the statement assumes only that it is a strictly increasing surjection of
   `[0,∞)`. `ConstructionData.chi_continuousOn` derives it: the restriction to `Ici 0` is a
   strictly monotone bijection, hence an `OrderIso` of a set carrying the order topology, hence
   continuous. Four lines, and no hypothesis had to be added. The blueprint asserted the fact
   without a reason; the proof of record now gives one.

The vocabulary this direction added to the library, all in `SpatialLine/`:
`CascadeData` (`Construction.lean`); `exists_isSymmetric_of_isSymLevyExponent`,
`ConstructionData` with its gauge inverse and gauge conjugate (`MainConstruction.lean`);
`sd_dilate_pair` and `sd_increment_isSymLevyExponent` (`SelfDecomposable.lean`), the second being
the three-case increment `0 ≤ c ≤ d` that the range `0 ≤ s ≤ t` of this theorem forces.
-/

/-! ### The analysis direction — **proved and moved** (2026-09-09, wave 3 merge)

`SpatialLine.main_analysis`, in `SpatialLine/MainAnalysis.lean`, with the statement verbatim,
and the bundling `SpatialLine.main_characterization` beside it, which names all three clauses of
the node in one declaration.

Reading: the conclusion produces an **`SDProfile`** — the admissible-exponent structure — and not
a bare pair, so the type this theorem ends in is the type `lem:admissible-cone` and Chapter 8
start from. The gauge `χ` is produced with the three properties `prop:canonical-gauge` gives it.

Class (b) — twin `Hemigroup.CascadeCore.main_analysis`.

Priced **L**, paid **L**, and the two halves were written in separate worktrees:
`SpatialLine.main_analysis_of_profileForm` is this statement with
`lem:selfdecomposable-exponents`(1) ⟹ (3) as its single hypothesis, and the merge supplied that
hypothesis from `SpatialLine.sd_exponents_one_implies_three`, so the closing step is an
application and nothing more. The prediction the assembly recorded — "it waits on that
declaration and on nothing else" — held exactly.

**What the assembly found.** The estimate read "the assembly itself is **M**; the **L** is
inherited from its parts", and that is right in cost but wrong in shape: the assembly is one
deep leg and a page of bookkeeping, with no analysis of its own. The bookkeeping is one step and
it is worth naming, because it is the only place in the chapter that consumes the gauge's
*surjectivity*: condition (1) of `lem:selfdecomposable-exponents` quantifies over pairs of
canonical scales `0 < c ≤ d`, and those are exponents of the family only because every
nonnegative number is `χ(t')` for some scale `t'`. That step is
`SpatialLine.isSymLevyExponent_dilate_diff`, and it holds for `0 ≤ c ≤ d`, the lower endpoint
included, which the node's own hypothesis does not need but `prop:kernel-regularity` does.

**The headline theorem's footprint.** `main_analysis` spends `fourier_toolbox_levy_unique`
(ledger **A3**, uniqueness) through the profile form and nothing else; `main_construction`
spends `fourier_toolbox_levy_converse` (A3) and `fourier_toolbox_bochner_symm` (**A1**);
`main_uniqueness` is Lean core. So the bundle prints Lean core plus those three names, and no
part of the theorem reaches A8, A9 or A11.
-/

/-! ### The uniqueness clause — **proved and moved** (2026-09-09, wave 3)

`SpatialLine.main_uniqueness`, in `SpatialLine/MainAnalysis.lean`, with the statement verbatim,
R1's four added gauge hypotheses included. Priced **M**; paid **S**, and the proof is the one
R1 predicted: read at `s = 0` the two representations give the same transform, so the
normalisation `χ_i(1) = 1` identifies the exponents at `t = 1`; then
`F(χ₁(t)ω) = F(χ₂(t)ω)` for every `ω`, the two gauge values are positive for `t > 0` because a
gauge fixes `0` and is strictly increasing, and `lem:dilation-invariance` forces `F ≡ 0` unless
their ratio is `1`.

**It prints Lean core, and that took one new library file.** `lem:dilation-invariance` wants
continuity of `F` at the origin, and the only route to it in the library was
`profile_integrability_mem`, which produces an `IsSymNegDef` and reads its continuity field —
spending ledger **A3** for a fact dominated convergence gives outright. Continuity of a
symmetric Lévy exponent is now `SpatialLine.SymLevyPair.continuous_exponent` and
`SpatialLine.SDProfile.continuous_exponent`, in `SpatialLine/ExponentContinuity.lean`, proved
from the truncation bound `1 - cos(ωx) ≤ 2(1 ∨ M²)(1 ∧ x²)` on a bounded frequency
neighbourhood, whose `ν`-integral is finite because the Lévy condition is a field of
`SymLevyPair`. Two headline declarations of this chapter — this one and
`strict_positivity_strict` — are Lean core because of it.
-/

/-! ## `cor:semigroup-case` (draft Corollary 7.4') — [T]

**Proved and moved entire** (2026-09-09, wave 3). All three declarations are in `SpatialLine`
with their statements verbatim, and all three print Lean core.

* `SpatialLine.semigroup_case_gaussian`, the boundary `α = 2`, in
  `SpatialLine/SemigroupCase.lean` with the witness `gaussianDatum` — wave 2, priced **S**,
  paid **S**.
* `SpatialLine.semigroup_case_profile`, the profile for `0 < α < 2`, in
  `SpatialLine/StableProfile.lean` — wave 3, priced **M**, paid **M**.
* `SpatialLine.semigroup_case`, the index clause, in `SpatialLine/SemigroupIndex.lean` — wave 3,
  priced **M**, paid **M**.

**What the estimate got wrong about the constant.** Wave 2 recorded that both remaining
declarations "wait on the convergence of `C_α = ∫₀^∞ (1 - cos u)u^{-1-α}du`, an improper
integral at both endpoints with no Mathlib support". The constant is not an obstacle at all:
the node never asks for its value, only for convergence, positivity and the scaling identity.
Convergence is the two regimes of the truncation compared against `Real.rpow` — `1 - cos u ≤
u²/2` near the origin, `≤ 2` beyond `1` — and those two comparisons **are** the two
integrability fields of `SDProfile`, so one argument discharges both obligations. The scaling
identity is run in `ℝ≥0∞` through `setLIntegral_Ioi_comp_mul`, which needs no integrability, so
the Bochner integral is touched exactly once. The witness is built on chapter 10's own
`stableConst` and `stableProfile` (`SpatialLine/Corners.lean`) rather than on a second copy, so
`prop:stable-family`'s remaining clauses, which quantify over `P.k = stableProfile α`, can use
it unchanged.

**What the estimate missed about the index clause.** It priced "the Cauchy-equation step
assembled with `covariance_similarity`, which is bookkeeping rather than analysis". The
bookkeeping is right, but there are **two** Cauchy equations and only one of them was priced.
The unpriced one is in the *scale* variable, hidden in the printed proof's phrase "homogeneity
gives `g_{s,t} = (t-s)g`": one-parametricity makes `μ_{0,t}` and `μ_{s,s+t}` the kernels of the
same operator, hence equal by the uniqueness half of `lem:convolution-representation`, so
`t ↦ g_{0,t}(ω)` is additive on `[0,∞)` and continuous there — and turning that into
`G(t) = t G(1)` needs the odd extension to `ℝ` before Mathlib's `map_real_smul` applies.
That is the longest part of the file. The *frequency* equation is cheaper than the printed
proof suggests: the normalisation makes `S_λ(1) = g(λ)`, so the multiplicative function is `g`
itself and no separate homomorphism `c` has to be handled, and `lem:action-rigidity`(3) is
therefore **not consumed** — what is consumed instead is `lem:no-lattice`, for strict
positivity of `g` off the origin, which the logarithm needs.

`α ≤ 2` is made explicit rather than asymptotic: the normalisation `g(1) = 1` forces the growth
constant of `lem:quadratic-growth` to satisfy `C ≥ 1/2`, and `ω = (2C+1)^{1/(α-2)}` is a
frequency at which the bound would fail if `α > 2`.

Two reusable lemmas came out of it, both in `SpatialLine/SemigroupIndex.lean`:
`eq_mul_of_addOn_of_continuousOn` (additive and continuous on `[0,∞)` implies linear there) and
`exists_eq_rpow_of_mul` (a continuous multiplicative function on `(0,∞)` is a power).
-/

/-! ## `lem:admissible-cone` (draft Lemma 7.6') — [T]

**Proved and moved** (2026-09-09, wave 2): `SpatialLine.admissible_cone`, in
`SpatialLine/AdmissibleCone.lean`, with the statement verbatim. Priced **S**, paid **S** — a
port of Paper I's `AdmissibleCone.lean`, field for field.

One thing the estimate did not name, and it is the only step of the proof that is not
arithmetic. Paper I's exponent is `ℝ≥0∞`-valued and its cone statement is too, so its proof
never leaves `lintegral`; here the node's statement is about `SDProfile.exponent`, a `.toReal`,
and `(x + y).toReal = x.toReal + y.toReal` needs both summands finite. The finiteness is
`lem:quadratic-growth` reached through `lem:profile-integrability`, packaged as
`SpatialLine.SDProfile.exponentL_ne_top`; the two labels were added to the node's `uses` and the
blueprint proof now says so. A reusable consequence for the rest of the chapter: every
`SDProfile` has a finite exponent at every frequency, so `exponent`/`exponentL` may be traded
freely from here on.
-/

/-! ## `prop:strict-positivity` (draft Proposition 7.5', clauses (1) and (2)) — [T]

New: on the half-line these facts were available *before* the gauge argument, from the vanishing
lemma and the monotonicity of Bernstein functions. Here they are consequences of the
classification, and that reversal is the chapter's structural point.
-/

/-! ### Clause (1) — **proved and moved** (2026-09-09, wave 2)

`SpatialLine.strict_positivity_monotone`, in `SpatialLine/StrictPositivity.lean`, with the
statement verbatim. Priced **S**, paid **S** but by a different route, and the route is the
finding: the skeleton priced the substitution `u = ωx`, which is a *second* change of variables
on top of the one `sd_exponents_three_implies_one` already performs. Monotonicity is that node
read at the single frequency `ω = 1`: `F(ω₂ ·) - F(ω₁ ·)` is a symmetric Lévy exponent for
`0 ≤ ω₁ ≤ ω₂`, and a symmetric Lévy exponent is nonnegative because it is a `toReal`. Four
lines. The proof of record was rewritten to it.

`F ≢ 0` is confirmed unused, as the skeleton's hypothesis archaeology predicted.
-/

/-! ### Clause (2) and its consequences — **proved and moved** (2026-09-09, wave 3)

`SpatialLine.strict_positivity_strict` and `SpatialLine.strict_positivity_consequences`, in
`SpatialLine/StrictPositivityStrict.lean`, with the statements verbatim. Priced **M** and **S**;
paid **M** and **S**. Both print Lean core.

**The three-step plan wave 2 wrote at the statement held**, and two of its steps came out
cheaper than written:

* Step 3, the rigidity step, needs no point-extraction and no covering. The tail integral
  `J(ε) = ∫_ε^∞ k(u) du/u` is finite for every `ε > 0` and invariant under the dilation, so it
  has no mass on `(ε, ϰε]`; antitonicity then bounds the integrand below by `k(ϰε)/(ϰε)` there,
  and an integral that vanishes on a set of positive measure forces that bound to be `0` **at
  the right endpoint**. Reading the conclusion at `ε = x/ϰ` gives `k(x) = 0` for an arbitrary
  `x > 0` directly. The one new library lemma the plan named,
  `map_mul_restrict_Ioi` generalised to `Ioi b`, is `SpatialLine.setLIntegral_Ioi_comp_mul'`.
* The consequences do **not** need `lem:lattice-zero`, against which they were priced. If a
  kernel is carried by `pℤ` then its cosine transform at `2π/p` is the integral of the constant
  `1`, so the increment exponent vanishes at a nonzero frequency, which clause (2) forbids.
  `Real.cos_int_mul_two_pi` is the whole of it.

The reusable pieces, all in `SpatialLine/StrictPositivityStrict.lean`:
`map_mul_restrict_Ioi'` and `setLIntegral_Ioi_comp_mul'` (the change of variables `u = cx` with
an arbitrary base point), `ae_restrict_Ioi_mul_iff` (a dilation of the half-line preserves
almost-everywhere statements), `ae_cos_ne_one`, `ae_eq_zero_of_profileJumpL_eq_zero`,
`SDProfile.lintegral_tail_ne_top`, `SDProfile.k_eq_zero_of_dilation_ae`,
`SDProfile.exponent_eq_zero_of_ae` and `SDProfile.exponent_neg`.
-/

/-! ## `prop:kernel-regularity` (draft Proposition 7.5', clause (3)) — ledger A8, A9

**Proved and moved** (2026-09-09, wave 3), both declarations, with their statements verbatim.

* The interface proper is now the **axiom** `SpatialLine.kernel_regularity_law`, in
  `SpatialLine/Interfaces.lean`, on `blueprint/trust-boundary.txt`, with ledger **A8**'s and
  **A9**'s `**Lean:**` lines naming it. It is the fourth name on the boundary and the first
  that is not a clause of `prop:fourier-toolbox`. Priced **L (interface)**; admitted, as the
  trust boundary anticipated.
* The assembly is `SpatialLine.kernel_regularity`, in `SpatialLine/KernelRegularity.lean`.
  Priced **M**; paid **S**, and the reason is the round's clearest instance of reading the
  obligation rather than the argument.

**The hypothesis check needs neither of the nodes the printed proof cites.**

1. *Self-decomposability of the kernel from the origin is a change of scale.*
   `def:self-decomposable` asks, for each `b > 1`, for a probability law whose transform is the
   missing factor `e^{-(F(χ(t)ω) - F(χ(t)ω/b))}`. Because the gauge is **onto** `[0,∞)`, that
   factor is the transform of an increment of the family itself: pick `t'` with
   `χ(t') = χ(t)/b`, necessarily `t' ≤ t`, and `lem:additivity` says `μ_{t',t}` is the law.
   So the clause is `prop:canonical-gauge` plus `lem:additivity`, and neither
   `lem:selfdecomposable-exponents` nor any Lévy pair enters, and
   `SpatialLine.isSelfDecomposable_kernel` prints Lean core.
2. *Nondegeneracy needs only that some frequency is moved*, which is `prop:canonical-gauge`'s
   last clause, not `prop:strict-positivity`(2). `SpatialLine.kernel_ne_dirac_zero`, Lean core.
   This is the third site in the chapter where that substitution works — after (ND) in the
   construction direction and the gauge's own nondegeneracy — and it is now worth stating as a
   rule of thumb: **`prop:strict-positivity`(2) is never needed to know that a kernel is not a
   point mass.**

The consequence for the axiom footprint is exactly what R27's split was for:
`kernel_regularity`'s `#print axioms` is Lean core plus `kernel_regularity_law`, with nothing
from the `[T]` hypothesis check. The blueprint's assignment paragraph was rewritten to the
checked route.
-/

end Skeleton
