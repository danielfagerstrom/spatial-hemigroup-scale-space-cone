/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Skeleton.Chapter7
import SpatialLine.ConeDefs

/-!
# The target types of Chapter 8 — the admissible cone

**This file carries `sorry`s and is not part of the `SpatialLine` library.**

## What writing this chapter down found

**1. The Choquet measure's tail identity has to be almost-everywhere, and phase A's is not.**
`lem:cin-rays`(2) says "`ϖ((x,∞)) = k(x)` for almost every `x > 0`", and it is right to: the map
`x ↦ ϖ((x,∞))` is right-continuous, while an `SDProfile`'s `k` is only `AntitoneOn (Ioi 0)`, so
a profile that is left-continuous at a jump admits **no** `ϖ` satisfying the identity at every
point. Phase A's `sd_exponents_symbol` and `sd_exponents_profile_measure` took the everywhere
form as a hypothesis, which is therefore a hypothesis some admissible profiles cannot meet.
`SpatialLine.HasProfileTail` is the a.e. form, matching Paper I's `HasLevyTail` and the
blueprint's own wording. Question **Q7** — whether to relax phase A too — was answered *yes* by
the review (2026-09-09), and R2 shows the choice was not a matter of taste: in its `toReal` form
the everywhere identity is satisfied by a measure with infinite tails, so `sd_exponents_symbol`
was false as written. It now takes `HasProfileTail`, and `sd_exponents_profile_measure` states
its tail conclusion in the same `ofReal` form. One convention holds throughout.

**2. `prop:choquet-cone`'s injectivity is false without the domain condition.** The
superposition map is stated on `ℝ≥0∞`, where two pairs outside the domain both give the constant
`⊤` and are not distinguished. The blueprint states the bijection *between the domain and the
cone*, so the Lean statement carries the finiteness hypothesis on both sides; without it the
uniqueness clause would be false as written rather than merely unprovable.

**3. `prop:cin-origin-singularity` says nothing at `c = ∞`.** The node puts
`c := k(0+) ∈ (0,∞]` and then gives three regimes, `c < 1`, `N < c ≤ N+1` for integer `N ≥ 1`,
and `c = 1`. No regime covers `c = ∞`, so the node makes no claim there, and `c = ∞` is common:
the stable profile `C_α^{-1}x^{-α}` has `k(0+) = ∞`, as does every completely monotone profile
with an unbounded Thorin measure. That is faithful to ledger A10, which is stated for finite `c`;
it is recorded because the sentence "put `c := k(0+)` in `(0,∞]`" invites the opposite reading.

**Corrected (review 2026-09-09, R26)**: this paragraph named the Matérn profile alongside the
stable one as a case of `c = ∞`, and it is not — `maternProfile γ θ` has `k(0+) = 2γ`, finite,
which is what SKELETON.md's F19 says. The Matérn family is in fact the *check* on the three
regimes: `γ = 1/2` gives `c = 1`, the threshold with its logarithmic singularity, which is the
`K_0` kernel of `matern_density_special`'s second clause; and `γ = 1` gives `c = 2`, hence
`N = 1` and a `C^0` density, which is the Laplace kernel's kink. Both are what A10 predicts.

**4. The delay equation's two forms are two different readings, not a rewriting.** The first,
`x p(x) = P(x) - (1/2)[P(x-τ) + P(x+τ)]`, is an identity between locally integrable functions
and is stated almost everywhere. The second, `x p'(x) = -(1/2)[p(x-τ) + p(x+τ)]`, is genuinely
distributional — `p` need not be differentiable — and is stated by testing against `C_c^∞`. The
node's "equivalently" is the passage between them, an integration by parts and not a rewriting.
-/

namespace Skeleton

open MeasureTheory Set Filter SpatialLine
open scoped ENNReal Topology

/-! ## `lem:cin-rays` (draft Lemma 8.1) — [T], **proved and moved (2026-09-09)**

Class (b) — twin `Hemigroup.dickman_superposition`: `Ein` becomes `Cin`, the one-sided profile
becomes the folded one, and the layer-cake exchange is the same. The growth clauses have no
causal counterpart, `Ein` being bounded by the identity where `Cin` is not.

All six declarations are proved and live in `SpatialLine`: `cin_elementary`,
`cin_expansion_zero` and `cin_expansion_top` in `SpatialLine/Cin.lean`; `cin_ray`,
`cin_superposition` and `cin_superposition_exists` in `SpatialLine/CinRays.lean`. Each prints
Lean core.

Priced (in the node table's order) M,S,S,M,M,M and paid M,S,S,M,S,S. The two divergences are
both about which half of the node is the work. `cin_superposition` and
`cin_superposition_exists` were priced M each and are **S**: the first is Paper I's
`exponent_eq_lintegral_ein` with `1 - cos` in place of `1 - e^{-·}`, the layer cake taking the
substitution without noticing the change, and the second is the quantile construction of
`Subordinator.lean` transcribed unchanged — the only edit is `IsCausal` becoming `IsFolded`,
`Iio 0` becoming `Iic 0`. What Paper I does **not** supply is `cin_expansion_top`, priced M and
paid M in full: `Ein` is bounded by the identity, so the causal article never meets a
conditionally convergent integral, and the constant `C` has to be reached by one integration by
parts against `sin v / v` with the remainder past `z` dominated by `∫_z^∞ v^{-2} dv`. The
`ScaleSpaceCore` candidate this wave produces is therefore the *tail measure*, not `Cin`:
`tailInv` and `exists_tailMeasure` now exist twice, in two articles, character for character.
-/

/-! ## `prop:choquet-cone` (draft Proposition 8.2) — [T]

Class (b) — twin `prop:extreme-rays`, which has no Lean declaration; the port is verbatim with
the Gaussian ray in the drift's place. The shape change TWINS.md records — the distinguished ray
is a genuine smoothing member here and a degenerate boundary member there — is invisible in the
Lean statements and visible only in `rem:cone-shape`.
-/

/-! ### Proved and moved — the node is closed (2026-09-09, waves 2 and 3)

All eight declarations are proved and live in `SpatialLine`. Wave 2 moved four into
`SpatialLine/ChoquetCone.lean` — `choquet_cone_forward`, `choquet_cone_surjective`,
`choquet_cone_domain` and `choquet_cone_linear`, each on Lean core. Priced M,M,M,S and paid
M,S,M,S — the surprise is that `choquet_cone_surjective` is **S** once
`choquet_cone_forward`'s Tonelli block exists, because the two are the same computation read in
the two directions, and the annotation that priced them separately at M each was pricing the
exchange twice.

`choquet_cone_domain`'s own re-price is recorded in the module docstring of
`SpatialLine/ChoquetCone.lean`: the blueprint asks for a comparison of `Cin(z)` with `z²` and
with `log z` uniform on compacta of the punctured line, and the checked route needs only two
*lower* bounds and monotonicity, monotonicity covering the bounded middle stretch outright.

Wave 3 moved the other four into `SpatialLine/ChoquetExtreme.lean` — `choquet_cone_injective`,
`choquet_cone_extreme_gaussian`, `choquet_cone_extreme_cin` and `choquet_cone_extreme_only`.
All four spend **uniqueness of the Lévy pair**, `prop:fourier-toolbox`(3)'s third clause, ledger
**A3**, which chapter 10 had already admitted as `SpatialLine.fourier_toolbox_levy_unique`; no
axiom was added for this chapter, and each of the four prints Lean core plus that one name. The
single place the interface is spent is `SpatialLine.sdProfile_unique` — two profiles with the
same exponent have the same Gaussian coefficient and the same profile measure — and everything
else goes through `SpatialLine.ae_eq_k_of_exponent_eq`.

Priced M–L, M, M, L and paid M–L, S, M, L. What the four cost against their re-prices:

* `choquet_cone_injective` — **M–L** as re-priced, and paid there. The two steps named as the
  price are what they cost: `SpatialLine.tail_eq_of_ae_tail_eq` (tails equal at almost every
  positive point are equal at every positive point — continuity from below along
  `Ioi (x + 1/(n+1))`, each term squeezed between two tails at points of the co-null good set)
  and `SpatialLine.measure_eq_of_tail_eq` (two folded measures with equal tails are equal — the
  restrictions to `Ioi ε` are *finite*, so `Measure.ext_of_Iic` applies where no π-system
  argument on the whole line does, an `Ioc ε t` being a difference of two finite tails). The
  π-system route the re-price anticipated is not the one taken: the Choquet measure of a bounded
  profile has infinite mass near the origin, so no exhausting sequence of finite-measure sets in
  a π-system generating the Borel sets exists, and the exhaustion has to happen *after* the
  restriction. Both lemmas are stated for arbitrary measures and are `ScaleSpaceCore`
  candidates.
* `choquet_cone_extreme_gaussian` — priced **M**, paid **S**. Read at the profile rather than in
  the coordinates the obligation is: the summed profile has the Gaussian datum's exponent, so
  its profile measure is null, so both summand profiles are null a.e., so each exponent is its
  own Gaussian coefficient times `ω²`. `lem:admissible-cone`'s `SDProfile.add` supplies the
  summed profile and was proved in wave 2, so the duplication risk the re-price named did not
  materialise. Domination of one Lévy measure by another, which the re-price expected to need,
  is not available in this development and is not used: equality with the null measure is.
* `choquet_cone_extreme_cin` — priced **M**, paid **M**, by exactly the route wave 2 recorded:
  `k₁ + k₂ = 1` a.e. on `(0,τ)` with both antitone makes each summand a.e. constant there, and
  a.e. zero above `τ` by nonnegativity. `choquet_cone_injective` is *not* used.
* `choquet_cone_extreme_only` — priced **L**, paid **L**, but the cost is not where the re-price
  put it. "A positive measure that is not a multiple of a Dirac splits" is not a piece of
  measure theory Mathlib has to supply: it is an infimum argument. With `T` the set of
  thresholds below which the Choquet measure carries mass and `τ = inf T`, either some threshold
  has mass on both sides — and then the two restrictions give two admissible exponents summing
  to the whole, extremality makes the lower one a multiple of the whole, and
  `choquet_cone_injective` turns that into an equality of measures the upper interval's mass
  refutes — or every threshold has mass on at most one side, and then the tails vanish above `τ`
  by the defining property of an infimum and below it by minimality, so the measure is carried
  by `{τ}` and the exponent is a multiple of `Cin(τ·)` with no `δ_τ` ever constructed. The
  Gaussian alternative is what remains when the Choquet measure vanishes; and the Gaussian
  coefficient is forced to zero as soon as it does not, by the same splitting applied to
  `(a,0)` and `(0,ϖ)`.
-/

/-! ## `lem:cin-delay-equation` (draft Lemma 8.4) — [T]

Class (c) — the causal article states the Dickman delay equation in prose in its cone remark and
has no node for it. The two-sided form averages the two neighbours where the causal form has one
delayed value.
-/

/-! ### Proved and moved — the node is closed (2026-09-10, waves 5 and 6)

All three declarations are proved and live in `SpatialLine`: the node's two,
`SpatialLine.cin_delay_equation` and `SpatialLine.cin_delay_equation_deriv`, in
`SpatialLine/CinDelayForm.lean`, together with the measure form
`SpatialLine.cin_delay_measure_form` that carries them and wave 5's
`SpatialLine.cin_delay_deriv_of_measure_form` in `SpatialLine/CinDelay.lean`. Each prints Lean
core; no axiom was admitted for this node.

**Changed (proof 2026-09-10): both declarations gained `hpmeas : AEMeasurable p volume`**, the
hypothesis wave 5 recorded as a review question at `cin_delay_deriv_of_measure_form`. It is not
a convenience but a repair: the reviewed statements were **false** without it. The hypothesis
`μ = volume.withDensity (ofReal ∘ p)` sees a non-measurable `p` only through the measurable
simple functions below it, so raising `p` on a Bernstein set --- inner measure zero, full outer
measure --- leaves the hypothesis intact while the conclusion fails on a set no null set
contains; and the derivative form fails likewise, at a test function supported where `p` was
altered but `p(·±τ)` was not, one side being junk-zero and the other not. Every call site
supplies the hypothesis, `prop:kernel-regularity` producing the density.

Priced (from wave 5's re-price) **L** for the single remaining obligation, and paid **L**, with
the two node declarations free on top of it. What the route cost, against the estimate:

* The estimate said "match the characteristic functions of those two finite signed measures and
  appeal to `Measure.ext_of_charFun` at the Jordan recombination", and that is what it cost.
  The left transform is the sine moment (`charFun_jordan_sub`, symmetry killing the cosine
  part), identified by differentiating `fourierCos μ` under the integral sign — the one place
  wave 3's moment `cin_law_integrable_abs` is spent — with the ODE
  `ω c'(ω) = −c(ω)(1 − cos τω)` read off `hasDerivAt_cin` and the chain rule.
* **The right transform came for free, and the estimate had priced a Fubini for it.** The
  measure `μ(x−τ, x]dx` is `μ ∗ (Lebesgue on [0,τ))`, a `Measure.conv`, so `charFun_conv`
  supplies its transform and the only integral to evaluate is `∫₀^τ e^{iωu}du`. The printed
  proof's signed Levy weight `y ν₂(dy) = ½ sgn(y)1_{|y|<τ}dy` is the difference of that window
  and its translate, halved: the same convolution, expressed so that only positive measures are
  convolved and the subtraction happens at the end. Nothing is convolved with a signed measure
  anywhere.
* A Tonelli *is* written, once, in `conv_delayWindow_eq_withDensity`, and it is spent
  identifying the convolution's **density**. The measure form does not need it; only
  `cin_delay_equation` does, which is the honest statement of what separates the node's two
  declarations.
* The primitive form's a.e. conclusion is reached without any set-integral machinery: the
  pairing holds for every bounded measurable test function, so it holds at the *sign* of the
  defect, and `∫|F₁ − F₂| = 0` follows in one line.

**What the earlier estimates were wrong about, twice over.** Wave 2 priced the primitive form
above the derivative form because Fourier uniqueness applied to `x p` presupposes the first
absolute moment; wave 3 proved the moment in four lines and re-read the ordering as "the
derivative form needs no signed-measure uniqueness and pays for it with a Parseval step
instead". Neither reading survives: there is no Parseval step, no Fourier inversion and no
multiplication formula pairing a finite measure with a Schwartz function — the ingredient wave 3
named as missing from Mathlib — because the identity is between measures and never between
distributions. Judgement point 10 in its plainest form: both estimates were made by reading the
printed proof and asking what it presupposes.
-/


/-! ## `prop:cin-origin-singularity` (draft §8, additive) — ledger A10

Class (c). The one `[A]` node of the chapter and the only place this article looks at a kernel's
local behaviour.

**What A10 carries**: the three regimes and the threshold formula, for a self-decomposable law
on the line with no Gaussian part, stated at the source in terms of the two-sided profile at the
origin (Sato Thm. 28.4 p. 191 for the smooth regime, Thm. 53.8 pp. 410–411 with (53.28) and
(53.30) for the singular regime and the threshold). **What it does not carry**: the translation
into this article's folding convention — the source's constant is the sum of the two one-sided
limits, which is exactly the folded `k(0+)` used here, and the source's antisymmetric constant
vanishes for a symmetric law — nor the propagation to the multiples of `τ`, which is
`cin_delay_equation_deriv` and is `[T]`. The ledger records a **deliberate narrowing**: the node
claims the *order* of the singularity and not the constant of (53.30), whose reading is not
settled.

Range: the entry and the node are stated for finite `c`; nothing is claimed when `k(0+)` is
infinite, which is the Matérn and stable case. See the module docstring, finding 3.

### Wave 6 (2026-09-10): the decision is re-taken, and the node was never blocked

**`prop:cin-origin-singularity` was never blocked on `lem:cin-delay-equation`.** Waves 4 and 5
both listed its three declarations under "blocked upstream --- behind `cin_delay_measure_form`",
and both were wrong. Read at the statements, the three quantify over an arbitrary `SDProfile`
with `a = 0`, its `c = k(0+)`, and a law with that exponent, and conclude about the law's density
near the origin: no `τ`, no delay equation, no propagation appears in any of them. What was
blocked on the delay equation is the *propagation* to the multiples of `τ`, and review Q8 moved
that out of the node into `rem:cin-propagation` in 2026-09-09. So closing `lem:cin-delay-equation`
this wave does not move this node at all: it is a **decision item, not a work item**, and it has
been so since Q8. This is judgement point 1 on an entry the campaign wrote itself, twice.

(With it: the node's `\uses` edge to `lem:cin-delay-equation` is vestigial for the same reason —
it was there for the propagation clause Q8 removed. Left in place; removing an edge is a review
decision, and the node's annotation does still discuss the delay equation under "what the entry
does not carry".)

**No axiom was admitted, and the reason is not that the statements are wrong.** They were checked
at their edges this wave and they hold up:

* `c = 0` — excluded by `hc0 : 0 < c` in the singular regime, by `1 ≤ N < c` in the smooth one,
  and by `c = 1` in the threshold one. The exclusion is **load-bearing**: with `a = 0` and
  `k(0+) = 0`, antitonicity and nonnegativity force `k ≡ 0` on `(0,∞)`, so the exponent vanishes
  and the law is `δ₀`, which has no density at all. A clause firing at `c = 0` would be false,
  not merely unprovable.
* The Gaussian — excluded twice, by `ha : P.a = 0` and by `c = 0`. Also load-bearing: a law with
  `a > 0` has a smooth density whatever `c` is, which no regime keyed to `c` alone predicts.
* `c = ∞` — excluded by the shape of the hypothesis, `Tendsto P.k (𝓝[>] 0) (𝓝 c)` with `c : ℝ`
  being unsatisfiable when the right limit is infinite. That is the stable profiles and every
  completely monotone profile with an unbounded Thorin measure, and it matches the entry's own
  range.
* None of the three is vacuous: the threshold regime is met by the `Cin` rays
  (`cin_origin_singularity_cin_ray`), the singular regime by `c·1_{(0,τ)}` for `0 < c < 1`, and
  the smooth regime by the Matérn profile at `γ = 1`, where `c = 2` and `N = 1`.

**What blocked admission was that nothing spends them, and one thing more.** No declaration in
`SpatialLine` used any of the three. The single assembly available — instantiating the threshold
regime at the `Cin` ray, whose hypotheses `cin_origin_singularity_cin_ray` already verifies, to
get "the `Cin` ray's kernel is logarithmically singular at the origin" — would consume **one** of
the three, leaving `cin_origin_singularity_unbounded` and `cin_origin_singularity_smooth` as two
names nothing spends. That is the `bridge_delay_law` situation the campaign declined three waves
running — and which the author settled at Chapter 9 on 2026-09-10 the other way about, by
narrowing the node rather than admitting the interface, so that declaration no longer exists.
Manufacturing a consumer to justify an admission is not a different decision from admitting
without one. Beyond that, admitting these names would put on the trust boundary a
step the ledger says it does **not** carry: the translation into this article's folding
convention. The translation is correct — for a symmetric law the folded `k(0+)` is
`k₂(0+) + k₂(0−)`, which is the source's constant — but it is asserted in the node's annotation
and not in the citation, so putting it behind an admitted name is a review decision, not a
prover's.

### Both obstacles were removed, and the entry is admitted (2026-09-15)

`lem:folding-translation` (`SpatialLine/TwoSidedProfile.lean`, Lean core) is the translation, and
`cor:origin-boundedness` is a consumer that reads all three regimes. **Ledger A10 was admitted on
2026-09-15, the author's decision**, as `sato_origin_singular`, `sato_origin_smooth` and
`sato_origin_threshold` in `SpatialLine/Interfaces.lean`, stated at Sato's letter over a
`TwoSidedProfile`.

**So the four declarations this section used to hold are gone from `Skeleton/`.** The three
regimes are `SpatialLine.cin_origin_singularity_unbounded`, `_smooth` and `_threshold`, and the
threshold corollary is `SpatialLine.origin_boundedness`, all four in
`SpatialLine/OriginSingularity.lean` and all four proved, at the signatures the reviewed skeleton
gave them. What is left here is the record above of how the statements were designed and checked,
which is the part of this chapter's skeleton that is still worth reading.
-/

/-! ### `cin_origin_singularity_cin_ray` — proved and moved (2026-09-09, wave 2)

The node's fourth declaration, the `[T]` half, is `SpatialLine.cin_origin_singularity_cin_ray`
in `SpatialLine/CinRays.lean`, on Lean core. **It needed nothing.** Priced **S given the
threshold clause**, it turns out to quantify over no law and to mention no density: it says that
`cinProfile τ` has right limit `1` at the origin and that the inner integral of the node's
threshold function vanishes on `(y,τ)`. Both are the constancy of an indicator on its own
interval. Ledger A10 bounds what the *node's* proof cites; it does not bound what this clause
needs, and reading the clause rather than the node is what makes the difference between S and
free.

The node was `\notready` until 2026-09-15: its three `[A]` clauses were unproved and no proof in
this development consumed them. With ledger A10 admitted it is `\leanok`, and this clause is
unaffected — it never spent A10 and still prints Lean core.

(The literal newline that stood in place of this backslash until wave 3 was a
non-raw-string-literal edit, the trap `CLAUDE.md` names; `scripts/check-control-chars.py` does
not see it, because a newline is not a control character.)
-/

/-! ## `cor:origin-boundedness` (module B step 2, 2026-09-15) — [A] on A10

The postdoc's P-0008. The threshold `c = 1` of the three regimes above is a statement about the
*profile*, and it is the boundary the external review's finding C found from the other side at
the Matérn closed form. The corollary says so once, for every admissible kernel; clause (2)'s two
named instances are `SpatialLine.cin_origin_singularity_cin_ray` and
`SpatialLine.matern_origin_constant`, both on Lean core, and only clause (1) is `[A]`.

**Why this is the consumer A10 lacked.** Wave 6 recorded that the one assembly available would
spend one of the three regimes and leave two unspent. This one reads all three: the smooth regime
above the threshold, the singular regime below it, the threshold regime at it.

**What the proof consumes**, beyond the three regimes: at `c = 1`, that the comparison
function `L` is unbounded at the origin — `k` is nonincreasing with `k(0+) = 1`, so `k ≤ 1` on
`(0,∞)`, the inner integrand is nonnegative, `K ≥ 1` and `L(x) ≥ log(1/|x|)`, which is the
argument row R100 already wrote down; and, for the passage from *one* unbounded representative to
*every* representative, a comparison of measures rather than of functions: a representative
bounded by `M` near the origin makes `μ((0,ε)) ≤ Mε`, while the regime's lower bound makes it at
least `c₁ε^c/c`, and the ratio `ε^{c-1}` is unbounded. Neither step needs measurability of the
competing representative, `lintegral` being monotone without it.

**Priced M once the interface is admitted; paid M–L on 2026-09-15**, the interface having been
admitted the same day. The estimate was right about which two steps the proof adds and wrong
about their weight: the measure comparison is three short lemmas, but the divergence of `L` at
the threshold costs four more — the integrability of the inner integrand on `(y,1)`, the
antitonicity of the inner integral in `y`, the integrability of `K(y)/y` on `(x,1)` (needed
because a Bochner integral of a non-integrable function is `0` by convention, which would make
the regime's lower bound vacuous rather than false), and only then the comparison with
`∫_{|x|}^1 y^{−1}dy`. `SpatialLine.origin_boundedness` and its seven supporting lemmas are in
`SpatialLine/OriginSingularity.lean`.
-/

end Skeleton
