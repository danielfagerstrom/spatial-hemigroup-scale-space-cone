/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Skeleton.Chapter8
import SpatialLine.Corners

/-!
# The target types of Chapter 9 — the subordination bridge

**This file carries `sorry`s and is not part of the `SpatialLine` library.**

`def:causal-admissible` is a definition and lives in `SpatialLine/Bridge.lean` with `\leanok`;
it is the **import candidate** TWINS.md names, to be replaced by the shared type when Paper I's
`Hemigroup.SelfDecomposableExponent` moves to `ScaleSpaceCore`. There is no lake dependency on
Paper I's package.

## What writing this chapter down found

**1. The causal *axioms* are not available here, and are not needed.** `prop:bridge-families`
begins "let `(Φ^I_{x,y})` be a time-causal family satisfying the causal axioms". Those axioms
are Paper I's `Hemigroup.CascadeFamily`, which this repository does not import. What the proof
uses is not the axioms but their **conclusion**: that in the canonical gauge the causal kernels
have Laplace transform `exp[-(F_I(yσ) - F_I(xσ))]`. So the family is quantified over that
specification, exactly as phase A quantifies over `IsKernelFamily` rather than over a proved
representation. Nothing is lost, the causal main theorem being an equivalence, and the statement
is honest about which half of the causal theory the bridge consumes.

**2. `lem:bridge-exponents` splits at the ledger boundary, and the split is visible.** The two
entries A11 and A12 carry exactly one step: that `exp(-τg)` is completely monotone for a
Bernstein `g` and that such a function with value `1` at the origin is a Laplace transform. That
step is `bridge_delay_law`, whose conclusion is the existence of the delay law; everything after
it — that a Gaussian mixture is positive definite, that the mixture's exponent has the profile
form, and the profile formula itself — is `[T]` and is the other two declarations. Splitting
that way means the `#print axioms` of the two `[T]` declarations will not mention A11 or A12 at
all once the delay law is a hypothesis.

**3. The probabilistic reading is a statement about `Measure.bind`, not about a probability
space.** "`Ψ` is the exponent of `B_{T_1}` with `T_1` independent of `B`" is the cosine transform
of `ρ.bind brownianLaw`, the mixture of Gaussian laws against the delay law. That keeps phase
A's decision — `def:self-decomposable` declined to introduce a probability space — and it is
also the object `eq:bridge-families` needs, so the same construction serves both nodes.

**4. `prop:bridge-families`(5) is `bridge_families`'s own conclusion at `s = 0`.** "The spatial
canonical gauge is the square root of the causal one" is the assertion that the kernel from the
origin at spatial scale `t` has transform `exp(-F_I(t²ω²/2))`, which is the displayed conclusion
of `bridge_families` read at `s = 0`. No separate declaration corresponds to it, and the node's
`\lean` tag is complete without one.
-/

namespace Skeleton

open MeasureTheory Set Filter SpatialLine
open scoped ENNReal Topology

/-! ## `lem:bridge-exponents` (draft Lemma 9.1) — `[T]`, no ledger entry

Class (c): the causal article has no bridge chapter. What is *not* new is the causal cone
itself, which is `def:causal-admissible`.

**THE DELAY-LAW INTERFACE IS DELETED (author's decision 2026-09-10), AND THE NODE'S TYPE MOVED
WITH IT.** The declaration that stood here, `bridge_delay_law`, asserted that a causally
admissible `F_I` has `exp(-F_I)` — and `exp(-τ(F_I - F_I(c²·)))` for every `τ > 0` and
`c ∈ [0,1)` — as the Laplace transform of a probability law on `[0,∞)`. It was the node's one
`[A]` step, carrying ledger **A11** clause (a) with **A12**, and it had **no consumer**:
`SpatialLine.bridge_exponents` was proved without reading it (see below), and nothing else in
the development spends it. The decision narrows the node rather than admitting two axioms
nothing needs:

* the blueprint statement drops the delay-law clause and states the mixture reading
  *conditionally* — given a delay law with the prescribed Laplace transform, `B_{T_1}` has
  cosine transform `exp(-Ψ)` — which is `SpatialLine.bridge_exponents_mixture` unchanged;
* `SpatialLine.bridge_exponents` **loses its hypothesis** `hρ`, which it never read. Its type
  is now `(F : CausalAdmissible) → ∃ Q : SDProfile, …`; dropping a hypothesis strengthens the
  theorem, and no consumer had to be rewired, the declaration having none outside the axiom
  guard;
* the existence of the delay is the blueprint's `rem:bridge-subordination`, which cites A11(a)
  and A12 in prose and is marked as not machine-checked.

The node is therefore `[T]` and `\leanok` at the two `SpatialLine` names, and this chapter
spends no ledger entry.
-/

/-! ### The admissibility clause and the mixture reading — **proved and moved**
(2026-09-10, wave 4)

`SpatialLine.bridge_exponents` and `SpatialLine.bridge_exponents_mixture`, statements verbatim,
in `SpatialLine/BridgeExponents.lean`. **Both are Lean core**, so neither ledger A11 nor A12 is
on either declaration's path. The two entries were spent only by `bridge_delay_law`, which had
no consumer at all, and which the author's decision of 2026-09-10 deleted along with the node's
delay-law clause; `bridge_exponents` lost the unused hypothesis `hρ` at the same time.

**The finding, and the price.** `bridge_exponents` was priced **L**, with the mixture-to-`LEₛ`
passage — the analysis half of Chapter 7 — named as the cost. That passage is not on the route,
and the declaration's hypothesis `hρ`, the delay law, was **carried unused** and is now gone.
What a proof cites
is an upper bound on what a statement needs: the printed proof uses the delay law to make
`Ψ - Ψ(c·)` positive definite and then calls `lem:selfdecomposable-exponents` to *produce* an
`SDProfile`, but the statement *prescribes* the profile, and a prescribed profile is checked
field by field.

Five of the six fields are termwise or Tonelli. The sixth is `k_antitone`, which the blueprint
itself singles out as "not visible term by term" because the derivative of `x g_u(x)` changes
sign at `x = √u` — and it becomes visible term by term in the right variable. The substitution
`u = x²v` leaves `du/u` invariant and moves the entire `x`-dependence into `k_I(x²v)`:

  `x ν₂(x) = ∫₀^∞ e^{-1/2v}/(v√(2πv)) · k_I(x²v) dv`.

That is `CausalAdmissible.ofReal_mul_mixDensityL`, and monotonicity follows by `lintegral_mono`.

**Paid M.** The cost is `mixDensityL_ne_top` — finiteness of the mixture off the origin — plus
the Tonelli exchange. Finiteness is where the *asymmetry of the two integrability fields* of
`def:causal-admissible` shows: the mixture integrand carries `du/u` where the first field
carries `du`, so the missing power of `u` has to come from the Gaussian, and it does:
`g_u(x)/u ≤ 16/x⁴` for `u ≤ 1` (`brownianDensity_div_le`). Above `1` the density is at most `1`
and the second field is used verbatim. The two Lévy conditions of `SDProfile` then come from
`lem:profile-integrability` and `∫(1 ∧ x²)g_u(x)dx ≤ 1 ∧ u`, so the spatial Lévy condition *is*
the causal integrability condition with the Gaussian doing the truncation.

`bridge_exponents_mixture` was priced **M** and paid **M**: conditioning is
`Measure.lintegral_bind` read through `1 - cos` rather than through `cos`, because Mathlib has
no Bochner `integral_bind` and that integrand is nonnegative.

**What the next round decided (2026-09-10).** `bridge_delay_law` was an `[A]` interface with no
consumer. Admitting it as an axiom would have made `lem:bridge-exponents` proved at the price of
two trust-boundary names nothing spends. The author narrowed the node instead: the delay-law
clause is dropped, the mixture clause quantifies over a delay law, and the existence moves to
the blueprint remark `rem:bridge-subordination`, cited and not machine-checked. The resulting
types are in the section note at the head of this chapter.
-/

/-! ## `prop:bridge-families` (draft Proposition 9.2) — [T]

Class (c). Note that the node's forward `\uses` edges to the corner nodes were removed on
2026-09-07 because they made the dependency graph cyclic; the identification of the images is a
computation done here and the corner nodes cite this one, not the other way round. The Lean
statements keep that direction.
-/

/-! ### The family clause and two corners — **proved and moved** (2026-09-10, wave 4)

`SpatialLine.bridge_families` (`SpatialLine/BridgeFamily.lean`),
`SpatialLine.bridge_families_delay` and `SpatialLine.bridge_families_stable`
(`SpatialLine/BridgeCorners.lean`), statements verbatim. `bridge_families` spends **A1** and
**A3's converse**, both inherited from `main_construction`; the other two are Lean core.

`bridge_families` was priced **L**, inherited from `main_construction`, and paid **M**: the
inheritance is real, and what is done here is three identifications, none of which repeats any
analysis.

1. **The scaling action.** `main_construction` hands back its `S` as the gauge conjugate
   `χ⁻¹(λχ(t))`, and the node asserts `S_λ t = λ t` as a **function equality**. Those differ
   off `[0,∞)`, where the conjugate is junk. The family is therefore assembled from
   `ConstructionData` directly, with `S := fun lam t => lam * t` and the four covariance
   obligations discharged at that `S`; that is legitimate because every field of
   `IsScaleCovariant` reads `S λ` on `Ici 0` only. This is the kind of mismatch that is
   invisible in prose and shows up the moment the target type is written down.
2. **The kernels.** The constructed kernels and the Gaussian mixtures are two families of
   symmetric probability measures with the same cosine transform, hence equal by
   `prop:fourier-uniqueness`; that is what carries `IsKernelFamily` from one to the other.
3. **The transform.** `fourierCos_bind_brownianLaw` at `σ = ω²/2`.

`hne` (the review's R6 addition) is spent exactly once, at (ND), through
`CausalAdmissible.exponent_of_nonpos`: a causal exponent vanishes on `(-∞,0]`, so a frequency
where `F_I` is nonzero is positive, and `√(2σ)` is the spatial frequency above it.

**Two findings at the corners.** `bridge_families_stable` consumes *neither* of its hypotheses:
`(ω²/2)^α = 2^{-α}|ω|^{2α}` is an `rpow` identity for every real `α`, and `0 < α ≤ 1` is a fact
about the node's range, not about the substitution. `bridge_families_delay`'s kernel clause does
not consume `0 ≤ v` either, `brownianLaw` being total. Both statements are kept verbatim and the
linter is silenced, as at `representation_symmetric`.

**Still stated: `bridge_families_gamma`, re-priced M-L.** It is the last declaration of the
node, and it needs two classical integrals, neither in Mathlib and neither reachable by the
route the Bessel corner took.

* The exponent clause needs the **exponential Frullani** integral
  `∫₀^∞(1 - e^{-σu})e^{-u}du/u = log(1+σ)`. `SpatialLine/Frullani.lean` has the *cosine*
  Frullani, not this one, but its technique transfers directly and is shorter here: with
  `G(σ) = ∫₀^∞(e^{-u} - e^{-(1+σ)u})du/u`, `G(0) = 0` and `G'(σ) = ∫₀^∞ e^{-(1+σ)u}du =
  1/(1+σ)`, and differentiation under the integral sign against a dominating function is the
  same step as `CausalAdmissible.hasDerivAt_exponent`. Priced **M** on its own.
* The profile clause needs the **first-passage Laplace transform**
  `∫₀^∞ x(2πu³)^{-1/2}e^{-x²/2u}e^{-σu}du = e^{-x√(2σ)}`. The route that exists in this library
  is through `besselK_half` (`SpatialLine/BesselHalf.lean`), which already has
  `K_{1/2}(z) = √(π/2z)e^{-z}`: the substitution `u = √(A/B)e^{v}` turns
  `∫₀^∞ u^{-3/2}e^{-A/u - Bu}du` into `(A/B)^{-1/4}·2·K_{1/2}(2√(AB))`, and at `A = x²/2`,
  `B = σ` that is the identity. What it costs is an **exponential** change of variables from
  `ℝ` onto `(0,∞)`, which is not `integral_comp_rpow_Ioi` and which this development has not
  needed before, plus the even-part folding of a Bochner integral on the line (the `ℝ≥0∞`
  folding is `lintegral_even_eq_two_mul`, in `SpatialLine/BridgeExponents.lean`). Priced
  **M-L** on its own, and it is the item to attempt first, because the skeleton already
  observes that `prop:thorin-subclass`(4) needs the same identity.
-/

/-! ### The Gamma corner — **PROVED AND MOVED (wave 5, 2026-09-10)**, and the node closes

`SpatialLine.bridge_families_gamma`, statement verbatim, in `SpatialLine/BridgeGamma.lean`,
**Lean core**. With it `prop:bridge-families` is `\leanok` at all five declarations.

Priced **M**, re-priced **M–L** by wave 4 on two classical integrals, and paid **M**. Both
re-pricings were of the *printed argument* rather than of the obligation, and each was wrong in
a different direction.

**The exponent clause needs no integral at all.** Wave 4 named the exponential Frullani
`∫₀^∞(1 - e^{-σu})e^{-u}du/u = log(1+σ)`, priced **M** on the technique of
`SpatialLine/Frullani.lean`. It is never written. Wave 4's own
`CausalAdmissible.bridgeDatum_exponent` says that `F_I(ω²/2)` **is** the exponent of the
`SDProfile` whose folded profile is `eq:bridge-profile`; so once the profile clause identifies
that profile with `maternProfile γ (1/√2)`, the exponent is evaluated by
`SpatialLine.lintegral_maternProfile` — the *spatial* Frullani, wave 2's, already proved for
`prop:matern-exponent`(1). Ten lines. The causal integral is an upper bound on what the
statement needs, and the two chapters' machinery meets in the middle.

**The first-passage identity was over-priced for a reason that does not hold in `ℝ≥0∞`.** Wave 4
priced `∫₀^∞ u^{-3/2}e^{-A/u-Bu}du = √(π/A)e^{-2√(AB)}` at **M–L**, the cost being "an
exponential change of variables from `ℝ` onto `(0,∞)`, which is not `integral_comp_rpow_Ioi`
and which this development has not needed before", plus the folding of a Bochner integral on the
line. In `ℝ≥0∞` both are cheap: the substitution is
`lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn`, which asks for measurability, the
derivative and **monotonicity** and neither injectivity nor an integrability side condition; and
the folding of the line onto the half-line is a set split, free where a Bochner split would
first have to prove the integrand integrable. The Bochner value comes back by the positivity
trick wave 4 recorded at `bridge_families_bessel`. It is
`SpatialLine.lintegral_Ioi_firstPassage` in `SpatialLine/FirstPassage.lean`, paid **M**, and
`prop:thorin-subclass`(4) can now use it.

**One coordinate choice halves the algebra.** Written with `c = √A/√B` and `s = √A√B` the final
step is `√c·√s = √(cs) = √A`; written with `(A/B)^{1/4}` and `(AB)^{1/4}`, which is how the
skeleton's note states the substitution, it is a page of `rpow` arithmetic.
-/

/-! ### The Bessel corner — **proved and moved** (2026-09-10, wave 4)

`SpatialLine.bridge_families_bessel`, statement verbatim, in `SpatialLine/BridgeBessel.lean`,
Lean core. Priced **M**, paid **M**: the substitution `w = 1/u` **is**
`integral_comp_rpow_Ioi` at `p = -1`, and what it leaves is
`Real.integral_rpow_mul_exp_neg_mul_Ioi` at shape `a + 1/2` and rate `(1+x²)/2`. Both were in
Mathlib; the estimate's "arithmetic plus one change of variables under an integral" was right.

**One step is worth reusing.** Getting from the Bochner integral, where the change of variables
lives, to the `ℝ≥0∞` integral the measure equality needs would normally cost an integrability
proof. It does not have to: `integral_eq_lintegral_of_nonneg_ae` holds *unconditionally*, both
sides being `0` when the integrand is not integrable, so a computed value that is **strictly
positive** already forces the `ℝ≥0∞` integral to be finite. `studentDensity_pos` is the whole
of it. Any later node that computes a density by a Bochner change of variables and then needs
it as a measure can use the same two lines.

The declaration is also `prop:student-t`(1)'s conditioning computation, so that node's `\lean`
tag was updated with it in `10-corners.tex`.

It lives in its own file because it needs the Brownian density in closed form
(`SpatialLine/BridgeExponents.lean`) and that file imports `SpatialLine/BridgeCorners.lean`.
-/

/-! ## `prop:bridge-strictness` (draft Proposition 9.3) — **proved and moved** (2026-09-10,
wave 4), **[A] → [T]**, and its membership sentence **split out** (2026-09-11, R44)

All five declarations are in `SpatialLine/Strictness.lean` with their statements verbatim, the
node is `\leanok`, and every one of them prints Lean core. The supporting files are
`SpatialLine/CausalExponent.lean` (the causal exponent as a Bochner integral, its finiteness
and its derivative) and `SpatialLine/CausalCone.lean` (the causal cone's sums, nonnegative
multiples and dilations, with their exponent identities).

**THE MEMBERSHIP SENTENCE IS NO LONGER THIS NODE'S (2026-09-11, R44, the author's decision).**
Clause (4) used to close with "containing the Gaussian ray and the Matérn, Student-t and
symmetric stable families", and nothing under this tag proved it: `IsSubordinated` is an
existential over `CausalAdmissible`, of which the development exhibits no instance. The fidelity
review of 2026-09-10 took the node to `notready` on that half alone; the author's decision splits
the sentence out as `lem:subordinated-members`, whose target type is `Skeleton.subordinated_members`
below. What stays here is what the five declarations prove, and the node is `\leanok` again.

**The finding: ledger A11 was not this node's obligation.** The skeleton read here, and the
blueprint's assignment clause, charged clause (2) to A11 for the step "a completely monotone
function vanishing at an interior point vanishes identically". Writing the Lean proof showed
the charge was against the printed *argument*, not against the *statement*. What clause (2)
needs is that

  `F_I'(σ) = b₀ + ∫₀^∞ e^{-σu} k_I(u) du > 0` for `σ > 0` unless `(b₀, k_I) = 0`,

and `def:causal-admissible` **hands the proof the representing measure** `b₀δ₀ + k_I(u)du`
rather than asking Bernstein's theorem to produce one. So the remaining obligation is the
positivity of an integral with a positive integrand, which is
`CausalAdmissible.deriv_integral_pos`, five lines. Bernstein's theorem produces a measure;
here there was one already. The blueprint node is now `\statusT`, its proof of record is
rewritten to this route with the Bernstein reading kept as a closing paragraph marked as what
is not needed, and `AXIOMS.md`'s A11 records clause (b) as retired — the entry stays, spent by
`prop:thorin-subclass` alone. This is judgement point 1 of the mathematician's charter in its
exact form: what a proof cites is an upper bound on what a statement needs.

**Prices.** (1) S priced, S paid. (2) M priced *given the interface*, **M paid with no
interface** — the differentiation under the integral sign (`hasDerivAt_exponent`, dominating
function `e^{-σu/2}k_I(u)`) is the whole cost and it replaces the interface rather than
sitting beside it. (3) S priced, S paid, once `cin_pos` was available to supply `hne`.
(3, general) M priced, M paid; `setOf_cos_eq_one` had to be restated because
`lattice_zero_mem_iff` states the lattice fact about a probability measure's `charFun` and
this clause reads it at the Choquet measure `ϖ`, which is not one. Wave 4's merge lifted the
single copy into `SpatialLine/LatticeZero.lean` as `SpatialLine.setOf_cos_eq_one`, where
`lattice_zero_mem_iff` now applies it too. (4) M priced, **M–L paid**, and the
cost is concentrated in one place the estimate did not name: closure of the *causal* cone under
dilation. Sums and nonnegative multiples act on `(b₀, k_I)` termwise and preserve both
integrability fields term by term; the dilation `k_I ↦ k_I(·/c)` does not, because the two
fields are stated on the two fixed windows `(0,1)` and `(1,∞)` and the change of variables
moves them. Reading the pair as the single condition
`∫₀^∞ (1 ∧ u) k_I(u) du/u < ∞` (`CausalAdmissible.lintegral_min_split`) is what makes the
change of variables cheap, `du/u` being scale-invariant, and `1 ∧ cx ≤ max(1,c)(1 ∧ x)` then
prices the dilated integral against the undilated one. That reading is recorded in the
blueprint's clause (4).

**What the statements needed that the prose did not say.** Clause (4)'s three closure clauses
quantify over `IsSubordinated`, which is an existential over `CausalAdmissible`; discharging
them therefore means *constructing* the witness, and that is why the causal cone needed three
`def`s rather than three lemmas. The spatial side has no `SDProfile.dilate` because
`lem:selfdecomposable-exponents` only ever uses the increment of a dilation.
-/

/-! ## `lem:subordinated-members` (draft Proposition 9.3(4), the membership sentence) — the
Gaussian, Matérn and stable conjuncts **PROVED AND MOVED (2026-09-11, R121)**; the Student-t
conjunct split out as `lem:student-subordinated`, the target ledger **A18** would supply

**PROVED AND MOVED (2026-09-11, R121).** The first, second and fourth conjuncts of the former
`subordinated_members` are `SpatialLine.subordinated_members`, statement verbatim in form, in
`SpatialLine/CausalData.lean`, **Lean core**. The Student-t conjunct is `student_subordinated`
below, `sorry`, and the blueprint node `lem:student-subordinated` carries it, `[A]` on A18 and
`notready`; `lem:subordinated-members` is narrowed to the three proved families and is `[T]`
and `\leanok` (the split was taken under the safe-direction delegation; A18 stays unadmitted,
the author's decision of 2026-09-11 being to split rather than admit).

*Priced against paid.* Gaussian **S**, paid **S** (the drift datum is ten lines, its exponent
four). Matérn **M**, paid **S–M**: the Gamma datum with its two integrability fields is seventy
lines modelled on `maternDatum`, and the member is the image identity `bridge_families_gamma`
plus a dilation by `√2θ` from `bridge_strictness_cone`, a dozen lines. Stable **M**, paid **M**:
the datum ports Paper I's `stableExponent` (sixty-five lines); the exponent `σ^α` was the one
step with a choice of route. Paper I matches derivatives on `(0,∞)` and limits at `0+`; the
limit is not needed here, because the profile is homogeneous — `k(u/c) = c^α k(u)`, so the
causal dilation of the datum is its multiple by `c^α`, and `exponent_dilate` with
`exponent_smul` give `F_I(σ) = σ^α F_I(1)` — and one derivative at `σ = 1`
(`hasDerivAt_exponent`, with `∫₀^∞ e^{-u}c_α u^{-α}du = α` from Mathlib's Gamma integral) fixes
the constant. The note below is the pricing as written before the proof.

**THE MEMBERSHIP SENTENCE IS ITS OWN NODE (2026-09-11, R44, the author's decision).** The
sentence "`S` contains the Gaussian ray and the Matérn, Student-t and symmetric stable families"
stood inside `prop:bridge-strictness`(4) and had no declaration under that node's tag, which is
what the fidelity review's row R44 found; the article's own rule — a `\leanok` node claims
exactly what its declarations prove, and an unformalised clause is split out rather than
disclosed in place — is applied here as it was at `prop:thorin-subclass`(3) → `lem:thorin-ggc`
and at `prop:polya-frequency`'s fourth exclusion → `lem:polya-student-exclusion`. The closure
and exclusion halves of clause (4) stay where they were, machine-checked as
`SpatialLine.bridge_strictness_cone`, and that node is `\leanok` again.

**What a proof needs is one causally admissible datum per family**, because `IsSubordinated` is
an existential over `CausalAdmissible` and this development constructs none: `CausalCone.lean`
has the three combinators (sums, nonnegative multiples, dilations) and no generator to feed
them. Per family, priced here at the statement:

* **Gaussian ray.** `b₀ = 2a`, `k_I = 0`. The four structure fields are trivial and the exponent
  is `CausalAdmissible.exponent` of a zero profile. **S**, about twenty lines.
* **Matérn.** The causal Gamma datum `k_I(u) = γe^{-u}`, whose image is `maternExponent γ 1/√2`
  by `SpatialLine.bridge_families_gamma` (proved); the general range `θ` follows from it by
  `CausalAdmissible.dilate`, the causal dilation `bridge_strictness_cone` already uses. The cost
  is the datum's two integrability fields for an exponential profile. **M**.
* **Student-t.** The Lévy data of the inverse-gamma delay law — that the inverse-gamma laws are
  generalized gamma convolutions, hence self-decomposable, hence that the causal Bessel family
  is causally admissible. That is exactly `Skeleton.student_causal` and exactly what ledger
  **A18** grounds (Halgreen §2, pp. 14–15); A18 is deliberately unadmitted for want of a
  consumer. **Interface**, not a proof: the member cannot be closed on Lean core.
* **Symmetric stable.** The causal stable datum `F_I(σ) = σ^{α/2}`, `0 < α/2 ≤ 1`, whose profile
  is a pure power; `SpatialLine.bridge_families_stable` (proved) already has the image identity
  `(ω²/2)^{α/2} = 2^{-α/2}|ω|^α`, and the positive multiple is absorbed by the cone clause of
  `bridge_strictness_cone`. What is missing is the datum, i.e. the causal twin of
  `SpatialLine.stableDatum`. **M**.

**The Student-t exponent is quantified over, not constructed.** There is no `studentExponent` in
this development, and `-log` of the closed form of `prop:student-t`(2) is junk at `ω = 0`
(`|0|^a K_a(0)`). So the clause reads: *any* `F` with `exp(-F) = φ̂_a` is subordinated. That
loses nothing — `exp` is injective, so the specification determines `F` pointwise — and
`SpatialLine.student_transform` evaluates the right-hand side wherever a consumer wants the
closed form. Judgement point 11 of the charter: a specification is a hypothesis, and a
hypothesis can be quantified over.

**Carried to the draft sync, not stated here** (R44's F8 finding): draft Proposition 9.3(4)
lists "and their Thorin-type superpositions" among the members of `S`, which the blueprint
dropped without record. That membership is the image half of `prop:thorin-subclass`(4) and
belongs there, not in this node; it is recorded in the node's annotation and in the review, and
it is not a clause of `subordinated_members`.
-/

/-! ## `lem:student-subordinated` — **PROVED AND MOVED (2026-09-15, module B step 2, R160)**

`SpatialLine.student_subordinated`, in `SpatialLine/StudentThorin.lean`, **Lean core**.

The node was split off here on 2026-09-11 (R121) as the third conjunct of the former
`subordinated_members`, `[A]` on ledger **A18** and `sorry`, waiting on `Skeleton.student_causal`
— the declaration that entry would have carried. It is now restated with the delay law as a
*hypothesis*: given a `CausalAdmissible` whose exponent has the inverse-gamma Laplace transform,
every exponent whose exponential is the Student-t cosine transform is subordinated. The
conclusion and its quantifier are the skeleton's verbatim.

**Priced "interface, not a proof"; paid S — eight lines.** The finding is the one this article
keeps making, and it was made here by writing the target type rather than by reading the printed
proof: what the *statement* needs is one causally admissible datum, which can be quantified over
(judgement point 11), while what the *printed proof* cited was the named-class theorem. The
existence of the datum is now the cited remark `rem:student-ggc`; A18 grounds it and is admitted
nowhere. Note that the hypothesis here is strictly weaker than the one `prop:student-t`(3) needs
— self-decomposability, not the generalized gamma convolution — and that is why the two nodes
are stated with different hypotheses rather than one.
-/

/-! ## `def:delay-data` and `lem:filtration-strictness` — the type G exponents and the
dimension filtration (2026-09-15, module B step 2, R163)

The two constructions of the P-0009 pass, stated as nodes on the author's decision of
2026-09-15. The vocabulary is `DelayDatum`, which is `CausalAdmissible` with `k_antitone`
dropped, its exponent, the predicate `IsTypeG`, and the polar profile `eq:polar-profile`;
the two theorems are the blueprint's two clauses.

### What writing the target types found

**1. The uniqueness the argument needs is this article's own, and neither
`prop:bridge-strictness`(1) nor ledger A11 supplies it.** Clause (1) of that node turns
membership in `S` into causal admissibility of `σ ↦ F(√(2σ))`, which is an *existential over
data*; to contradict it one has to rule out **every** causally admissible datum with the given
exponent, and that is uniqueness of the delay data. Ledger A11 carries the uniqueness of the
representing measure at its citation, but **the admitted statement is the existence equivalence
only** (`AXIOMS.md`, A11), so nothing on the trust boundary provides it. What does provide it is
`SpatialLine.laplace_uniqueness_locally_finite` (`prop:laplace-uniqueness-locally-finite`, `[T]`,
Lean core), together with the derivative formula in the proof of `prop:bridge-strictness`(2) and
one dominated limit at `σ → ∞` for the drift. So the node is `[T]` and spends no ledger entry —
the kind of finding judgement point 9 asks for, and it was made by searching this development
before Mathlib.

**2. The differentiation and integrability steps of the bridge read no monotonicity.** The proof
of `prop:bridge-strictness`(2) dominates the `σ`-derivative of the causal integrand by
`e^{-σu/2}k_I(u)`, and the finiteness, Lévy-condition and exponent steps in the proof of
`lem:bridge-exponents` dominate by `k_I` below `1` and by `k_I(u)/u` above it. All four read
only the two integrability fields, so they apply to a `DelayDatum`; only `k_antitone` reads
monotonicity, and that is exactly the field the lemma makes the question. In Lean this means
`bridgeDatum` cannot be reused as it stands — it produces an `SDProfile`, whose `k_antitone`
field is the conclusion here rather than a hypothesis — and the mixture's five other fields
would have to be reproved for a `DelayDatum`. That is the largest single item in the price
below.

**3. The sharp elementary threshold at `d = 1` is `c ≤ 6 + 4√2`, not `c ≤ e/2`.** The remark's
sufficient condition drops the negative half of the derivative of the bump term and gives
`c r²e^{-r²/2} ≤ 1`, that is `c ≤ e/2 ≈ 1.36`. Keeping the negative half and bounding
`log(1/p) ≤ (1-p)/√p` gives `c(3/2 - √2) ≤ 1`, that is `c ≤ 6 + 4√2 ≈ 11.66`, which is what
lets **one** hypothesis cover both `c = 4` and `c = 8` and so lets clause (2) inherit
admissibility from clause (1) instead of repeating it. The numerical threshold is
`c₁ ≈ 12.61`, so the elementary bound is within 8% of it. Found while writing the target type,
not while reading the printed proof (judgement point 10).

### The price, written beside the statement (2026-09-15)

Neither theorem is attempted; both are `sorry`, the node is `\notready`, and the blueprint
carries the proof of record. Per piece, at the statement:

* `filtrationDatum` as a term of `DelayDatum` — the two integrability fields for
  `u^{-1/2} + c·1_{[1,2]}` — **S–M, about 90 lines.** The pure-power halves are
  `ScaleSpaceCore`'s `integrableOn_stableCausalProfile` and `..._div` at `α = 1/2` up to a
  constant; the bump adds a bounded indicator on a set of measure one.
* the closed form of `polarProfile` at `d = 1, 2, 3` — **L, about 200 lines.** The pure-power
  term is a Gamma integral, which Mathlib has
  (`Real.integral_rpow_mul_exp_neg_mul_Ioi`); the bump term is
  `1_{[1,2]}(r²/2v) = 1_{[r²/4, r²/2]}(v)` under the integral, and then the regularized lower
  incomplete gamma, **which Mathlib does not have at the pin**. At `d = 1` and `d = 2` it is
  `erf` and `e^{-x}`, both available; at `d = 3` it would have to be written out.
* the admissibility clause — **M–L, about 150 lines**: the five `SDProfile` fields for a
  `DelayDatum`, i.e. `bridgeDatum` again without `k_antitone`, plus the identification of the
  spatial profile with `polarProfile D 1`.
* the monotonicity bounds — **M, about 120 lines**: `log(1/p) ≤ (1-p)/√p`, two exact
  one-variable maxima, and `6912/3125 < π` (`Real.pi_gt_3141592`).
* the failure of monotonicity at an explicit point — **S, about 40 lines** per point, the
  witnesses being `r = 1` at `d = 2, c = 8` and `r = √2` at `d = 3, c = 4`, with `Real.exp_one`
  bounds.
* not subordinated — **M, about 120 lines**: the derivative formula for a `DelayDatum`, the
  dominated limit at `σ → ∞`, `laplace_uniqueness_locally_finite`, and the failure of a
  nonincreasing version on two intervals of positive measure.

**Total 550–850 lines**, against the 250–400 the P-0009 pass priced from the printed argument,
and the difference is items 1 and 3: the pass priced the analysis and not the vocabulary, and a
`DelayDatum` has no bridge in the development because every consumer so far had `k_antitone`.
Clause (2) is the more expensive half and is blocked in one place that is not a matter of
effort — the regularized incomplete gamma at `d = 3` — which is why the two clauses are two
declarations.
-/

/-- **`def:delay-data`** — a *delay datum*: `def:causal-admissible` with the monotonicity of the
profile dropped, so that the class it generates is the type G exponents rather than the
subordinated slice. The remaining fields are `ScaleSpace.CausalAdmissible`'s, in its order, with
`k_antitone` replaced by the measurability that field used to supply. -/
structure DelayDatum where
  /-- The drift coefficient. -/
  b₀ : ℝ
  /-- The delay profile, a density against `du/u` on `(0,∞)`; **not** assumed nonincreasing. -/
  k : ℝ → ℝ
  b₀_nonneg : 0 ≤ b₀
  k_nonneg : ∀ u ∈ Set.Ioi (0 : ℝ), 0 ≤ k u
  /-- What `k_antitone` supplied in `CausalAdmissible` and a delay datum must assume. -/
  k_aemeasurable : AEMeasurable k (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
  /-- A normalisation, not a constraint, as in `CausalAdmissible`. -/
  k_zero : k 0 = 0
  /-- `∫₀¹ k(u)\,du < ∞`. -/
  integrable_near_zero : ∫⁻ u in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (k u) ≠ ⊤
  /-- `∫₁^∞ k(u)\,u^{-1}du < ∞`. -/
  integrable_at_top : ∫⁻ u in Set.Ioi (1 : ℝ), ENNReal.ofReal (k u / u) ≠ ⊤

namespace DelayDatum

/-- **`def:delay-data`'s exponent** `F_I(σ) = b₀σ + ∫₀^∞ (1 - e^{-σu})\,k(u)\,du/u`,
`ℝ≥0∞`-valued; `CausalAdmissible.exponentL` with the weaker datum. -/
noncomputable def exponentL (D : DelayDatum) (σ : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (D.b₀ * σ)
    + ∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal ((1 - Real.exp (-(σ * u))) * D.k u / u)

/-- The real-valued exponent. -/
noncomputable def exponent (D : DelayDatum) (σ : ℝ) : ℝ := (D.exponentL σ).toReal

/-- Every causally admissible datum is a delay datum: the monotonicity field is forgotten and
supplies the measurability. This is the inclusion `S ⊆ G` in one line. -/
noncomputable def ofCausal (F : CausalAdmissible) : DelayDatum where
  b₀ := F.b₀
  k := F.k
  b₀_nonneg := F.b₀_nonneg
  k_nonneg := F.k_nonneg
  k_aemeasurable := F.aemeasurable_k
  k_zero := F.k_zero
  integrable_near_zero := F.integrable_near_zero
  integrable_at_top := F.integrable_at_top

@[simp] theorem ofCausal_exponent (F : CausalAdmissible) (σ : ℝ) :
    (ofCausal F).exponent σ = F.exponent σ := rfl

end DelayDatum

/-- **`def:delay-data`'s class `G`** — the *type G exponents*: those of the form
`F(ω) = F_I(ω²/2)` for a delay datum. The name is `rem:dimension-filtration`'s and is justified
there by the radial theorem, which is cited and not asserted; the class defined here is defined
by the displayed form alone, so no dimension theory enters it. -/
def IsTypeG (F : ℝ → ℝ) : Prop := ∃ D : DelayDatum, ∀ ω : ℝ, F ω = D.exponent (ω ^ 2 / 2)

/-- **`eq:polar-profile`** — the polar profile in dimension `d` of a delay datum,
`k_d(r) = (2/Γ(d/2))∫₀^∞ v^{d/2-1}e^{-v}k_I(r²/2v)\,dv`. At `d = 1` it is the folded spatial
profile of `eq:bridge-profile`, the factor `2` being `|S⁰|`. -/
noncomputable def polarProfile (D : DelayDatum) (d : ℕ) (r : ℝ) : ℝ :=
  2 / Real.Gamma ((d : ℝ) / 2) *
    ∫ v in Set.Ioi (0 : ℝ), v ^ ((d : ℝ) / 2 - 1) * Real.exp (-v) * D.k (r ^ 2 / (2 * v))

/-- The delay profile `k^{(c)}(u) = u^{-1/2} + c·1_{[1,2]}(u)` of `lem:filtration-strictness`,
guarded at the origin the way `CausalAdmissible`'s profiles are. -/
noncomputable def filtrationProfile (c : ℝ) : ℝ → ℝ := fun u =>
  if 0 < u then u ^ (-(1 : ℝ) / 2) + (if u ∈ Set.Icc (1 : ℝ) 2 then c else 0) else 0

/-- **`lem:filtration-strictness`(1)** — the subordinated slice is strictly smaller than the type
G exponents: `S ⊆ G`, and for `0 < c ≤ 6 + 4√2` the delay datum with profile `k^{(c)}` has an
exponent that is admissible, with Gaussian coefficient `0` and folded profile the polar profile
at `d = 1`, and is not subordinated.

The existence of the datum is **asserted**, not hypothesised: a conditional statement here would
be vacuous exactly where the construction is the content. -/
theorem filtration_strictness_typeG (c : ℝ) (hc : 0 < c) (hc' : c ≤ 6 + 4 * Real.sqrt 2) :
    (∀ F : ℝ → ℝ, IsSubordinated F → IsTypeG F) ∧
      ∃ D : DelayDatum, D.b₀ = 0 ∧ (∀ u ∈ Set.Ioi (0 : ℝ), D.k u = filtrationProfile c u) ∧
        (∃ P : SDProfile, P.a = 0 ∧ (∀ r ∈ Set.Ioi (0 : ℝ), P.k r = polarProfile D 1 r) ∧
          ∀ ω : ℝ, P.exponent ω = D.exponent (ω ^ 2 / 2)) ∧
        ¬ IsSubordinated fun ω => D.exponent (ω ^ 2 / 2) := by
  sorry

/-- **`lem:filtration-strictness`(2)** — the polar profiles cross the dimensions one at a time:
at `c = 4` the profiles in dimensions `1` and `2` are nonincreasing and the one in dimension `3`
is not; at `c = 8` the profile in dimension `1` is nonincreasing and the one in dimension `2` is
not.

`AntitoneOn` is the statement about the function itself, which for these data is the statement
about its a.e. class, each `polarProfile` of `filtrationProfile` being continuous on `(0,∞)`;
the blueprint proof says so where it turns a positive derivative into the failure of a
nonincreasing version. The development has no notion of a self-decomposable law on `ℝ^d`, so the
clause is typed through the polar profile, which is what Sato's criterion evaluates; the
membership reading is `rem:dimension-filtration`'s and is cited there. -/
theorem filtration_strictness_dimension :
    (∃ D : DelayDatum, D.b₀ = 0 ∧ (∀ u ∈ Set.Ioi (0 : ℝ), D.k u = filtrationProfile 4 u) ∧
        AntitoneOn (polarProfile D 1) (Set.Ioi 0) ∧ AntitoneOn (polarProfile D 2) (Set.Ioi 0) ∧
        ¬ AntitoneOn (polarProfile D 3) (Set.Ioi 0)) ∧
      ∃ D : DelayDatum, D.b₀ = 0 ∧ (∀ u ∈ Set.Ioi (0 : ℝ), D.k u = filtrationProfile 8 u) ∧
        AntitoneOn (polarProfile D 1) (Set.Ioi 0) ∧
          ¬ AntitoneOn (polarProfile D 2) (Set.Ioi 0) := by
  sorry

end Skeleton
