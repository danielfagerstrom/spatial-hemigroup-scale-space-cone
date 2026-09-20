/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Skeleton.Chapter4

/-!
# The target types of Chapter 5 — the cascade

**This file carries `sorry`s and is not part of the `SpatialLine` library.**

## What writing this chapter down found

**`cor:monotonicity`'s exceptional set was defined so that the conclusion is false at `ω = 0`.**
The blueprint wrote `E := ⋃ (N_{p,q} ∖ {0})`, the union over rational `0 ≤ p < q`, and then
concluded that `G(·,ω)` is strictly increasing *for every `ω` outside `E`*. But `0 ∉ E` by
construction, while `G(t,0) = 0` for every `t` — so the conclusion fails at the one frequency the
set-difference deliberately removed. The blueprint's own **proof** has it right ("for
`ω ∉ E ∪ {0}`"), which is how the discrepancy was visible at all. Fixed by deleting the
`∖ {0}`: `E := ⋃ N_{p,q}` is still a countable union of subgroups, still countable, and now
contains `0`. Recorded in the part file as `% CHANGED (skeleton 2026-09-08)`.

This is the shape of error the phase exists to find: it is invisible in prose, harmless to the
argument, and would have made every downstream `\uses` of the corollary state something false.

**Infinite divisibility is stated at the transform.** "Every kernel `μ_{s,t}` is infinitely
divisible" is rendered as: for each `n` there is a probability measure whose cosine transform is
the `n`-th root of the kernel's. Mathlib has no convolution power of measures, and introducing
one to state a clause that is immediately consumed through transforms would be vocabulary without
a consumer.

**`G` is not a definition.** The blueprint's `G(t,ω) := g_{0,t}(ω)` is written inline as
`exponent (μ 0 t) ω` throughout. It is an abbreviation in the text, and giving it a name in the
`sorry`-free library before the representation is proved would name a function of a hypothesised
object.
-/

namespace Skeleton

open MeasureTheory Set Filter SpatialLine
open scoped ENNReal Topology

/-! ## `lem:additivity` (draft Lemma 5.1') — [T]

**Proved and moved** (2026-09-09): `SpatialLine.additivity`, in
`SpatialLine/Additivity.lean`. Priced **S**, paid **M** — the estimate was made against
the ten clauses and was right about them; what it did not price is that the whole of
`lem:nonvanishing` and the uniqueness clause of `lem:convolution-representation` had to be
proved first, in `SpatialLine/Pairing.lean` and `SpatialLine/Cascade.lean`. See the note in
`SpatialLine/Cascade.lean` on the deliberate duplication of Chapter 4.
-/

/-! ## `thm:increments-levy` (draft Theorem 5.2') — [T]

**Proved and moved** (2026-09-09, wave 2): `SpatialLine.increments_levy` and
`SpatialLine.increments_levy_infinitely_divisible`, in `SpatialLine/Increments.lean`. Priced
**L**, paid **L** — the estimate of "several days" was made against the paper proof and was
high: the whole node cost one session, and the three findings below say where the estimate went
wrong.

The development is four files, following the causal twin's shape:
`SpatialLine/NullArray.lean` (the partition and the null-array limit),
`SpatialLine/Tightness.lean` (`eq:truncation` and the two uniform bounds),
`SpatialLine/LevyExtraction.lean` (the test function and the weak limit) and
`SpatialLine/Increments.lean` (the split at the origin).

**What the estimate did not have.**

* **The Fubini step of `eq:truncation` is in Mathlib and had not been looked for.** The wave-1
  reconnaissance found `measureReal_abs_gt_le_integral_charFun` and read it as "the blueprint's
  `eq:truncation` already integrated"; the load-bearing lemma is the one *above* it in the same
  file, `MeasureTheory.integral_charFun_Icc`, which states
  `∫_{-r}^{r} charFun ρ = 2r ∫ sinc(rx) dρ` for a **finite** measure and does the Tonelli swap
  internally. With it the truncation inequality is `Real.log_le_sub_one_of_pos` and a sum over
  the partition; the swap, which was the expensive-looking part, is not ours to do. The tail
  bound is then the same lemma at `r = 1/R` rather than a second argument.

* **The removable singularity needs no case split.** The blueprint defines
  `k_ω(x) = (1 - cos ωx)/(1 ∧ x²)` with `k_ω(0) := ω²/2` and argues continuity from
  `1 - cos u = u²/2 + O(u⁴)`. The closed form
  `k_ω(x) = (ω²/2)·sinc(ωx/2)²·(1 ∨ x²)` is equal to it, is continuous because `Real.sinc` is,
  and needs no `if`; the whole of `levyTest`'s continuity, its bound `max(ω²/2, 2)` and the
  identity `k_ω(x)(1 ∧ x²) = 1 - cos ωx` (which holds at the origin too, both sides vanishing)
  are three short proofs. This is a route change in the formalisation only, recorded in
  `SpatialLine/LevyExtraction.lean`; it does not touch the mathematics of record.

* **Tightness delivers the folding for free.** The blueprint takes the weak limit and then reads
  it in two pieces. In Lean the limit is a *cluster point* in `FiniteMeasure ℝ`, obtained from
  Mathlib's Prokhorov theorem with the monotone compacts `[0, n+1]` and the tolerances the
  truncation inequality supplies — and the membership condition that gives tightness,
  `ϱ([0,n+1]ᶜ) ≤ u_n` with `u_n → 0`, already forces `ϱ(Iio 0) = 0`. No portmanteau argument is
  needed to know that the limit is carried by the half-line, which is what makes the Lévy
  measure folded.

**The trust boundary.** `increments_levy` is machine-checked to **Lean core**: the null-array
limit, the truncation inequality and the extraction are all proved, and nothing is cited. The
closing sentence, `increments_levy_infinitely_divisible`, is the one declaration of Chapter 5
that spends interfaces — `fourier_toolbox_levy_converse` (ledger **A3**) and the axiom wave 2
added, `fourier_toolbox_bochner_symm` (ledger **A1**, `SpatialLine/Interfaces.lean`) —
exactly the two clauses the blueprint proof cites. Splitting the node into two declarations is
what keeps the first at Lean core.

**The two elementary inequalities** stay where wave 1 put them,
`SpatialLine.sub_one_sub_exp_neg_le` and `SpatialLine.one_sub_sinc_ge` in
`SpatialLine/Truncation.lean`, and their constants `u²` and `2/(3π²)` are now the proof of
record's (author's decision 2026-09-09); the sharper `u²/2` and `2/15` survive as a remark in
the blueprint, marked as not machine-checked.
-/

/-! ## `cor:monotonicity` (draft Corollary 5.3') — [T]

**Proved and moved** (2026-09-09): `SpatialLine.monotonicity_zero_set` and
`SpatialLine.monotonicity_strict`, in `SpatialLine/Monotonicity.lean`. Priced **S**, paid **M**
— the estimate was "given `lattice_zero_isClosedSubgroup` and `lattice_zero_trichotomy`", and
those are Chapter 2's, unproved on this branch, so both had to be proved here
(`SpatialLine/Lattice.lean`, under different names, duplication recorded).

Chapter 2's own estimate for the trichotomy was **M–L**, "depending on a Mathlib lookup that
has not been done". The lookup: `AddSubgroup.dense_or_cyclic` (in
`Mathlib.Topology.Algebra.Order.Archimedean`) gives it in four lines once the zero set is known
to be a closed subgroup, and there is no dense-but-not-all case to exclude by hand — a closed
dense subgroup is everything. The estimate should be **M**, and the expensive half is the
subgroup property, not the classification: `μ̂(ω) = 1` has to be turned into "`cos(ωx) = 1` for
`μ`-a.e. `x`" before the cosine addition formula can be applied.
-/

/-! ## `cor:smoothed-transmittance` (draft Corollary 5.4') — [T]

**Proved and moved** (2026-09-09): `SpatialLine.smoothed_transmittance` and
`SpatialLine.smoothed_transmittance_strictAnti`, in `SpatialLine/Transmittance.lean`. Priced
**S**, paid **S** on top of `SpatialLine/Cascade.lean`.

What proving it found: the positivity clause `0 < Θ(t)` does **not** need `lem:nonvanishing`,
which the blueprint proof cites for it. The integrand `e^{-x²/2}` is strictly positive at every
point of the line and the kernel is a probability measure, so the integral is positive for the
elementary reason. Only the antitone clause and the strict clause spend the positivity of the
transform, and the strict clause spends it only on the factor `μ̂_{0,s} ρ`. The node's `\uses`
is unchanged, being right for those two clauses.
-/

end Skeleton
