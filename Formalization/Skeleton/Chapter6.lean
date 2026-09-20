/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Skeleton.Chapter5

/-!
# The target types of Chapter 6 — scale covariance

**This file carries `sorry`s and is not part of the `SpatialLine` library.**

## What writing this chapter down found

**1. `lem:covariance-fourier`'s proviso disappears in the setting every use is in.** The
blueprint states the three-way equivalence under (A1)–(A5), with clause (3) carrying "whenever
the exponents exist" — because (A1)–(A5) alone do not give `lem:nonvanishing`. The node's own
annotation says the proviso is vacuous under (A6)–(A7) and that every later use is in that
setting. The Lean statement therefore takes `PreCascadeCore` (which carries (A6)–(A7)) plus a
kernel family, and clause (3) is unconditional. The (A1)–(A5)-only version is not stated, because
nothing consumes it; this is a **narrowing** and it is recorded rather than silently taken.

**2. The equivalence is stated on the `scale` field, with the `S`-shape fields as hypotheses.**
`IsScaleCovariant` bundles four things, three of which are conditions on `S` alone and are shared
by all three clauses of the equivalence. Paper I made the same split (`covariance_laplace`
forward, `isScaleCovariant_of_repr_map` back); stating it as a single `↔` with the shape fields
hypothesised says the same thing once.

**3. `prop:canonical-gauge` produces the gauge as an existential, not as a definition.** `χ` is
`c⁻¹` and `c` is `lam ↦ S lam 1`; naming `χ` in the library would require the inverse to exist,
which is the theorem. Everything downstream — `thm:main-characterization` above all — quantifies
over a `χ` with the stated properties, which is what `rem:gauge-freedom` says the gauge is.
-/

namespace Skeleton

open MeasureTheory Set Filter SpatialLine
open scoped ENNReal Topology

/-! ## `lem:covariance-fourier` (draft Lemma 6.1') — [T]

**Proved and moved** (2026-09-09): `SpatialLine.covariance_fourier` and
`SpatialLine.covariance_similarity`, in `SpatialLine/Covariance.lean`. Priced **S**, paid **S**.

The two narrowings the skeleton took are unchanged and are recorded in the moved file; the
`S_λ 0 = 0` clause of `eq:similarity` became the standalone
`SpatialLine.IsScaleCovariant.S_zero`, since Chapter 6 uses it four times.
-/

/-! ## `lem:no-lattice` (draft Lemma 6.0') — [T]

**Proved and moved** (2026-09-09): `SpatialLine.no_lattice`, in `SpatialLine/NoLattice.lean`.
Priced **M**, paid **M** — but the M is almost entirely the lattice block of Chapter 2
(`SpatialLine/Lattice.lean`, shared with `cor:monotonicity`). Given that block, the node is
**S**: the chain of zero sets is three lines, and the chain comparison is cheaper element-wise
than set-wise — one generator of each lattice lands in the other and produces `3/2 = n` or
`2/3 = n` in `ℤ`, which `omega` refutes, so no classification of the inclusions is needed.
-/

/-! ## `lem:dilation-invariance` (additive) — [T]

**Proved and moved** (2026-09-09): `SpatialLine.dilation_invariance`, in
`SpatialLine/Dilation.lean`. Priced **S**, paid **S**.
-/

/-! ## `lem:action-rigidity` (draft Lemma 6.2') — [T]

**Proved and moved** (2026-09-09): `SpatialLine.action_rigidity_injective`,
`SpatialLine.action_rigidity_group`, `SpatialLine.action_rigidity_continuous` and
`SpatialLine.action_rigidity_no_fixed_point`, in `SpatialLine/Rigidity.lean`. Priced
**S, S, M, S**; paid **S, S, S, S**.

What clause (3) found: the estimate said "the Lean cost is the continuous inverse, not the
domination", and **no inverse function is needed**. `tendsto_order` splits the claim into two
one-sided statements, each of which follows from `StrictAntiOn Θ` by contraposition against a
bound `θ_t`'s own continuity supplies; `Set.invFunOn` never appears. The estimate identified
the right half as the hard one and named the wrong obligation inside it.
-/

/-! ## `lem:dilation-atom` (draft Lemma 6.2'') — [T]

**Proved and moved** (2026-09-09): `SpatialLine.dilation_atom`, in
`SpatialLine/Dilation.lean`. Priced **S**, paid **S** — by a different route from the
blueprint proof, which the moved file records.
-/

/-! ## `prop:canonical-gauge` (draft Proposition 6.3') — [T]

**Proved and moved** (2026-09-09): the orbit coordinate in wave 1 as
`SpatialLine.canonical_gauge_orbit` (`SpatialLine/Gauge.lean`), the gauge itself in wave 2 as
`SpatialLine.canonical_gauge` (`SpatialLine/GaugeLevy.lean`). Priced **M**, paid **M** for the
orbit half and one line for the rest — wave 1's `canonical_gauge_of_levy` proves all seven
clauses from `IsSymLevyExponent (exponent (μ 0 1))` as a hypothesis, and wave 2 supplies it from
`SpatialLine.increments_levy`. `#print axioms` reduces to Lean core: the Lévy clause is the
null-array limit, which is proved outright, and the trust boundary is spent only by
`thm:increments-levy`'s infinite-divisibility sentence, which this node does not use.

**The specification-as-hypothesis move paid.** Wave 1 could have left the whole node open on an
**L** upstream node; instead it stated the seven clauses with the one waiting clause as a
hypothesis, and the node then closed by one application. Nothing was constructed that had no
consumer, and no clause was proved twice.

Wave 1's two findings about the argument stand, and one of them is now the proof of record:

* the whole of the direction clause is one statement, `lt_S_of_one_lt` (`ϰ > 1` and `u > 0`
  imply `u < S_ϰ u`), and from it strict monotonicity of `λ ↦ S_λ t` follows for **every**
  `t > 0` by one line of the group law. Neither "continuous and injective on a connected set,
  hence strictly monotone" nor the separate exclusion of the decreasing case is needed. This is
  still a divergence from the printed proof and is recorded in the node's annotation;
* the blueprint's proof of surjectivity used that `S_λ`, being a monotone bijection of
  `[0,∞)`, is continuous **in the scale variable** — a fact this chapter has not proved.
  Monotonicity alone gives that `sSup` and `sInf` of the orbit are fixed by every `S_κ`:
  `M ≤ S_κ M` because every `c(λ) = S_κ(c(λ/κ)) ≤ S_κ M`, and applying that at `κ` and at
  `κ⁻¹` closes it. **The blueprint proof was rewritten to this route** (author's decision
  2026-09-09), so the printed surjectivity argument is now the checked one.
-/

end Skeleton
