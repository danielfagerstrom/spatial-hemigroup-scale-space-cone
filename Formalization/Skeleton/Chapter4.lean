/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Skeleton.Chapter3

/-!
# Chapter 4 — the convolution representation: **proved and moved**

**This file no longer carries any declaration.** The proving campaign of 2026-09-09 discharged
both nodes of the chapter with their statements verbatim, and the five declarations moved into the
`sorry`-free library:

| blueprint node | declarations | file |
|---|---|---|
| `lem:convolution-representation` | `SpatialLine.representation_existsUnique`, `SpatialLine.representation_symmetric` | `SpatialLine/Representation.lean` |
| `lem:convolution-representation` (converse) | `SpatialLine.representation_converse` | `SpatialLine/ConvolutionOperator.lean` |
| `lem:nonvanishing` | `SpatialLine.nonvanishing`, `SpatialLine.nonvanishing_exponent` | `SpatialLine/Nonvanishing.lean` |

The file itself is kept because `Skeleton.Chapter5` imports it and the later chapters are still
being proved; it is the chapter's design record until the whole skeleton is retired.

## What writing this chapter down found (statement phase, 2026-09-08)

**1. The axiom lists in this chapter are not the full core, and the split of `Family.lean` makes
that expressible.** `lem:convolution-representation` names (A1), (A2), (A4), (A5) and nothing
else — no cascade, no continuity — and `lem:nonvanishing` names (A1)–(A3) and (A5)–(A7), which is
exactly `PreCascadeCore`. Both are stated with those hypotheses and no others. The representation
is therefore stated against a bare operator family with three hypotheses spelled out, not against
a structure; that is deliberate, because `prop:no-positivity-no-classification` is the article's
own witness that the surrounding axioms are separable.

**2. `IsKernelFamily` is where (A4) goes.** Every later chapter's hypothesis list reads
"(A1)–(A7)", and the only work (A4) does in those lists is to produce the representation. Since
the representation is supplied to those nodes as `IsKernelFamily` — whose first field is that the
kernels are *probability* measures — the later statements need `PreCascadeCore` plus
`IsKernelFamily` and not `IsPositive`. This is a hypothesis-archaeology finding, and it is
recorded at each node rather than silently exploited.

**3. Nonvanishing is stated at the transform, not at the exponent.** `SpatialLine.exponent` is
`-log ∘ fourierCos`, total and junk where the transform is nonpositive. So `nonvanishing` is the
statement that the junk region is not entered, and every clause about `g` is downstream of it.
Stating it the other way round — an exponent-valued definition carrying a positivity proof —
would have put a proof obligation inside a definition in the `sorry`-free library.

## What proving the chapter found (proving phase, 2026-09-09)

**4. The symmetry rider carries two hypotheses its proof does not consume, and that matters
downstream.** `representation_symmetric` lists (A2), (A4) and (A5) because the node lists them,
but the proof uses only (A3) and a representing measure already in hand. `lem:nonvanishing` — whose
hypothesis list is `PreCascadeCore`, with no (A4) — therefore *cannot* call the node, and calls the
single-operator form `SpatialLine.isSymmetric_of_reflL1` instead. The node's statement was left
verbatim and the linter silenced; the correct reading of finding 2 above is that (A4) is spent
exactly once, in `representation_existsUnique`, and never again.

**5. The uniqueness clause is where the line and the half-line genuinely diverge.** Paper I reads
uniqueness off a Laplace transform, injective on causal measures, by testing the operator on
`1_{(0,1)}`. There is no half-line here to clamp an exponential to, and the blueprint's own device
is used instead: `SpatialLine.charCLM ω` pairs against the character `e^{iωx}`, bounded on all of
`ℝ`, and `SpatialLine.charCLM_mconvL1` factorises the pairing as `μ̂(ω) · f̂(ω)`. The Gaussian test
function is load-bearing twice — once here, because its transform has no zeros, and once in
`continuousOn_fourierCos_kernel`, where (A7) is divided by it.

**6. The nonvanishing argument was formalised as a chain, not as a minimum.** The blueprint takes
`t_* := min {t ≥ s : μ̂_{s,t}(ω) = 0}` and contradicts joint continuity at `(t_*, t_*)`. The Lean
runs an equivalent argument that needs no infimum and no closed-set reasoning: on the compact
triangle `{(a,b) : s ≤ a ≤ b ≤ t}` the transform is *uniformly* continuous and equals `1` on the
diagonal, so one `δ` serves for all pairs, and multiplicativity walks from `s` to `t` in steps of
`δ/2` by induction on the step count. Both arguments consume exactly the same hypothesis — joint
continuity of `(a,b) ↦ μ̂_{a,b}(ω)` on the index set — so the blueprint proof is left as written.

**7. Prices.** `lem:convolution-representation` was estimated **L** and cost about that, but the
cost is concentrated in the port rather than in the mathematics: `SpatialLine/BochnerConvolution.lean`
and the transport block of `SpatialLine/ConvolutionOperator.lean` are Paper I's files with
causality deleted, and they compiled almost unchanged. `lem:nonvanishing` was estimated **M** and
cost rather less than the representation but more than `M` suggests, the two-thirds of it that is
new being the `charFun` bridge and the compactness argument.
-/
