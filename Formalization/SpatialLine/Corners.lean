/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.Bridge
import SpatialLine.CornerDefs
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# The corners: the named profiles, densities and special functions

Blueprint: `blueprint/src/parts/10-corners.tex`, and `prop:corner-generators` in Chapter 11.
Nothing here is a blueprint node; these are the objects the corner propositions quantify over.

Most of them moved to `SpatialLine/CornerDefs.lean` on 2026-09-14, unchanged, so that the
modules below Chapter 10 that read them do not import this file; see that file's docstring.
What is left here is `erfc`, the Laplace law and the Student-t and inverse-gamma objects, which
nothing below Chapter 10 reads. The moved definitions are re-exported by the import above, so
every consumer of this file reads them as before.

## Profiles are functions, not `SDProfile` values

The Matérn, stable and Thorin data are defined here as plain functions and the corner
propositions state admissibility **existentially**, `∃ Q : SDProfile, Q.a = … ∧ …`. That is
phase A's shape — `Skeleton.semigroup_case_profile` and `Skeleton.semigroup_case_gaussian` state
the stable and Gaussian corners exactly so — and it is the shape the mathematics asks for:
admissibility of a named profile is the *content* of `prop:matern-exponent`(1), not a side
condition a definition may discharge. Building `maternProfile` as an `SDProfile` value would
prove `lem:profile-integrability` for it inside the `sorry`-free library, leaving the node that
asserts it with nothing to say. See SKELETON.md, finding F12.

## The special functions Mathlib does not have

Mathlib (v4.31.0) has no modified Bessel function and no error function. `besselK` is defined in
`SpatialLine/CornerDefs.lean` by the integral representation DLMF (10.32.9) uses; the second is

* `erfc y = (2/\sqrt\pi)∫_y^∞ e^{-v^2}\,dv` — the definition itself, needing nothing cited.

No property of either is proved here; they exist so that the nodes can be typed.
-/

namespace SpatialLine

open MeasureTheory Set
open scoped ENNReal

/-! ## Special functions -/

/-- **`erfc`**, the complementary error function,
`erfc(y) = (2/\sqrt\pi)∫_y^∞ e^{-v^2}\,dv`. -/
noncomputable def erfc (y : ℝ) : ℝ :=
  2 / Real.sqrt Real.pi * ∫ v in Ioi y, Real.exp (-v ^ 2)

/-- The Laplace law of range `θ`, whose convolution operator is `prop:corner-generators`'
`\Lambda_θ`. -/
noncomputable def laplaceLaw (θ : ℝ) : Measure ℝ :=
  volume.withDensity fun x => ENNReal.ofReal (laplaceDensity θ x)

/-! ## The Student-t corner -/

/-- The Student-t density with `2a` degrees of freedom at spatial scale `t`:
`φ_t(x) = \frac{\Gamma(a+1/2)}{\sqrt\pi\,\Gamma(a)}\,t^{-1}(1 + (x/t)^2)^{-a-1/2}`.

The scaling convention is `prop:student-t`(1)'s, and it is the one that makes the degrees of
freedom `2a` rather than `a`; the node's own `CHECK` says to read it together with the rate in
the inverse-gamma law below. -/
noncomputable def studentDensity (a t x : ℝ) : ℝ :=
  Real.Gamma (a + 1 / 2) / (Real.sqrt Real.pi * Real.Gamma a) * t⁻¹
    * (1 + (x / t) ^ 2) ^ (-a - 1 / 2)

/-- The Student-t law with `2a` degrees of freedom at spatial scale `t`. -/
noncomputable def studentLaw (a t : ℝ) : Measure ℝ :=
  volume.withDensity fun x => ENNReal.ofReal (studentDensity a t x)

/-- The mixing law of the causal Bessel family: the scaled inverse-gamma density
`p_{T_1}(u) = u^{-a-1}e^{-1/(2u)}/(2^a\Gamma(a))` on `(0,∞)`. -/
noncomputable def inverseGammaDensity (a u : ℝ) : ℝ :=
  Set.indicator (Ioi (0 : ℝ))
    (fun u => u ^ (-a - 1) * Real.exp (-(2 * u)⁻¹) / (2 ^ a * Real.Gamma a)) u

/-- The scaled inverse-gamma law of shape `a`, the causal Bessel family's delay law. -/
noncomputable def inverseGammaLaw (a : ℝ) : Measure ℝ :=
  volume.withDensity fun u => ENNReal.ofReal (inverseGammaDensity a u)

end SpatialLine
