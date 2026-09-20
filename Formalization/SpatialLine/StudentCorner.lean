/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.Corners

/-!
# `prop:student-t`(1), the scaling clause

Blueprint: `blueprint/src/parts/10-corners.tex`, `prop:student-t`, the second half of clause (1):
`φ_t = t⁻¹φ_1(·/t)`, here in the equivalent form `studentLaw a t = (studentLaw a 1).map (t · )`.

## What the clause needs, and what its proof cites

The node's proof obtains clause (1) by conditioning the Brownian kernel on the inverse-gamma
delay law, and the annotation says the scaling clause is `prop:bridge-families`. That is an
upper bound on what the statement needs, not the obligation. `studentLaw` is *defined* by the
explicit density, so the identity here is the change of variables for a density under a
dilation and nothing else: `studentDensity a t (tx) = t⁻¹ studentDensity a 1 x` is arithmetic,
and Mathlib's `Real.map_volume_mul_left` with `setLIntegral_map` does the rest. Neither
`Skeleton.bridge_families_bessel` nor any Chapter 9 node is consumed, and this declaration is
therefore not blocked on that chapter — which the skeleton's annotation ("given
`bridge_families_bessel`") could be read as saying it was.

What *does* rest on the conditioning computation is the other half of clause (1), the
identification of `φ_1` with the law of `B_{T_1}`; that is `bridge_families_bessel` and it stays
where it is.
-/

namespace SpatialLine

open MeasureTheory Set Filter
open scoped ENNReal Topology

theorem measurable_studentDensity (a t : ℝ) :
    Measurable fun x : ℝ => ENNReal.ofReal (studentDensity a t x) := by
  unfold studentDensity
  fun_prop

/-- The dilation identity for the density: `φ_t(tx) = t⁻¹φ_1(x)`. -/
theorem studentDensity_dilate {t : ℝ} (ht : 0 < t) (a x : ℝ) :
    studentDensity a t (t * x) = t⁻¹ * studentDensity a 1 x := by
  unfold studentDensity
  rw [show t * x / t = x by field_simp, show x / 1 = x by ring]
  simp only [inv_one]
  ring

/-- **`prop:student-t`(1), the scaling.** The kernel at scale `t` is the dilate of the kernel at
canonical scale `1`.

**Priced M; paid S.** The M was priced "given `bridge_families_bessel`"; the statement consumes
no Chapter 9 node at all — see the module docstring. -/
theorem student_density (a : ℝ) (ha : 0 < a) :
    ∀ t : ℝ, 0 < t → studentLaw a t = (studentLaw a 1).map fun x => t * x := by
  intro t ht
  refine Measure.ext fun s hs => ?_
  rw [Measure.map_apply (measurable_const_mul t) hs, studentLaw, studentLaw,
    withDensity_apply _ hs, withDensity_apply _ ((measurable_const_mul t) hs)]
  have key := setLIntegral_map (μ := (volume : Measure ℝ)) (s := s)
    (f := fun y : ℝ => ENNReal.ofReal (studentDensity a t y)) (g := fun x : ℝ => t * x)
    hs (measurable_studentDensity a t) (measurable_const_mul t)
  rw [Real.map_volume_mul_left ht.ne', Measure.restrict_smul, lintegral_smul_measure] at key
  have hpt : ∀ x : ℝ, ENNReal.ofReal (studentDensity a t (t * x))
      = ENNReal.ofReal t⁻¹ * ENNReal.ofReal (studentDensity a 1 x) := by
    intro x
    rw [studentDensity_dilate ht, ENNReal.ofReal_mul (by positivity)]
  simp only [hpt] at key
  rw [lintegral_const_mul _ (measurable_studentDensity a 1),
    abs_of_pos (by positivity : (0:ℝ) < t⁻¹), smul_eq_mul] at key
  exact (ENNReal.mul_right_inj (by simp [ENNReal.ofReal_eq_zero]; positivity)
    ENNReal.ofReal_ne_top).mp key

end SpatialLine
