/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.TwoSidedProfile
import SpatialLine.OriginSingularity
import SpatialLine.MaternCorner

/-!
# The Matérn member at the boundedness threshold

Blueprint: `blueprint/src/parts/10-corners.tex`, `prop:matern-exponent`(1), read at the origin;
`blueprint/src/parts/08-cone.tex`, `cor:origin-boundedness` and `lem:folding-translation`.

The Matérn profile at range `θ` is `k(x) = 2γe^{-x/θ}`, so `k(0+) = 2γ`: the member sits in
ledger A10's singular regime for `γ < 1/2`, at its threshold for `γ = 1/2`, and in its smooth
regime for `γ > 1/2`. That is the same boundary the external review's finding C found from the
other side — the closed form `(|x|/2t)^{γ-1/2}K_{γ-1/2}(|x|/t)` is a Matérn *covariance* only for
smoothness `γ - 1/2 > 0`, and at `γ = 1/2` it is `K_0`, which diverges at the origin — and the
agreement of the two is the witness that the folding translation of
`SpatialLine/TwoSidedProfile.lean` is the right one. Both sides are recorded in
`blueprint/AXIOMS.md` at A10.

`matern_origin_constant` is the profile half, and it is on Lean core. The closed-form half is
**not** proved here, and the two halves of it are priced very differently (`SKELETON.md` § 25).

* *Boundedness above the threshold*, that `(z/2)^ν K_ν(z)` stays bounded as `z → 0` for `ν > 0`,
  needs the small-argument asymptotic of `K_ν` — ledger **A16**, unadmitted — or the elementary
  substitution `w = (z/2)e^u` in the defining integral, which bounds it by `Γ(ν)`. Priced **M**,
  about 150 lines, and not attempted.
* *Unboundedness at the threshold* needs **no** asymptotic, which is worth recording: it is
  `K_0(z) = ∫_0^∞ e^{-z\cosh u}du ≥ M e^{-z\cosh M}` for every `M`, and the right-hand side tends
  to `M` as `z → 0`. What the classical proof cites — the logarithmic asymptotic — is an upper
  bound on what the obligation needs. Priced **S–M**, about 90 lines, of which the domination
  `e^{-z\cosh u} ≤ e^{-z/2}e^{-(z/2)u}` and `integrableOn_exp_neg_Ioi_zero` are the only
  analysis. Not attempted here; the blueprint claims nothing about it.

The *rate* at the threshold — that the divergence is logarithmic — is A16's asymptotic and is
asserted nowhere in this article.
-/

namespace SpatialLine

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-! ## The profile at the origin -/

/-- **The Matérn profile has right limit `2γ` at the origin.** -/
theorem maternProfile_tendsto_nhdsGT (γ : ℝ) {θ : ℝ} (hθ : 0 < θ) :
    Tendsto (maternProfile γ θ) (𝓝[>] (0 : ℝ)) (𝓝 (2 * γ)) := by
  have hcont : Continuous fun x : ℝ => 2 * γ * Real.exp (-(x / θ)) := by fun_prop
  have hlim : Tendsto (fun x : ℝ => 2 * γ * Real.exp (-(x / θ))) (𝓝[>] (0 : ℝ)) (𝓝 (2 * γ)) := by
    have h : Tendsto (fun x : ℝ => 2 * γ * Real.exp (-(x / θ))) (𝓝[>] (0 : ℝ))
        (𝓝 (2 * γ * Real.exp (-((0 : ℝ) / θ)))) :=
      (hcont.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    simpa using h
  refine Tendsto.congr' ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (maternProfile_of_pos hx γ θ).symm

/-- **The Matérn member's constant at the origin, and the three regimes it selects.**

The datum of `prop:matern-exponent`(1) has Gaussian coefficient `0` and folded profile with right
limit `2γ`; its two-sided profile has both one-sided limits equal to `γ`, so ledger A10's constant
`c = k(0+) + k(0−)` is `2γ`. The three iffs are the translation of A10's three regimes into the
family's own parameter: the singular regime is `γ < 1/2`, the threshold `γ = 1/2`, and the smooth
regime `γ > 1/2`. -/
theorem matern_origin_constant {γ θ : ℝ} (hγ : 0 < γ) (hθ : 0 < θ) :
    (maternDatum γ θ hγ hθ).a = 0 ∧
      Tendsto (maternDatum γ θ hγ hθ).k (𝓝[>] (0 : ℝ)) (𝓝 (2 * γ)) ∧
      Tendsto (maternDatum γ θ hγ hθ).twoSided.k (𝓝[>] (0 : ℝ)) (𝓝 γ) ∧
      Tendsto (maternDatum γ θ hγ hθ).twoSided.k (𝓝[<] (0 : ℝ)) (𝓝 γ) ∧
      (2 * γ < 1 ↔ γ < 1 / 2) ∧ (2 * γ = 1 ↔ γ = 1 / 2) ∧ (1 < 2 * γ ↔ 1 / 2 < γ) := by
  have hk : Tendsto (maternDatum γ θ hγ hθ).k (𝓝[>] (0 : ℝ)) (𝓝 (2 * γ)) := by
    rw [maternDatum_k]
    exact maternProfile_tendsto_nhdsGT γ hθ
  have hhalf : 2 * γ / 2 = γ := by ring
  refine ⟨rfl, hk, ?_, ?_, by constructor <;> intro h <;> linarith,
    by constructor <;> intro h <;> linarith, by constructor <;> intro h <;> linarith⟩
  · have := twoSided_tendsto_nhdsGT (maternDatum γ θ hγ hθ) hk
    rwa [hhalf] at this
  · have := twoSided_tendsto_nhdsLT (maternDatum γ θ hγ hθ) hk
    rwa [hhalf] at this

/-! ## The threshold read in the family's own parameter

Added 2026-09-15 with the admission of ledger A10. `cor:origin-boundedness`(2) does not stop at
`k(0+) = 2γ`: it says that the Matérn member's kernel is bounded at the origin exactly for
`γ > 1/2`, which is the *consequence* of clause (1) at this member. The bundle below is that
consequence, so that the node's Lean tag names a declaration for each of its clauses rather than
leaving the modus ponens to the reader. -/

/-- **`cor:origin-boundedness`(2) at the Matérn member.** The kernel of the Matérn member of
index `γ` and range `θ` has a continuous representative for `γ > 1/2`, and for `γ ≤ 1/2` no
representative of it is bounded near the origin. This is `origin_boundedness` at `c = 2γ`, the
constant being `matern_origin_constant`.

`[A]`, ledger **A10** at all three regimes, through `origin_boundedness`. -/
theorem matern_origin_boundedness {γ θ : ℝ} (hγ : 0 < γ) (hθ : 0 < θ)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hsym : IsSymmetric μ)
    (hcos : ∀ ω : ℝ, fourierCos μ ω = Real.exp (-(maternDatum γ θ hγ hθ).exponent ω)) :
    (1 / 2 < γ → ∃ p : ℝ → ℝ, μ = volume.withDensity (fun x => ENNReal.ofReal (p x)) ∧
        Continuous p) ∧
      (γ ≤ 1 / 2 → ∀ p : ℝ → ℝ, μ = volume.withDensity (fun x => ENNReal.ofReal (p x)) →
        ∀ δ : ℝ, 0 < δ → ∀ M : ℝ, ∃ x : ℝ, 0 < |x| ∧ |x| < δ ∧ M < p x) := by
  obtain ⟨ha, hk, -, -, -, -, -⟩ := matern_origin_constant hγ hθ
  have h := origin_boundedness (maternDatum γ θ hγ hθ) ha (by linarith : (0 : ℝ) < 2 * γ) hk
    μ hsym hcos
  exact ⟨fun hγ' => h.1 (by linarith), fun hγ' => h.2 (by linarith)⟩

end SpatialLine
