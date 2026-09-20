/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import ScaleSpaceCore.CausalCone
import SpatialLine.Bridge
import SpatialLine.SelfDecomposable
import SpatialLine.ProfileTail
import SpatialLine.Symbol
import SpatialLine.ExponentContinuity
import SpatialLine.LatticeZero

/-!
# `prop:bridge-strictness`: the bridge is not onto

Blueprint: `blueprint/src/parts/09-bridge.tex` — `prop:bridge-strictness`, clauses (1)–(3).

## The criterion, and what `IsSubordinated` unfolds to

`SpatialLine.IsSubordinated F` is `∃ F_I : CausalAdmissible, ∀ ω, F ω = F_I(ω²/2)`, so clause
(1)'s forward direction is definitional and its converse is the substitution
`σ = ω²/2` read backwards, which needs the exponent's evenness (`SDProfile.exponent_neg`)
because `√(ω²) = |ω|`.

## Clause (2) spends no ledger entry

The printed proof cites **A11** (Bernstein) for the step "a completely monotone function
vanishing at an interior point vanishes identically". `ScaleSpaceCore/CausalCone.lean` shows
that step is not the obligation: `F_I' = b₀ + ∫₀^∞ e^{-σu}k_I(u)\,du` is *given* as a Laplace
transform by `def:causal-admissible`, and an integral of a strictly positive integrand vanishes
only when the data do. So `bridge_strictness_increasing` is machine-checked to Lean core, and
the blueprint's proof of record has been rewritten to the checked route.

## Where the lattice fact lives

Clause (3) reads `cos(ω₀u) = 1` as the lattice `(2π/|ω₀|)ℤ` at the Choquet measure `ϖ`, which
is not a probability measure, so `lattice_zero_mem_iff` does not apply to it. The set equality
itself is `SpatialLine.setOf_cos_eq_one` in `SpatialLine/LatticeZero.lean`, where
`lem:lattice-zero` is: this file carried a second copy on the branch and wave 4's merge lifted
the one copy into the node's own file (2026-09-10).
-/

namespace SpatialLine

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-! ## `Cin` is strictly positive off the origin -/

/-- `Cin(z) > 0` for `z > 0`.

Near the origin this is the expansion `Cin(z) = z²/4 + O(z⁴)` of `lem:cin-rays`(3) in the
quantitative form `cin_sub_sq_bound`; beyond `1` it is monotonicity. -/
theorem cin_pos {z : ℝ} (hz : 0 < z) : 0 < cin z := by
  have hunit : ∀ y : ℝ, 0 < y → y ≤ 1 → 0 < cin y := by
    intro y hy hy1
    have hb := cin_sub_sq_bound hy.le hy1
    have hb' : -(5 / 96 * y ^ 4) ≤ cin y - y ^ 2 / 4 := (abs_le.mp hb).1
    nlinarith [sq_nonneg y, pow_le_pow_left₀ hy.le hy1 2]
  rcases le_or_gt z 1 with h | h
  · exact hunit z hz h
  · exact lt_of_lt_of_le (hunit 1 one_pos le_rfl)
      (monotoneOn_cin (by norm_num : (1 : ℝ) ∈ Ici (0 : ℝ))
        (mem_Ici.mpr hz.le : z ∈ Ici (0 : ℝ)) h.le)

/-! ## `prop:bridge-strictness`(1), the criterion -/

/-- **`prop:bridge-strictness`(1), the criterion.** `F` is subordinated exactly when
`σ ↦ F(√(2σ))` is causally admissible.

`Skeleton.bridge_strictness_criterion`'s statement verbatim. -/
theorem bridge_strictness_criterion (P : SDProfile) :
    IsSubordinated P.exponent ↔
      ∃ FI : CausalAdmissible, ∀ σ : ℝ, 0 ≤ σ →
        FI.exponent σ = P.exponent (Real.sqrt (2 * σ)) := by
  constructor
  · rintro ⟨FI, hFI⟩
    refine ⟨FI, fun σ hσ => ?_⟩
    rw [hFI (Real.sqrt (2 * σ)), Real.sq_sqrt (by linarith : (0 : ℝ) ≤ 2 * σ)]
    ring_nf
  · rintro ⟨FI, hFI⟩
    refine ⟨FI, fun ω => ?_⟩
    have hσ : (0 : ℝ) ≤ ω ^ 2 / 2 := by positivity
    rw [hFI _ hσ]
    have h2 : 2 * (ω ^ 2 / 2) = ω ^ 2 := by ring
    rw [h2, Real.sqrt_sq_eq_abs]
    rcases abs_choice ω with h | h
    · rw [h]
    · rw [h, P.exponent_neg]

/-! ## `prop:bridge-strictness`(2), strict increase -/

/-- **`prop:bridge-strictness`(2), strict increase.** Every subordinated exponent other than `0`
is strictly increasing on `(0,∞)`, with a strictly positive derivative there.

`Skeleton.bridge_strictness_increasing`'s statement verbatim.

**Proof of record rewritten (2026-09-10).** The printed proof charged the step to ledger
**A11**; the machine-checked route does not use it. See the module docstring and
`SpatialLine/CausalExponent.lean`. -/
theorem bridge_strictness_increasing (P : SDProfile) (hsub : IsSubordinated P.exponent)
    (hne : ∃ ω : ℝ, P.exponent ω ≠ 0) :
    StrictMonoOn P.exponent (Ioi 0) ∧
      ∀ ω : ℝ, 0 < ω → 0 < deriv P.exponent ω := by
  obtain ⟨FI, hFI⟩ := hsub
  -- The causal exponent is not identically zero on `[0,∞)`.
  have hneFI : ∃ τ : ℝ, 0 ≤ τ ∧ FI.exponent τ ≠ 0 := by
    obtain ⟨ω, hω⟩ := hne
    exact ⟨ω ^ 2 / 2, by positivity, fun h => hω (by rw [hFI ω, h])⟩
  have hfun : P.exponent = fun ω : ℝ => FI.exponent (ω ^ 2 / 2) := funext hFI
  -- The chain rule at a positive frequency.
  have hderiv : ∀ ω : ℝ, 0 < ω → 0 < deriv P.exponent ω := by
    intro ω hω
    have hσ : (0 : ℝ) < ω ^ 2 / 2 := by positivity
    have hinner : HasDerivAt (fun y : ℝ => y ^ 2 / 2) ω ω := by
      have h := (hasDerivAt_pow 2 ω).div_const 2
      simpa using h
    have hchain : HasDerivAt P.exponent
        ((FI.b₀ + ∫ u in Ioi (0 : ℝ), Real.exp (-(ω ^ 2 / 2 * u)) * FI.k u) * ω) ω := by
      rw [hfun]
      exact (FI.hasDerivAt_exponent hσ).comp ω hinner
    rw [hchain.deriv]
    exact mul_pos (FI.deriv_integral_pos hσ hneFI) hω
  refine ⟨?_, hderiv⟩
  refine strictMonoOn_of_deriv_pos (convex_Ioi 0) P.continuous_exponent.continuousOn ?_
  intro x hx
  rw [interior_Ioi] at hx
  exact hderiv x hx

/-! ## `prop:bridge-strictness`(3), the `Cin` rays -/

/-- **`prop:bridge-strictness`(3), no `Cin` ray is subordinated.**

`Skeleton.bridge_strictness_cin`'s statement verbatim. The stationary point is exhibited:
`Cin'(2πn) = (1 - cos 2πn)/2πn = 0`, which contradicts clause (2). -/
theorem bridge_strictness_cin {τ : ℝ} (hτ : 0 < τ) (P : SDProfile)
    (hP : ∀ ω : ℝ, P.exponent ω = cin (τ * ω)) : ¬ IsSubordinated P.exponent := by
  intro hsub
  -- The exponent is not identically zero: `Cin(τ) > 0`.
  have hne : ∃ ω : ℝ, P.exponent ω ≠ 0 :=
    ⟨1, by rw [hP 1, mul_one]; exact (cin_pos hτ).ne'⟩
  obtain ⟨-, hderiv⟩ := bridge_strictness_increasing P hsub hne
  -- The frequency `ω₀ = 2π/τ` is stationary.
  set ω₀ : ℝ := 2 * Real.pi / τ with hω₀
  have hω₀pos : 0 < ω₀ := by
    have := Real.pi_pos
    positivity
  have hfun : P.exponent = fun ω : ℝ => cin (τ * ω) := funext hP
  have hd : HasDerivAt P.exponent (cinIntegrand (τ * ω₀) * τ) ω₀ := by
    rw [hfun]
    have hinner : HasDerivAt (fun y : ℝ => τ * y) τ ω₀ := by
      simpa using (hasDerivAt_id ω₀).const_mul τ
    exact (hasDerivAt_cin (τ * ω₀)).comp ω₀ hinner
  have hval : τ * ω₀ = 2 * Real.pi := by
    rw [hω₀]
    field_simp
  have hzero : cinIntegrand (τ * ω₀) = 0 := by
    rw [hval, cinIntegrand]
    have : Real.cos (2 * Real.pi) = 1 := Real.cos_two_pi
    rw [this]
    simp
  rw [hzero, zero_mul] at hd
  have := hderiv ω₀ hω₀pos
  rw [hd.deriv] at this
  exact lt_irrefl 0 this

/-! ## `prop:bridge-strictness`(3), the general stationary-point criterion -/

/-- The symbol is even in the frequency. -/
theorem symbolL_neg (a : ℝ) (ϖ : Measure ℝ) (ω : ℝ) : symbolL a ϖ (-ω) = symbolL a ϖ ω := by
  rw [symbolL, symbolL]
  congr 1
  · congr 1
    ring
  · refine lintegral_congr fun v => ?_
    rw [neg_mul, Real.cos_neg]

/-- **`prop:bridge-strictness`(3), the general stationary-point criterion.**

`Skeleton.bridge_strictness_stationary`'s statement verbatim. An admissible `F` has a stationary
point at `ω₀ ≠ 0` exactly when its Gaussian coefficient vanishes and its Choquet measure is
carried by the lattice `(2π/|ω₀|)ℤ`; and no such `F` with `F ≢ 0` is subordinated.

The first conjunct is `eq:symbol` read as a sum of two nonnegative `ℝ≥0∞` terms: the sum
vanishes exactly when both do, the first says `a = 0` and the second says `cos(ω₀u) = 1` for
`ϖ`-almost every `u`, which is `setOf_cos_eq_one`. The second conjunct is
`bridge_strictness_increasing` transported to `|ω₀|` through the symbol's evenness. -/
theorem bridge_strictness_stationary (P : SDProfile) (ϖ : Measure ℝ)
    (hϖ : HasProfileTail P.k ϖ) {ω₀ : ℝ} (hω₀ : ω₀ ≠ 0) :
    (symbolL P.a ϖ ω₀ = 0 ↔
        P.a = 0 ∧ ϖ {u : ℝ | ∃ n : ℤ, u = 2 * Real.pi / |ω₀| * n}ᶜ = 0) ∧
      ((∃ ω : ℝ, P.exponent ω ≠ 0) → symbolL P.a ϖ ω₀ = 0 → ¬ IsSubordinated P.exponent) := by
  have hsq : (0 : ℝ) < ω₀ ^ 2 := by positivity
  have hmeas : AEMeasurable (fun v : ℝ => ENNReal.ofReal (1 - Real.cos (ω₀ * v))) ϖ :=
    (SymLevyPair.measurable_one_sub_cos ω₀).aemeasurable
  have hjump : (∫⁻ v, ENNReal.ofReal (1 - Real.cos (ω₀ * v)) ∂ϖ) = 0
      ↔ ϖ {u : ℝ | ∃ n : ℤ, u = 2 * Real.pi / |ω₀| * n}ᶜ = 0 := by
    rw [lintegral_eq_zero_iff' hmeas]
    constructor
    · intro h
      have hcos : ∀ᵐ v ∂ϖ, Real.cos (ω₀ * v) = 1 := by
        filter_upwards [h] with v hv
        have hle : 1 - Real.cos (ω₀ * v) ≤ 0 :=
          ENNReal.ofReal_eq_zero.mp (by simpa using hv)
        linarith [Real.cos_le_one (ω₀ * v)]
      rw [ae_iff] at hcos
      have heq : {u : ℝ | ∃ n : ℤ, u = 2 * Real.pi / |ω₀| * n}ᶜ
          = {a : ℝ | ¬ Real.cos (ω₀ * a) = 1} := by
        rw [← setOf_cos_eq_one hω₀, compl_setOf]
      rw [heq]
      exact hcos
    · intro h
      have hcos : ∀ᵐ v ∂ϖ, Real.cos (ω₀ * v) = 1 := by
        rw [ae_iff]
        have heq : {a : ℝ | ¬ Real.cos (ω₀ * a) = 1}
            = {u : ℝ | ∃ n : ℤ, u = 2 * Real.pi / |ω₀| * n}ᶜ := by
          rw [← setOf_cos_eq_one hω₀, compl_setOf]
        rw [heq]
        exact h
      filter_upwards [hcos] with v hv
      simp [hv]
  refine ⟨?_, ?_⟩
  · rw [symbolL, add_eq_zero]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, hjump.mp h2⟩
      have hle := ENNReal.ofReal_eq_zero.mp h1
      nlinarith [P.a_nonneg]
    · rintro ⟨h1, h2⟩
      refine ⟨?_, hjump.mpr h2⟩
      rw [h1]
      simp
  · intro hne hzero hsub
    obtain ⟨-, hderiv⟩ := bridge_strictness_increasing P hsub hne
    have habs : (0 : ℝ) < |ω₀| := abs_pos.mpr hω₀
    have hsymabs : symbolL P.a ϖ |ω₀| = 0 := by
      rcases abs_choice ω₀ with h | h
      · rw [h]; exact hzero
      · rw [h, symbolL_neg]; exact hzero
    have hkey := sd_exponents_symbol P P.exponent (fun _ => rfl) ϖ hϖ |ω₀|
    rw [hsymabs] at hkey
    have hle : |ω₀| * deriv P.exponent |ω₀| ≤ 0 := ENNReal.ofReal_eq_zero.mp hkey.symm
    nlinarith [hderiv |ω₀| habs]

/-! ## `prop:bridge-strictness`(4), the subordinated slice is a proper subcone -/

/-- **`prop:bridge-strictness`(4).** The subordinated exponents form a convex cone closed under
dilation, and it omits every extreme `Cin` ray.

`Skeleton.bridge_strictness_cone`'s statement verbatim. The three closure clauses are the causal
cone's three constructions (`CausalAdmissible.add`, `.smul`, `.dilate`) read through the
substitution `σ = ω²/2`, which turns a spatial dilation by `λ` into a causal dilation by `λ²`;
the exclusion is `bridge_strictness_cin` at the ray `lem:cin-rays`(1) exhibits. -/
theorem bridge_strictness_cone :
    (∀ F G : ℝ → ℝ, IsSubordinated F → IsSubordinated G →
        IsSubordinated fun ω => F ω + G ω) ∧
      (∀ (F : ℝ → ℝ) (c : ℝ), 0 ≤ c → IsSubordinated F → IsSubordinated fun ω => c * F ω) ∧
      (∀ (F : ℝ → ℝ) (lam : ℝ), 0 < lam → IsSubordinated F →
        IsSubordinated fun ω => F (lam * ω)) ∧
      ∀ τ : ℝ, 0 < τ → ¬ IsSubordinated fun ω => cin (τ * ω) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro F G ⟨FI, hFI⟩ ⟨GI, hGI⟩
    refine ⟨FI.add GI, fun ω => ?_⟩
    show F ω + G ω = _
    rw [ScaleSpace.CausalAdmissible.exponent_add FI GI (by positivity : (0 : ℝ) ≤ ω ^ 2 / 2),
      hFI ω, hGI ω]
  · rintro F c hc ⟨FI, hFI⟩
    refine ⟨FI.smul hc, fun ω => ?_⟩
    show c * F ω = _
    rw [ScaleSpace.CausalAdmissible.exponent_smul FI hc (ω ^ 2 / 2), hFI ω]
  · rintro F lam hlam ⟨FI, hFI⟩
    have hsq : (0 : ℝ) < lam ^ 2 := by positivity
    refine ⟨FI.dilate hsq, fun ω => ?_⟩
    show F (lam * ω) = _
    rw [ScaleSpace.CausalAdmissible.exponent_dilate FI hsq (ω ^ 2 / 2), hFI (lam * ω)]
    congr 1
    ring
  · intro τ hτ
    obtain ⟨Q, -, -, hQ⟩ := cin_ray hτ
    have hfun : (fun ω : ℝ => cin (τ * ω)) = Q.exponent := (funext hQ).symm
    rw [hfun]
    exact bridge_strictness_cin hτ Q hQ

end SpatialLine
