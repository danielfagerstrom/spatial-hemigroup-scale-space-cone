/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.CinRays
import SpatialLine.AdmissibleCone
import SpatialLine.Growth
import SpatialLine.ProfileOfMeasure
import Mathlib.MeasureTheory.Integral.Layercake

/-!
# `prop:choquet-cone`: the superposition map, its domain, and its linearity

Blueprint: `blueprint/src/parts/08-cone.tex`, `prop:choquet-cone`. Four of the node's eight
declarations are here -- the map into the cone, its surjectivity with the inverse the node names,
the domain condition, and linearity. The remaining four (injectivity and the three extremality
clauses) are still in `Formalization/Skeleton/Chapter8.lean`; what they wait on is recorded
there.

## The construction, and where it now lives

The map into the cone is `choquetSDProfile` — the `SDProfile` whose profile is the tail of `ϖ` —
together with the domain condition `domain_iff` reduces to the two integrability conditions of
`lem:profile-integrability`, and the two layer-cake exchanges behind that reduction. All of it
moved to `SpatialLine/ProfileOfMeasure.lean` on 2026-09-14, unchanged, because Chapter 7's
`lem:selfdecomposable-exponents`, (2) implies (3), builds its profile the same way and must not
import the four theorems below to do it (ADR-0005). The import above re-exports it, so the
proofs here read it as before.

## The domain at one frequency

`lintegral_cin_ne_top_iff` is the load-bearing lemma of `choquet_cone_domain`: for a single
`omega != 0`, finiteness of `int Cin(tau omega) dvarpi` is equivalent to the domain condition.
Sufficiency is `choquet_cone_forward` followed by `lem:quadratic-growth`; necessity is the
pointwise bound `exists_domain_le_cin`.

That bound is where the estimate was cheaper than expected. The blueprint proof asks for a
comparison of `Cin(z)` with `z^2` near `0` and with `log z` at infinity that is *uniform on
compact subsets of the punctured line*, and a first attempt spends its effort on a two-sided
comparison valid at every `z`. None is needed: three regimes suffice, and the middle one -- the
bounded stretch between `tau b = 1` and a threshold -- is covered by monotonicity of `Cin`
alone, `Cin(tau b) >= Cin(1) >= 19/96`. The two extreme regimes then need only the *lower*
bounds `Cin(z) >= (19/96)z^2` on `[0,1]` and `Cin(z) >= (1 + log z)/2` past a threshold, both
one-line consequences of the expansions of `lem:cin-rays`(1). Upper bounds are never used.
-/

namespace SpatialLine

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-- **`prop:choquet-cone`, the map lands in the cone.** -/
theorem choquet_cone_forward {a : ℝ} (ha : 0 ≤ a) (ϖ : Measure ℝ) (hfold : IsFolded ϖ)
    (hdom : ∫⁻ τ, ENNReal.ofReal (min (τ ^ 2) (1 + Real.log (max 1 τ))) ∂ϖ ≠ ⊤) :
    ∃ Q : SDProfile, Q.a = a ∧ HasProfileTail Q.k ϖ ∧
      ∀ ω : ℝ, Q.exponentL ω = cinSuperpositionL a ϖ ω := by
  refine ⟨choquetSDProfile ha ϖ hfold hdom, rfl, hasProfileTail_choquetSDProfile ha ϖ hfold hdom,
    fun ω => ?_⟩
  exact cin_superposition _ ϖ (hasProfileTail_choquetSDProfile ha ϖ hfold hdom) ω

/-- **`prop:choquet-cone`, the map is onto the cone**, with the inverse the blueprint names. -/
theorem choquet_cone_surjective (P : SDProfile) :
    ∃ ϖ : Measure ℝ, HasProfileTail P.k ϖ ∧
      (∫⁻ τ, ENNReal.ofReal (min (τ ^ 2) (1 + Real.log (max 1 τ))) ∂ϖ ≠ ⊤) ∧
      ∀ ω : ℝ, P.exponentL ω = cinSuperpositionL P.a ϖ ω := by
  obtain ⟨ϖ, htail⟩ := cin_superposition_exists P
  obtain ⟨hfold, htaileq⟩ := htail
  refine ⟨ϖ, ⟨hfold, htaileq⟩, ?_, fun ω => cin_superposition P ϖ ⟨hfold, htaileq⟩ ω⟩
  refine (domain_iff ϖ hfold).mpr ⟨?_, ?_⟩
  · rw [lintegral_min_sq_eq ϖ hfold]
    have heq : (∫⁻ x in Ioo (0 : ℝ) 1, ϖ (Ioi x) * ENNReal.ofReal x)
        = ∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (x * P.k x) := by
      refine lintegral_congr_ae ?_
      filter_upwards [ae_restrict_of_ae_restrict_of_subset
        (show Ioo (0 : ℝ) 1 ⊆ Ioi 0 from Ioo_subset_Ioi_self) htaileq,
        ae_restrict_mem measurableSet_Ioo] with x hx hxm
      rw [hx, ← ENNReal.ofReal_mul (P.k_nonneg x (mem_Ioi.mpr hxm.1)), mul_comm]
    rw [heq]
    exact P.integrable_near_zero
  · rw [lintegral_log_max_eq ϖ hfold]
    have heq : (∫⁻ x in Ioi (1 : ℝ), ϖ (Ioi x) * ENNReal.ofReal x⁻¹)
        = ∫⁻ x in Ioi (1 : ℝ), ENNReal.ofReal (P.k x / x) := by
      refine lintegral_congr_ae ?_
      filter_upwards [ae_restrict_of_ae_restrict_of_subset
        (show Ioi (1 : ℝ) ⊆ Ioi 0 from Ioi_subset_Ioi zero_le_one) htaileq,
        ae_restrict_mem measurableSet_Ioi] with x hx hxm
      rw [hx, ← ENNReal.ofReal_mul (P.k_nonneg x
        (mem_Ioi.mpr (lt_trans zero_lt_one hxm))), div_eq_mul_inv]
    rw [heq]
    exact P.integrable_at_top

/-! ## The domain, at one frequency and at all -/

/-- **The domain condition is sufficient**, at every frequency at once. -/
theorem lintegral_cin_ne_top_of_domain (ϖ : Measure ℝ) (hfold : IsFolded ϖ)
    (hdom : (∫⁻ τ, ENNReal.ofReal (domainIntegrand τ) ∂ϖ) ≠ ⊤) (ω : ℝ) :
    (∫⁻ τ, ENNReal.ofReal (cin (τ * ω)) ∂ϖ) ≠ ⊤ := by
  have h := cin_superposition (choquetSDProfile le_rfl ϖ hfold hdom) ϖ
    (hasProfileTail_choquetSDProfile le_rfl ϖ hfold hdom) ω
  have hfin := (choquetSDProfile (le_rfl (a := (0 : ℝ))) ϖ hfold hdom).exponentL_ne_top ω
  rw [h, cinSuperpositionL] at hfin
  simp only [show (choquetSDProfile (le_rfl (a := (0 : ℝ))) ϖ hfold hdom).a = 0 from rfl,
    zero_mul, ENNReal.ofReal_zero, zero_add] at hfin
  exact hfin

/-! ### The lower bounds on `Cin` that make the condition necessary -/

/-- `Cin(z) ≥ (19/96)z²` on `[0,1]`, from the expansion at the origin. -/
theorem cin_ge_sq {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) : 19 / 96 * z ^ 2 ≤ cin z := by
  have h := cin_expansion_zero_bound (z := z) (by rw [abs_of_nonneg hz0]; exact hz1)
  have habs := abs_le.mp h
  nlinarith [habs.1, sq_nonneg z, pow_le_pow_left₀ hz0 hz1 4, sq_nonneg (z ^ 2)]

/-- `Cin(z) ≥ 19/96` for `z ≥ 1`: monotonicity from the value at `1`. -/
theorem cin_ge_const {z : ℝ} (hz : 1 ≤ z) : 19 / 96 ≤ cin z := by
  have h1 : (19 : ℝ) / 96 * 1 ^ 2 ≤ cin 1 := cin_ge_sq zero_le_one le_rfl
  have := monotoneOn_cin (mem_Ici.mpr zero_le_one) (mem_Ici.mpr (le_trans zero_le_one hz)) hz
  linarith [h1, this]

/-- `Cin(z) ≥ log z - K` for `z ≥ 1`, with `K = 2 - C` the constant of the expansion. -/
theorem cin_ge_log {z : ℝ} (hz : 1 ≤ z) : Real.log z + cinConst - 2 ≤ cin z := by
  have h := abs_le.mp (cin_expansion_top_bound hz)
  have hz0 : (0 : ℝ) < z := lt_of_lt_of_le zero_lt_one hz
  have : z⁻¹ ≤ 1 := by rw [inv_le_one_iff₀]; right; exact hz
  linarith [h.1]

/-- Past a threshold, `Cin(z)` dominates `1 + log z`. -/
theorem exists_cin_ge_one_add_log :
    ∃ Z : ℝ, 1 ≤ Z ∧ ∀ z : ℝ, Z ≤ z → (1 + Real.log z) / 2 ≤ cin z := by
  refine ⟨max 1 (Real.exp (2 * (2 - cinConst) + 1)), le_max_left _ _, fun z hz => ?_⟩
  have hz1 : (1 : ℝ) ≤ z := le_trans (le_max_left _ _) hz
  have hzexp : Real.exp (2 * (2 - cinConst) + 1) ≤ z := le_trans (le_max_right _ _) hz
  have hlog : 2 * (2 - cinConst) + 1 ≤ Real.log z := by
    rw [← Real.log_exp (2 * (2 - cinConst) + 1)]
    exact Real.log_le_log (Real.exp_pos _) hzexp
  linarith [cin_ge_log hz1]

/-- **The domain condition is necessary**, in the pointwise form the integral consumes: at any
one frequency `b > 0` the domain integrand is dominated by a multiple of `Cin(τ b)`.

Three regimes, and they are the three the blueprint names: below `τ b = 1` the comparison is
`Cin(z) ≍ z²`; above a threshold it is `Cin(z) ≍ log z`; and the bounded middle stretch is
covered by monotonicity alone, `Cin(τb) ≥ Cin(1)`. The last is what removes the need for a
uniform two-sided comparison, which is where a first attempt at this lemma spends its effort. -/
theorem exists_domain_le_cin {b : ℝ} (hb : 0 < b) :
    ∃ M : ℝ, 0 < M ∧ ∀ τ : ℝ, 0 < τ → domainIntegrand τ ≤ M * cin (τ * b) := by
  obtain ⟨Z, hZ1, hZ⟩ := exists_cin_ge_one_add_log
  set S : ℝ := max 1 (max (Z / b) (Real.exp (-1 - 2 * Real.log b))) with hS
  have hS1 : (1 : ℝ) ≤ S := le_max_left _ _
  have hlogS : 0 ≤ Real.log S := Real.log_nonneg hS1
  set M₁ : ℝ := 96 / (19 * b ^ 2) with hM₁
  set M₂ : ℝ := (1 + Real.log S) * 96 / 19 with hM₂
  set M : ℝ := max M₁ (max M₂ 4) with hM
  have hM4 : (4 : ℝ) ≤ M := le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨M, by linarith, fun τ hτ => ?_⟩
  have hτb : 0 < τ * b := mul_pos hτ hb
  have hcinnn : 0 ≤ cin (τ * b) := cin_nonneg' _
  rcases le_or_gt (τ * b) 1 with hA | hA
  · -- the quadratic regime
    have hlow : 19 / 96 * (τ * b) ^ 2 ≤ cin (τ * b) := cin_ge_sq hτb.le hA
    have hMM : M₁ ≤ M := le_max_left _ _
    calc domainIntegrand τ ≤ τ ^ 2 := min_le_left _ _
      _ ≤ M₁ * cin (τ * b) := by
          rw [hM₁]
          rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
          nlinarith [hlow, sq_nonneg τ, hb.le]
      _ ≤ M * cin (τ * b) := mul_le_mul_of_nonneg_right hMM hcinnn
  · rcases lt_or_ge τ S with hB | hC
    · -- the bounded middle stretch
      have hlow : 19 / 96 ≤ cin (τ * b) := cin_ge_const hA.le
      have hmax : Real.log (max 1 τ) ≤ Real.log S := by
        refine Real.log_le_log (by positivity) ?_
        exact max_le hS1 hB.le
      have hMM : M₂ ≤ M := le_trans (le_max_left _ _) (le_max_right _ _)
      calc domainIntegrand τ ≤ 1 + Real.log (max 1 τ) := min_le_right _ _
        _ ≤ 1 + Real.log S := by linarith
        _ ≤ M₂ * cin (τ * b) := by
            rw [hM₂]
            nlinarith [hlow, hlogS]
        _ ≤ M * cin (τ * b) := mul_le_mul_of_nonneg_right hMM hcinnn
    · -- the logarithmic regime
      have hZle : Z / b ≤ τ := le_trans (le_trans (le_max_left _ _) (le_max_right 1 _)) hC
      have hZb : Z ≤ τ * b := by
        rw [div_le_iff₀ hb] at hZle; linarith
      have hexp : Real.exp (-1 - 2 * Real.log b) ≤ τ :=
        le_trans (le_trans (le_max_right _ _) (le_max_right 1 _)) hC
      have hlogτ : -1 - 2 * Real.log b ≤ Real.log τ := by
        rw [← Real.log_exp (-1 - 2 * Real.log b)]
        exact Real.log_le_log (Real.exp_pos _) hexp
      have hτ1 : (1 : ℝ) ≤ τ := le_trans hS1 hC
      have hlogmul : Real.log (τ * b) = Real.log τ + Real.log b := Real.log_mul hτ.ne' hb.ne'
      have hlow : (1 + Real.log (τ * b)) / 2 ≤ cin (τ * b) := hZ _ hZb
      have hmaxeq : max 1 τ = τ := max_eq_right hτ1
      calc domainIntegrand τ ≤ 1 + Real.log (max 1 τ) := min_le_right _ _
        _ = 1 + Real.log τ := by rw [hmaxeq]
        _ ≤ 4 * cin (τ * b) := by rw [hlogmul] at hlow; linarith
        _ ≤ M * cin (τ * b) := mul_le_mul_of_nonneg_right hM4 hcinnn

theorem cin_mul_abs (τ ω : ℝ) : cin (τ * ω) = cin (τ * |ω|) := by
  rcases le_or_gt 0 ω with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h, mul_neg, cin_neg]

/-- **The domain, at one frequency.** For `ω ≠ 0`, finiteness of the superposition integral is
exactly `prop:choquet-cone`'s domain condition. -/
theorem lintegral_cin_ne_top_iff (ϖ : Measure ℝ) (hfold : IsFolded ϖ) {ω : ℝ} (hω : ω ≠ 0) :
    (∫⁻ τ, ENNReal.ofReal (cin (τ * ω)) ∂ϖ) ≠ ⊤ ↔
      (∫⁻ τ, ENNReal.ofReal (domainIntegrand τ) ∂ϖ) ≠ ⊤ := by
  refine ⟨fun hfin => ?_, fun hdom => lintegral_cin_ne_top_of_domain ϖ hfold hdom ω⟩
  have hb : 0 < |ω| := abs_pos.mpr hω
  obtain ⟨M, hMpos, hMle⟩ := exists_domain_le_cin hb
  have hpos : ∀ᵐ τ ∂ϖ, 0 < τ := by
    rw [ae_iff]
    refine measure_mono_null (fun t ht => ?_) hfold
    simp only [not_lt, mem_setOf_eq] at ht
    exact mem_Iic.mpr ht
  have hle : (∫⁻ τ, ENNReal.ofReal (domainIntegrand τ) ∂ϖ)
      ≤ ENNReal.ofReal M * ∫⁻ τ, ENNReal.ofReal (cin (τ * ω)) ∂ϖ := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono_ae ?_
    filter_upwards [hpos] with τ hτ
    rw [← ENNReal.ofReal_mul hMpos.le, cin_mul_abs]
    exact ENNReal.ofReal_le_ofReal (hMle τ hτ)
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) hle

/-- **`prop:choquet-cone`, the domain.** -/
theorem choquet_cone_domain (ϖ : Measure ℝ) (hfold : IsFolded ϖ) :
    ((∃ ω : ℝ, ω ≠ 0 ∧ ∫⁻ τ, ENNReal.ofReal (cin (τ * ω)) ∂ϖ ≠ ⊤) ↔
        ∀ ω : ℝ, ∫⁻ τ, ENNReal.ofReal (cin (τ * ω)) ∂ϖ ≠ ⊤) ∧
      ((∀ ω : ℝ, ∫⁻ τ, ENNReal.ofReal (cin (τ * ω)) ∂ϖ ≠ ⊤) ↔
        ∫⁻ τ, ENNReal.ofReal (min (τ ^ 2) (1 + Real.log (max 1 τ))) ∂ϖ ≠ ⊤) := by
  have hsecond : (∀ ω : ℝ, ∫⁻ τ, ENNReal.ofReal (cin (τ * ω)) ∂ϖ ≠ ⊤) ↔
      (∫⁻ τ, ENNReal.ofReal (domainIntegrand τ) ∂ϖ) ≠ ⊤ := by
    refine ⟨fun h => (lintegral_cin_ne_top_iff ϖ hfold one_ne_zero).mp (h 1), fun hdom ω => ?_⟩
    exact lintegral_cin_ne_top_of_domain ϖ hfold hdom ω
  refine ⟨⟨fun ⟨ω₀, hω₀, hfin⟩ => ?_, fun h => ⟨1, one_ne_zero, h 1⟩⟩, hsecond⟩
  exact hsecond.mpr ((lintegral_cin_ne_top_iff ϖ hfold hω₀).mp hfin)

/-! ## Linearity -/

/-- **`prop:choquet-cone`, linearity of the map.** -/
theorem choquet_cone_linear (a₁ a₂ c : ℝ) (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (hc : 0 ≤ c)
    (ϖ₁ ϖ₂ : Measure ℝ) (ω : ℝ) :
    cinSuperpositionL (a₁ + a₂) (ϖ₁ + ϖ₂) ω
        = cinSuperpositionL a₁ ϖ₁ ω + cinSuperpositionL a₂ ϖ₂ ω ∧
      cinSuperpositionL (c * a₁) (ENNReal.ofReal c • ϖ₁) ω
        = ENNReal.ofReal c * cinSuperpositionL a₁ ϖ₁ ω := by
  constructor
  · rw [cinSuperpositionL, cinSuperpositionL, cinSuperpositionL, lintegral_add_measure,
      show (a₁ + a₂) * ω ^ 2 = a₁ * ω ^ 2 + a₂ * ω ^ 2 from by ring,
      ENNReal.ofReal_add (by positivity) (by positivity)]
    ring
  · rw [cinSuperpositionL, cinSuperpositionL, lintegral_smul_measure, mul_add,
      ← ENNReal.ofReal_mul hc, mul_assoc, smul_eq_mul]

end SpatialLine
