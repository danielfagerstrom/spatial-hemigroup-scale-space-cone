/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.BridgeExponents
import SpatialLine.MainConstruction

/-!
# `prop:bridge-families`: the bridge on families

Blueprint: `blueprint/src/parts/09-bridge.tex` — `prop:bridge-families`, the family clause. The
corners are `SpatialLine/BridgeCorners.lean`.

## The causal family enters by its specification, not by Paper I's axioms

The node begins "let `(Φ^I)` be a time-causal family satisfying the causal axioms". Those axioms
are Paper I's, and this repository does not import them. What the proof uses is not the axioms
but their *conclusion*: that the causal kernels are probability laws on `[0,∞)` with Laplace
transform `exp[-(F_I(yσ) - F_I(xσ))]`. The statement quantifies over that, and nothing is lost,
the causal characterization being an equivalence. This is the skeleton's finding 1, and it is
the general principle that a specification is a hypothesis and a hypothesis can be quantified
over: what cannot be quantified over is a *construction*, and no construction is needed here.

## The route, and what it costs

The spatial exponent `Ψ = F_I(·²/2)` is admissible by `lem:bridge-exponents`
(`CausalAdmissible.bridgeDatum`), so `thm:main-characterization`'s construction direction builds
a family with the right transforms. The work left is three identifications:

* **the gauge action.** `main_construction` produces its scaling action as the gauge conjugate
  `χ⁻¹(λχ(t))`, which is `λt` only on `[0,∞)`; the node asserts `S_λ t = λt` as a *function*.
  So the family is assembled from `ConstructionData` directly, with `S` given as `λt` and the
  four covariance obligations discharged at that `S` — which is legitimate because every field
  of `IsScaleCovariant` reads `S λ` on `[0,∞)` only. `bridgeConstruction_gaugeAction` is the
  identification, and with the identity gauge it is one line.
* **the kernels.** The constructed kernels and the mixtures `μ^I_{s²,t²} ∘ g` are two families
  of symmetric probability measures with the same cosine transform, so they are equal by
  `prop:fourier-uniqueness`. That is what turns `IsKernelFamily` for the former into
  `IsKernelFamily` for the latter.
* **the transform.** `fourierCos_bind_brownianLaw` at `σ = ω²/2`, which is the conditioning
  computation of `lem:bridge-exponents`'s probabilistic reading, read at a pair of scales.

`Ψ ≢ 0` comes from `F_I ≢ 0` through `CausalAdmissible.exponent_of_nonpos`: a causal exponent
vanishes on `(-∞,0]`, so a frequency where `F_I` is nonzero is a positive one, and `√(2σ)` is
the spatial frequency above it.
-/

namespace SpatialLine

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal

end SpatialLine

namespace ScaleSpace.CausalAdmissible

open SpatialLine
open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal

/-- **A causal exponent vanishes off the nonnegative half-line.** Both terms of
`def:causal-admissible` are nonpositive there, so both read as `0` in `ℝ≥0∞`. -/
theorem exponent_of_nonpos (F : CausalAdmissible) {σ : ℝ} (hσ : σ ≤ 0) : F.exponent σ = 0 := by
  have hzero : F.exponentL σ = 0 := by
    rw [exponentL]
    have h1 : ENNReal.ofReal (F.b₀ * σ) = 0 :=
      ENNReal.ofReal_eq_zero.mpr (mul_nonpos_of_nonneg_of_nonpos F.b₀_nonneg hσ)
    have h2 : (∫⁻ u in Ioi (0 : ℝ),
        ENNReal.ofReal ((1 - Real.exp (-(σ * u))) * F.k u / u)) = 0 := by
      refine (lintegral_eq_zero_iff' ?_).mpr ?_
      · exact ((((measurable_const.sub (measurable_expIntegrand σ)).aemeasurable).mul
          F.aemeasurable_k).div aemeasurable_id).ennreal_ofReal
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        have hu0 : (0 : ℝ) < u := hu
        have hk : 0 ≤ F.k u := F.k_nonneg u hu0
        have hexp : (1 : ℝ) ≤ Real.exp (-(σ * u)) := Real.one_le_exp_iff.mpr (by nlinarith)
        have hle : (1 - Real.exp (-(σ * u))) * F.k u / u ≤ 0 := by
          apply div_nonpos_of_nonpos_of_nonneg _ hu0.le
          nlinarith
        simpa using ENNReal.ofReal_eq_zero.mpr hle
    rw [h1, h2, add_zero]
  rw [exponent, hzero]
  simp

end ScaleSpace.CausalAdmissible

namespace SpatialLine

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal

/-! ## The construction data of the subordinated family -/

/-- The subordinated profile in the **identity gauge**, which is the node's canonical gauge:
`prop:bridge-families`(5) says the spatial scale `t` is the square root of the causal scale, and
that is what makes `χ = id` here. -/
noncomputable def bridgeConstruction (F : CausalAdmissible) : ConstructionData where
  P := F.bridgeDatum
  χ := id
  chi_zero := rfl
  chi_mono := strictMono_id.strictMonoOn _
  chi_surj := fun y hy => ⟨y, hy, rfl⟩

theorem bridgeConstruction_expo (F : CausalAdmissible) (s t ω : ℝ) :
    (bridgeConstruction F).expo s t ω
      = F.exponent (t ^ 2 * ω ^ 2 / 2) - F.exponent (s ^ 2 * ω ^ 2 / 2) := by
  show (F.bridgeDatum).exponent (id t * ω) - (F.bridgeDatum).exponent (id s * ω) = _
  rw [ScaleSpace.CausalAdmissible.bridgeDatum_exponent,
    ScaleSpace.CausalAdmissible.bridgeDatum_exponent]
  congr 2 <;> · simp only [id_eq]; ring

/-- In the identity gauge the gauge action is the dilation itself, on `[0,∞)`. -/
theorem bridgeConstruction_gaugeAction (F : CausalAdmissible) {lam t : ℝ} (hlam : 0 < lam)
    (ht : 0 ≤ t) : (bridgeConstruction F).gaugeAction lam t = lam * t := by
  have h := (bridgeConstruction F).chi_gaugeAction hlam ht
  simpa [bridgeConstruction] using h

/-- **(ND) for the subordinated exponent.** A causal exponent that is nonzero somewhere is
nonzero at a positive frequency, and `√(2σ)` is the spatial frequency above it. -/
theorem bridgeDatum_ne_zero (F : CausalAdmissible) (hne : ∃ σ : ℝ, F.exponent σ ≠ 0) :
    ∃ ω : ℝ, F.bridgeDatum.exponent ω ≠ 0 := by
  obtain ⟨σ, hσ⟩ := hne
  have hσpos : 0 < σ := by
    by_contra h
    exact hσ (F.exponent_of_nonpos (not_lt.mp h))
  refine ⟨Real.sqrt (2 * σ), ?_⟩
  rw [ScaleSpace.CausalAdmissible.bridgeDatum_exponent, Real.sq_sqrt (by linarith)]
  simpa using hσ

/-! ## The node -/

/-- **`prop:bridge-families`, the family.**

`Skeleton.bridge_families`'s statement verbatim. The subordinated kernels satisfy (A1)–(A8) and
(ND) with `S_λ t = λt`, `t` is the canonical gauge, and the exponent is `F_I(·²/2)`.

Clause (5) of the node — that the spatial canonical gauge is the square root of the causal one —
is this conclusion read at `s = 0`, and needs no separate declaration.

`hne` is the review's R6 addition and is spent exactly once, at (ND): without it `F_I = 0` and
`μ^I = δ₀` meet every hypothesis and the conclusion is false, every operator being the identity.

Priced **L**, inherited from `main_construction`; paid **M**, because the inheritance is real —
what is done here is three identifications (the gauge action, the kernels, the transform) and
none of them repeats any analysis. -/
theorem bridge_families (F : CausalAdmissible) (hne : ∃ σ : ℝ, F.exponent σ ≠ 0)
    (μI : ℝ → ℝ → Measure ℝ)
    (hprob : ∀ x y : ℝ, 0 ≤ x → x ≤ y → IsProbabilityMeasure (μI x y))
    (hcausal : ∀ x y : ℝ, 0 ≤ x → x ≤ y → μI x y (Iio 0) = 0)
    (hlap : ∀ x y : ℝ, 0 ≤ x → x ≤ y → ∀ σ : ℝ, 0 ≤ σ →
      ∫ u, Real.exp (-(σ * u)) ∂(μI x y)
        = Real.exp (-(F.exponent (y * σ) - F.exponent (x * σ)))) :
    ∃ Fam : CascadeFamily, Fam.S = (fun lam t => lam * t) ∧
      IsKernelFamily Fam.Φ (fun s t => (μI (s ^ 2) (t ^ 2)).bind brownianLaw) ∧
      ∀ s t ω : ℝ, 0 ≤ s → s ≤ t →
        fourierCos ((μI (s ^ 2) (t ^ 2)).bind brownianLaw) ω
          = Real.exp (-(F.exponent (t ^ 2 * ω ^ 2 / 2) - F.exponent (s ^ 2 * ω ^ 2 / 2))) := by
  have hsq : ∀ s t : ℝ, 0 ≤ s → s ≤ t → (0 : ℝ) ≤ s ^ 2 ∧ s ^ 2 ≤ t ^ 2 :=
    fun s t hs hst => ⟨sq_nonneg s, by nlinarith⟩
  have htrans : ∀ s t ω : ℝ, 0 ≤ s → s ≤ t →
      fourierCos ((μI (s ^ 2) (t ^ 2)).bind brownianLaw) ω
        = Real.exp (-(F.exponent (t ^ 2 * ω ^ 2 / 2) - F.exponent (s ^ 2 * ω ^ 2 / 2))) := by
    intro s t ω hs hst
    obtain ⟨hs2, hst2⟩ := hsq s t hs hst
    haveI := hprob _ _ hs2 hst2
    rw [fourierCos_bind_brownianLaw (hcausal _ _ hs2 hst2) ω,
      hlap _ _ hs2 hst2 (ω ^ 2 / 2) (by positivity),
      show t ^ 2 * (ω ^ 2 / 2) = t ^ 2 * ω ^ 2 / 2 from by ring,
      show s ^ 2 * (ω ^ 2 / 2) = s ^ 2 * ω ^ 2 / 2 from by ring]
  have hker : ∀ s t : ℝ, 0 ≤ s → s ≤ t →
      (bridgeConstruction F).kernel s t = (μI (s ^ 2) (t ^ 2)).bind brownianLaw := by
    intro s t hs hst
    obtain ⟨hs2, hst2⟩ := hsq s t hs hst
    haveI := hprob _ _ hs2 hst2
    haveI := isProbabilityMeasure_bind_brownianLaw (μI (s ^ 2) (t ^ 2))
    refine Measure.ext_of_charFun (funext fun ω => ?_)
    have h1 := (bridgeConstruction F).charFun_kernel hs hst ω
    have h2 : charFun ((μI (s ^ 2) (t ^ 2)).bind brownianLaw) ω
        = ((fourierCos ((μI (s ^ 2) (t ^ 2)).bind brownianLaw) ω : ℝ) : ℂ) :=
      charFun_eq_fourierCos_of_symmetric (isSymmetric_bind_brownianLaw _) ω
    rw [h1, h2, htrans s t ω hs hst, bridgeConstruction_expo]
  have hneP := bridgeDatum_ne_zero F hne
  have hnd : ∀ s t : ℝ, 0 ≤ s → s < t →
      (bridgeConstruction F).cascadeData.κ s t ≠ Measure.dirac 0 :=
    fun s t hs hst => (bridgeConstruction F).kernel_ne_dirac hneP hs hst
  refine ⟨{ toCascadeCore := (bridgeConstruction F).cascadeData.cascadeCore hnd
            S := fun lam t => lam * t
            covariant := (bridgeConstruction F).cascadeData.isScaleCovariant
              (fun lam t => lam * t)
              (fun lam hlam t ht => by simpa using mul_nonneg hlam.le ht)
              (fun lam hlam s _ t _ hst => by simpa using mul_lt_mul_of_pos_left hst hlam)
              (fun lam hlam t ht => ⟨lam⁻¹ * t, by
                simp only [mem_Ici] at ht ⊢
                exact mul_nonneg (inv_nonneg.mpr hlam.le) ht, by field_simp⟩)
              (fun lam hlam s t hs hst => by
                rw [show lam * s = (bridgeConstruction F).gaugeAction lam s from
                    (bridgeConstruction_gaugeAction F hlam hs).symm,
                  show lam * t = (bridgeConstruction F).gaugeAction lam t from
                    (bridgeConstruction_gaugeAction F hlam (hs.trans hst)).symm]
                exact (bridgeConstruction F).kernel_map_const_mul hlam hs hst) },
    rfl, ?_, htrans⟩
  have hkf := (bridgeConstruction F).cascadeData.isKernelFamily
  exact { isProbability := fun s t hs hst => by
            rw [← hker s t hs hst]; exact hkf.isProbability s t hs hst
          conv := fun s t hs hst f => by
            rw [← hker s t hs hst]; exact hkf.conv s t hs hst f }

end SpatialLine
