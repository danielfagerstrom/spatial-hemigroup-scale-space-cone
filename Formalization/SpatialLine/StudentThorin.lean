/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.ThorinBridgeOnto
import SpatialLine.StudentTransform

/-!
# The Student-t corner at the level of Thorin measures

Blueprint: `lem:student-subordinated` (chapter 9) and `prop:student-t`(3) (chapter 10), both
restated on 2026-09-15 (module B step 2, ledger row R160) with the *Thorin representation of the
inverse-gamma delay law* as a hypothesis rather than with the named-class result (ledger **A18**,
Halgreen 1979) as an admitted interface.

## What the hypothesis is, and why it is at the source's letter

Halgreen's definition of a generalized gamma convolution (1979, p. 13, formulas (2) and (3)) is
a statement about the Laplace transform: `F` is a GGC if

`∫ e^{-su} F(du) = exp{-as - ∫ log(1 + s/y) U(dy)}`

for some `a ≥ 0` and some measure `U` on `(0,∞)` with `∫₀¹ |log y| U(dy) < ∞` and
`∫₁^∞ y^{-1} U(dy) < ∞`. That is exactly the hypothesis of the two theorems below, with `U`
folded (`IsFolded`) and the two integrability conditions in the equivalent compact form
`causalThorinExponentL U 1 ≠ ⊤` — Halgreen's own §2 (5) at `λ = -a < 0`, `χ = 1`, `ψ = 0`
delivers both, the `U` it exhibits having density `g_a(2y)` on `(0,∞)`.

What is *not* assumed here, and is machine-checked instead, is everything between that
representation and the article's statements: the passage from a Thorin measure to a causally
admissible datum in the sense of `def:causal-admissible` (`causalThorinDatum`, the causal
Frullani identity of `causal_thorin_frullani` together with the two integrability windows), the
identification of the bridge image with the Student-t law (`bridge_families_bessel`), and the
spatial Thorin representation of that image (`thorin_bridge`).

So no interface name is admitted for the Student-t corner: ledger **A18** grounds a hypothesis
that the article's own remark cites, and grounds nothing inside a Lean proof.

## What writing the statements found

**The interface as it stood could not have discharged the clause it was recorded against.**
`Skeleton.student_causal` asserted only that the inverse-gamma law is the delay law of *some*
causally admissible exponent — self-decomposability — while `Skeleton.student_thorin` concludes
that the spatial profile is *completely monotone*, which is membership in the Thorin subclass and
needs the causal profile to be a Laplace transform. Admitting A18 in that form would have left
`prop:student-t`(3) unprovable: the GGC content of Halgreen's theorem, which is what the clause
consumes, was dropped by the shape of the Lean statement. The hypothesis below carries it.

**The subordination clause needs no Thorin measure at all**, only a causally admissible datum
with the right Laplace transform; it is stated that way (`student_subordinated`), and the Thorin
hypothesis enters only at `student_thorin`.
-/

namespace SpatialLine

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-! ## The causal Thorin exponent -/

/-- **Halgreen's (2), the integral term**: the causal Thorin exponent
`∫_{(0,∞)} log(1 + σ/θ) U(dθ)`, `ℝ≥0∞`-valued.

`ℝ≥0∞` first, as everywhere in this development: the integrand is nonnegative for `σ ≥ 0` and
`θ > 0`, so the integral needs no side condition. -/
noncomputable def causalThorinExponentL (U : Measure ℝ) (σ : ℝ) : ℝ≥0∞ :=
  ∫⁻ θ, ENNReal.ofReal (Real.log (1 + σ / θ)) ∂U

/-- The real-valued causal Thorin exponent. -/
noncomputable def causalThorinExponent (U : Measure ℝ) (σ : ℝ) : ℝ :=
  (causalThorinExponentL U σ).toReal

/-- `log(1 + σ/θ) ≤ max 1 σ * log(1 + 1/θ)` for `θ > 0` and `σ ≥ 0`: the Thorin integrand at a
general `σ` against the same integrand at `σ = 1`.

For `σ ≤ 1` it is monotonicity of the logarithm; for `σ ≥ 1` it is Bernoulli's inequality
`1 + σ/θ ≤ (1 + 1/θ)^σ`. -/
theorem log_one_add_div_le {θ σ : ℝ} (hθ : 0 < θ) (hσ : 0 ≤ σ) :
    Real.log (1 + σ / θ) ≤ max 1 σ * Real.log (1 + 1 / θ) := by
  have hinvpos : (0 : ℝ) < 1 / θ := by positivity
  have hbase : (0 : ℝ) < 1 + 1 / θ := by linarith
  have hlog : 0 ≤ Real.log (1 + 1 / θ) := Real.log_nonneg (by linarith)
  rcases le_total σ 1 with h | h
  · have hmax : max 1 σ = 1 := max_eq_left h
    rw [hmax, one_mul]
    refine Real.log_le_log (by positivity) ?_
    have hdiv : σ / θ ≤ 1 / θ := by gcongr
    linarith
  · have hmax : max 1 σ = σ := max_eq_right h
    rw [hmax]
    have hb := one_add_mul_self_le_rpow_one_add (s := 1 / θ) (by linarith) h
    have hmul : σ * (1 / θ) = σ / θ := by ring
    rw [hmul] at hb
    calc Real.log (1 + σ / θ) ≤ Real.log ((1 + 1 / θ) ^ σ) :=
          Real.log_le_log (by positivity) hb
      _ = σ * Real.log (1 + 1 / θ) := Real.log_rpow hbase σ

/-- **The Thorin integral is finite at every `σ ≥ 0` once it is finite at `σ = 1`.** -/
theorem causalThorinExponentL_ne_top {U : Measure ℝ} (hU : IsFolded U)
    (hfin : causalThorinExponentL U 1 ≠ ⊤) {σ : ℝ} (hσ : 0 ≤ σ) :
    causalThorinExponentL U σ ≠ ⊤ := by
  refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (a := ENNReal.ofReal (max 1 σ))
    ENNReal.ofReal_ne_top hfin) ?_
  rw [causalThorinExponentL, causalThorinExponentL, ← lintegral_const_mul' _ _
    ENNReal.ofReal_ne_top]
  refine lintegral_mono_ae ?_
  filter_upwards [ae_pos_of_isFolded hU] with θ hθ
  rw [← ENNReal.ofReal_mul (le_trans zero_le_one (le_max_left 1 σ))]
  refine ENNReal.ofReal_le_ofReal ?_
  simpa [one_div] using log_one_add_div_le hθ hσ

/-- `e^{-θu} ≤ ((log 2)⁻¹ + 2/u) * log(1 + 1/θ)` for `θ, u > 0`.

The Laplace weight is dominated by the Thorin weight at `σ = 1`: near `θ = 0` because the
exponential is bounded by `1` and the logarithm by `log 2` from below, and at `θ = ∞` because
`e^{-θu} ≤ (θu)^{-1}` while `log(1 + 1/θ) ≥ (θ + 1)^{-1}`. -/
theorem exp_neg_mul_le_log_one_add_inv {θ u : ℝ} (hθ : 0 < θ) (hu : 0 < u) :
    Real.exp (-(θ * u)) ≤ ((Real.log 2)⁻¹ + 2 / u) * Real.log (1 + 1 / θ) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hinvpos : (0 : ℝ) < 1 / θ := by positivity
  have hlogpos : 0 ≤ Real.log (1 + 1 / θ) := Real.log_nonneg (by linarith)
  have h2u : (0 : ℝ) ≤ 2 / u := by positivity
  have hinv2 : (0 : ℝ) ≤ (Real.log 2)⁻¹ := inv_nonneg.mpr hlog2.le
  rcases le_total θ 1 with h | h
  · have h2 : Real.log 2 ≤ Real.log (1 + 1 / θ) := by
      refine Real.log_le_log (by norm_num) ?_
      have hge : (1 : ℝ) ≤ 1 / θ := by
        rw [le_div_iff₀ hθ]; linarith
      linarith
    have hexp : Real.exp (-(θ * u)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have hstep : (1 : ℝ) ≤ (Real.log 2)⁻¹ * Real.log (1 + 1 / θ) := by
      have hmul := mul_le_mul_of_nonneg_left h2 hinv2
      rwa [inv_mul_cancel₀ hlog2.ne'] at hmul
    calc Real.exp (-(θ * u)) ≤ 1 := hexp
      _ ≤ (Real.log 2)⁻¹ * Real.log (1 + 1 / θ) := hstep
      _ ≤ ((Real.log 2)⁻¹ + 2 / u) * Real.log (1 + 1 / θ) := by nlinarith
  · have hθ1 : (θ : ℝ) + 1 ≠ 0 := by positivity
    have hb : 1 / (θ + 1) ≤ Real.log (1 + 1 / θ) := by
      have hx : (0 : ℝ) < 1 + 1 / θ := by linarith
      have h1 := one_sub_inv_le_log hx
      have hinv : (1 + 1 / θ)⁻¹ = θ / (θ + 1) := by field_simp
      rw [hinv] at h1
      have h2 : (1 : ℝ) - θ / (θ + 1) = 1 / (θ + 1) := by
        field_simp
        ring
      rwa [h2] at h1
    have he : Real.exp (-(θ * u)) ≤ 1 / (θ * u) := by
      have hx : (0 : ℝ) < θ * u := by positivity
      have hle : θ * u ≤ Real.exp (θ * u) := by
        linarith [Real.add_one_le_exp (θ * u)]
      have hrw : Real.exp (-(θ * u)) = 1 / Real.exp (θ * u) := by
        rw [Real.exp_neg, one_div]
      rw [hrw]
      exact one_div_le_one_div_of_le hx hle
    have hchain : 1 / (θ * u) ≤ 2 / u * (1 / (θ + 1)) := by
      rw [div_mul_div_comm, mul_one, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    calc Real.exp (-(θ * u)) ≤ 1 / (θ * u) := he
      _ ≤ 2 / u * (1 / (θ + 1)) := hchain
      _ ≤ 2 / u * Real.log (1 + 1 / θ) := mul_le_mul_of_nonneg_left hb h2u
      _ ≤ ((Real.log 2)⁻¹ + 2 / u) * Real.log (1 + 1 / θ) := by nlinarith

/-- **The Laplace transform of a causal Thorin measure is finite on `(0,∞)`.** -/
theorem laplaceL_ne_top_of_causalThorin {U : Measure ℝ} (hU : IsFolded U)
    (hfin : causalThorinExponentL U 1 ≠ ⊤) {u : ℝ} (hu : 0 < u) : laplaceL U u ≠ ⊤ := by
  refine ne_top_of_le_ne_top (ENNReal.mul_ne_top
    (a := ENNReal.ofReal ((Real.log 2)⁻¹ + 2 / u)) ENNReal.ofReal_ne_top hfin) ?_
  rw [laplaceL, causalThorinExponentL, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono_ae ?_
  filter_upwards [ae_pos_of_isFolded hU] with θ hθ
  have hc : (0 : ℝ) ≤ (Real.log 2)⁻¹ + 2 / u := by
    have : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  rw [← ENNReal.ofReal_mul hc]
  refine ENNReal.ofReal_le_ofReal ?_
  simpa [one_div, mul_comm] using exp_neg_mul_le_log_one_add_inv hθ hu

/-! ## The causal Thorin datum -/

/-- The delay profile attached to a causal Thorin measure: `k_I(u) = ∫ e^{-θu} U(dθ)` on
`(0,∞)`, and `0` elsewhere. -/
noncomputable def causalThorinProfile (U : Measure ℝ) : ℝ → ℝ :=
  Set.indicator (Ioi (0 : ℝ)) fun u => (laplaceL U u).toReal

theorem causalThorinProfile_ofReal {U : Measure ℝ} (hU : IsFolded U)
    (hfin : causalThorinExponentL U 1 ≠ ⊤) {u : ℝ} (hu : 0 < u) :
    ENNReal.ofReal (causalThorinProfile U u) = laplaceL U u := by
  rw [causalThorinProfile, Set.indicator_of_mem (show u ∈ Ioi (0 : ℝ) from hu)]
  exact ENNReal.ofReal_toReal (laplaceL_ne_top_of_causalThorin hU hfin hu)

/-- The same identity in the argument order `thorin_bridge` and `causal_thorin_frullani` use. -/
theorem causalThorinProfile_ofReal' {U : Measure ℝ} (hU : IsFolded U)
    (hfin : causalThorinExponentL U 1 ≠ ⊤) {u : ℝ} (hu : 0 < u) :
    ENNReal.ofReal (causalThorinProfile U u)
      = ∫⁻ θ, ENNReal.ofReal (Real.exp (-(θ * u))) ∂U := by
  rw [causalThorinProfile_ofReal hU hfin hu, laplaceL]
  exact lintegral_congr fun θ => by rw [mul_comm]

theorem causalThorinProfile_nonneg {U : Measure ℝ} (u : ℝ) : 0 ≤ causalThorinProfile U u := by
  rw [causalThorinProfile]
  exact Set.indicator_nonneg (fun _ _ => ENNReal.toReal_nonneg) u

theorem causalThorinProfile_zero {U : Measure ℝ} : causalThorinProfile U 0 = 0 := by
  rw [causalThorinProfile]
  exact Set.indicator_of_notMem (lt_irrefl 0) _

theorem causalThorinProfile_antitone {U : Measure ℝ} (hU : IsFolded U)
    (hfin : causalThorinExponentL U 1 ≠ ⊤) : AntitoneOn (causalThorinProfile U) (Ioi (0 : ℝ)) := by
  intro u hu v hv huv
  have hu0 : (0 : ℝ) < u := hu
  have hv0 : (0 : ℝ) < v := hv
  rw [causalThorinProfile, Set.indicator_of_mem hu, Set.indicator_of_mem hv]
  refine ENNReal.toReal_mono (laplaceL_ne_top_of_causalThorin hU hfin hu0) ?_
  rw [laplaceL, laplaceL]
  refine lintegral_mono_ae ?_
  filter_upwards [ae_pos_of_isFolded hU] with θ hθ
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by nlinarith))

/-- σ-finiteness of a causal Thorin measure, read off its Laplace transform at `u = 1`. -/
theorem sigmaFinite_of_causalThorin {U : Measure ℝ} (hU : IsFolded U)
    (hfin : causalThorinExponentL U 1 ≠ ⊤) : SigmaFinite U :=
  sigmaFinite_of_laplaceL_ne_top (y := 1) (laplaceL_ne_top_of_causalThorin hU hfin one_pos)

/-- **The causal exponent of a Thorin datum is the Thorin integral**, which is the causal
Frullani identity with the transform substituted for the profile. -/
theorem lintegral_causalThorinProfile {U : Measure ℝ} (hU : IsFolded U)
    (hfin : causalThorinExponentL U 1 ≠ ⊤) {σ : ℝ} (hσ : 0 ≤ σ) :
    (∫⁻ u in Ioi (0 : ℝ),
        ENNReal.ofReal ((1 - Real.exp (-(σ * u))) * causalThorinProfile U u / u))
      = causalThorinExponentL U σ := by
  haveI : SigmaFinite U := sigmaFinite_of_causalThorin hU hfin
  haveI : SFinite U := inferInstance
  rw [causalThorinExponentL, ← causal_thorin_frullani hU hσ]
  refine setLIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
  have hu0 : (0 : ℝ) < u := hu
  have hnn : 0 ≤ (1 - Real.exp (-(σ * u))) / u :=
    div_nonneg (ScaleSpace.CausalAdmissible.one_sub_exp_bounds hσ hu0.le).1 hu0.le
  rw [← causalThorinProfile_ofReal' hU hfin hu0, ← ENNReal.ofReal_mul hnn]
  congr 1
  ring

/-- The two integrability windows of `def:causal-admissible`, bounded by the Thorin integral at
`σ = 1`. -/
theorem lintegral_min_causalThorinProfile {U : Measure ℝ} (hU : IsFolded U)
    (hfin : causalThorinExponentL U 1 ≠ ⊤) :
    (∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (min 1 u * causalThorinProfile U u / u)) ≠ ⊤ := by
  have hbound : (∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (min 1 u * causalThorinProfile U u / u))
      ≤ ENNReal.ofReal (Real.exp 1)
        * ∫⁻ u in Ioi (0 : ℝ),
            ENNReal.ofReal ((1 - Real.exp (-(1 * u))) * causalThorinProfile U u / u) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' measurableSet_Ioi fun u hu => ?_
    have hu0 : (0 : ℝ) < u := hu
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    refine ENNReal.ofReal_le_ofReal ?_
    have hk := causalThorinProfile_nonneg (U := U) u
    have hm := min_one_le_exp_one_mul hu0.le
    rw [div_le_iff₀ hu0, mul_assoc, div_mul_cancel₀ _ hu0.ne', ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hm hk
  refine ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_) hbound
  rw [lintegral_causalThorinProfile hU hfin zero_le_one]
  exact hfin

/-- **The causal Thorin datum**: a folded measure `U` on `(0,∞)` whose Thorin integral is finite
at `σ = 1` — Halgreen's conditions (3) — is the Thorin measure of a causally admissible exponent
with drift `b₀`, whose delay profile is the Laplace transform of `U`. -/
noncomputable def causalThorinDatum (b₀ : ℝ) (U : Measure ℝ) (hb : 0 ≤ b₀) (hU : IsFolded U)
    (hfin : causalThorinExponentL U 1 ≠ ⊤) : CausalAdmissible where
  b₀ := b₀
  k := causalThorinProfile U
  b₀_nonneg := hb
  k_nonneg := fun u _ => causalThorinProfile_nonneg u
  k_antitone := causalThorinProfile_antitone hU hfin
  k_zero := causalThorinProfile_zero
  integrable_near_zero := by
    have h := lintegral_min_causalThorinProfile hU hfin
    rw [ScaleSpace.CausalAdmissible.lintegral_min_split] at h
    exact (ENNReal.add_ne_top.mp h).1
  integrable_at_top := by
    have h := lintegral_min_causalThorinProfile hU hfin
    rw [ScaleSpace.CausalAdmissible.lintegral_min_split] at h
    exact (ENNReal.add_ne_top.mp h).2

@[simp] theorem causalThorinDatum_k {b₀ : ℝ} {U : Measure ℝ} (hb : 0 ≤ b₀) (hU : IsFolded U)
    (hfin : causalThorinExponentL U 1 ≠ ⊤) :
    (causalThorinDatum b₀ U hb hU hfin).k = causalThorinProfile U := rfl

/-- **Halgreen's (2) is the causal exponent of the datum**: `F_I(σ) = b₀σ + ∫log(1 + σ/θ)U(dθ)`
for `σ ≥ 0`. -/
theorem causalThorinDatum_exponent {b₀ : ℝ} {U : Measure ℝ} (hb : 0 ≤ b₀) (hU : IsFolded U)
    (hfin : causalThorinExponentL U 1 ≠ ⊤) {σ : ℝ} (hσ : 0 ≤ σ) :
    (causalThorinDatum b₀ U hb hU hfin).exponent σ = b₀ * σ + causalThorinExponent U σ := by
  have hL : (causalThorinDatum b₀ U hb hU hfin).exponentL σ
      = ENNReal.ofReal (b₀ * σ) + causalThorinExponentL U σ := by
    rw [ScaleSpace.CausalAdmissible.exponentL]
    exact congrArg _ (lintegral_causalThorinProfile hU hfin hσ)
  rw [ScaleSpace.CausalAdmissible.exponent, hL, causalThorinExponent,
    ENNReal.toReal_add ENNReal.ofReal_ne_top (causalThorinExponentL_ne_top hU hfin hσ),
    ENNReal.toReal_ofReal (by positivity)]

/-! ## `lem:student-subordinated`

The membership needs no Thorin measure: a causally admissible datum whose delay law is the
inverse-gamma law is enough, and the passage from it to membership in `S` is the conditioning
identity `bridge_families_bessel` with the mixture transform of `lem:bridge-exponents`.
-/

/-- **`lem:student-subordinated`** (restated 2026-09-15, module B step 2, R160) — if the
inverse-gamma law of shape `a > 0` is the delay law of a causally admissible exponent `F`, then
every exponent whose exponential is the cosine transform of the Student-t law of shape `a` is
subordinated, with `F` as its causal ancestor.

The exponent is quantified over through its transform, as in the withdrawn
`Skeleton.student_subordinated`: there is no closed-form Student-t exponent in this development
and `-log` of `prop:student-t`(2)'s closed form is junk at `ω = 0`. That loses nothing, `exp`
being injective.

**Lean core.** The hypothesis is what ledger **A18** grounds, and it is cited at
`rem:student-ggc` rather than admitted. -/
theorem student_subordinated {a : ℝ} (ha : 0 < a) (F : CausalAdmissible)
    (hF : ∀ σ : ℝ, 0 ≤ σ →
      ∫ u, Real.exp (-(σ * u)) ∂(inverseGammaLaw a) = Real.exp (-F.exponent σ))
    (G : ℝ → ℝ) (hG : ∀ ω : ℝ, Real.exp (-G ω) = fourierCos (studentLaw a 1) ω) :
    IsSubordinated G := by
  haveI := isProbabilityMeasure_inverseGammaLaw ha
  refine ⟨F, fun ω => ?_⟩
  have h1 : Real.exp (-G ω) = Real.exp (-F.exponent (ω ^ 2 / 2)) := by
    rw [hG ω, ← bridge_families_bessel a ha,
      fourierCos_bind_brownianLaw (inverseGammaLaw_Iio_zero a) ω, hF _ (by positivity)]
  exact neg_injective (Real.exp_eq_exp.mp h1)

/-! ## `prop:student-t`(3)

The Thorin measure enters here and nowhere else: complete monotonicity of the *spatial* profile
is a statement about every derivative at every point, and what delivers it is `thorin_bridge`,
whose hypothesis is that the causal profile is the Laplace transform of `U_I`.
-/

/-- **`prop:student-t`(3)** (restated 2026-09-15, module B step 2, R160) — if the inverse-gamma
law of shape `a > 0` is a generalized gamma convolution at Halgreen's letter — a folded `U` with
`∫ log(1 + 1/θ) U(dθ) < ∞` and `E e^{-σT₁} = exp{-∫ log(1 + σ/θ) U(dθ)}` for `σ ≥ 0` — then the
Student-t law of shape `a` is the law of a symmetric self-decomposable family whose profile is
completely monotone, which is membership in the symmetric Thorin subclass, and whose Thorin
measure is **twice** the image of `U` under `θ ↦ √(2θ)`.

The last two conjuncts say more than the printed clause (3), which asserts self-decomposability
and membership only; the Thorin measure and the vanishing Gaussian coefficient are recorded here
because the checked route produces them.

**Spends ledger A3 and A11** through `thorin_bridge`, both already on the trust boundary, and no
name of its own; ledger **A18** is the hypothesis and is not admitted. -/
theorem student_thorin {a : ℝ} (ha : 0 < a) (U : Measure ℝ) (hU : IsFolded U)
    (hfin : causalThorinExponentL U 1 ≠ ⊤)
    (hrep : ∀ σ : ℝ, 0 ≤ σ →
      ∫ u, Real.exp (-(σ * u)) ∂(inverseGammaLaw a) = Real.exp (-causalThorinExponent U σ)) :
    ∃ Q : SDProfile, Q.a = 0 ∧ IsCompletelyMonotone Q.k ∧
      (∀ ω : ℝ, fourierCos (studentLaw a 1) ω = Real.exp (-Q.exponent ω)) ∧
      (∀ ω : ℝ, Q.exponentL ω
        = thorinExponentL Q.a (ENNReal.ofReal 2 • U.map fun θ => Real.sqrt (2 * θ)) ω) := by
  haveI := isProbabilityMeasure_inverseGammaLaw ha
  set F : CausalAdmissible := causalThorinDatum 0 U le_rfl hU hfin with hFdef
  have hFexp : ∀ σ : ℝ, 0 ≤ σ → F.exponent σ = causalThorinExponent U σ := by
    intro σ hσ
    rw [hFdef, causalThorinDatum_exponent le_rfl hU hfin hσ, zero_mul, zero_add]
  have hFb : F.b₀ = 0 := rfl
  have hk : ∀ u : ℝ, 0 < u →
      ENNReal.ofReal (F.k u) = ∫⁻ θ, ENNReal.ofReal (Real.exp (-(θ * u))) ∂U := by
    intro u hu
    rw [hFdef, causalThorinDatum_k, causalThorinProfile_ofReal' hU hfin hu]
  obtain ⟨Q, hQa, -, hQexp⟩ := bridge_exponents F
  obtain ⟨-, hQcm, hQthorin⟩ := thorin_bridge F U hU hk Q hQexp
  have hQa0 : Q.a = 0 := by rw [hQa, hFb, zero_div]
  refine ⟨Q, hQa0, hQcm, fun ω => ?_, hQthorin⟩
  rw [hQexp ω, hFexp _ (by positivity), ← hrep _ (by positivity),
    ← bridge_families_bessel a ha, fourierCos_bind_brownianLaw (inverseGammaLaw_Iio_zero a) ω]

end SpatialLine
