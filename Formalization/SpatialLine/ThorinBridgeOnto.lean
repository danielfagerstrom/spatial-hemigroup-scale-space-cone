/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.ThorinBridge

/-!
# The bridge on Thorin subclasses is onto, and the measure map is injective

Blueprint: `prop:thorin-subclass`(4), the sentence after the identity — "the map `U_I ↦ U` is a
linear bijection between the two domains of Thorin measures, so the subordination bridge restricts
to a linear bijection of the causal Thorin subclass onto the symmetric one". `thorin_bridge`
proves the forward map; this file proves the rest (row R120).

## What proving this found

**Surjectivity needs no uniqueness and no Bernstein.** Given a symmetric Thorin member `(a, U)`,
the causal datum is *built*: `U_I = ½·(image of U under θ ↦ θ²/2)`, `k_I` its Laplace transform,
`b₀ = 2a`. The exponent identity is then a direct computation — the causal Frullani integral
`∫₀^∞ (1 - e^{-σu})e^{-θu}du/u = log(1 + σ/θ)` under the measure, followed by the change of
variables `θ = θ'²/2`, which turns `log(1 + (ω²/2)/θ)` into `log(1 + ω²/θ'²)` exactly. Going
through `thorin_bridge` and the uniqueness of the Thorin measure instead would have spent A3 and
A11 for nothing. So `thorin_bridge_onto` prints Lean core.

**The causal Frullani integral is two Tonellis and no special function.** Writing
`(1 - e^{-σu})/u = ∫₀^σ e^{-su}ds` and integrating out `u` first leaves `∫₀^σ ds/(s + θ)`, a
logarithm. `SpatialLine/BridgeGamma.lean` had recorded that the *bridge* never needed this
integral; the converse direction does, and it is elementary.

**The causal integrability fields come from the spatial Thorin integral at `ω = 1`.** `min(1,u)`
is at most `e·(1 - e^{-u})`, so the two fields are bounded by `e` times the causal exponent at
`σ = 1`, which by the identity above is `½∫log(1 + 2/θ'²)U(dθ')`, and `log(1 + 2x) ≤ 2log(1 + x)`
bounds it by the spatial Thorin integral at `ω = 1` — finite because the spatial exponent is.
The integrability conditions of the two domains are never compared term by term.
-/

namespace SpatialLine

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-! ## Elementary integrals -/

/-- `∫₀^∞ e^{-cu}du = c⁻¹`, `ℝ≥0∞`-valued. -/
theorem lintegral_Ioi_exp_neg_mul {c : ℝ} (hc : 0 < c) :
    (∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(c * u)))) = ENNReal.ofReal c⁻¹ := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_neg_Ioi_zero hc)
    (.of_forall fun _ => (Real.exp_pos _).le)]
  congr 1
  have h := integral_exp_mul_Ioi (a := -c) (by linarith) 0
  simp only [mul_zero, Real.exp_zero] at h
  calc (∫ u in Ioi (0 : ℝ), Real.exp (-(c * u))) = ∫ u in Ioi (0 : ℝ), Real.exp (-c * u) := by
        refine integral_congr_ae (.of_forall fun u => ?_)
        simp only [neg_mul]
    _ = c⁻¹ := by rw [h]; field_simp

/-- `(1 - e^{-σu})/u = ∫₀^σ e^{-su}ds` for `u > 0`, `σ ≥ 0`, `ℝ≥0∞`-valued. -/
theorem ofReal_one_sub_exp_div_eq_lintegral {σ u : ℝ} (hσ : 0 ≤ σ) (hu : 0 < u) :
    ENNReal.ofReal ((1 - Real.exp (-(σ * u))) / u)
      = ∫⁻ s in Ioc (0 : ℝ) σ, ENNReal.ofReal (Real.exp (-(s * u))) := by
  have hcont : Continuous fun s : ℝ => Real.exp (-(s * u)) := by fun_prop
  rw [← ofReal_integral_eq_lintegral_ofReal
    ((hcont.integrableOn_Icc (a := 0) (b := σ)).mono_set Ioc_subset_Icc_self)
    (.of_forall fun _ => (Real.exp_pos _).le), ← intervalIntegral.integral_of_le hσ]
  congr 1
  have hderiv : ∀ s ∈ uIcc (0 : ℝ) σ,
      HasDerivAt (fun s : ℝ => -Real.exp (-(s * u)) / u) (Real.exp (-(s * u))) s := by
    intro s _
    have h1 : HasDerivAt (fun s : ℝ => -(s * u)) (-u) s :=
      (hasDerivAt_mul_const u).neg
    have h2 := (h1.exp.neg).div_const u
    have hval : Real.exp (-(s * u)) = -(Real.exp (-(s * u)) * -u) / u := by
      field_simp
    rw [hval]
    exact h2
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable _ _)]
  simp only [zero_mul, neg_zero, Real.exp_zero]
  ring

/-- `∫₀^σ ds/(s + θ) = log(1 + σ/θ)` for `θ > 0`, `σ ≥ 0`, `ℝ≥0∞`-valued. -/
theorem lintegral_Ioc_inv_add {σ θ : ℝ} (hσ : 0 ≤ σ) (hθ : 0 < θ) :
    (∫⁻ s in Ioc (0 : ℝ) σ, ENNReal.ofReal (s + θ)⁻¹)
      = ENNReal.ofReal (Real.log (1 + σ / θ)) := by
  have hcont : ContinuousOn (fun s : ℝ => (s + θ)⁻¹) (Icc 0 σ) :=
    ContinuousOn.inv₀ (by fun_prop) fun s hs => by linarith [hs.1]
  rw [← ofReal_integral_eq_lintegral_ofReal
    ((hcont.integrableOn_Icc).mono_set Ioc_subset_Icc_self)
    ((ae_restrict_iff' measurableSet_Ioc).mpr (.of_forall fun s hs => by
      have : 0 < s + θ := by linarith [hs.1]
      positivity)),
    ← intervalIntegral.integral_of_le hσ,
    intervalIntegral.integral_comp_add_right (fun s : ℝ => s⁻¹) θ,
    integral_inv_of_pos (by linarith) (by linarith)]
  congr 2
  field_simp
  ring

/-- **The causal Frullani identity under a measure**, the twin of `thorin_frullani`: for a folded
`U_I` and `σ ≥ 0`,
`∫₀^∞ (1 - e^{-σu})\,(∫e^{-θu}U_I(dθ))\,du/u = ∫\log(1 + σ/θ)\,U_I(dθ)`. -/
theorem causal_thorin_frullani {UI : Measure ℝ} [SFinite UI] (hUI : IsFolded UI) {σ : ℝ}
    (hσ : 0 ≤ σ) :
    (∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal ((1 - Real.exp (-(σ * u))) / u)
        * ∫⁻ θ, ENNReal.ofReal (Real.exp (-(θ * u))) ∂UI)
      = ∫⁻ θ, ENNReal.ofReal (Real.log (1 + σ / θ)) ∂UI := by
  have hmeas : Measurable (Function.uncurry
      (fun (u θ : ℝ) => ENNReal.ofReal ((1 - Real.exp (-(σ * u))) / u)
        * ENNReal.ofReal (Real.exp (-(θ * u))))) := by
    unfold Function.uncurry
    fun_prop
  have hstep : (∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal ((1 - Real.exp (-(σ * u))) / u)
        * ∫⁻ θ, ENNReal.ofReal (Real.exp (-(θ * u))) ∂UI)
      = ∫⁻ u in Ioi (0 : ℝ), ∫⁻ θ, ENNReal.ofReal ((1 - Real.exp (-(σ * u))) / u)
          * ENNReal.ofReal (Real.exp (-(θ * u))) ∂UI :=
    lintegral_congr fun u => by rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [hstep, lintegral_lintegral_swap hmeas.aemeasurable]
  have hae : ∀ᵐ θ ∂UI, 0 < θ := by
    rw [ae_iff]
    refine measure_mono_null (fun θ hθ => ?_) hUI
    simpa using not_lt.mp hθ
  refine lintegral_congr_ae ?_
  filter_upwards [hae] with θ hθ
  have h1 : (∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal ((1 - Real.exp (-(σ * u))) / u)
        * ENNReal.ofReal (Real.exp (-(θ * u))))
      = ∫⁻ u in Ioi (0 : ℝ), ∫⁻ s in Ioc (0 : ℝ) σ,
          ENNReal.ofReal (Real.exp (-((s + θ) * u))) := by
    refine setLIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    rw [ofReal_one_sub_exp_div_eq_lintegral hσ hu, ← lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun s => ?_
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    ring
  have hmeas2 : Measurable (Function.uncurry
      (fun (u s : ℝ) => ENNReal.ofReal (Real.exp (-((s + θ) * u))))) := by
    unfold Function.uncurry
    fun_prop
  rw [h1, lintegral_lintegral_swap hmeas2.aemeasurable, ← lintegral_Ioc_inv_add hσ hθ]
  refine setLIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
  exact lintegral_Ioi_exp_neg_mul (by linarith [hs.1])

/-- `min(1, u) ≤ e\,(1 - e^{-u})` for `u ≥ 0`: the Laplace weight of the causal integrability
fields against the causal exponent's weight at `σ = 1`. -/
theorem min_one_le_exp_one_mul {u : ℝ} (hu : 0 ≤ u) :
    min 1 u ≤ Real.exp 1 * (1 - Real.exp (-(1 * u))) := by
  rw [one_mul]
  have hinv : Real.exp u * Real.exp (-u) = 1 := by rw [← Real.exp_add]; simp
  rcases le_total u 1 with h | h
  · rw [min_eq_right h]
    have h1 : Real.exp u ≤ Real.exp 1 := Real.exp_le_exp.mpr h
    have h2 : 0 ≤ 1 - Real.exp (-u) := by
      have := Real.exp_le_one_iff.mpr (by linarith : -u ≤ 0); linarith
    have h4 := Real.add_one_le_exp u
    nlinarith [mul_le_mul_of_nonneg_right h1 h2]
  · rw [min_eq_left h]
    have h1 : Real.exp (-u) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
    have hinv1 : Real.exp 1 * Real.exp (-1) = 1 := by rw [← Real.exp_add]; simp
    have h4 := Real.add_one_le_exp (1 : ℝ)
    nlinarith [Real.exp_pos (1 : ℝ)]

/-! ## The two changes of variables on folded measures -/

theorem measurable_halfSq : Measurable fun θ : ℝ => θ ^ 2 / 2 := by fun_prop

theorem measurable_sqrtTwoMul : Measurable fun θ : ℝ => Real.sqrt (2 * θ) := by fun_prop

/-- On a folded measure, `θ ↦ √(2θ)` undoes `θ ↦ θ²/2`. -/
theorem map_sqrtTwoMul_map_halfSq {U : Measure ℝ} (hU : IsFolded U) :
    (U.map fun θ : ℝ => θ ^ 2 / 2).map (fun θ : ℝ => Real.sqrt (2 * θ)) = U := by
  rw [Measure.map_map measurable_sqrtTwoMul measurable_halfSq]
  have hae : ∀ᵐ θ ∂U, 0 < θ := by
    rw [ae_iff]
    refine measure_mono_null (fun θ hθ => ?_) hU
    simpa using not_lt.mp hθ
  conv_rhs => rw [← Measure.map_id (μ := U)]
  refine Measure.map_congr ?_
  filter_upwards [hae] with θ hθ
  simp only [Function.comp_apply, id_eq]
  rw [show 2 * (θ ^ 2 / 2) = θ ^ 2 by ring, Real.sqrt_sq hθ.le]

/-- On a folded measure, `θ ↦ θ²/2` undoes `θ ↦ √(2θ)`. -/
theorem map_halfSq_map_sqrtTwoMul {U : Measure ℝ} (hU : IsFolded U) :
    (U.map fun θ : ℝ => Real.sqrt (2 * θ)).map (fun θ : ℝ => θ ^ 2 / 2) = U := by
  rw [Measure.map_map measurable_halfSq measurable_sqrtTwoMul]
  have hae : ∀ᵐ θ ∂U, 0 < θ := by
    rw [ae_iff]
    refine measure_mono_null (fun θ hθ => ?_) hU
    simpa using not_lt.mp hθ
  conv_rhs => rw [← Measure.map_id (μ := U)]
  refine Measure.map_congr ?_
  filter_upwards [hae] with θ hθ
  simp only [Function.comp_apply, id_eq]
  rw [Real.sq_sqrt (by linarith)]
  ring

/-! ## The node's remaining sentence -/

/-- **`prop:thorin-subclass`(4), linearity of the measure map** `U_I ↦ 2·(image of U_I under
θ ↦ √(2θ))`, over `ℝ≥0∞` scalars. Lean core. -/
theorem thorin_bridge_measure_linear (c : ℝ≥0∞) (UI₁ UI₂ : Measure ℝ) :
    ENNReal.ofReal 2 • (c • UI₁ + UI₂).map (fun θ : ℝ => Real.sqrt (2 * θ))
      = c • (ENNReal.ofReal 2 • UI₁.map (fun θ : ℝ => Real.sqrt (2 * θ)))
        + ENNReal.ofReal 2 • UI₂.map (fun θ : ℝ => Real.sqrt (2 * θ)) := by
  rw [Measure.map_add _ _ measurable_sqrtTwoMul, Measure.map_smul, smul_add, smul_comm]

/-- **`prop:thorin-subclass`(4), injectivity of the measure map.** Two folded measures with the
same image under `U_I ↦ 2·(image of U_I under θ ↦ √(2θ))` are equal: the image is undone by
`θ ↦ θ²/2` on folded measures. Lean core. -/
theorem thorin_bridge_measure_injective {UI₁ UI₂ : Measure ℝ} (h₁ : IsFolded UI₁)
    (h₂ : IsFolded UI₂)
    (h : ENNReal.ofReal 2 • UI₁.map (fun θ : ℝ => Real.sqrt (2 * θ))
      = ENNReal.ofReal 2 • UI₂.map (fun θ : ℝ => Real.sqrt (2 * θ))) :
    UI₁ = UI₂ := by
  have hcancel : ∀ m : Measure ℝ, ENNReal.ofReal 2⁻¹ • ENNReal.ofReal 2 • m = m := fun m => by
    rw [smul_smul, ← ENNReal.ofReal_mul (by norm_num)]
    norm_num
  have hmap : UI₁.map (fun θ : ℝ => Real.sqrt (2 * θ))
      = UI₂.map (fun θ : ℝ => Real.sqrt (2 * θ)) := by
    rw [← hcancel (UI₁.map _), h, hcancel]
  rw [← map_halfSq_map_sqrtTwoMul h₁, hmap, map_halfSq_map_sqrtTwoMul h₂]

/-- **`prop:thorin-subclass`(4), surjectivity: every symmetric Thorin member is the bridge image
of a causal Thorin member.**

Given an `SDProfile` `Q` with a Thorin representation at a folded `U`, there is a causally
admissible `F` and a folded `U_I` such that `F`'s delay profile is the Laplace transform of `U_I`
(the hypothesis of `thorin_bridge`), `b₀ = 2a`, `U` is twice the image of `U_I` under
`θ ↦ √(2θ)`, and `Q`'s exponent is `F_I(ω²/2)`.

**Lean core.** The route, which is the route of record: `U_I` is half the image of `U` under
`θ ↦ θ²/2` and `k_I` its transform, finite on `(0,∞)` because `U`'s is; the causal Frullani
identity under `U_I` computes `F_I(σ)`, and at `σ = ω²/2` the change of variables returns
`eq:thorin`; at `σ = 1` it bounds the two integrability fields by the spatial Thorin integral at
`ω = 1`. -/
theorem thorin_bridge_onto (Q : SDProfile) (U : Measure ℝ) (hU : IsFolded U)
    (hrep : ∀ ω : ℝ, Q.exponentL ω = thorinExponentL Q.a U ω) :
    ∃ (F : CausalAdmissible) (UI : Measure ℝ), IsFolded UI ∧
      (∀ u : ℝ, 0 < u →
        ENNReal.ofReal (F.k u) = ∫⁻ θ, ENNReal.ofReal (Real.exp (-(θ * u))) ∂UI) ∧
      F.b₀ = 2 * Q.a ∧
      U = ENNReal.ofReal 2 • UI.map (fun θ : ℝ => Real.sqrt (2 * θ)) ∧
      ∀ ω : ℝ, Q.exponent ω = F.exponent (ω ^ 2 / 2) := by
  obtain ⟨hsig, hU1, -, hUsq⟩ := thorin_measure_facts hU (thorin_lintegral_ne_top hrep 1)
  haveI : SigmaFinite U := hsig
  set UI : Measure ℝ := ENNReal.ofReal 2⁻¹ • U.map (fun θ : ℝ => θ ^ 2 / 2) with hUIdef
  have hUIfold : IsFolded UI := by
    rw [hUIdef, IsFolded, Measure.smul_apply, Measure.map_apply measurable_halfSq measurableSet_Iic,
      measure_mono_null (fun θ hθ => ?_) hU, smul_eq_mul, mul_zero]
    simp only [mem_preimage, mem_Iic] at hθ ⊢
    by_contra hc
    have : 0 < θ ^ 2 / 2 := by have := pow_pos (not_le.mp hc) 2; positivity
    linarith
  -- the Laplace transform of `U_I`, read on `U`
  have hLI : ∀ g : ℝ → ℝ, Measurable g →
      (∫⁻ θ, ENNReal.ofReal (g θ) ∂UI)
        = ENNReal.ofReal 2⁻¹ * ∫⁻ θ, ENNReal.ofReal (g (θ ^ 2 / 2)) ∂U := by
    intro g hg
    rw [hUIdef, lintegral_smul_measure, lintegral_map (by fun_prop) measurable_halfSq]
    rfl
  have hLIfin : ∀ u : ℝ, 0 < u → (∫⁻ θ, ENNReal.ofReal (Real.exp (-(θ * u))) ∂UI) ≠ ⊤ := by
    intro u hu
    rw [hLI (fun θ => Real.exp (-(θ * u))) (by fun_prop)]
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ne_top_of_le_ne_top
      (ENNReal.mul_ne_top (a := ENNReal.ofReal (Real.exp (u / 2))) ENNReal.ofReal_ne_top
        (laplaceL_ne_top_of_facts hU hU1 hUsq (by linarith : (0 : ℝ) < u / 2))) ?_)
    rw [laplaceL, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun θ => ?_
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
    nlinarith [mul_nonneg hu.le (sq_nonneg (θ - 1 / 2))]
  have hUIsig : SigmaFinite UI := by
    refine sigmaFinite_of_laplaceL_ne_top (y := 1) ?_
    have hone : laplaceL UI 1 = ∫⁻ θ, ENNReal.ofReal (Real.exp (-(θ * 1))) ∂UI :=
      lintegral_congr fun θ => by rw [one_mul, mul_one]
    rw [hone]
    exact hLIfin 1 one_pos
  set kI : ℝ → ℝ := Set.indicator (Ioi (0 : ℝ))
    (fun u => (∫⁻ θ, ENNReal.ofReal (Real.exp (-(θ * u))) ∂UI).toReal) with hkIdef
  have hkI : ∀ u : ℝ, 0 < u →
      ENNReal.ofReal (kI u) = ∫⁻ θ, ENNReal.ofReal (Real.exp (-(θ * u))) ∂UI := by
    intro u hu
    rw [hkIdef, Set.indicator_of_mem (show u ∈ Ioi (0 : ℝ) from hu)]
    exact ENNReal.ofReal_toReal (hLIfin u hu)
  have hkI_nonneg : ∀ u ∈ Ioi (0 : ℝ), 0 ≤ kI u := fun u _ => by
    rw [hkIdef]; exact Set.indicator_nonneg (fun _ _ => ENNReal.toReal_nonneg) u
  have haeI : ∀ᵐ θ ∂UI, 0 < θ := by
    rw [ae_iff]
    refine measure_mono_null (fun θ hθ => ?_) hUIfold
    simpa using not_lt.mp hθ
  have hkI_anti : AntitoneOn kI (Ioi (0 : ℝ)) := by
    intro u hu v hv huv
    have hu0 : (0 : ℝ) < u := hu
    have hv0 : (0 : ℝ) < v := hv
    rw [hkIdef, Set.indicator_of_mem hu, Set.indicator_of_mem hv]
    refine ENNReal.toReal_mono (hLIfin u hu0) (lintegral_mono_ae ?_)
    filter_upwards [haeI] with θ hθ
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by nlinarith))
  -- the causal exponent integral, against `U_I`
  have hexpI : ∀ σ : ℝ, 0 ≤ σ →
      (∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal ((1 - Real.exp (-(σ * u))) * kI u / u))
        = ∫⁻ θ, ENNReal.ofReal (Real.log (1 + σ / θ)) ∂UI := by
    intro σ hσ
    rw [← causal_thorin_frullani hUIfold hσ]
    refine setLIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    have hu0 : (0 : ℝ) < u := hu
    have hnn : 0 ≤ (1 - Real.exp (-(σ * u))) / u :=
      div_nonneg (ScaleSpace.CausalAdmissible.one_sub_exp_bounds hσ hu0.le).1 hu0.le
    rw [← hkI u hu0, ← ENNReal.ofReal_mul hnn]
    congr 1
    ring
  -- the two integrability fields
  have hmin : (∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (min 1 u * kI u / u)) ≠ ⊤ := by
    have hbound : (∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (min 1 u * kI u / u))
        ≤ ENNReal.ofReal (Real.exp 1)
          * ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal ((1 - Real.exp (-(1 * u))) * kI u / u) := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine setLIntegral_mono' measurableSet_Ioi fun u hu => ?_
      have hu0 : (0 : ℝ) < u := hu
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
      refine ENNReal.ofReal_le_ofReal ?_
      have hk := hkI_nonneg u hu
      have hm := min_one_le_exp_one_mul hu0.le
      rw [div_le_iff₀ hu0, mul_assoc, div_mul_cancel₀ _ hu0.ne', ← mul_assoc]
      exact mul_le_mul_of_nonneg_right hm hk
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_) hbound
    rw [hexpI 1 zero_le_one, hLI (fun θ => Real.log (1 + 1 / θ)) (by fun_prop)]
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ne_top_of_le_ne_top
      (ENNReal.mul_ne_top (a := 2) (by norm_num) (thorin_lintegral_ne_top hrep 1)) ?_)
    rw [← lintegral_const_mul' _ _ (by norm_num)]
    refine lintegral_mono fun θ => ?_
    have hx : (0 : ℝ) ≤ 1 ^ 2 / θ ^ 2 := by positivity
    have heq : 1 / (θ ^ 2 / 2) = 2 * (1 ^ 2 / θ ^ 2) := by rw [one_div_div]; ring
    rw [heq, show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
      ← ENNReal.ofReal_mul (by norm_num)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hpow := Real.log_pow (1 + 1 ^ 2 / θ ^ 2) 2
    push_cast at hpow
    rw [← hpow]
    exact Real.log_le_log (by positivity) (by nlinarith [sq_nonneg (1 ^ 2 / θ ^ 2)])
  rw [ScaleSpace.CausalAdmissible.lintegral_min_split] at hmin
  obtain ⟨hnear, htop⟩ := ENNReal.add_ne_top.mp hmin
  let F : CausalAdmissible :=
    { b₀ := 2 * Q.a
      k := kI
      b₀_nonneg := by have := Q.a_nonneg; positivity
      k_nonneg := hkI_nonneg
      k_antitone := hkI_anti
      k_zero := by rw [hkIdef]; exact Set.indicator_of_notMem (lt_irrefl 0) _
      integrable_near_zero := hnear
      integrable_at_top := htop }
  refine ⟨F, UI, hUIfold, hkI, rfl, ?_, fun ω => ?_⟩
  · rw [hUIdef, Measure.map_smul, smul_smul, ← ENNReal.ofReal_mul (by norm_num),
      map_sqrtTwoMul_map_halfSq hU]
    norm_num
  · have hσ : (0 : ℝ) ≤ ω ^ 2 / 2 := by positivity
    have hL : F.exponentL (ω ^ 2 / 2) = Q.exponentL ω := by
      rw [hrep ω, ScaleSpace.CausalAdmissible.exponentL, thorinExponentL]
      change ENNReal.ofReal (2 * Q.a * (ω ^ 2 / 2))
          + ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal ((1 - Real.exp (-(ω ^ 2 / 2 * u))) * kI u / u)
        = _
      rw [hexpI _ hσ, hLI (fun θ => Real.log (1 + ω ^ 2 / 2 / θ)) (by fun_prop)]
      congr 2
      · ring
      · refine lintegral_congr fun θ => ?_
        congr 2
        ring
    rw [SDProfile.exponent, ScaleSpace.CausalAdmissible.exponent, hL]

end SpatialLine
