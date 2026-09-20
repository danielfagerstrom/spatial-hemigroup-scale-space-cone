/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.Thorin
import SpatialLine.BridgeGamma
import SpatialLine.ChoquetExtreme

/-!
# The bridge on Thorin subclasses

Blueprint: `prop:thorin-subclass`(4) — a causally admissible exponent with a completely monotone
delay profile subordinates to a symmetric Thorin member, and the spatial Thorin measure is
**twice** the image of the causal one under `θ ↦ √(2θ)`.

## What proving this found

**The a.e.-to-pointwise antitone lemma the wave-5 estimate said was missing is already here.**
The re-price of this clause named, as the step no estimate had contained, "the general fact that
two antitone functions agreeing a.e., one of them continuous, agree everywhere", and said that
"this development has no such lemma yet". It has had one since wave 2:
`eqOn_of_ae_eq_of_antitoneOn` in `SpatialLine/ProfileUniqueness.lean`, together with the composed
form `eqOn_of_profileMeasure_eq` that goes from equal profile measures straight to a pointwise
identity on `(0,∞)`. `thorin_subclass_representation` itself runs on it. So the *only* work in
this clause is the mixture identity below; the passage the estimate feared costs one application.

**σ-finiteness of `U_I` is a consequence of the hypothesis, not a missing hypothesis.** The
Tonelli of the mixture identity needs `U_I` s-finite and the statement does not assume it. It
does not have to: `hk` says that the causal profile is the Laplace transform of `U_I`, and a
*real* value at `u = 1` makes that transform finite there, which is `sigmaFinite_of_lintegral_ne_top`
applied to a weight that vanishes nowhere. The same two lines give σ-finiteness of the image
measure from finiteness of its own transform, which is what `thorin_of_laplace` needs.

**The exponent clause is `thorin_of_laplace`, already proved, and no second Tonelli.** Once the
folded profile is exhibited as the Laplace transform of the image measure, chapter 10's own
forward step turns that into `eq:thorin`. The change of variables `θ' = √(2θ)` never has to be
performed *inside* the Thorin integral: it is performed once, in the image measure, and the
Frullani computation is then quoted rather than repeated.
-/

namespace SpatialLine

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-- **A measure whose Laplace transform is finite at one point is σ-finite.**

The weight `e^{-yθ}` is strictly positive at every real `θ`, so its zero set is empty and
`sigmaFinite_of_lintegral_ne_top` applies with no support hypothesis at all. Note that no sign
condition on `y` is needed either: only finiteness of the integral is used. -/
theorem sigmaFinite_of_laplaceL_ne_top {m : Measure ℝ} {y : ℝ} (h : laplaceL m y ≠ ⊤) :
    SigmaFinite m := by
  refine sigmaFinite_of_lintegral_ne_top (g := fun t => ENNReal.ofReal (Real.exp (-(y * t))))
    (by fun_prop) ?_ h
  convert measure_empty (μ := m) using 2
  ext t
  simp [ENNReal.ofReal_eq_zero, not_le, Real.exp_pos]

end SpatialLine

namespace ScaleSpace.CausalAdmissible

open SpatialLine
open MeasureTheory Set Filter
open scoped ENNReal Topology

/-- **The mixture identity of `prop:thorin-subclass`(4).**

If the causal profile is the Laplace transform of `U_I`, then `x ν₂(x)`, the object
`eq:bridge-profile` folds by `2`, is the Laplace transform of the image of `U_I` under
`θ ↦ √(2θ)`:
`x∫₀^∞ g_u(x)k_I(u)du/u = ∫ e^{-x√(2θ)}U_I(dθ)`.

The inner integral is `lintegral_Ioi_firstPassage` at `A = x²/2` and `B = θ`, and `IsFolded U_I`
is what supplies `B > 0`: at an atom of `U_I` at the origin the first-passage lemma does not
apply, which is the same exclusion `thorin_subclass_representation` makes on the spatial side. -/
theorem ofReal_mul_mixDensityL_laplace (F : CausalAdmissible) {UI : Measure ℝ} [SFinite UI]
    (hUI : IsFolded UI)
    (hk : ∀ u : ℝ, 0 < u → ENNReal.ofReal (F.k u)
      = ∫⁻ θ, ENNReal.ofReal (Real.exp (-(θ * u))) ∂UI)
    {x : ℝ} (hx : 0 < x) :
    ENNReal.ofReal x * F.mixDensityL x
      = ∫⁻ θ, ENNReal.ofReal (Real.exp (-(x * Real.sqrt (2 * θ)))) ∂UI := by
  have hsp : (0 : ℝ) < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  set C : ℝ := x * (Real.sqrt (2 * Real.pi))⁻¹ with hCdef
  have hC : 0 < C := by rw [hCdef]; positivity
  have h1 : ENNReal.ofReal x * F.mixDensityL x
      = ∫⁻ u in Ioi (0 : ℝ), ∫⁻ θ, ENNReal.ofReal
            (C * (u ^ (-(3 : ℝ) / 2) * Real.exp (-(x ^ 2 / 2 / u))))
            * ENNReal.ofReal (Real.exp (-(θ * u))) ∂UI := by
    rw [mixDensityL, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    have hu0 : (0 : ℝ) < u := hu
    have hsu : (0 : ℝ) < Real.sqrt u := Real.sqrt_pos.mpr hu0
    have halg : ENNReal.ofReal x * ENNReal.ofReal (brownianDensity u x * F.k u / u)
        = ENNReal.ofReal (C * (u ^ (-(3 : ℝ) / 2) * Real.exp (-(x ^ 2 / 2 / u))))
            * ENNReal.ofReal (F.k u) := by
      rw [← ENNReal.ofReal_mul hx.le, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [brownianDensity_eq hu0, rpow_neg_three_half hu0,
        show 2 * Real.pi * u = (2 * Real.pi) * u by ring, Real.sqrt_mul (by positivity),
        show -x ^ 2 / (2 * u) = -(x ^ 2 / 2 / u) by ring, hCdef]
      field_simp
    rw [halg, hk u hu0, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [h1]
  have hmeas : Measurable (Function.uncurry
      (fun (u θ : ℝ) => ENNReal.ofReal (C * (u ^ (-(3 : ℝ) / 2) * Real.exp (-(x ^ 2 / 2 / u))))
        * ENNReal.ofReal (Real.exp (-(θ * u))))) := by
    unfold Function.uncurry
    fun_prop
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  have hae : ∀ᵐ θ ∂UI, 0 < θ := by
    rw [ae_iff]
    refine measure_mono_null (fun θ hθ => ?_) hUI
    simpa using not_lt.mp hθ
  refine lintegral_congr_ae ?_
  filter_upwards [hae] with θ hθ
  have hinner : (∫⁻ u in Ioi (0 : ℝ),
        ENNReal.ofReal (C * (u ^ (-(3 : ℝ) / 2) * Real.exp (-(x ^ 2 / 2 / u))))
          * ENNReal.ofReal (Real.exp (-(θ * u))))
      = ENNReal.ofReal C * ∫⁻ u in Ioi (0 : ℝ),
          ENNReal.ofReal (u ^ (-(3 : ℝ) / 2) * Real.exp (-(x ^ 2 / 2 / u + θ * u))) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    have hu0 : (0 : ℝ) < u := hu
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hC.le]
    congr 1
    rw [show -(x ^ 2 / 2 / u + θ * u) = -(x ^ 2 / 2 / u) + -(θ * u) by ring, Real.exp_add]
    ring
  rw [hinner, lintegral_Ioi_firstPassage (by positivity : (0 : ℝ) < x ^ 2 / 2) hθ,
    ← ENNReal.ofReal_mul hC.le]
  congr 1
  have hsA : Real.sqrt (Real.pi / (x ^ 2 / 2)) = Real.sqrt (2 * Real.pi) / x := by
    rw [show Real.pi / (x ^ 2 / 2) = (2 * Real.pi) / x ^ 2 by field_simp,
      Real.sqrt_div (by positivity), Real.sqrt_sq hx.le]
  have hsB : 2 * Real.sqrt (x ^ 2 / 2 * θ) = x * Real.sqrt (2 * θ) := by
    rw [show x ^ 2 / 2 * θ = (x / 2) ^ 2 * (2 * θ) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    ring
  rw [hsA, hsB, hCdef]
  field_simp

end ScaleSpace.CausalAdmissible

namespace SpatialLine

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-- **The image of a folded measure under `θ ↦ √(2θ)` is folded.** -/
theorem isFolded_map_sqrt {UI : Measure ℝ} (hUI : IsFolded UI) :
    IsFolded (UI.map fun θ : ℝ => Real.sqrt (2 * θ)) := by
  have hm : Measurable fun θ : ℝ => Real.sqrt (2 * θ) := by fun_prop
  rw [IsFolded, Measure.map_apply hm measurableSet_Iic]
  have hpre : (fun θ : ℝ => Real.sqrt (2 * θ)) ⁻¹' Iic 0 = Iic (0 : ℝ) := by
    ext θ
    simp only [mem_preimage, mem_Iic]
    constructor
    · intro h
      by_contra hc
      push Not at hc
      have : 0 < Real.sqrt (2 * θ) := Real.sqrt_pos.mpr (by linarith)
      linarith
    · intro h
      rw [Real.sqrt_eq_zero_of_nonpos (by linarith)]
  rw [hpre, hUI]

/-- **`prop:thorin-subclass`(4), the bridge on Thorin subclasses.**

`Skeleton.thorin_bridge`'s statement verbatim: if the causal delay profile is the Laplace
transform of `U_I`, then any `SDProfile` whose exponent is `F_I(ω²/2)` has Gaussian coefficient
`b₀/2`, a completely monotone folded profile, and the Thorin representation at **twice** the
image of `U_I` under `θ ↦ √(2θ)`.

**Spends ledger A3** (`fourier_toolbox_levy_unique`, through `sdProfile_unique`) and ledger
**A11** (`bernstein_completely_monotone`, at its easy direction — a Laplace transform is
completely monotone — which is a name already on the trust boundary). Nothing else.

The route, which is the route of record: the mixture identity above exhibits the folded profile
of `eq:bridge-profile` as the Laplace transform of `U`; `Q` is quantified over, so A3's
uniqueness returns only *a.e.* equality of `Q.k` with that profile, and
`eqOn_of_profileMeasure_eq` upgrades it, the transform being continuous on `(0,∞)` and `Q.k`
antitone there; complete monotonicity is then Bernstein's easy direction, and the exponent
identity is `thorin_of_laplace`. -/
theorem thorin_bridge (F : CausalAdmissible) (UI : Measure ℝ) (hUI : IsFolded UI)
    (hk : ∀ u : ℝ, 0 < u →
      ENNReal.ofReal (F.k u) = ∫⁻ θ, ENNReal.ofReal (Real.exp (-(θ * u))) ∂UI)
    (Q : SDProfile) (hQ : ∀ ω : ℝ, Q.exponent ω = F.exponent (ω ^ 2 / 2)) :
    Q.a = F.b₀ / 2 ∧ IsCompletelyMonotone Q.k ∧
      ∀ ω : ℝ, Q.exponentL ω
        = thorinExponentL Q.a
            (ENNReal.ofReal 2 • UI.map fun θ => Real.sqrt (2 * θ)) ω := by
  -- σ-finiteness of `U_I`, read off the Laplace representation at `u = 1`.
  have hUIsig : SigmaFinite UI := by
    refine sigmaFinite_of_laplaceL_ne_top (y := 1) ?_
    have hone : (∫⁻ θ, ENNReal.ofReal (Real.exp (-(1 * θ))) ∂UI)
        = ∫⁻ θ, ENNReal.ofReal (Real.exp (-(θ * 1))) ∂UI :=
      lintegral_congr fun θ => by rw [one_mul, mul_one]
    rw [laplaceL, hone, ← hk 1 one_pos]
    exact ENNReal.ofReal_ne_top
  haveI : SFinite UI := inferInstance
  have hmm : Measurable fun θ : ℝ => Real.sqrt (2 * θ) := by fun_prop
  set U : Measure ℝ := ENNReal.ofReal 2 • UI.map fun θ : ℝ => Real.sqrt (2 * θ) with hUdef
  have hlapU : ∀ y : ℝ, laplaceL U y
      = ENNReal.ofReal 2 * ∫⁻ θ, ENNReal.ofReal (Real.exp (-(y * Real.sqrt (2 * θ)))) ∂UI := by
    intro y
    rw [laplaceL, hUdef, lintegral_smul_measure, lintegral_map (by fun_prop) hmm]
    rfl
  have hUfold : IsFolded U := by
    rw [hUdef, IsFolded, Measure.smul_apply, isFolded_map_sqrt hUI, smul_eq_mul, mul_zero]
  -- the folded profile of `eq:bridge-profile` is the Laplace transform of `U`
  have hbridge : ∀ x : ℝ, 0 < x → ENNReal.ofReal (F.bridgeProfile x) = laplaceL U x := by
    intro x hx
    have hfin : ENNReal.ofReal x * F.mixDensityL x ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (F.mixDensityL_ne_top hx.ne')
    have hM : ENNReal.ofReal x * F.mixDensityL x
        = ∫⁻ θ, ENNReal.ofReal (Real.exp (-(x * Real.sqrt (2 * θ)))) ∂UI :=
      F.ofReal_mul_mixDensityL_laplace hUI hk hx
    rw [hlapU x, ← hM, F.bridgeProfile_eq hx.le,
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_toReal hfin]
  have hLfin : ∀ x : ℝ, 0 < x → laplaceL U x ≠ ⊤ := fun x hx => by
    rw [← hbridge x hx]; exact ENNReal.ofReal_ne_top
  set k' : ℝ → ℝ := fun x => (laplaceL U x).toReal with hk'def
  have hk'nonneg : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ k' x := fun _ _ => ENNReal.toReal_nonneg
  have hk'cont : ContinuousOn k' (Ioi 0) := continuousOn_laplaceReal hUfold hLfin
  have hk'meas : AEMeasurable k' (volume.restrict (Ioi (0 : ℝ))) :=
    hk'cont.aemeasurable measurableSet_Ioi
  have hbk' : Set.EqOn F.bridgeProfile k' (Ioi 0) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    rw [hk'def]
    simp only
    rw [← hbridge x hx0, ENNReal.toReal_ofReal (F.bridgeProfile_nonneg hx0.le)]
  -- uniqueness at the profile: ledger A3, and it returns an a.e. identity
  have hexp : ∀ ω, Q.exponent ω = F.bridgeDatum.exponent ω := fun ω => by
    rw [F.bridgeDatum_exponent ω]; exact hQ ω
  obtain ⟨hQa, hQprof⟩ := sdProfile_unique hexp
  have hprof : profileMeasure Q.k = profileMeasure k' := by
    rw [hQprof, ScaleSpace.CausalAdmissible.bridgeDatum_k, profileMeasure, profileMeasure]
    refine withDensity_congr_ae ?_
    filter_upwards [self_mem_ae_restrict (measurableSet_Ioi (a := (0 : ℝ)))] with x hx
    rw [hbk' hx]
  have heqOn : Set.EqOn Q.k k' (Ioi 0) :=
    eqOn_of_profileMeasure_eq Q.k_antitone Q.k_nonneg hk'meas hk'nonneg hk'cont hprof
  have hlap : ∀ x : ℝ, 0 < x → ENNReal.ofReal (Q.k x) = laplaceL U x := fun x hx => by
    rw [heqOn hx, hk'def]; exact ENNReal.ofReal_toReal (hLfin x hx)
  haveI : SigmaFinite U := sigmaFinite_of_laplaceL_ne_top (hLfin 1 one_pos)
  refine ⟨by rw [hQa, ScaleSpace.CausalAdmissible.bridgeDatum_a], ?_, ?_⟩
  · refine (bernstein_completely_monotone Q.k).mpr ⟨U, ?_, fun x hx => ⟨hLfin x hx, heqOn hx⟩⟩
    exact measure_mono_null Iio_subset_Iic_self hUfold
  · exact thorin_of_laplace hUfold hlap

end SpatialLine
