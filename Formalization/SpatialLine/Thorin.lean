/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.CornerDefs
import SpatialLine.Frullani
import SpatialLine.SelfDecomposable
import SpatialLine.CinRays
import SpatialLine.LaplaceUniqueness
import SpatialLine.ProfileUniqueness
import SpatialLine.AdmissibleCone
import SpatialLine.TransformBridge

/-!
# The symmetric Thorin representation

Blueprint: `prop:thorin-subclass`, the equivalence of clauses (1) and (2) with the uniqueness of
the Thorin measure. Proved by wave 3 of the campaign (2026-09-09).

## The shape of the argument

Everything runs through one lemma, `laplaceL_eq_of_thorin`: *if a folded `U` represents an
admissible exponent through `eq:thorin`, the profile `k` is the Laplace transform of `U` on
`(0,∞)`, pointwise.* Both directions of the node and its uniqueness clause are corollaries — the
converse feeds that identity back to Bernstein's theorem, the uniqueness clause feeds it to
Laplace uniqueness, and the forward direction is Bernstein's theorem followed by the same Tonelli
read the other way.

## Three things the writing found

**1. A11's uniqueness clause is not spent, and the node's uniqueness clause is `[T]`.** The
ledger entry records three uses of Bernstein's theorem and says of the third that "uniqueness of
the representing measure is what makes the Thorin measure well defined". It is not needed: two
folded measures whose Laplace transforms agree and are finite on a ray are equal by
`laplace_uniqueness_locally_finite`, which this development proves
(`prop:laplace-uniqueness-locally-finite`). So the admitted axiom is the existence equivalence
alone, and the trust base is charged for less than the citation carries.

**2. The integrability clause of `eq:thorin` is a consequence, not a hypothesis.** Finiteness of
the Thorin integral at the *single* frequency `ω = 1` — which `SDProfile.exponentL_ne_top` gives
for free whenever `U` represents an admissible exponent — already yields σ-finiteness of `U`,
finiteness of `U` on `(0,1]`, and both halves of the node's condition
(`thorin_measure_facts`). In particular the converse direction never reads the clause: the
`rintro` pattern of `thorin_subclass_representation` discards it. It is stated because
`eq:thorin` states it and because it is what makes the representation a representation, not
because a proof consumes it.

**3. The Lévy condition for the reconstructed profile is a Gaussian average away.** The step that
looked expensive was showing that `k'(x) = ∫e^{-θx}U(dθ)` is the profile of a symmetric Lévy pair
at all, its Lévy condition `∫(1 ∧ x²)ν < ∞` not being visible in the Thorin integral. It is:
integrate the identity `profileJumpL k ω = profileJumpL k' ω` over `ω` against a standard
Gaussian. Tonelli replaces the weight `1 - cos ωx` by `1 - e^{-x²/2}`, which is trapped between
`(1 ∧ x²)/3` and `1 ∧ x²` by two lines of `Real.add_one_le_exp`, and the condition transfers
(`lintegral_min_ne_top_of_profileJump_eq`). Averaging over a *uniform* `ω` would give the weight
`1 - \sin x/x`, whose lower bound needs a fourth-order estimate on `\sin`; the Gaussian needs
none, and `fourierCos_gaussianReal` was already in the library.
-/

namespace SpatialLine

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-! ## Two elementary bounds on the Thorin weight -/

/-- `1 - x⁻¹ ≤ log x`, the reverse of `Real.log_le_sub_one_of_pos` read at `x⁻¹`. -/
theorem one_sub_inv_le_log {x : ℝ} (hx : 0 < x) : 1 - x⁻¹ ≤ Real.log x := by
  have h := Real.log_le_sub_one_of_pos (x := x⁻¹) (by positivity)
  rw [Real.log_inv] at h
  linarith

/-- On `(0,1]` the Thorin weight at `ω = 1` dominates `log(1/θ)`. -/
theorem log_inv_le_thorin_weight {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    Real.log θ⁻¹ ≤ Real.log (1 + 1 ^ 2 / θ ^ 2) := by
  have h1 : θ⁻¹ ≤ 1 + 1 ^ 2 / θ ^ 2 := by
    have h2 : θ⁻¹ ≤ θ⁻¹ * θ⁻¹ := by
      have : (1 : ℝ) ≤ θ⁻¹ := by rw [le_inv_comm₀ (by norm_num) hθ]; simpa using hθ1
      nlinarith [inv_pos.mpr hθ]
    have h3 : θ⁻¹ * θ⁻¹ = 1 ^ 2 / θ ^ 2 := by field_simp
    linarith
  exact Real.log_le_log (by positivity) h1

/-- On `(1,∞)` twice the Thorin weight at `ω = 1` dominates `θ⁻²`. -/
theorem inv_sq_le_thorin_weight {θ : ℝ} (hθ : 1 < θ) :
    (θ ^ 2)⁻¹ ≤ 2 * Real.log (1 + 1 ^ 2 / θ ^ 2) := by
  have hθ0 : (0 : ℝ) < θ := lt_trans one_pos hθ
  have hpos : (0 : ℝ) < 1 + 1 ^ 2 / θ ^ 2 := by positivity
  have h := one_sub_inv_le_log hpos
  have hval : 1 - (1 + 1 ^ 2 / θ ^ 2)⁻¹ = (θ ^ 2 + 1)⁻¹ := by
    have h2 : (0 : ℝ) < θ ^ 2 := by positivity
    field_simp
    ring
  rw [hval] at h
  have hb : (θ ^ 2)⁻¹ ≤ 2 * (θ ^ 2 + 1)⁻¹ := by
    have h2 : (0 : ℝ) < θ ^ 2 := by positivity
    have h3 : (0 : ℝ) < θ ^ 2 + 1 := by positivity
    rw [inv_eq_one_div, inv_eq_one_div, ← mul_div_assoc, mul_one,
      div_le_div_iff₀ h2 h3]
    nlinarith [hθ, hθ0]
  linarith

/-! ## A σ-finiteness criterion -/

/-- A measure integrating to a finite value a function that vanishes only on a null set is
σ-finite: the level sets carry finite measure by Markov's inequality, and together with the
zero set they span. -/
theorem sigmaFinite_of_lintegral_ne_top {μ : Measure ℝ} {g : ℝ → ℝ≥0∞}
    (hg : Measurable g) (hnull : μ {y | g y = 0} = 0) (h : ∫⁻ y, g y ∂μ ≠ ⊤) :
    SigmaFinite μ := by
  refine ⟨⟨fun n => {y | ((n : ℝ≥0∞) + 1)⁻¹ ≤ g y} ∪ {y | g y = 0}, fun _ => trivial,
    fun n => ?_, ?_⟩⟩
  · have hcne : ((n : ℝ≥0∞) + 1)⁻¹ ≠ 0 := by simp
    have hkey : ((n : ℝ≥0∞) + 1)⁻¹ * μ {y | ((n : ℝ≥0∞) + 1)⁻¹ ≤ g y} ≤ ∫⁻ y, g y ∂μ :=
      mul_meas_ge_le_lintegral₀ hg.aemeasurable _
    have hfin : μ {y | ((n : ℝ≥0∞) + 1)⁻¹ ≤ g y} ≠ ⊤ := by
      intro hcon
      rw [hcon, ENNReal.mul_top hcne] at hkey
      exact h (top_le_iff.mp hkey)
    calc μ ({y | ((n : ℝ≥0∞) + 1)⁻¹ ≤ g y} ∪ {y | g y = 0})
        ≤ μ {y | ((n : ℝ≥0∞) + 1)⁻¹ ≤ g y} + μ {y | g y = 0} := measure_union_le _ _
      _ < ⊤ := by rw [hnull, add_zero]; exact lt_top_iff_ne_top.mpr hfin
  · refine eq_univ_of_forall fun y => ?_
    by_cases hy : g y = 0
    · exact mem_iUnion.mpr ⟨0, Or.inr hy⟩
    · obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt hy
      refine mem_iUnion.mpr ⟨n, Or.inl ?_⟩
      refine le_trans ?_ hn.le
      exact ENNReal.inv_le_inv.mpr (by exact_mod_cast Nat.le_succ n)

/-! ## What finiteness of the Thorin integral at one frequency gives -/

/-- **Everything the representation's integrability clause is worth, read off one frequency.**

Finiteness of the Thorin integral at `ω = 1` — which `SDProfile.exponentL_ne_top` supplies
whenever `U` represents an admissible exponent — already gives that `U` is σ-finite, that it is
finite on `(0,1]`, and both halves of the node's integrability condition. The three regimes are
the annotation's: `log(1 + θ⁻²) ≍ 2log(1/θ)` near `0`, `≍ θ⁻²` at infinity, and bounded below by
`log 2` in between. -/
theorem thorin_measure_facts {U : Measure ℝ} (hU : IsFolded U)
    (hlog : (∫⁻ θ, ENNReal.ofReal (Real.log (1 + 1 ^ 2 / θ ^ 2)) ∂U) ≠ ⊤) :
    SigmaFinite U ∧ U (Ioc (0 : ℝ) 1) ≠ ⊤
      ∧ (∫⁻ θ in Ioc (0 : ℝ) 1, ENNReal.ofReal (Real.log θ⁻¹) ∂U) ≠ ⊤
      ∧ (∫⁻ θ in Ioi (1 : ℝ), ENNReal.ofReal ((θ ^ 2)⁻¹) ∂U) ≠ ⊤ := by
  have hmeas : Measurable fun θ : ℝ => ENNReal.ofReal (Real.log (1 + 1 ^ 2 / θ ^ 2)) := by
    fun_prop
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine sigmaFinite_of_lintegral_ne_top hmeas ?_ hlog
    refine measure_mono_null (fun θ hθ => ?_) hU
    by_contra hcon
    have hθ0 : (0 : ℝ) < θ := not_le.mp (by simpa using hcon)
    have hθ2 : (0 : ℝ) < θ ^ 2 := by positivity
    have hpos : (0 : ℝ) < 1 ^ 2 / θ ^ 2 := by
      rw [one_pow]; exact div_pos one_pos hθ2
    have hlogpos : (0 : ℝ) < Real.log (1 + 1 ^ 2 / θ ^ 2) := Real.log_pos (by linarith)
    simp only [mem_setOf_eq, ENNReal.ofReal_eq_zero] at hθ
    linarith
  · have hb : ENNReal.ofReal (Real.log 2) * U (Ioc (0 : ℝ) 1)
        ≤ ∫⁻ θ, ENNReal.ofReal (Real.log (1 + 1 ^ 2 / θ ^ 2)) ∂U := by
      rw [← setLIntegral_const (Ioc (0 : ℝ) 1) (ENNReal.ofReal (Real.log 2))]
      refine le_trans (lintegral_mono_ae ?_) (setLIntegral_le_lintegral _ _)
      refine (ae_restrict_iff' measurableSet_Ioc).mpr (.of_forall fun θ hθ => ?_)
      refine ENNReal.ofReal_le_ofReal (Real.log_le_log (by norm_num) ?_)
      have hθ0 : (0 : ℝ) < θ := hθ.1
      have h1 : (1 : ℝ) ≤ 1 ^ 2 / θ ^ 2 := by
        rw [le_div_iff₀ (by positivity)]
        nlinarith [hθ.1, hθ.2]
      linarith
    intro hcon
    rw [hcon, ENNReal.mul_top (by simp [Real.log_pos])] at hb
    exact hlog (top_le_iff.mp hb)
  · refine ne_top_of_le_ne_top hlog ?_
    refine le_trans (lintegral_mono_ae ?_) (setLIntegral_le_lintegral _ _)
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (.of_forall fun θ hθ => ?_)
    exact ENNReal.ofReal_le_ofReal (log_inv_le_thorin_weight hθ.1 hθ.2)
  · have hb : (∫⁻ θ in Ioi (1 : ℝ), ENNReal.ofReal ((θ ^ 2)⁻¹) ∂U)
        ≤ 2 * ∫⁻ θ, ENNReal.ofReal (Real.log (1 + 1 ^ 2 / θ ^ 2)) ∂U := by
      calc (∫⁻ θ in Ioi (1 : ℝ), ENNReal.ofReal ((θ ^ 2)⁻¹) ∂U)
          ≤ ∫⁻ θ in Ioi (1 : ℝ), 2 * ENNReal.ofReal (Real.log (1 + 1 ^ 2 / θ ^ 2)) ∂U := by
            refine lintegral_mono_ae ?_
            refine (ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun θ hθ => ?_)
            have hbb := inv_sq_le_thorin_weight (θ := θ) hθ
            calc ENNReal.ofReal ((θ ^ 2)⁻¹)
                ≤ ENNReal.ofReal (2 * Real.log (1 + 1 ^ 2 / θ ^ 2)) :=
                  ENNReal.ofReal_le_ofReal hbb
              _ = 2 * ENNReal.ofReal (Real.log (1 + 1 ^ 2 / θ ^ 2)) := by
                  rw [ENNReal.ofReal_mul (by norm_num)]
                  norm_num
        _ = 2 * ∫⁻ θ in Ioi (1 : ℝ), ENNReal.ofReal (Real.log (1 + 1 ^ 2 / θ ^ 2)) ∂U := by
            rw [lintegral_const_mul' _ _ (by norm_num)]
        _ ≤ 2 * ∫⁻ θ, ENNReal.ofReal (Real.log (1 + 1 ^ 2 / θ ^ 2)) ∂U :=
            mul_le_mul_right (setLIntegral_le_lintegral _ _) 2
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top (by norm_num) hlog) hb

/-! ## The Tonelli step -/

/-- **The Frullani identity under the Thorin integral.** For a folded `U`, the profile integral
of `eq:sd-profile` taken against the Laplace transform of `U` is the Thorin integral of
`eq:thorin`.

This is exactly the computation the node's annotation says ledger A11 does **not** carry: the
elementary integral of `prop:matern-exponent`(1), here `integral_frullani`, and the Tonelli that
turns the mixture into `eq:thorin`. -/
theorem thorin_frullani {U : Measure ℝ} [SFinite U] (hU : IsFolded U) (ω : ℝ) :
    (∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal ((1 - Real.cos (ω * x)) / x) * laplaceL U x)
      = ENNReal.ofReal 2⁻¹ * ∫⁻ θ, ENNReal.ofReal (Real.log (1 + ω ^ 2 / θ ^ 2)) ∂U := by
  have hmeas : Measurable (Function.uncurry
      (fun (x θ : ℝ) => ENNReal.ofReal ((1 - Real.cos (ω * x)) / x)
        * ENNReal.ofReal (Real.exp (-(x * θ))))) := by
    unfold Function.uncurry
    fun_prop
  have hstep1 : (∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal ((1 - Real.cos (ω * x)) / x) * laplaceL U x)
      = ∫⁻ x in Ioi (0 : ℝ), ∫⁻ θ, ENNReal.ofReal ((1 - Real.cos (ω * x)) / x)
          * ENNReal.ofReal (Real.exp (-(x * θ))) ∂U := by
    refine lintegral_congr fun x => ?_
    rw [laplaceL, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [hstep1, lintegral_lintegral_swap hmeas.aemeasurable]
  have hae : ∀ᵐ θ ∂U, 0 < θ := by
    rw [ae_iff]
    refine measure_mono_null (fun θ hθ => ?_) hU
    simpa using not_lt.mp hθ
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr_ae ?_
  filter_upwards [hae] with θ hθ
  have hinner : (∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal ((1 - Real.cos (ω * x)) / x)
        * ENNReal.ofReal (Real.exp (-(x * θ))))
      = ∫⁻ x in Ioi (0 : ℝ),
          ENNReal.ofReal ((1 - Real.cos (ω * x)) * Real.exp (-(θ * x)) / x) := by
    refine setLIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx0 : (0 : ℝ) < x := hx
    have hnn : 0 ≤ (1 - Real.cos (ω * x)) / x := by
      have := Real.cos_le_one (ω * x)
      positivity
    rw [← ENNReal.ofReal_mul hnn]
    congr 1
    rw [mul_comm x θ]
    field_simp
  rw [hinner]
  have hint := integrableOn_frullani hθ ω
  have hnn : ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))),
      0 ≤ (1 - Real.cos (ω * x)) * Real.exp (-(θ * x)) / x := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun x hx => ?_)
    have hx0 : (0 : ℝ) < x := hx
    have h1 := Real.cos_le_one (ω * x)
    have h2 := (Real.exp_pos (-(θ * x))).le
    positivity
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, integral_frullani hθ ω]
  rw [show (1 : ℝ)/2 = 2⁻¹ by norm_num,
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2⁻¹)]


theorem exp_neg_le_four_div_sq {y : ℝ} (hy : 0 < y) : Real.exp (-y) ≤ 4 / y ^ 2 := by
  have h1 : y / 2 ≤ Real.exp (y / 2) := by
    have := Real.add_one_le_exp (y / 2); linarith
  have h2 : y ^ 2 / 4 ≤ Real.exp y := by
    have hy2 : (0 : ℝ) < y / 2 := by linarith
    have : Real.exp (y / 2) * Real.exp (y / 2) = Real.exp y := by
      rw [← Real.exp_add]; ring_nf
    nlinarith [Real.exp_pos (y / 2)]
  have h3 : (0 : ℝ) < y ^ 2 / 4 := by positivity
  rw [Real.exp_neg, inv_le_iff_one_le_mul₀ (Real.exp_pos y)]
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0 : ℝ) < y ^ 2)]
  nlinarith

theorem laplaceL_ne_top_of_facts {U : Measure ℝ} (hU : IsFolded U)
    (h1 : U (Ioc (0 : ℝ) 1) ≠ ⊤) (h2 : (∫⁻ θ in Ioi (1 : ℝ), ENNReal.ofReal ((θ ^ 2)⁻¹) ∂U) ≠ ⊤)
    {x : ℝ} (hx : 0 < x) : laplaceL U x ≠ ⊤ := by
  have hae : ∀ᵐ θ ∂U, θ ∈ Ioi (0 : ℝ) := by
    rw [ae_iff]
    refine measure_mono_null (fun θ hθ => ?_) hU
    simpa using not_lt.mp (by simpa using hθ)
  have hres : U.restrict (Ioi (0 : ℝ)) = U := Measure.restrict_eq_self_of_ae_mem hae
  have hsplit : Ioi (0 : ℝ) = Ioc (0 : ℝ) 1 ∪ Ioi 1 := (Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  have hdisj : Disjoint (Ioc (0 : ℝ) 1) (Ioi 1) := Ioc_disjoint_Ioi le_rfl
  rw [laplaceL, ← hres, hsplit, lintegral_union measurableSet_Ioi hdisj]
  refine ENNReal.add_ne_top.mpr ⟨?_, ?_⟩
  · refine ne_top_of_le_ne_top h1 ?_
    calc (∫⁻ θ in Ioc (0 : ℝ) 1, ENNReal.ofReal (Real.exp (-(x * θ))) ∂U)
        ≤ ∫⁻ _ in Ioc (0 : ℝ) 1, 1 ∂U := by
          refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioc).mpr
            (.of_forall fun θ hθ => ?_))
          have : Real.exp (-(x * θ)) ≤ 1 := by
            rw [Real.exp_le_one_iff]
            nlinarith [hθ.1, hx]
          simpa using ENNReal.ofReal_le_one.mpr this
      _ = U (Ioc (0 : ℝ) 1) := by rw [setLIntegral_one]
  · refine ne_top_of_le_ne_top
      (ENNReal.mul_ne_top (a := ENNReal.ofReal (4 / x ^ 2)) ENNReal.ofReal_ne_top h2) ?_
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioi).mpr
      (.of_forall fun θ hθ => ?_))
    have hθ0 : (1 : ℝ) < θ := hθ
    have hxθ : (0 : ℝ) < x * θ := by nlinarith
    have hb := exp_neg_le_four_div_sq hxθ
    have heq : (4 : ℝ) / (x * θ) ^ 2 = 4 / x ^ 2 * (θ ^ 2)⁻¹ := by
      field_simp
    rw [heq] at hb
    calc ENNReal.ofReal (Real.exp (-(x * θ)))
        ≤ ENNReal.ofReal (4 / x ^ 2 * (θ ^ 2)⁻¹) := ENNReal.ofReal_le_ofReal hb
      _ = ENNReal.ofReal (4 / x ^ 2) * ENNReal.ofReal ((θ ^ 2)⁻¹) := by
          rw [ENNReal.ofReal_mul (by positivity)]



theorem integrable_exp_neg_mul {U : Measure ℝ} {x : ℝ}
    (hfin : laplaceL U x ≠ ⊤) : Integrable (fun θ : ℝ => Real.exp (-(x * θ))) U := by
  refine ⟨(by fun_prop : Continuous fun θ : ℝ => Real.exp (-(x * θ))).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (.of_forall fun θ => (Real.exp_pos _).le)]
  exact lt_top_iff_ne_top.mpr hfin

theorem laplaceReal_eq_integral (U : Measure ℝ) (x : ℝ) :
    (laplaceL U x).toReal = ∫ θ, Real.exp (-(x * θ)) ∂U := by
  rw [integral_eq_lintegral_of_nonneg_ae (.of_forall fun θ => (Real.exp_pos _).le)
    (by fun_prop : Continuous fun θ : ℝ => Real.exp (-(x * θ))).aestronglyMeasurable]
  rfl

theorem continuousOn_laplaceReal {U : Measure ℝ} (hU : IsFolded U)
    (hfin : ∀ x : ℝ, 0 < x → laplaceL U x ≠ ⊤) :
    ContinuousOn (fun x => (laplaceL U x).toReal) (Ioi 0) := by
  have hae : ∀ᵐ θ ∂U, θ ∈ Ioi (0 : ℝ) := by
    rw [ae_iff]
    refine measure_mono_null (fun θ hθ => ?_) hU
    simpa using not_lt.mp (by simpa using hθ)
  have hcont : ∀ x₀ : ℝ, 0 < x₀ →
      ContinuousAt (fun x => ∫ θ, Real.exp (-(x * θ)) ∂U) x₀ := by
    intro x₀ hx₀
    refine continuousAt_of_dominated (bound := fun θ => Real.exp (-(x₀ / 2 * θ)))
      (.of_forall fun x =>
        (by fun_prop : Continuous fun θ : ℝ => Real.exp (-(x * θ))).aestronglyMeasurable)
      ?_ (integrable_exp_neg_mul (hfin _ (by linarith))) ?_
    · filter_upwards [eventually_gt_nhds (by linarith : x₀ / 2 < x₀)] with x hxx
      filter_upwards [hae] with θ hθ
      have hθ0 : (0 : ℝ) < θ := hθ
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (by nlinarith)
    · exact .of_forall fun θ => by fun_prop
  refine ContinuousOn.congr (fun x hx => (hcont x hx).continuousWithinAt) ?_
  intro x _
  exact laplaceReal_eq_integral U x

theorem lintegral_gaussian_one_sub_cos (x : ℝ) :
    (∫⁻ ω, ENNReal.ofReal (1 - Real.cos (ω * x))
        ∂(ProbabilityTheory.gaussianReal 0 1))
      = ENNReal.ofReal (1 - Real.exp (-(x ^ 2 / 2))) := by
  set N := ProbabilityTheory.gaussianReal 0 1 with hN
  have hcos : Integrable (fun ω : ℝ => Real.cos (ω * x)) N := by
    refine Integrable.mono' (integrable_const 1) (by fun_prop) (.of_forall fun ω => ?_)
    simpa using Real.abs_cos_le_one (ω * x)
  have hint : Integrable (fun ω : ℝ => 1 - Real.cos (ω * x)) N :=
    (integrable_const 1).sub hcos
  have hnn : ∀ᵐ ω ∂N, 0 ≤ 1 - Real.cos (ω * x) :=
    .of_forall fun ω => by linarith [Real.cos_le_one (ω * x)]
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
  congr 1
  rw [integral_sub (integrable_const 1) hcos]
  have hval : (∫ ω, Real.cos (ω * x) ∂N) = Real.exp (-(x ^ 2 / 2)) := by
    have : (∫ ω, Real.cos (ω * x) ∂N) = fourierCos N x := by
      rw [fourierCos_apply]
      exact integral_congr_ae (.of_forall fun ω => by simp [mul_comm])
    rw [this, hN, fourierCos_gaussianReal]
    norm_num
  rw [hval]
  simp



theorem gaussianWeight_le (x : ℝ) : 1 - Real.exp (-(x ^ 2 / 2)) ≤ min 1 (x ^ 2) := by
  have h1 : Real.exp (-(x ^ 2 / 2)) ≥ 1 - x ^ 2 / 2 := by
    have := Real.add_one_le_exp (-(x ^ 2 / 2))
    linarith
  have h2 : (0 : ℝ) < Real.exp (-(x ^ 2 / 2)) := Real.exp_pos _
  refine le_min (by linarith) (by nlinarith [sq_nonneg x])

theorem le_gaussianWeight (x : ℝ) : min 1 (x ^ 2) / 3 ≤ 1 - Real.exp (-(x ^ 2 / 2)) := by
  have hu : (0 : ℝ) ≤ x ^ 2 / 2 := by positivity
  have hexp : Real.exp (x ^ 2 / 2) ≥ 1 + x ^ 2 / 2 := by
    have := Real.add_one_le_exp (x ^ 2 / 2); linarith
  have hpos : (0 : ℝ) < 1 + x ^ 2 / 2 := by positivity
  have hle : Real.exp (-(x ^ 2 / 2)) ≤ (1 + x ^ 2 / 2)⁻¹ := by
    rw [Real.exp_neg, inv_le_inv₀ (Real.exp_pos _) hpos]
    exact hexp
  have hkey : 1 - (1 + x ^ 2 / 2)⁻¹ = x ^ 2 / (2 + x ^ 2) := by
    have h2 : (0 : ℝ) < 2 + x ^ 2 := by positivity
    field_simp
    ring
  have hb : min 1 (x ^ 2) / 3 ≤ x ^ 2 / (2 + x ^ 2) := by
    have h2 : (0 : ℝ) < 2 + x ^ 2 := by positivity
    rcases le_total (x ^ 2) 1 with h | h
    · rw [min_eq_right h, div_le_div_iff₀ (by norm_num) h2]
      nlinarith [sq_nonneg x]
    · rw [min_eq_left h, div_le_div_iff₀ (by norm_num) h2]
      nlinarith
  linarith

theorem gaussian_average_profileJump {k : ℝ → ℝ}
    (hkm : AEMeasurable k (volume.restrict (Ioi (0 : ℝ)))) (hk₀ : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ k x) :
    (∫⁻ ω, profileJumpL k ω ∂(ProbabilityTheory.gaussianReal 0 1))
      = ∫⁻ x, ENNReal.ofReal (1 - Real.exp (-(x ^ 2 / 2))) ∂(profileMeasure k) := by
  have hmeas : Measurable (Function.uncurry
      (fun (ω x : ℝ) => ENNReal.ofReal (1 - Real.cos (ω * x)))) := by
    unfold Function.uncurry
    fun_prop
  have hstep : (∫⁻ ω, profileJumpL k ω ∂(ProbabilityTheory.gaussianReal 0 1))
      = ∫⁻ ω, (∫⁻ x, ENNReal.ofReal (1 - Real.cos (ω * x)) ∂(profileMeasure k))
          ∂(ProbabilityTheory.gaussianReal 0 1) := by
    refine lintegral_congr fun ω => ?_
    rw [lintegral_one_sub_cos_profileMeasure hk₀ hkm ω]
  rw [hstep, lintegral_lintegral_swap hmeas.aemeasurable]
  refine lintegral_congr fun x => ?_
  exact lintegral_gaussian_one_sub_cos x

theorem lintegral_min_ne_top_of_profileJump_eq {k₁ k₂ : ℝ → ℝ}
    (h₁m : AEMeasurable k₁ (volume.restrict (Ioi (0 : ℝ)))) (h₁₀ : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ k₁ x)
    (h₂m : AEMeasurable k₂ (volume.restrict (Ioi (0 : ℝ)))) (h₂₀ : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ k₂ x)
    (hfin : (∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂(profileMeasure k₁)) ≠ ⊤)
    (heq : ∀ ω : ℝ, profileJumpL k₁ ω = profileJumpL k₂ ω) :
    (∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂(profileMeasure k₂)) ≠ ⊤ := by
  have hup : ∀ ν : Measure ℝ, (∫⁻ x, ENNReal.ofReal (1 - Real.exp (-(x ^ 2 / 2))) ∂ν)
      ≤ ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν := fun ν =>
    lintegral_mono fun x => ENNReal.ofReal_le_ofReal (gaussianWeight_le x)
  have hlow : ∀ ν : Measure ℝ, (∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν)
      ≤ 3 * ∫⁻ x, ENNReal.ofReal (1 - Real.exp (-(x ^ 2 / 2))) ∂ν := by
    intro ν
    rw [← lintegral_const_mul' _ _ (by norm_num)]
    refine lintegral_mono fun x => ?_
    have h := le_gaussianWeight x
    calc ENNReal.ofReal (min 1 (x ^ 2))
        ≤ ENNReal.ofReal (3 * (1 - Real.exp (-(x ^ 2 / 2)))) := by
          refine ENNReal.ofReal_le_ofReal ?_
          linarith
      _ = 3 * ENNReal.ofReal (1 - Real.exp (-(x ^ 2 / 2))) := by
          rw [ENNReal.ofReal_mul (by norm_num)]
          norm_num
  have hmid : (∫⁻ x, ENNReal.ofReal (1 - Real.exp (-(x ^ 2 / 2))) ∂(profileMeasure k₂))
      = ∫⁻ x, ENNReal.ofReal (1 - Real.exp (-(x ^ 2 / 2))) ∂(profileMeasure k₁) := by
    rw [← gaussian_average_profileJump h₂m h₂₀, ← gaussian_average_profileJump h₁m h₁₀]
    exact (lintegral_congr fun ω => (heq ω).symm)
  have hchain : (∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂(profileMeasure k₂))
      ≤ 3 * ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂(profileMeasure k₁) := by
    calc (∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂(profileMeasure k₂))
        ≤ 3 * ∫⁻ x, ENNReal.ofReal (1 - Real.exp (-(x ^ 2 / 2))) ∂(profileMeasure k₂) :=
          hlow _
      _ = 3 * ∫⁻ x, ENNReal.ofReal (1 - Real.exp (-(x ^ 2 / 2))) ∂(profileMeasure k₁) := by
          rw [hmid]
      _ ≤ 3 * ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂(profileMeasure k₁) := by
          exact mul_le_mul_right (hup _) 3
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top (by norm_num) hfin) hchain


/-- The Thorin integral is finite at every frequency, for any `U` representing an admissible
exponent: the exponent is finite (`lem:quadratic-growth`) and the Gaussian term is. -/
theorem thorin_lintegral_ne_top {P : SDProfile} {U : Measure ℝ}
    (hrep : ∀ ω : ℝ, P.exponentL ω = thorinExponentL P.a U ω) (ω : ℝ) :
    (∫⁻ θ, ENNReal.ofReal (Real.log (1 + ω ^ 2 / θ ^ 2)) ∂U) ≠ ⊤ := by
  intro hcon
  have h := P.exponentL_ne_top ω
  rw [hrep ω, thorinExponentL, hcon,
    ENNReal.mul_top (by simp : ENNReal.ofReal (2 : ℝ)⁻¹ ≠ 0)] at h
  simp at h

/-- **From the Laplace representation of the profile to the Thorin representation.**

The forward half of the correspondence, and the one that needs no interface: if the profile is
the Laplace transform of a folded `U` on `(0,∞)`, the exponent is `eq:thorin` at `U`. It is
`thorin_frullani` with the transform substituted for the profile, and it is used twice — by
`thorin_subclass_representation`'s forward direction and by the stable corner's Thorin
density. -/
theorem thorin_of_laplace {P : SDProfile} {U : Measure ℝ} [SFinite U] (hU : IsFolded U)
    (hlap : ∀ x : ℝ, 0 < x → ENNReal.ofReal (P.k x) = laplaceL U x) (ω : ℝ) :
    P.exponentL ω = thorinExponentL P.a U ω := by
  have hj : profileJumpL P.k ω
      = ENNReal.ofReal 2⁻¹ * ∫⁻ θ, ENNReal.ofReal (Real.log (1 + ω ^ 2 / θ ^ 2)) ∂U := by
    rw [← thorin_frullani hU ω, profileJumpL]
    refine setLIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx0 : (0 : ℝ) < x := hx
    have hnn : 0 ≤ (1 - Real.cos (ω * x)) / x := by
      have := Real.cos_le_one (ω * x)
      positivity
    rw [← hlap x hx0, ← ENNReal.ofReal_mul hnn]
    congr 1
    field_simp
  rw [P.exponentL_eq_add_jump ω, hj, thorinExponentL]

/-- **From the Thorin representation to the Laplace representation of the profile.**

If a folded `U` represents an admissible exponent through `eq:thorin`, then the profile `k` *is*
the Laplace transform of `U` on `(0,∞)`, pointwise.

This is the load-bearing step of `prop:thorin-subclass`(1) iff (2), and it is what both
directions of the node run on: the converse gets complete monotonicity of `k` by feeding it back
to Bernstein's theorem, and the uniqueness clause gets `U' = U` from it by
`prop:laplace-uniqueness-locally-finite`.

**Spends ledger A3** through `fourier_toolbox_levy_unique`, and nothing else. The route:
`thorin_frullani` turns the Thorin integral into the jump part of the profile `k'` defined as
the transform of `U`, so `k` and `k'` have the same jump part at every frequency; the Gaussian
average of that identity carries the Lévy condition from `k` to `k'`
(`lintegral_min_ne_top_of_profileJump_eq`), which is what makes `k'` the profile of a symmetric
Lévy pair at all; uniqueness of the pair identifies the two profile measures; and
`eqOn_of_profileMeasure_eq` turns that into a pointwise identity on `(0,∞)`, `k'` being
continuous there and `k` antitone. -/
theorem laplaceL_eq_of_thorin {P : SDProfile} {U : Measure ℝ} (hU : IsFolded U)
    (hrep : ∀ ω : ℝ, P.exponentL ω = thorinExponentL P.a U ω) :
    ∀ x : ℝ, 0 < x → laplaceL U x ≠ ⊤ ∧ P.k x = (laplaceL U x).toReal := by
  obtain ⟨hsig, hU1, hUlog, hUsq⟩ :=
    thorin_measure_facts hU (thorin_lintegral_ne_top hrep 1)
  haveI : SigmaFinite U := hsig
  have hLfin : ∀ x : ℝ, 0 < x → laplaceL U x ≠ ⊤ := fun x hx =>
    laplaceL_ne_top_of_facts hU hU1 hUsq hx
  set k' : ℝ → ℝ := fun x => (laplaceL U x).toReal with hk'def
  have hk'ofReal : ∀ x : ℝ, 0 < x → ENNReal.ofReal (k' x) = laplaceL U x := fun x hx =>
    ENNReal.ofReal_toReal (hLfin x hx)
  have hk'nonneg : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ k' x := fun x _ => ENNReal.toReal_nonneg
  have hk'cont : ContinuousOn k' (Ioi 0) := continuousOn_laplaceReal hU hLfin
  have hk'meas : AEMeasurable k' (volume.restrict (Ioi (0 : ℝ))) :=
    hk'cont.aemeasurable measurableSet_Ioi
  -- The jump part of `k'` is the Thorin integral.
  have hjump : ∀ ω : ℝ, profileJumpL k' ω
      = ENNReal.ofReal 2⁻¹ * ∫⁻ θ, ENNReal.ofReal (Real.log (1 + ω ^ 2 / θ ^ 2)) ∂U := by
    intro ω
    rw [← thorin_frullani hU ω, profileJumpL]
    refine setLIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx0 : (0 : ℝ) < x := hx
    have hnn : 0 ≤ (1 - Real.cos (ω * x)) / x := by
      have := Real.cos_le_one (ω * x)
      positivity
    rw [← hk'ofReal x hx0, ← ENNReal.ofReal_mul hnn]
    congr 1
    field_simp
  -- The two profiles have the same jump part.
  have hjumpeq : ∀ ω : ℝ, profileJumpL P.k ω = profileJumpL k' ω := by
    intro ω
    have h := hrep ω
    rw [P.exponentL_eq_add_jump ω, thorinExponentL, ← hjump ω] at h
    exact (ENNReal.add_right_inj (by simp)).mp h
  -- The Lévy condition transfers to `k'`.
  have hkm : AEMeasurable P.k (volume.restrict (Ioi (0 : ℝ))) :=
    aemeasurable_restrict_of_antitoneOn measurableSet_Ioi P.k_antitone
  have hPfin : (∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂(profileMeasure P.k)) ≠ ⊤ :=
    (profile_integrability P.k_nonneg hkm).mpr ⟨P.integrable_near_zero, P.integrable_at_top⟩
  have hk'fin : (∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂(profileMeasure k')) ≠ ⊤ :=
    lintegral_min_ne_top_of_profileJump_eq hkm P.k_nonneg hk'meas hk'nonneg hPfin hjumpeq
  -- Two symmetric Lévy pairs with the same exponent.
  obtain ⟨Q, hQa, hQν, hQe⟩ := profile_integrability_pair P
  set Q' : SymLevyPair :=
    ⟨P.a, profileMeasure k', P.a_nonneg, isFolded_profileMeasure k', hk'fin⟩ with hQ'def
  have hsame : ∀ ω, Q.exponent ω = Q'.exponent ω := by
    intro ω
    have h1 : Q.exponentL ω = P.exponentL ω :=
      (exponentL_eq_of_profileMeasure P Q hQa hQν ω).symm
    have h2 : Q'.exponentL ω = ENNReal.ofReal (P.a * ω ^ 2) + profileJumpL k' ω := by
      rw [SymLevyPair.exponentL]
      congr 1
      exact lintegral_one_sub_cos_profileMeasure hk'nonneg hk'meas ω
    rw [SymLevyPair.exponent, SymLevyPair.exponent, h1, h2, P.exponentL_eq_add_jump ω, hjumpeq ω]
  obtain ⟨-, hνeq⟩ := fourier_toolbox_levy_unique Q Q' hsame
  have hprof : profileMeasure P.k = profileMeasure k' := by rw [← hQν, hνeq]
  have heqOn : Set.EqOn P.k k' (Ioi 0) :=
    eqOn_of_profileMeasure_eq P.k_antitone P.k_nonneg hk'meas hk'nonneg hk'cont hprof
  exact fun x hx => ⟨hLfin x hx, heqOn hx⟩

/-! ## The node -/

/-- **`prop:thorin-subclass`, (1) iff (2).** An admissible exponent has a completely monotone
profile exactly when it has a symmetric Thorin representation, and the Thorin measure is unique.

**Spends ledger A11** (`bernstein_completely_monotone`, the existence equivalence only) and
ledger **A3** (`fourier_toolbox_levy_unique`, through `laplaceL_eq_of_thorin`). Everything else
is `[T]`: the elementary integral and its Tonelli, the integrability correspondence, the
exclusion of an atom of `U` at the origin, and — the article's own economy — the uniqueness of
the Thorin measure, which is `prop:laplace-uniqueness-locally-finite` and not A11's uniqueness
clause. -/
theorem thorin_subclass_representation (P : SDProfile) :
    IsCompletelyMonotone P.k ↔
      ∃ U : Measure ℝ, IsFolded U ∧
        (∫⁻ θ in Ioc (0 : ℝ) 1, ENNReal.ofReal (Real.log θ⁻¹) ∂U
          + ∫⁻ θ in Ioi (1 : ℝ), ENNReal.ofReal (θ ^ (-2 : ℝ)) ∂U ≠ ⊤) ∧
        (∀ ω : ℝ, P.exponentL ω = thorinExponentL P.a U ω) ∧
        ∀ U' : Measure ℝ, IsFolded U' →
          (∀ ω : ℝ, P.exponentL ω = thorinExponentL P.a U' ω) → U' = U := by
  constructor
  · intro hcm
    obtain ⟨U, hUneg, hUlap⟩ := (bernstein_completely_monotone P.k).mp hcm
    -- Bernstein's measure has no atom at the origin: one would bound `k` below by a positive
    -- constant, and `k` tends to `0` at infinity.
    have hUzero : U {(0 : ℝ)} = 0 := by
      by_contra hc
      have hcle : ∀ x : ℝ, 0 < x → U {(0 : ℝ)} ≤ laplaceL U x := by
        intro x hx
        have hone : (∫⁻ θ in {(0 : ℝ)}, ENNReal.ofReal (Real.exp (-(x * θ))) ∂U)
            = U {(0 : ℝ)} := by
          rw [setLIntegral_congr_fun (measurableSet_singleton (0 : ℝ))
            (g := fun _ => (1 : ℝ≥0∞))
            (fun θ hθ => by rw [show θ = 0 from hθ]; simp), setLIntegral_one]
        rw [← hone]
        exact setLIntegral_le_lintegral _ _
      have hUne : U {(0 : ℝ)} ≠ ⊤ :=
        ne_top_of_le_ne_top (hUlap 1 one_pos).1 (hcle 1 one_pos)
      set c : ℝ := (U {(0 : ℝ)}).toReal with hcdef
      have hcpos : 0 < c := ENNReal.toReal_pos hc hUne
      have hge : ∀ x : ℝ, 0 < x → c ≤ P.k x := by
        intro x hx
        rw [(hUlap x hx).2]
        exact ENNReal.toReal_mono (hUlap x hx).1 (hcle x hx)
      have hev : ∀ᶠ x in atTop, P.k x < c := P.tendsto_k_atTop (Iio_mem_nhds hcpos)
      obtain ⟨x, hx1, hx2⟩ := (hev.and (eventually_gt_atTop (0 : ℝ))).exists
      exact absurd (hge x hx2) (not_le.mpr hx1)
    have hUfold : IsFolded U := by
      have hsub : Iic (0 : ℝ) = Iio (0 : ℝ) ∪ {(0 : ℝ)} := by
        ext y; simp [le_iff_lt_or_eq]
      rw [IsFolded, hsub]
      exact measure_union_null hUneg hUzero
    -- The transform is finite at `1`, so `U` is σ-finite and Tonelli applies.
    haveI hsig : SigmaFinite U := by
      refine sigmaFinite_of_lintegral_ne_top
        (g := fun θ : ℝ => ENNReal.ofReal (Real.exp (-(1 * θ)))) (by fun_prop) ?_
        (hUlap 1 one_pos).1
      have hempty : {y : ℝ | ENNReal.ofReal (Real.exp (-(1 * y))) = 0} = ∅ := by
        ext y
        simp [ENNReal.ofReal_eq_zero, not_le, Real.exp_pos]
      rw [hempty]
      exact measure_empty
    have hrep : ∀ ω : ℝ, P.exponentL ω = thorinExponentL P.a U ω :=
      thorin_of_laplace hUfold fun x hx => by
        rw [(hUlap x hx).2]
        exact ENNReal.ofReal_toReal (hUlap x hx).1
    refine ⟨U, hUfold, ?_, hrep, ?_⟩
    · obtain ⟨-, -, hlogint, hsqint⟩ :=
        thorin_measure_facts hUfold (thorin_lintegral_ne_top hrep 1)
      have hconv : (∫⁻ θ in Ioi (1 : ℝ), ENNReal.ofReal (θ ^ (-2 : ℝ)) ∂U)
          = ∫⁻ θ in Ioi (1 : ℝ), ENNReal.ofReal ((θ ^ 2)⁻¹) ∂U := by
        refine setLIntegral_congr_fun measurableSet_Ioi fun θ hθ => ?_
        have hθ0 : (0 : ℝ) < θ := lt_trans one_pos hθ
        congr 1
        rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hθ0.le, Real.rpow_natCast]
      rw [hconv]
      exact ENNReal.add_ne_top.mpr ⟨hlogint, hsqint⟩
    · intro U' hU' hrep'
      have h' := laplaceL_eq_of_thorin hU' hrep'
      refine laplace_uniqueness_locally_finite (τ₀ := 0) hU' hUfold (fun τ hτ => ?_)
        (fun τ hτ => (h' τ hτ).1)
      have e1 : laplaceL U' τ = ENNReal.ofReal (P.k τ) := by
        rw [(h' τ hτ).2]
        exact (ENNReal.ofReal_toReal (h' τ hτ).1).symm
      have e2 : laplaceL U τ = ENNReal.ofReal (P.k τ) := by
        rw [(hUlap τ hτ).2]
        exact (ENNReal.ofReal_toReal (hUlap τ hτ).1).symm
      rw [e1, e2]
  · rintro ⟨U, hUfold, -, hrep, -⟩
    exact (bernstein_completely_monotone P.k).mpr
      ⟨U, measure_mono_null Iio_subset_Iic_self hUfold, laplaceL_eq_of_thorin hUfold hrep⟩

end SpatialLine
