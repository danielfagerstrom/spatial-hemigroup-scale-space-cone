/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.CinMoment
import SpatialLine.CosineUniqueness

/-!
# `lem:cin-delay-equation`: the reduction of the derivative form to the measure form

Blueprint: `blueprint/src/parts/08-cone.tex`, `lem:cin-delay-equation`.

Wave 3 recorded, at `Skeleton.cin_delay_equation_deriv`, that read through
`∫ p·g dx = ∫ g dμ` both of the node's forms are statements about `μ` alone, and that the
derivative form is equivalent to

`∫ (x φ(x))' dμ(x) = ½∫ [φ(x+τ) + φ(x−τ)] dμ(x)` for every test `φ`,

in which neither the density nor its nonnegativity appears. That reduction is what this file
proves — not as a reduction of one `sorry` to another, but as a theorem taking the measure form
as a **hypothesis** and delivering the node's declaration. The measure form is then a target
that can be attacked without the density, and this theorem is what connects it back.

## What writing it down found

**At the measure level the node's two forms are the same statement, and the recorded ordering
between them is about the density forms only.** Wave 2 priced the primitive form above the
derivative form because applying Fourier uniqueness to `x p` presupposes the first absolute
moment; wave 3 proved the moment and re-read the ordering as "the derivative form needs no
signed-measure uniqueness and pays for it with a Parseval step instead". Both readings are
about `p`. Read at `μ`, one integration by parts turns the measure form into

`x·μ(dx) = (P(x) − ½[P(x−τ) + P(x+τ)]) dx`,

an identity between two **finite signed measures** on the line --- the left one finite by
`cin_law_integrable_abs`, the right one because `∫|P(·+τ) − P| ≤ τ` --- whose right-hand side is
the primitive form's. So the primitive form is not the harder of the two; it is the *same* one,
written without a test function, and what separates them from the node's two declarations is
only the passage to a density. The obligation that remains is therefore a single one: match the
two characteristic functions and appeal to `Measure.ext_of_charFun` at the Jordan
recombination, exactly as `ae_eq_zero_of_even_of_integral_cos_eq_zero` does in chapter 3. Its
inputs are the differentiation of `fourierCos μ` under the integral sign (justified by the
moment) and the elementary ODE `ω·c'(ω) = −c(ω)(1 − cos τω)`, which is `hasDerivAt_cin` and the
chain rule at `c = e^{−Cin(τ·)}`.

**One hypothesis the reviewed statement does not carry is needed here.** The node quantifies
over any `p` with `μ = volume.withDensity (ofReal ∘ p)` and `0 ≤ᵐ p`, and does not ask `p` to be
measurable. Every change of variables between `∫ · dμ` and `∫ p · dx` does
(`integral_withDensity_eq_integral_smul₀` asks for `AEMeasurable`), so this theorem carries
`AEMeasurable p volume` explicitly. Whether the node's own statement should carry it is a
review question, not a prover's: it is satisfied at every call site, the densities being
produced by `prop:kernel-regularity`.

Proving campaign, wave 5, chapter 8 (2026-09-10).
-/

namespace SpatialLine

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

/-- Reading an integral against a measure with density `p` as an integral against Lebesgue
measure. Unconditional in `g`: `integral_withDensity_eq_integral_smul₀` is an identity between
two Bochner integrals, junk on both sides where the integrand is not integrable. -/
theorem integral_eq_integral_density {μ : Measure ℝ} {p : ℝ → ℝ}
    (hpmeas : AEMeasurable p volume) (hpos : 0 ≤ᵐ[volume] p)
    (hp : μ = volume.withDensity fun x => ENNReal.ofReal (p x)) (g : ℝ → ℝ) :
    ∫ x, g x ∂μ = ∫ x, p x * g x := by
  have hcast : (fun x : ℝ => ENNReal.ofReal (p x))
      = fun x : ℝ => (((p x).toNNReal : ℝ≥0) : ℝ≥0∞) := rfl
  rw [hp, hcast, integral_withDensity_eq_integral_smul₀ hpmeas.real_toNNReal]
  refine integral_congr_ae ?_
  filter_upwards [hpos] with x hx
  simp only [Pi.zero_apply] at hx
  simp only [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ hx]

/-- A density of a probability measure is integrable. -/
theorem integrable_density {μ : Measure ℝ} [IsProbabilityMeasure μ] {p : ℝ → ℝ}
    (hpmeas : AEMeasurable p volume) (hpos : 0 ≤ᵐ[volume] p)
    (hp : μ = volume.withDensity fun x => ENNReal.ofReal (p x)) :
    Integrable p volume := by
  refine ⟨hpmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal hpos]
  have hmass : (∫⁻ x, ENNReal.ofReal (p x) ∂(volume : Measure ℝ)) = μ univ := by
    rw [hp, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [hmass, measure_univ]
  exact ENNReal.one_lt_top

/-- **`lem:cin-delay-equation`, the derivative form, from the measure form.**

The hypothesis is the reduced target recorded at `Skeleton.cin_delay_equation_deriv`: an
identity between two integrals against `μ` alone, with no density in it. The conclusion is the
node's declaration verbatim. Nothing about `Cin` is used --- the reduction is the change of
variables `∫ g dμ = ∫ p·g dx` and two translations of Lebesgue measure --- so the same theorem
serves any law with a density. -/
theorem cin_delay_deriv_of_measure_form {τ : ℝ} (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (p : ℝ → ℝ) (hpmeas : AEMeasurable p volume) (hpos : 0 ≤ᵐ[volume] p)
    (hp : μ = volume.withDensity fun x => ENNReal.ofReal (p x))
    (hform : ∀ φ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
      ∫ x, deriv (fun y => y * φ y) x ∂μ = ∫ x, (φ (x + τ) + φ (x - τ)) / 2 ∂μ) :
    ∀ φ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
      -∫ x, p x * deriv (fun y => y * φ y) x
        = -∫ x, (p (x - τ) + p (x + τ)) / 2 * φ x := by
  have hpint : Integrable p volume := integrable_density hpmeas hpos hp
  have hchange := integral_eq_integral_density hpmeas hpos hp
  intro φ hφ hsupp
  have hφcont : Continuous φ := hφ.continuous
  obtain ⟨C, hC⟩ := hsupp.exists_bound_of_continuous hφcont
  -- the four integrability facts the splitting needs
  have hb1 : Integrable (fun x : ℝ => p x * φ (x + τ)) volume := by
    have := hpint.bdd_mul (c := C)
      ((hφcont.comp (continuous_id.add continuous_const)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => hC (x + τ))
    simpa [mul_comm] using this
  have hb2 : Integrable (fun x : ℝ => p x * φ (x - τ)) volume := by
    have := hpint.bdd_mul (c := C)
      ((hφcont.comp (continuous_id.sub continuous_const)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => hC (x - τ))
    simpa [mul_comm] using this
  have hb3 : Integrable (fun x : ℝ => p (x - τ) * φ x) volume := by
    have := (integrable_translate hpint τ).bdd_mul (c := C)
      hφcont.aestronglyMeasurable (Filter.Eventually.of_forall hC)
    simpa [mul_comm] using this
  have hb4 : Integrable (fun x : ℝ => p (x + τ) * φ x) volume := by
    have hshift : Integrable (fun x : ℝ => p (x + τ)) volume := by
      simpa [sub_neg_eq_add] using integrable_translate hpint (-τ)
    have := hshift.bdd_mul (c := C)
      hφcont.aestronglyMeasurable (Filter.Eventually.of_forall hC)
    simpa [mul_comm] using this
  -- the two translations
  have e1 : ∫ x, p (x - τ) * φ x = ∫ x, p x * φ (x + τ) := by
    have h := integral_sub_right_eq_self (μ := (volume : Measure ℝ))
      (fun y : ℝ => p y * φ (y + τ)) τ
    simpa using h
  have e2 : ∫ x, p (x + τ) * φ x = ∫ x, p x * φ (x - τ) := by
    have h := integral_add_right_eq_self (μ := (volume : Measure ℝ))
      (fun y : ℝ => p y * φ (y - τ)) τ
    simpa using h
  -- the two splittings
  have hL : ∫ x, p x * ((φ (x + τ) + φ (x - τ)) / 2)
      = ((∫ x, p x * φ (x + τ)) + ∫ x, p x * φ (x - τ)) / 2 := by
    rw [← integral_add hb1 hb2, ← integral_div]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  have hR : ∫ x, (p (x - τ) + p (x + τ)) / 2 * φ x
      = ((∫ x, p (x - τ) * φ x) + ∫ x, p (x + τ) * φ x) / 2 := by
    rw [← integral_add hb3 hb4, ← integral_div]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  -- and the reduction itself
  have hmain : ∫ x, p x * deriv (fun y => y * φ y) x
      = ∫ x, (p (x - τ) + p (x + τ)) / 2 * φ x := by
    rw [← hchange (deriv fun y => y * φ y), hform φ hφ hsupp,
      hchange fun x => (φ (x + τ) + φ (x - τ)) / 2, hL, hR, e1, e2]
  rw [hmain]

end SpatialLine
