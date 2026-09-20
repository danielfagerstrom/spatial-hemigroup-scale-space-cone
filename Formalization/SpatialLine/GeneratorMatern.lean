/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.Generator
import SpatialLine.MaternCorner
import SpatialLine.ChoquetExtreme
import SpatialLine.ProfileTail

/-!
# The Matern corner of the generator

Blueprint: `prop:corner-generators`(3) — `𝒜_t = (2γ/t)(Λ_t - I)`, a compound Poisson generator
with Laplace-distributed jumps at rate `2γ/t`, bounded of norm at most `4γ/t`.

## What proving this found

**The clause is two computations, and the first is a change of variables, not an identity of
operators.** The Choquet measure of the Matern profile is `2γe^{-v}dv` on `(0,∞)`
(`matern_jump_measure`), identified from `HasProfileTail` by the same pair of chapter-8 lemmas
the stable corner uses; after that the generator's `ϖ`-integral is
`∫₀^∞ 2γe^{-v}[g(x) - ½(g(x-tv) + g(x+tv))]dv`, and the whole content is
`mconv_laplaceLaw`: convolution by the Laplace law of range `t` *is* the average
`∫₀^∞ ½(g(x-tv) + g(x+tv))e^{-v}dv`. That is the dilation `y = tv` folded across the origin,
and it is where `0 < t` is spent — the only place in the clause.

**Boundedness needs no operator norm and no `L^p` theory.** "Bounded of norm at most `4γ/t`" is
read on `L^∞` as the sup-norm bound of the statement, which follows from `‖Λ_tg‖_∞ ≤ ‖g‖_∞`,
itself `norm_integral_le_of_norm_le` against the probability density. The `L¹` half of the
node's norm claim is the same bound with the two norms exchanged and is not stated separately.

**The measurability side condition is the R18 hypothesis doing its work.** Both sides of clause
(1) are Bochner integrals, which return `0` on a non-integrable integrand and do not return it
together; the review added `AEStronglyMeasurable g` and a uniform bound, and both are consumed
here — the bound to dominate the three integrands, and the measurability to know the dilated
translates `v ↦ g(x ± tv)` are measurable at all, which needs
`aestronglyMeasurable_comp_mul_left` because a dilation is only quasi-measure-preserving.
-/

namespace SpatialLine

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-! ## The Laplace kernel -/
/-- The Laplace density is nonnegative. -/
theorem laplaceDensity_nonneg {θ : ℝ} (hθ : 0 < θ) (x : ℝ) : 0 ≤ laplaceDensity θ x := by
  rw [laplaceDensity]; positivity

/-- The Laplace density is even. -/
theorem laplaceDensity_neg (θ x : ℝ) : laplaceDensity θ (-x) = laplaceDensity θ x := by
  rw [laplaceDensity, laplaceDensity, abs_neg]

/-- The Laplace density is continuous. -/
theorem continuous_laplaceDensity (θ : ℝ) : Continuous (laplaceDensity θ) := by
  unfold laplaceDensity; fun_prop

/-- The Laplace density is measurable. -/
theorem measurable_laplaceDensity (θ : ℝ) : Measurable (laplaceDensity θ) :=
  (continuous_laplaceDensity θ).measurable

/-- At range `t`, the density read at the dilated point `tv` is `(2t)^{-1}e^{-v}`; this is the
change of variables the corner's computation runs on. -/
theorem laplaceDensity_dilate {t : ℝ} (ht : 0 < t) {v : ℝ} (hv : 0 < v) :
    laplaceDensity t (t * v) = (2 * t)⁻¹ * Real.exp (-v) := by
  have htv : 0 < t * v := mul_pos ht hv
  rw [laplaceDensity, abs_of_pos htv]
  field_simp

/-- The Laplace density is integrable on the positive half-line. -/
theorem integrableOn_laplaceDensity_Ioi {θ : ℝ} (hθ : 0 < θ) :
    IntegrableOn (laplaceDensity θ) (Ioi (0 : ℝ)) := by
  have hneg : -θ⁻¹ < 0 := by simp [hθ]
  have h : IntegrableOn (fun y : ℝ => (2 * θ)⁻¹ * Real.exp (-θ⁻¹ * y)) (Ioi (0 : ℝ)) :=
    (integrableOn_exp_mul_Ioi hneg 0).const_mul _
  refine h.congr_fun (fun y hy => ?_) measurableSet_Ioi
  have hy0 : (0 : ℝ) < y := hy
  rw [laplaceDensity, abs_of_pos hy0]
  field_simp

/-- The Laplace density is integrable on the negative half-line. -/
theorem integrableOn_laplaceDensity_Iic {θ : ℝ} (hθ : 0 < θ) :
    IntegrableOn (laplaceDensity θ) (Iic (0 : ℝ)) := by
  have hpos : (0 : ℝ) < θ⁻¹ := by positivity
  have h : IntegrableOn (fun y : ℝ => (2 * θ)⁻¹ * Real.exp (θ⁻¹ * y)) (Iic (0 : ℝ)) :=
    (integrableOn_exp_mul_Iic hpos 0).const_mul _
  refine h.congr_fun (fun y hy => ?_) measurableSet_Iic
  have hy0 : y ≤ 0 := hy
  rw [laplaceDensity, abs_of_nonpos hy0]
  field_simp

/-- The Laplace density is integrable on the line. -/
theorem integrable_laplaceDensity {θ : ℝ} (hθ : 0 < θ) : Integrable (laplaceDensity θ) := by
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
  exact (integrableOn_laplaceDensity_Iic hθ).union (integrableOn_laplaceDensity_Ioi hθ)

/-- The convolution by the Laplace kernel, written on the half-line at the dilated scale. -/
theorem mconv_laplaceLaw {t : ℝ} (ht : 0 < t) (g : ℝ → ℝ)
    (hgm : AEStronglyMeasurable g volume) {C : ℝ} (hC : ∀ y, |g y| ≤ C) (x : ℝ) :
    mconv (laplaceLaw t) g x
      = ∫ v in Ioi (0 : ℝ), (g (x - t * v) + g (x + t * v)) / 2 * Real.exp (-v) := by
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC x)
  have hρnn := laplaceDensity_nonneg ht
  have hρint := integrable_laplaceDensity ht
  -- `y ↦ g (x - y)` and `y ↦ g (x + y)` are almost everywhere strongly measurable
  have hgsub : AEStronglyMeasurable (fun y : ℝ => g (x - y)) volume :=
    hgm.comp_measurePreserving (volume.measurePreserving_sub_left x)
  have hgadd : AEStronglyMeasurable (fun y : ℝ => g (x + y)) volume :=
    hgm.comp_measurePreserving (measurePreserving_add_left volume x)
  -- the three integrands
  have hdom : ∀ (h : ℝ → ℝ), (∀ y, |h y| ≤ C) → AEStronglyMeasurable h volume →
      Integrable (fun y => laplaceDensity t y * h y) := by
    intro h hb hm
    refine Integrable.mono' (hρint.const_mul C) (by fun_prop) (.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρnn y)]
    have := hb y
    nlinarith [hρnn y, abs_nonneg (h y)]
  have h1 : Integrable (fun y : ℝ => laplaceDensity t y * g (x - y)) :=
    hdom _ (fun y => hC _) hgsub
  have h2 : Integrable (fun y : ℝ => laplaceDensity t y * g (x + y)) :=
    hdom _ (fun y => hC _) hgadd
  -- unfold the measure
  have hstep0 : mconv (laplaceLaw t) g x = ∫ y, laplaceDensity t y * g (x - y) := by
    rw [mconv, laplaceLaw,
      integral_withDensity_eq_integral_toReal_smul
        (measurable_laplaceDensity t).ennreal_ofReal
        (.of_forall fun y => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (.of_forall fun y => ?_)
    show (ENNReal.ofReal (laplaceDensity t y)).toReal • g (x - y)
      = laplaceDensity t y * g (x - y)
    rw [smul_eq_mul, ENNReal.toReal_ofReal (hρnn y)]
  rw [hstep0]
  -- split the line at the origin
  have hsplit : (∫ y, laplaceDensity t y * g (x - y))
      = (∫ y in Iic (0 : ℝ), laplaceDensity t y * g (x - y))
        + ∫ y in Ioi (0 : ℝ), laplaceDensity t y * g (x - y) := by
    rw [← setIntegral_univ (f := fun y : ℝ => laplaceDensity t y * g (x - y)),
      ← Iic_union_Ioi (a := (0 : ℝ)),
      setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi h1.integrableOn h1.integrableOn]
  -- the left half is the right half reflected
  have hrefl : (∫ y in Iic (0 : ℝ), laplaceDensity t y * g (x - y))
      = ∫ y in Ioi (0 : ℝ), laplaceDensity t y * g (x + y) := by
    have h := integral_comp_neg_Iic (0 : ℝ) fun u : ℝ => laplaceDensity t u * g (x + u)
    rw [neg_zero] at h
    rw [← h]
    refine setIntegral_congr_fun measurableSet_Iic (fun y _ => ?_)
    show laplaceDensity t y * g (x - y) = laplaceDensity t (-y) * g (x + -y)
    rw [laplaceDensity_neg, ← sub_eq_add_neg]
  rw [hsplit, hrefl,
    ← integral_add h2.integrableOn h1.integrableOn]
  -- the dilation `y = tv`
  have hsub := integral_comp_mul_left_Ioi
    (fun y : ℝ => laplaceDensity t y * g (x + y) + laplaceDensity t y * g (x - y)) 0 ht
  rw [mul_zero] at hsub
  have hval : (∫ v in Ioi (0 : ℝ),
      (laplaceDensity t (t * v) * g (x + t * v) + laplaceDensity t (t * v) * g (x - t * v)))
      = t⁻¹ * ∫ y in Ioi (0 : ℝ),
        (laplaceDensity t y * g (x + y) + laplaceDensity t y * g (x - y)) := by
    simpa using hsub
  have hfin : (∫ v in Ioi (0 : ℝ),
      (laplaceDensity t (t * v) * g (x + t * v) + laplaceDensity t (t * v) * g (x - t * v)))
      = t⁻¹ * ∫ v in Ioi (0 : ℝ), (g (x - t * v) + g (x + t * v)) / 2 * Real.exp (-v) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun v hv => ?_)
    have hv0 : (0 : ℝ) < v := hv
    rw [laplaceDensity_dilate ht hv0]
    have ht0 : t ≠ 0 := ne_of_gt ht
    field_simp
    ring
  rw [hval] at hfin
  exact mul_left_cancel₀ (inv_ne_zero (ne_of_gt ht)) hfin

/-- Scaling the argument preserves almost-everywhere strong measurability: the pushforward of
Lebesgue measure under `v ↦ tv` is a positive multiple of itself. -/
theorem aestronglyMeasurable_comp_mul_left {f : ℝ → ℝ} (hf : AEStronglyMeasurable f volume)
    {t : ℝ} (ht : t ≠ 0) : AEStronglyMeasurable (fun v : ℝ => f (t * v)) volume := by
  refine hf.comp_quasiMeasurePreserving ⟨measurable_const_mul t, ?_⟩
  rw [show (Measure.map (fun v : ℝ => t * v) volume) = ENNReal.ofReal |t⁻¹| • volume from
    Real.map_volume_mul_left ht]
  intro s hs
  simp [hs]

/-! ## The Matérn jump measure -/

/-- The Choquet measure of the Matern profile of shape `γ` at unit range: `2γe^{-v}dv` on
`(0,∞)`. -/
noncomputable def maternJump (γ : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi (0 : ℝ))).withDensity fun v => ENNReal.ofReal (2 * γ * Real.exp (-v))

/-- `maternJump` is carried by the positive half-line. -/
theorem isFolded_maternJump (γ : ℝ) : IsFolded (maternJump γ) := by
  rw [IsFolded, maternJump, withDensity_apply _ measurableSet_Iic,
    Measure.restrict_restrict measurableSet_Iic]
  convert lintegral_zero_measure _
  rw [Measure.restrict_eq_zero]
  convert measure_empty (μ := (volume : Measure ℝ))
  ext z
  simp only [mem_inter_iff, mem_Iic, mem_Ioi, mem_empty_iff_false, iff_false, not_and, not_lt]
  exact fun h => h

/-- The tail of `maternJump γ` at a positive point is the Matern profile there. -/
theorem maternJump_tail {γ : ℝ} (hγ : 0 < γ) {y : ℝ} (hy : 0 < y) :
    maternJump γ (Ioi y) = ENNReal.ofReal (maternProfile γ 1 y) := by
  rw [maternJump, withDensity_apply _ measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi]
  have hset : Ioi y ∩ Ioi (0 : ℝ) = Ioi y := by
    ext z; simp only [mem_inter_iff, mem_Ioi]; exact ⟨fun h => h.1, fun h => ⟨h, lt_trans hy h⟩⟩
  rw [hset]
  have hint : IntegrableOn (fun v : ℝ => 2 * γ * Real.exp (-v)) (Ioi y) :=
    (integrableOn_exp_neg_Ioi y).const_mul _
  have hnn : ∀ᵐ v ∂(volume.restrict (Ioi y)), 0 ≤ 2 * γ * Real.exp (-v) := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun v _ => by positivity)
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, integral_const_mul,
    integral_exp_neg_Ioi, maternProfile_eq_exp one_pos hy]
  norm_num

/-- **The Choquet measure of the Matern corner.** A folded measure whose tails are the Matern
profile almost everywhere on `(0,∞)` *is* `2γe^{-v}dv`; the identification is by tails, as in
the stable corner. -/
theorem matern_jump_measure {γ : ℝ} (hγ : 0 < γ) (ϖ : Measure ℝ)
    (hϖ : HasProfileTail (maternProfile γ 1) ϖ) : ϖ = maternJump γ := by
  refine measure_eq_of_tail_eq hϖ.1 (isFolded_maternJump γ)
    (fun x hx => measure_Ioi_ne_top hϖ hx) (fun x hx => ?_)
  refine tail_eq_of_ae_tail_eq ?_ hx
  have hpos : ∀ᵐ y ∂(volume.restrict (Ioi (0 : ℝ))), (0 : ℝ) < y :=
    (ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun y hy => hy)
  filter_upwards [hϖ.2, hpos] with y hy hy0
  rw [hy, maternJump_tail hγ hy0]

/-- A Bochner integral against `maternJump γ` is the weighted integral on the half-line. -/
theorem integral_maternJump {γ : ℝ} (hγ : 0 ≤ γ) (h : ℝ → ℝ) :
    ∫ v, h v ∂(maternJump γ) = ∫ v in Ioi (0 : ℝ), 2 * γ * Real.exp (-v) * h v := by
  rw [maternJump, integral_withDensity_eq_integral_toReal_smul
      (by fun_prop : Measurable fun v : ℝ => ENNReal.ofReal (2 * γ * Real.exp (-v)))
      (.of_forall fun v => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (.of_forall fun v => ?_)
  show (ENNReal.ofReal (2 * γ * Real.exp (-v))).toReal • h v = 2 * γ * Real.exp (-v) * h v
  rw [smul_eq_mul, ENNReal.toReal_ofReal (by positivity)]

/-! ## `prop:corner-generators`(3) -/

/-- **`prop:corner-generators`(3), the Matern corner.** In the canonical gauge the generator is
`𝒜_t = (2γ/t)(Λ_t - I)`, convolution by the Laplace kernel of range `t` minus the identity at
rate `2γ/t`, and it is bounded on `L^∞` by `4γ/t`.

`Skeleton.corner_generator_matern`'s type verbatim, hypotheses included: `g` is measurable and
uniformly bounded, which is review finding **R18** — both sides are Bochner integrals and they
do not return their junk value together. -/
theorem corner_generator_matern (γ : ℝ) (hγ : 0 < γ) {t : ℝ} (ht : 0 < t) (ϖ : Measure ℝ)
    (hϖ : HasProfileTail (maternProfile γ 1) ϖ) (g : ℝ → ℝ)
    (hgm : AEStronglyMeasurable g volume) (hgb : ∃ C : ℝ, ∀ x, |g x| ≤ C) :
    (∀ x : ℝ, scaleGenerator 0 ϖ t g x = 2 * γ / t * (mconv (laplaceLaw t) g x - g x)) ∧
      ((∃ C : ℝ, ∀ x, |g x| ≤ C) →
        ∀ C : ℝ, (∀ x, |g x| ≤ C) → ∀ x, |scaleGenerator 0 ϖ t g x| ≤ 4 * γ / t * C) := by
  obtain ⟨C₀, hC₀⟩ := hgb
  have hjump : ϖ = maternJump γ := matern_jump_measure hγ ϖ hϖ
  have ht0 : t ≠ 0 := ne_of_gt ht
  -- the identity, at an arbitrary bound
  have hmain : ∀ (C : ℝ), (∀ x, |g x| ≤ C) → ∀ x : ℝ,
      scaleGenerator 0 ϖ t g x = 2 * γ / t * (mconv (laplaceLaw t) g x - g x) := by
    intro C hC x
    have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC x)
    have hgsub : AEStronglyMeasurable (fun v : ℝ => g (x - t * v)) volume :=
      aestronglyMeasurable_comp_mul_left
        (hgm.comp_measurePreserving (volume.measurePreserving_sub_left x)) ht0
    have hgadd : AEStronglyMeasurable (fun v : ℝ => g (x + t * v)) volume :=
      aestronglyMeasurable_comp_mul_left
        (hgm.comp_measurePreserving (measurePreserving_add_left volume x)) ht0
    have hexp : AEStronglyMeasurable (fun v : ℝ => 2 * γ * Real.exp (-v))
        (volume.restrict (Ioi (0 : ℝ))) := by fun_prop
    have hsum : AEStronglyMeasurable (fun v : ℝ => g (x - t * v) + g (x + t * v)) volume :=
      hgsub.add hgadd
    have hhalf : AEStronglyMeasurable
        (fun v : ℝ => (g (x - t * v) + g (x + t * v)) / 2) volume := by
      have hprod : ((fun v : ℝ => g (x - t * v) + g (x + t * v)) * fun _ : ℝ => (2 : ℝ)⁻¹)
          = fun v : ℝ => (g (x - t * v) + g (x + t * v)) / 2 := by
        funext v
        simp [Pi.mul_apply, div_eq_mul_inv]
      exact hprod ▸ hsum.mul (aestronglyMeasurable_const (b := (2 : ℝ)⁻¹))
    have hm1 : AEStronglyMeasurable
        (fun v : ℝ => 2 * γ * Real.exp (-v) * (g x - (g (x - t * v) + g (x + t * v)) / 2))
        (volume.restrict (Ioi (0 : ℝ))) :=
      hexp.mul (aestronglyMeasurable_const.sub hhalf.restrict)
    have hm2 : AEStronglyMeasurable
        (fun v : ℝ => 2 * γ * Real.exp (-v) * ((g (x - t * v) + g (x + t * v)) / 2))
        (volume.restrict (Ioi (0 : ℝ))) :=
      hexp.mul hhalf.restrict
    -- the two integrands on the half-line
    have hint1 : IntegrableOn
        (fun v : ℝ => 2 * γ * Real.exp (-v) * (g x - (g (x - t * v) + g (x + t * v)) / 2))
        (Ioi (0 : ℝ)) := by
      refine Integrable.mono' (((integrableOn_exp_neg_Ioi (0 : ℝ)).const_mul (2 * γ * (2 * C))))
        hm1 ((ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun v _ => ?_))
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * γ * Real.exp (-v))]
      have h1 := hC x
      have h2 := hC (x - t * v)
      have h3 := hC (x + t * v)
      have hb : |g x - (g (x - t * v) + g (x + t * v)) / 2| ≤ 2 * C := by
        calc |g x - (g (x - t * v) + g (x + t * v)) / 2|
            ≤ |g x| + |(g (x - t * v) + g (x + t * v)) / 2| := abs_sub _ _
          _ ≤ C + (|g (x - t * v)| + |g (x + t * v)|) / 2 := by
              rw [abs_div, abs_two]
              have := abs_add_le (g (x - t * v)) (g (x + t * v))
              linarith
          _ ≤ 2 * C := by linarith
      have hpos : (0:ℝ) ≤ 2 * γ * Real.exp (-v) := by positivity
      nlinarith [hpos]
    have hint2 : IntegrableOn
        (fun v : ℝ => 2 * γ * Real.exp (-v) * ((g (x - t * v) + g (x + t * v)) / 2))
        (Ioi (0 : ℝ)) := by
      refine Integrable.mono' (((integrableOn_exp_neg_Ioi (0 : ℝ)).const_mul (2 * γ * C)))
        hm2 ((ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun v _ => ?_))
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * γ * Real.exp (-v))]
      have h2 := hC (x - t * v)
      have h3 := hC (x + t * v)
      have hb : |(g (x - t * v) + g (x + t * v)) / 2| ≤ C := by
        rw [abs_div, abs_two]
        have := abs_add_le (g (x - t * v)) (g (x + t * v))
        linarith
      have hpos : (0:ℝ) ≤ 2 * γ * Real.exp (-v) := by positivity
      nlinarith [hpos]
    have hint3 : IntegrableOn (fun v : ℝ => 2 * γ * Real.exp (-v) * g x) (Ioi (0 : ℝ)) :=
      ((integrableOn_exp_neg_Ioi (0 : ℝ)).const_mul (2 * γ)).mul_const _
    -- unfold the generator
    rw [scaleGenerator, hjump, integral_maternJump hγ.le]
    have hsplit : (∫ v in Ioi (0 : ℝ),
          2 * γ * Real.exp (-v) * (g x - (g (x - t * v) + g (x + t * v)) / 2))
        = (∫ v in Ioi (0 : ℝ), 2 * γ * Real.exp (-v) * g x)
          - ∫ v in Ioi (0 : ℝ), 2 * γ * Real.exp (-v) * ((g (x - t * v) + g (x + t * v)) / 2) := by
      rw [← integral_sub hint3 hint2]
      refine setIntegral_congr_fun measurableSet_Ioi (fun v _ => ?_)
      ring
    have hone : (∫ v in Ioi (0 : ℝ), 2 * γ * Real.exp (-v) * g x) = 2 * γ * g x := by
      have : (fun v : ℝ => 2 * γ * Real.exp (-v) * g x)
          = fun v : ℝ => (2 * γ * g x) * Real.exp (-v) := by funext v; ring
      rw [this, integral_const_mul, integral_exp_neg_Ioi_zero, mul_one]
    have htwo : (∫ v in Ioi (0 : ℝ),
          2 * γ * Real.exp (-v) * ((g (x - t * v) + g (x + t * v)) / 2))
        = 2 * γ * mconv (laplaceLaw t) g x := by
      rw [mconv_laplaceLaw ht g hgm hC x, ← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi (fun v _ => ?_)
      ring
    rw [hsplit, hone, htwo]
    field_simp
    ring
  refine ⟨hmain C₀ hC₀, fun _ C hC x => ?_⟩
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC x)
  rw [hmain C hC x]
  have hconv : |mconv (laplaceLaw t) g x| ≤ C := by
    rw [mconv_laplaceLaw ht g hgm hC x]
    have hbound : ‖∫ v in Ioi (0 : ℝ), (g (x - t * v) + g (x + t * v)) / 2 * Real.exp (-v)‖
        ≤ ∫ v in Ioi (0 : ℝ), C * Real.exp (-v) := by
      refine norm_integral_le_of_norm_le ((integrableOn_exp_neg_Ioi (0 : ℝ)).const_mul C)
        ((ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun v _ => ?_))
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_pos _).le]
      have h2 := hC (x - t * v)
      have h3 := hC (x + t * v)
      have hb : |(g (x - t * v) + g (x + t * v)) / 2| ≤ C := by
        rw [abs_div, abs_two]
        have := abs_add_le (g (x - t * v)) (g (x + t * v))
        linarith
      nlinarith [(Real.exp_pos (-v)).le]
    rw [integral_const_mul, integral_exp_neg_Ioi_zero, mul_one, Real.norm_eq_abs] at hbound
    exact hbound
  have hgx := hC x
  have hsub : |mconv (laplaceLaw t) g x - g x| ≤ 2 * C := by
    have := abs_sub (mconv (laplaceLaw t) g x) (g x)
    linarith
  rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * γ / t)]
  have hpos : (0:ℝ) < 2 * γ / t := by positivity
  calc 2 * γ / t * |mconv (laplaceLaw t) g x - g x| ≤ 2 * γ / t * (2 * C) := by
        exact mul_le_mul_of_nonneg_left hsub hpos.le
    _ = 4 * γ / t * C := by field_simp; ring

end SpatialLine
