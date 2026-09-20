/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.GeneratorMatern
import SpatialLine.GeneratorDomain
import SpatialLine.Thorin

/-!
# The Thorin corner of the generator

Blueprint: `prop:corner-generators`(4) — for a Thorin member with `a = 0` the generator is the
Thorin mixture of Matérn generators, `𝒜_t = t^{-1}∫(Λ_{t/θ} - I)\,U(dθ)`.

## The hypothesis class, and why it had to change

The reviewed statement (R18) asked only that `g` be measurable and bounded, which is right for
the Matérn clause and **wrong here**. There `ϖ` is the finite measure `2γe^{-v}dv` and
boundedness alone gives absolute convergence; for a general Thorin member `ϖ` is infinite near
the origin — the stable member has `C_α^{-1}αv^{-α-1}dv` — and for a merely bounded measurable
`g` the `ϖ`-integral of the second difference need not converge at all, the second difference
having no reason to vanish as `v → 0`. Both sides being Bochner integrals, they would then
return their junk value `0` independently: the left-hand side junks while the right may still
converge, and nothing in the statement rules that out. The hypothesis class is therefore
narrowed to the one the node is about and the one its own proof consumes — `ContDiff ℝ 2 g` with
`g` and `g''` bounded, which is exactly `scale_evolution_absconv`'s class. That is where the
narrowing pays: `scale_evolution_absconv` *is* the integrability the Fubini below needs, and
without it there is no proof rather than a longer one.

## What proving it found

**The mixture is a pushforward, and that removes the density entirely.** The recorded route
identified `ϖ` as `(∫⁻ θe^{-θv}\,U(dθ))\,dv` and then asked for the density's almost-everywhere
finiteness before `integral_withDensity_eq_integral_toReal_smul` could be applied, with a Fubini
on top. Writing the same measure as the image of `U ⊗ Exp` under `(θ, u) ↦ u/θ` — which is what
"mix the exponential law of rate `θ` over `U`" says without choosing a density — replaces those
two steps by `integral_map` and the ordinary product Fubini, and the `⊤`-valued density, its
measurability and its a.e. finiteness never appear. Steps (iii) of the recorded route drops out;
step (iv) becomes `integrable_map_measure` applied to `scale_evolution_absconv`.

**The tails are one Tonelli.** `ϖ(y,∞) = ∫⁻_θ Exp{u : u/θ > y}\,U(dθ) = ∫⁻_θ e^{-θy}\,U(dθ)`,
which is `laplaceL U y` on the nose, and `laplaceL_eq_of_thorin` turns the representation into
that identity. The identification is then chapter 8's pair `tail_eq_of_ae_tail_eq` and
`measure_eq_of_tail_eq`, exactly as in the stable and Matérn corners.

**The exponential law was already in the library.** `expLaw` is `maternJump (1/2)`, whose tail
and whose Bochner integral chapter 10 had proved; the two lemmas below are one rewrite each.

**Axiom footprint.** The node spends ledger **A3** (`fourier_toolbox_levy_unique`) through
`laplaceL_eq_of_thorin`, which is the `\uses` edge to `prop:thorin-subclass` that the blueprint
proof already declares — the representation `k(x) = ∫e^{-θx}U(dθ)` is that node's, not this
one's. Everything else is Lean core.
-/

namespace SpatialLine

open MeasureTheory Set
open scoped ENNReal

/-! ## The exponential law -/
/-- The standard exponential law on `(0,∞)`. -/
noncomputable def expLaw : Measure ℝ := maternJump (1 / 2)

theorem expLaw_tail {y : ℝ} (hy : 0 < y) : expLaw (Ioi y) = ENNReal.ofReal (Real.exp (-y)) := by
  rw [expLaw, maternJump_tail (by norm_num) hy, maternProfile_eq_exp one_pos hy]
  norm_num

theorem isFolded_expLaw : IsFolded expLaw := isFolded_maternJump _

theorem integral_expLaw (h : ℝ → ℝ) :
    ∫ u, h u ∂expLaw = ∫ u in Ioi (0 : ℝ), Real.exp (-u) * h u := by
  rw [expLaw, integral_maternJump (by norm_num)]
  refine setIntegral_congr_fun measurableSet_Ioi (fun u _ => ?_)
  norm_num

instance isProbabilityMeasure_expLaw : IsProbabilityMeasure expLaw := by
  constructor
  rw [expLaw, maternJump, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hint : IntegrableOn (fun v : ℝ => 2 * (1 / 2 : ℝ) * Real.exp (-v)) (Ioi (0 : ℝ)) :=
    (integrableOn_exp_neg_Ioi 0).const_mul _
  have hnn : ∀ᵐ v ∂(volume.restrict (Ioi (0 : ℝ))), 0 ≤ 2 * (1 / 2 : ℝ) * Real.exp (-v) :=
    (ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun v _ => by positivity)
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, integral_const_mul,
    integral_exp_neg_Ioi_zero]
  norm_num

/-- **The Choquet measure of a Thorin member**, as a mixture: the image of `U ⊗ Exp` under
`(θ, u) ↦ u/θ`, which is `∫ θ e^{-θv}\,U(dθ)\,dv` written without a density. -/
noncomputable def thorinJump (U : Measure ℝ) : Measure ℝ :=
  (U.prod expLaw).map fun p : ℝ × ℝ => p.2 / p.1

theorem measurable_div_snd_fst : Measurable fun p : ℝ × ℝ => p.2 / p.1 :=
  measurable_snd.div measurable_fst

theorem isFolded_thorinJump {U : Measure ℝ} [SFinite U] (hU : IsFolded U) :
    IsFolded (thorinJump U) := by
  rw [IsFolded, thorinJump, Measure.map_apply measurable_div_snd_fst measurableSet_Iic,
    Measure.prod_apply (measurable_div_snd_fst measurableSet_Iic)]
  refine (lintegral_eq_zero_iff' ?_).mpr ?_
  · exact (measurable_measure_prodMk_left
      (measurable_div_snd_fst measurableSet_Iic)).aemeasurable
  · filter_upwards [ae_pos_of_isFolded hU] with θ hθ
    have hset : (Prod.mk θ ⁻¹' ((fun p : ℝ × ℝ => p.2 / p.1) ⁻¹' Iic 0)) = Iic 0 := by
      ext u
      simp only [mem_preimage, mem_Iic]
      constructor
      · intro h
        by_contra hc
        push Not at hc
        exact absurd h (not_le.mpr (div_pos hc hθ))
      · intro h
        exact div_nonpos_of_nonpos_of_nonneg h hθ.le
    rw [hset]
    exact isFolded_expLaw

theorem thorinJump_tail {U : Measure ℝ} [SFinite U] (hU : IsFolded U) {y : ℝ} (hy : 0 < y) :
    thorinJump U (Ioi y) = laplaceL U y := by
  rw [thorinJump, Measure.map_apply measurable_div_snd_fst measurableSet_Ioi,
    Measure.prod_apply (measurable_div_snd_fst measurableSet_Ioi), laplaceL_apply]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_pos_of_isFolded hU] with θ hθ
  have hset : (Prod.mk θ ⁻¹' ((fun p : ℝ × ℝ => p.2 / p.1) ⁻¹' Ioi y)) = Ioi (y * θ) := by
    ext u
    simp only [mem_preimage, mem_Ioi]
    rw [lt_div_iff₀ hθ]
  rw [hset, expLaw_tail (by positivity)]

theorem thorin_jump_measure {P : SDProfile} {U : Measure ℝ} (hU : IsFolded U)
    (hrep : ∀ ω : ℝ, P.exponentL ω = thorinExponentL P.a U ω) (ϖ : Measure ℝ)
    (hϖ : HasProfileTail P.k ϖ) : ϖ = thorinJump U := by
  obtain ⟨hsig, -, -, -⟩ := thorin_measure_facts hU (thorin_lintegral_ne_top hrep 1)
  haveI : SigmaFinite U := hsig
  refine measure_eq_of_tail_eq hϖ.1 (isFolded_thorinJump hU)
    (fun x hx => measure_Ioi_ne_top hϖ hx) (fun x hx => ?_)
  refine tail_eq_of_ae_tail_eq ?_ hx
  have hpos : ∀ᵐ y ∂(volume.restrict (Ioi (0 : ℝ))), (0 : ℝ) < y :=
    (ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun y hy => hy)
  filter_upwards [hϖ.2, hpos] with y hy hy0
  obtain ⟨hne, hval⟩ := laplaceL_eq_of_thorin hU hrep y hy0
  rw [hy, thorinJump_tail hU hy0, hval, ENNReal.ofReal_toReal hne]

/-- The inner slice: at a fixed Thorin coordinate the exponential average of the second
difference is `g - Λ_{t/θ}g`. -/
theorem integral_expLaw_secondDifference {θ t : ℝ} (hθ : 0 < θ) (ht : 0 < t) (g : ℝ → ℝ)
    (hgm : AEStronglyMeasurable g volume) {C : ℝ} (hC : ∀ y, |g y| ≤ C) (x : ℝ) :
    (∫ u, (g x - (g (x - t * (u / θ)) + g (x + t * (u / θ))) / 2) ∂expLaw)
      = g x - mconv (laplaceLaw (t / θ)) g x := by
  have htθ : (0 : ℝ) < t / θ := div_pos ht hθ
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC x)
  have hgsub : AEStronglyMeasurable (fun u : ℝ => g (x - t / θ * u)) volume :=
    aestronglyMeasurable_comp_mul_left
      (hgm.comp_measurePreserving (volume.measurePreserving_sub_left x)) (ne_of_gt htθ)
  have hgadd : AEStronglyMeasurable (fun u : ℝ => g (x + t / θ * u)) volume :=
    aestronglyMeasurable_comp_mul_left
      (hgm.comp_measurePreserving (measurePreserving_add_left volume x)) (ne_of_gt htθ)
  have hhalf : AEStronglyMeasurable
      (fun u : ℝ => (g (x - t / θ * u) + g (x + t / θ * u)) / 2 * Real.exp (-u)) volume := by
    refine (((hgsub.add hgadd).mul (aestronglyMeasurable_const (b := (2 : ℝ)⁻¹))).mul
      (by fun_prop : AEStronglyMeasurable (fun u : ℝ => Real.exp (-u)) volume)).congr
      (.of_forall fun u => ?_)
    show (g (x - t / θ * u) + g (x + t / θ * u)) * 2⁻¹ * Real.exp (-u)
      = (g (x - t / θ * u) + g (x + t / θ * u)) / 2 * Real.exp (-u)
    ring
  have hI1 : IntegrableOn (fun u : ℝ => Real.exp (-u) * g x) (Ioi (0 : ℝ)) :=
    (integrableOn_exp_neg_Ioi 0).mul_const _
  have hI2 : IntegrableOn
      (fun u : ℝ => (g (x - t / θ * u) + g (x + t / θ * u)) / 2 * Real.exp (-u))
      (Ioi (0 : ℝ)) := by
    refine Integrable.mono' ((integrableOn_exp_neg_Ioi (0 : ℝ)).const_mul C) hhalf.restrict
      ((ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun u _ => ?_))
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_pos _).le]
    have hb : |(g (x - t / θ * u) + g (x + t / θ * u)) / 2| ≤ C := by
      rw [abs_div, abs_two]
      have := abs_add_le (g (x - t / θ * u)) (g (x + t / θ * u))
      have h2 := hC (x - t / θ * u)
      have h3 := hC (x + t / θ * u)
      linarith
    nlinarith [(Real.exp_pos (-u)).le]
  rw [integral_expLaw]
  have hrw : ∀ u : ℝ, Real.exp (-u) * (g x - (g (x - t * (u / θ)) + g (x + t * (u / θ))) / 2)
      = Real.exp (-u) * g x - (g (x - t / θ * u) + g (x + t / θ * u)) / 2 * Real.exp (-u) := by
    intro u
    rw [show t * (u / θ) = t / θ * u by ring]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi (fun u _ => hrw u), integral_sub hI1 hI2,
    mconv_laplaceLaw htθ g hgm hC x]
  congr 1
  · have : (fun u : ℝ => Real.exp (-u) * g x) = fun u : ℝ => g x * Real.exp (-u) := by
      funext u; ring
    rw [this, integral_const_mul, integral_exp_neg_Ioi_zero, mul_one]

theorem integral_thorinJump {U : Measure ℝ} [SFinite U] (h : ℝ → ℝ)
    (hm : AEStronglyMeasurable h (thorinJump U)) (hint : Integrable h (thorinJump U)) :
    ∫ v, h v ∂(thorinJump U) = ∫ θ, (∫ u, h (u / θ) ∂expLaw) ∂U := by
  have hφ : AEMeasurable (fun p : ℝ × ℝ => p.2 / p.1) (U.prod expLaw) :=
    measurable_div_snd_fst.aemeasurable
  have hint2 : Integrable (fun p : ℝ × ℝ => h (p.2 / p.1)) (U.prod expLaw) :=
    (integrable_map_measure hm hφ).mp hint
  rw [thorinJump, integral_map hφ hm]
  exact integral_prod _ hint2

theorem corner_generator_thorin (P : SDProfile) (hP : P.a = 0) (U : Measure ℝ) (hU : IsFolded U)
    (hrep : ∀ ω : ℝ, P.exponentL ω = thorinExponentL 0 U ω) (ϖ : Measure ℝ)
    (hϖ : HasProfileTail P.k ϖ) {t : ℝ} (ht : 0 < t) (g : ℝ → ℝ)
    (hg : ContDiff ℝ 2 g) (hgb : ∃ C : ℝ, ∀ x, |g x| ≤ C)
    (hgb2 : ∃ C : ℝ, ∀ x, |iteratedDeriv 2 g x| ≤ C) (x : ℝ) :
    scaleGenerator 0 ϖ t g x
      = t⁻¹ * ∫ θ, (mconv (laplaceLaw (t / θ)) g x - g x) ∂U := by
  obtain ⟨C, hC⟩ := hgb
  have hrep' : ∀ ω : ℝ, P.exponentL ω = thorinExponentL P.a U ω := by rw [hP]; exact hrep
  obtain ⟨hsig, -, -, -⟩ := thorin_measure_facts hU (thorin_lintegral_ne_top hrep' 1)
  haveI : SigmaFinite U := hsig
  have hjump : ϖ = thorinJump U := thorin_jump_measure hU hrep' ϖ hϖ
  have hgm : AEStronglyMeasurable g volume := hg.continuous.aestronglyMeasurable
  have hint : Integrable (fun v : ℝ => g x - (g (x - t * v) + g (x + t * v)) / 2) ϖ :=
    scale_evolution_absconv P ϖ hϖ ht g hg ⟨C, hC⟩ hgb2 x
  have hhc : Continuous fun v : ℝ => g x - (g (x - t * v) + g (x + t * v)) / 2 := by
    have hgc : Continuous g := hg.continuous
    fun_prop
  rw [hjump] at hint ⊢
  rw [scaleGenerator, integral_thorinJump _ hhc.aestronglyMeasurable hint]
  have hinner : ∀ᵐ θ ∂U,
      (∫ u, (g x - (g (x - t * (u / θ)) + g (x + t * (u / θ))) / 2) ∂expLaw)
        = g x - mconv (laplaceLaw (t / θ)) g x := by
    filter_upwards [ae_pos_of_isFolded hU] with θ hθ
    exact integral_expLaw_secondDifference hθ ht g hgm hC x
  rw [integral_congr_ae hinner]
  have hneg : (∫ θ, (g x - mconv (laplaceLaw (t / θ)) g x) ∂U)
      = -∫ θ, (mconv (laplaceLaw (t / θ)) g x - g x) ∂U := by
    rw [← integral_neg]
    refine integral_congr_ae (.of_forall fun θ => ?_)
    ring
  rw [hneg]
  ring

end SpatialLine
