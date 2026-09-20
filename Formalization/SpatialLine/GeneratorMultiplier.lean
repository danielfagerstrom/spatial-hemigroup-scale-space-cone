/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.GeneratorL1
import SpatialLine.Symbol
import SpatialLine.SelfDecomposable
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The generator at unit scale is the Fourier multiplier with symbol `-B`

Blueprint: `prop:scale-evolution`'s multiplier clause, `𝒜_1 = -B(D)`.

## The convention, and why the identity is stated twice

Mathlib's Fourier transform carries the `2π` inside the exponent, `𝓕f(w) = ∫e^{-2πixw}f(x)dx`,
so the article's transform at `ω` is Mathlib's at `ω/2π` and a multiplier identity written with
`𝓕` would read `B(2πω)`. The identity is therefore stated through the **cosine and sine
transforms separately**, in the article's own convention; the two real identities together are
exactly the complex multiplier identity, and neither needs a complex coercion. See SKELETON.md,
finding **F14**.

Both are instances of one lemma. The character `κ_φ(x) = cos(ωx - φ)` is the cosine transform's
kernel at `φ = 0` and the sine transform's at `φ = π/2`, and every step below is uniform in `φ`:
the second derivative brings down `-ω²` whatever `φ` is, and the symmetric average of the two
translates is `cos(ωv)·κ_φ`, because `cos(A + B) + cos(A - B) = 2cos A cos B` does not see the
phase. So the chapter's core identity is proved once, for a phase-shifted cosine, and read off
twice.

## What proving it found

**The `L¹` route is the whole cost, and it is now a file of its own.** The estimate at the
statement priced this clause `L` on a majorant of the second difference integrable in `x`;
`SpatialLine/GeneratorL1.lean` supplies it, and what is left here is arithmetic: two
integrations by parts for the Gaussian term, one change of variables for the jump term, and the
exchange itself.

**The Gaussian term needs no Fourier theory at all.** `∫κ_φ(x)g''(x)dx = -ω²∫κ_φ(x)g(x)dx` is
Mathlib's integration by parts on the line (`integral_mul_deriv_eq_deriv_mul_of_integrable`)
applied twice, the boundary terms vanishing because every factor is bounded times Schwartz. The
phase bookkeeping is `κ_{φ+π/2} = sin(ω· - φ)` and `κ_{φ+π} = -κ_φ`, which is why the two passes
compose into a single `-ω²` rather than into a sine.

**The jump term is a change of variables, not an approximation.** For a *fixed* displacement the
translation identity is exact — `∫κ_φ(x)·½(f(x-v) + f(x+v))dx = cos(ωv)∫κ_φ(x)f(x)dx` — so the
`x`-integral of the second difference is `(1 - cos ωv)` times the transform, and integrating that
against `ϖ` reproduces `symbol` term by term. Nothing is estimated except the exchange.

**σ-finiteness of the Choquet measure is not a hypothesis.** Fubini needs it, and
`HasProfileTail` gives it: `ϖ` is carried by `(0,∞)` and its rays there are finite
(`measure_Ioi_ne_top`), so `Iic 0 ∪ (1/(n+1), ∞)` is a finite spanning sequence.
-/

namespace SpatialLine

open MeasureTheory Set
open scoped ENNReal

/-! ## The phase-shifted cosine -/

/-- The character `κ_φ(x) = cos(ωx - φ)`: the cosine transform's kernel at `φ = 0` and the sine
transform's at `φ = π/2`. -/
noncomputable def kar (ω φ x : ℝ) : ℝ := Real.cos (ω * x - φ)

theorem kar_zero (ω x : ℝ) : kar ω 0 x = Real.cos (ω * x) := by rw [kar, sub_zero]

theorem kar_pi_div_two (ω x : ℝ) : kar ω (Real.pi / 2) x = Real.sin (ω * x) := by
  rw [kar, show ω * x - Real.pi / 2 = -(Real.pi / 2 - ω * x) by ring, Real.cos_neg,
    Real.cos_pi_div_two_sub]

theorem sin_eq_kar (ω φ x : ℝ) : Real.sin (ω * x - φ) = kar ω (φ + Real.pi / 2) x := by
  rw [kar, show ω * x - (φ + Real.pi / 2) = -(Real.pi / 2 - (ω * x - φ)) by ring, Real.cos_neg,
    Real.cos_pi_div_two_sub]

theorem kar_shift_pi (ω φ x : ℝ) : kar ω (φ + Real.pi / 2 + Real.pi / 2) x = -kar ω φ x := by
  rw [kar, kar, show ω * x - (φ + Real.pi / 2 + Real.pi / 2) = (ω * x - φ) - Real.pi by ring,
    Real.cos_sub_pi]

theorem hasDerivAt_kar (ω φ x : ℝ) :
    HasDerivAt (kar ω φ) (-(ω * Real.sin (ω * x - φ))) x := by
  have h : HasDerivAt (fun y : ℝ => ω * y - φ) ω x := by
    simpa using ((hasDerivAt_id x).const_mul ω).sub_const φ
  exact ((Real.hasDerivAt_cos (ω * x - φ)).comp x h).congr_deriv (by ring)

theorem continuous_kar (ω φ : ℝ) : Continuous (kar ω φ) := by unfold kar; fun_prop

theorem abs_kar_le (ω φ x : ℝ) : |kar ω φ x| ≤ 1 := Real.abs_cos_le_one _

/-! ## Integrability against a character -/

theorem integrable_bdd_one_mul {u : ℝ → ℝ} (hu : Continuous u) (hb : ∀ x, |u x| ≤ 1)
    (g : SignalClass) : Integrable (fun x => u x * g x) volume :=
  (g.integrable (μ := (volume : Measure ℝ))).bdd_mul hu.aestronglyMeasurable
    (.of_forall fun x => by rw [Real.norm_eq_abs]; exact hb x)

theorem integrable_kar_mul (ω φ : ℝ) (g : SignalClass) :
    Integrable (fun x => kar ω φ x * g x) volume :=
  integrable_bdd_one_mul (continuous_kar ω φ) (abs_kar_le ω φ) g

theorem integrable_kar_shift_mul (ω φ v : ℝ) (g : SignalClass) :
    Integrable (fun x => kar ω φ (x + v) * g x) volume :=
  integrable_bdd_one_mul ((continuous_kar ω φ).comp (continuous_id.add continuous_const))
    (fun x => abs_kar_le ω φ (x + v)) g

theorem integrable_kar_mul_translate (ω φ v : ℝ) (g : SignalClass) :
    Integrable (fun x => kar ω φ x * g (x - v)) volume :=
  (integrable_translate (g.integrable (μ := (volume : Measure ℝ))) v).bdd_mul
    (continuous_kar ω φ).aestronglyMeasurable
    (.of_forall fun x => by rw [Real.norm_eq_abs]; exact abs_kar_le ω φ x)

/-! ## The translation identity -/

theorem integral_kar_mul_translate (ω φ v : ℝ) (g : SignalClass) :
    ∫ x, kar ω φ x * g (x - v) = ∫ x, kar ω φ (x + v) * g x := by
  have h := integral_add_right_eq_self (μ := (volume : Measure ℝ))
    (fun y : ℝ => kar ω φ y * g (y - v)) v
  rw [← h]
  refine integral_congr_ae (.of_forall fun x => ?_)
  simp

theorem cos_add_add_cos_sub (A B : ℝ) :
    Real.cos (A + B) + Real.cos (A - B) = 2 * (Real.cos B * Real.cos A) := by
  rw [Real.cos_add, Real.cos_sub]; ring

/-- The symmetric average of two translates of a character is the character times `cos(ωv)`;
the phase does not enter. -/
theorem kar_add_kar (ω φ v x : ℝ) :
    kar ω φ (x + v) + kar ω φ (x - v) = 2 * (Real.cos (ω * v) * kar ω φ x) := by
  rw [kar, kar, kar, show ω * (x + v) - φ = (ω * x - φ) + ω * v by ring,
    show ω * (x - v) - φ = (ω * x - φ) - ω * v by ring]
  exact cos_add_add_cos_sub _ _

/-- **The transform of a symmetric second difference at a fixed displacement**: multiplication by
`1 - cos(ωv)`, exactly, for every phase. -/
theorem integral_kar_mul_secondDifference (ω φ v : ℝ) (g : SignalClass) :
    ∫ x, kar ω φ x * (g x - (g (x - v) + g (x + v)) / 2)
      = (1 - Real.cos (ω * v)) * ∫ x, kar ω φ x * g x := by
  have hI0 := integrable_kar_mul ω φ g
  have hIm := integrable_kar_mul_translate ω φ v g
  have hIp : Integrable (fun x => kar ω φ x * g (x + v)) volume := by
    have h := integrable_kar_mul_translate ω φ (-v) g
    refine h.congr (.of_forall fun x => ?_)
    simp only [sub_neg_eq_add]
  have hdiv : Integrable
      (fun x => (kar ω φ x * g (x - v) + kar ω φ x * g (x + v)) / 2) volume :=
    (hIm.add hIp).div_const 2
  have key : (fun x => kar ω φ x * (g x - (g (x - v) + g (x + v)) / 2))
      = fun x => kar ω φ x * g x - (kar ω φ x * g (x - v) + kar ω φ x * g (x + v)) / 2 := by
    funext x; ring
  have hm : ∫ x, kar ω φ x * g (x - v) = ∫ x, kar ω φ (x + v) * g x :=
    integral_kar_mul_translate ω φ v g
  have hp : ∫ x, kar ω φ x * g (x + v) = ∫ x, kar ω φ (x - v) * g x := by
    have h := integral_kar_mul_translate ω φ (-v) g
    rw [show (fun x : ℝ => kar ω φ x * g (x - -v)) = fun x : ℝ => kar ω φ x * g (x + v) from
      funext fun x => by simp only [sub_neg_eq_add]] at h
    rw [h]
    refine integral_congr_ae (.of_forall fun x => ?_)
    simp only [← sub_eq_add_neg]
  have hIa := integrable_kar_shift_mul ω φ v g
  have hIb := integrable_kar_shift_mul ω φ (-v) g
  have hIb' : Integrable (fun x => kar ω φ (x - v) * g x) volume := by
    refine hIb.congr (.of_forall fun x => ?_)
    simp only [← sub_eq_add_neg]
  have hsum : ((∫ x, kar ω φ (x + v) * g x) + ∫ x, kar ω φ (x - v) * g x) / 2
      = Real.cos (ω * v) * ∫ x, kar ω φ x * g x := by
    rw [← integral_add hIa hIb', ← integral_div, ← integral_const_mul]
    refine integral_congr_ae (.of_forall fun x => ?_)
    show (kar ω φ (x + v) * g x + kar ω φ (x - v) * g x) / 2
      = Real.cos (ω * v) * (kar ω φ x * g x)
    rw [show kar ω φ (x + v) * g x + kar ω φ (x - v) * g x
        = (kar ω φ (x + v) + kar ω φ (x - v)) * g x from by ring, kar_add_kar]
    ring
  rw [key, integral_sub hI0 hdiv, integral_div, integral_add hIm hIp, hm, hp, hsum]
  ring

/-! ## Integration by parts against a character -/

theorem integrable_sin_phase_mul (ω φ c : ℝ) (g : SignalClass) :
    Integrable (fun x => c * Real.sin (ω * x - φ) * g x) volume := by
  refine (g.integrable (μ := (volume : Measure ℝ))).bdd_mul (by fun_prop) (c := |c|)
    (.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  have := Real.abs_sin_le_one (ω * x - φ)
  nlinarith [abs_nonneg c, abs_nonneg (Real.sin (ω * x - φ))]

/-- Integration by parts once: the character's derivative is `ω` times the shifted character. -/
theorem integral_kar_mul_deriv (ω φ : ℝ) (g : SignalClass) :
    ∫ x, kar ω φ x * deriv (⇑g) x = ∫ x, ω * Real.sin (ω * x - φ) * g x := by
  set h : SignalClass := SchwartzMap.derivCLM ℝ ℝ g with hh
  have hhc : ⇑h = deriv ⇑g := funext fun x => SchwartzMap.derivCLM_apply ℝ g x
  have key := MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := kar ω φ) (u' := fun x => -(ω * Real.sin (ω * x - φ))) (v := ⇑g) (v' := ⇑h)
    (fun x _ => hasDerivAt_kar ω φ x)
    (fun x _ => by rw [hhc]; exact g.hasDerivAt x)
    (by simpa [Pi.mul_def] using integrable_kar_mul ω φ h)
    (by
      have := integrable_sin_phase_mul ω φ (-ω) g
      refine this.congr (.of_forall fun x => ?_)
      simp)
    (by simpa [Pi.mul_def] using integrable_kar_mul ω φ g)
  rw [hhc] at key
  rw [key, ← integral_neg]
  congr 1
  funext x
  ring

/-- **Integration by parts twice**: against a character the second derivative is multiplication
by `-ω²`, for every phase. -/
theorem integral_kar_mul_iteratedDeriv_two (ω φ : ℝ) (g : SignalClass) :
    ∫ x, kar ω φ x * iteratedDeriv 2 (⇑g) x = -ω ^ 2 * ∫ x, kar ω φ x * g x := by
  set g₁ : SignalClass := SchwartzMap.derivCLM ℝ ℝ g with hg₁
  have hg₁c : ⇑g₁ = deriv ⇑g := funext fun x => SchwartzMap.derivCLM_apply ℝ g x
  have hd2 : ∀ x, iteratedDeriv 2 (⇑g) x = deriv (⇑g₁) x := by
    intro x
    rw [iteratedDeriv_succ, iteratedDeriv_one, hg₁c]
  have step1 : ∫ x, kar ω φ x * iteratedDeriv 2 (⇑g) x
      = ∫ x, ω * Real.sin (ω * x - φ) * g₁ x := by
    rw [← integral_kar_mul_deriv ω φ g₁]
    refine integral_congr_ae (.of_forall fun x => ?_)
    show kar ω φ x * iteratedDeriv 2 (⇑g) x = kar ω φ x * deriv (⇑g₁) x
    rw [hd2 x]
  have step2 : ∫ x, ω * Real.sin (ω * x - φ) * g₁ x
      = ω * ∫ x, kar ω (φ + Real.pi / 2) x * deriv (⇑g) x := by
    rw [← integral_const_mul]
    refine integral_congr_ae (.of_forall fun x => ?_)
    show ω * Real.sin (ω * x - φ) * g₁ x = ω * (kar ω (φ + Real.pi / 2) x * deriv (⇑g) x)
    rw [sin_eq_kar, hg₁c]
    ring
  have step3 : ∫ x, kar ω (φ + Real.pi / 2) x * deriv (⇑g) x = ω * ∫ x, -kar ω φ x * g x := by
    rw [integral_kar_mul_deriv ω (φ + Real.pi / 2) g, ← integral_const_mul]
    refine integral_congr_ae (.of_forall fun x => ?_)
    show ω * Real.sin (ω * x - (φ + Real.pi / 2)) * g x = ω * (-kar ω φ x * g x)
    rw [sin_eq_kar, kar_shift_pi]
    ring
  have hneg : ∫ x, -kar ω φ x * g x = -∫ x, kar ω φ x * g x := by
    rw [← integral_neg]
    refine integral_congr_ae (.of_forall fun x => ?_)
    show -kar ω φ x * g x = -(kar ω φ x * g x)
    ring
  rw [step1, step2, step3, hneg]
  ring

/-! ## The Choquet measure is σ-finite, and the symbol in real form -/

/-- A Choquet measure is σ-finite: it is carried by `(0,∞)` and its rays there are finite, so
`Iic 0 ∪ (1/(n+1), ∞)` is a finite spanning sequence. Not a hypothesis of any node; Fubini needs
it and `HasProfileTail` gives it. -/
theorem sigmaFinite_of_hasProfileTail {k : ℝ → ℝ} {ϖ : Measure ℝ} (hϖ : HasProfileTail k ϖ) :
    SigmaFinite ϖ := by
  refine ⟨⟨⟨fun n : ℕ => Iic 0 ∪ Ioi (1 / (n + 1 : ℝ)), fun _ => trivial, fun n => ?_, ?_⟩⟩⟩
  · have hpos : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
    have hfin : ϖ (Ioi (1 / (n + 1 : ℝ))) ≠ ⊤ := measure_Ioi_ne_top hϖ hpos
    calc ϖ (Iic 0 ∪ Ioi (1 / (n + 1 : ℝ))) ≤ ϖ (Iic 0) + ϖ (Ioi (1 / (n + 1 : ℝ))) :=
          measure_union_le _ _
      _ < ⊤ := by rw [hϖ.1, zero_add]; exact lt_top_iff_ne_top.mpr hfin
  · refine eq_univ_of_forall fun x => ?_
    rcases le_or_gt x 0 with hx | hx
    · exact mem_iUnion.mpr ⟨0, Or.inl hx⟩
    · obtain ⟨n, hn⟩ := exists_nat_one_div_lt hx
      exact mem_iUnion.mpr ⟨n, Or.inr hn⟩

/-- The symbol as a sum of its two terms, in the real form the multiplier identity consumes. -/
theorem symbol_eq_add (Q : SDProfile) {ϖ : Measure ℝ} (hϖ : HasProfileTail Q.k ϖ) (ω : ℝ) :
    symbol Q.a ϖ ω = 2 * Q.a * ω ^ 2 + ∫ v, (1 - Real.cos (ω * v)) ∂ϖ := by
  have h1 : (0 : ℝ) ≤ 2 * Q.a * ω ^ 2 := by nlinarith [Q.a_nonneg, sq_nonneg ω]
  have h2 : (0 : ℝ) ≤ ∫ v, (1 - Real.cos (ω * v)) ∂ϖ :=
    integral_nonneg fun v => by
      simp only [Pi.zero_apply]
      linarith [Real.cos_le_one (ω * v)]
  rw [symbol_apply, symbolL_eq_ofReal Q (lintegral_min_one_sq_ne_top hϖ) ω,
    ENNReal.toReal_ofReal (by linarith)]

/-! ## The Fubini exchange, and the multiplier identity -/

/-- The second derivative of a Schwartz function, as a Schwartz function. -/
theorem iteratedDeriv_two_schwartz (f : SignalClass) (x : ℝ) :
    iteratedDeriv 2 (⇑f) x = (SchwartzMap.derivCLM ℝ ℝ (SchwartzMap.derivCLM ℝ ℝ f)) x := by
  have h1 : ⇑(SchwartzMap.derivCLM ℝ ℝ f) = deriv ⇑f :=
    funext fun y => SchwartzMap.derivCLM_apply ℝ f y
  rw [iteratedDeriv_succ, iteratedDeriv_one,
    SchwartzMap.derivCLM_apply ℝ (SchwartzMap.derivCLM ℝ ℝ f) x, h1]

/-- **The joint integrability the Fubini needs**: the second difference at displacement `tv` is
integrable over `(x, v)` against `volume ⊗ ϖ`.

The `x`-integral at a fixed displacement is bounded by `3M·max(1,t²)·(1 ∧ v²)`, `M` being the sum
of the two `L¹` norms of `f` and `f''` — the crude bound for large displacements, the quadratic
one for small (`lintegral_enorm_secondDifference_le_min`) — and `∫(1 ∧ v²)ϖ < ∞` is
`lintegral_min_hasProfileTail`. This is where the `L¹` estimates of
`SpatialLine/GeneratorL1.lean` are spent, and the only place. The scale is a hypothesis of no
use here: the bound holds for every real `t`. -/
theorem integrable_uncurry_kar_secondDifference (P : SDProfile) (ϖ : Measure ℝ)
    (hϖ : HasProfileTail P.k ϖ) (f : SignalClass) (ω φ t : ℝ) :
    Integrable (Function.uncurry fun x v : ℝ =>
      kar ω φ x * (f x - (f (x - t * v) + f (x + t * v)) / 2)) (volume.prod ϖ) := by
  haveI : SigmaFinite ϖ := sigmaFinite_of_hasProfileTail hϖ
  have hfc : Continuous (⇑f) := f.continuous
  set F : ℝ × ℝ → ℝ := Function.uncurry fun x v : ℝ =>
    kar ω φ x * (f x - (f (x - t * v) + f (x + t * v)) / 2) with hF
  have hFcont : Continuous F := by
    have h1 : Continuous fun p : ℝ × ℝ => kar ω φ p.1 :=
      (continuous_kar ω φ).comp continuous_fst
    have h2 : Continuous fun p : ℝ × ℝ => (f : ℝ → ℝ) p.1 := hfc.comp continuous_fst
    have h3 : Continuous fun p : ℝ × ℝ => (f : ℝ → ℝ) (p.1 - t * p.2) :=
      hfc.comp (continuous_fst.sub (continuous_const.mul continuous_snd))
    have h4 : Continuous fun p : ℝ × ℝ => (f : ℝ → ℝ) (p.1 + t * p.2) :=
      hfc.comp (continuous_fst.add (continuous_const.mul continuous_snd))
    exact h1.mul (h2.sub ((h3.add h4).div_const 2))
  have hFmeas : AEStronglyMeasurable F (volume.prod ϖ) := hFcont.aestronglyMeasurable
  set M : ℝ≥0∞ := (∫⁻ x, ‖f x‖ₑ) + ∫⁻ x, ‖iteratedDeriv 2 (⇑f) x‖ₑ with hM
  have hMne : M ≠ ⊤ := by
    have ha := (f.integrable (μ := (volume : Measure ℝ))).2
    have hb := ((SchwartzMap.derivCLM ℝ ℝ (SchwartzMap.derivCLM ℝ ℝ f)).integrable
      (μ := (volume : Measure ℝ))).2
    rw [hasFiniteIntegral_iff_enorm] at ha hb
    refine ENNReal.add_ne_top.mpr ⟨ha.ne, ?_⟩
    rw [lintegral_congr fun x => by rw [iteratedDeriv_two_schwartz f x]]
    exact hb.ne
  have hM1 : (∫⁻ x, ‖f x‖ₑ) ≤ M := le_self_add
  have hM2 : (∫⁻ x, ‖iteratedDeriv 2 (⇑f) x‖ₑ) ≤ M := le_add_self
  have hinner : ∀ v : ℝ, (∫⁻ x, ‖F (x, v)‖ₑ)
      ≤ 3 * M * ENNReal.ofReal (max 1 (t ^ 2)) * ENNReal.ofReal (min 1 (v ^ 2)) := by
    intro v
    have hstep : (∫⁻ x, ‖F (x, v)‖ₑ) ≤ 3 * M * ENNReal.ofReal (min 1 ((t * v) ^ 2)) := by
      refine le_trans (lintegral_mono fun x => ?_)
        (lintegral_enorm_secondDifference_le_min (f.smooth 2) hM1 hM2 (t * v))
      show ‖kar ω φ x * ((f : ℝ → ℝ) x
          - ((f : ℝ → ℝ) (x - t * v) + (f : ℝ → ℝ) (x + t * v)) / 2)‖ₑ
        ≤ ‖(f : ℝ → ℝ) x - ((f : ℝ → ℝ) (x - t * v) + (f : ℝ → ℝ) (x + t * v)) / 2‖ₑ
      rw [enorm_mul]
      calc ‖kar ω φ x‖ₑ
            * ‖(f : ℝ → ℝ) x - ((f : ℝ → ℝ) (x - t * v) + (f : ℝ → ℝ) (x + t * v)) / 2‖ₑ
          ≤ 1 * ‖(f : ℝ → ℝ) x - ((f : ℝ → ℝ) (x - t * v) + (f : ℝ → ℝ) (x + t * v)) / 2‖ₑ := by
            gcongr
            rw [Real.enorm_eq_ofReal_abs]
            exact ENNReal.ofReal_le_one.mpr (abs_kar_le ω φ x)
        _ = _ := one_mul _
    refine hstep.trans ?_
    have hprod : 3 * M * ENNReal.ofReal (max 1 (t ^ 2)) * ENNReal.ofReal (min 1 (v ^ 2))
        = 3 * M * ENNReal.ofReal (max 1 (t ^ 2) * min 1 (v ^ 2)) := by
      rw [ENNReal.ofReal_mul (le_trans zero_le_one (le_max_left _ _)), mul_assoc]
    rw [hprod]
    exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (min_one_sq_mul_le t v))
  refine ⟨hFmeas, ?_⟩
  rw [hasFiniteIntegral_iff_enorm, lintegral_prod_symm _ hFmeas.enorm]
  calc ∫⁻ v, (∫⁻ x, ‖F (x, v)‖ₑ) ∂ϖ
      ≤ ∫⁻ v, 3 * M * ENNReal.ofReal (max 1 (t ^ 2))
          * ENNReal.ofReal (min 1 (v ^ 2)) ∂ϖ := lintegral_mono hinner
    _ = 3 * M * ENNReal.ofReal (max 1 (t ^ 2))
          * ∫⁻ v, ENNReal.ofReal (min 1 (v ^ 2)) ∂ϖ :=
        lintegral_const_mul' _ _ (by finiteness)
    _ < ⊤ := by
        refine ENNReal.mul_lt_top ?_ (lt_top_iff_ne_top.mpr (lintegral_min_hasProfileTail hϖ))
        refine ENNReal.mul_lt_top ?_ ENNReal.ofReal_lt_top
        exact ENNReal.mul_lt_top (by norm_num) (lt_top_iff_ne_top.mpr hMne)

/-- **The multiplier identity at a phase and at every scale**: against `κ_φ` the generator at
scale `t` acts by multiplication by `-t^{-1}B(tω)`.

The Gaussian term is two integrations by parts, the jump term is the exact translation identity
at displacement `tv` integrated against the Choquet measure, and the exchange of the two
integrals is the Fubini above. The two `2at\omega^2` terms cancel, which is why the answer is
`-t^{-1}B(t\omega)` and not the sum of two scale-dependent pieces.

Stated at every positive scale rather than only at `t = 1`: `prop:scale-evolution`'s clause is
the case `t = 1`, and the general case is what `eq:evolution-signal` will read backwards. -/
theorem integral_kar_mul_scaleGenerator (P : SDProfile) (ϖ : Measure ℝ)
    (hϖ : HasProfileTail P.k ϖ) (f : SignalClass) (ω φ : ℝ) {t : ℝ} (ht : 0 < t) :
    ∫ x, kar ω φ x * scaleGenerator P.a ϖ t (⇑f) x
      = -(t⁻¹ * symbol P.a ϖ (t * ω)) * ∫ x, kar ω φ x * f x := by
  haveI : SigmaFinite ϖ := sigmaFinite_of_hasProfileTail hϖ
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hFint := integrable_uncurry_kar_secondDifference P ϖ hϖ f ω φ t
  have hgen : ∀ x : ℝ, kar ω φ x * scaleGenerator P.a ϖ t (⇑f) x
      = kar ω φ x * (2 * P.a * t * iteratedDeriv 2 (⇑f) x)
        - t⁻¹ * (kar ω φ x * ∫ v, ((f : ℝ → ℝ) x
            - ((f : ℝ → ℝ) (x - t * v) + (f : ℝ → ℝ) (x + t * v)) / 2) ∂ϖ) := by
    intro x
    rw [scaleGenerator]
    ring
  have hA : Integrable (fun x => kar ω φ x * (2 * P.a * t * iteratedDeriv 2 (⇑f) x)) volume := by
    refine ((integrable_kar_mul ω φ
      (SchwartzMap.derivCLM ℝ ℝ (SchwartzMap.derivCLM ℝ ℝ f))).const_mul
      (2 * P.a * t)).congr (.of_forall fun x => ?_)
    show 2 * P.a * t * (kar ω φ x * (SchwartzMap.derivCLM ℝ ℝ (SchwartzMap.derivCLM ℝ ℝ f)) x)
      = kar ω φ x * (2 * P.a * t * iteratedDeriv 2 (⇑f) x)
    rw [iteratedDeriv_two_schwartz f x]
    ring
  have hB0 : Integrable (fun x => kar ω φ x * ∫ v, ((f : ℝ → ℝ) x
      - ((f : ℝ → ℝ) (x - t * v) + (f : ℝ → ℝ) (x + t * v)) / 2) ∂ϖ) volume := by
    refine (hFint.integral_prod_left).congr (.of_forall fun x => ?_)
    show (∫ v, kar ω φ x * ((f : ℝ → ℝ) x
        - ((f : ℝ → ℝ) (x - t * v) + (f : ℝ → ℝ) (x + t * v)) / 2) ∂ϖ)
      = kar ω φ x * ∫ v, ((f : ℝ → ℝ) x
        - ((f : ℝ → ℝ) (x - t * v) + (f : ℝ → ℝ) (x + t * v)) / 2) ∂ϖ
    exact integral_const_mul _ _
  have hB : Integrable (fun x => t⁻¹ * (kar ω φ x * ∫ v, ((f : ℝ → ℝ) x
      - ((f : ℝ → ℝ) (x - t * v) + (f : ℝ → ℝ) (x + t * v)) / 2) ∂ϖ)) volume :=
    hB0.const_mul _
  have hgauss : ∫ x, kar ω φ x * (2 * P.a * t * iteratedDeriv 2 (⇑f) x)
      = 2 * P.a * t * (-ω ^ 2 * ∫ x, kar ω φ x * f x) := by
    rw [← integral_kar_mul_iteratedDeriv_two ω φ f, ← integral_const_mul]
    refine integral_congr_ae (.of_forall fun x => ?_)
    show kar ω φ x * (2 * P.a * t * iteratedDeriv 2 (⇑f) x)
      = 2 * P.a * t * (kar ω φ x * iteratedDeriv 2 (⇑f) x)
    ring
  have hjump : (∫ x, kar ω φ x * ∫ v, ((f : ℝ → ℝ) x
        - ((f : ℝ → ℝ) (x - t * v) + (f : ℝ → ℝ) (x + t * v)) / 2) ∂ϖ)
      = (∫ v, (1 - Real.cos (t * ω * v)) ∂ϖ) * ∫ x, kar ω φ x * f x := by
    have hstep1 : (∫ x, kar ω φ x * ∫ v, ((f : ℝ → ℝ) x
          - ((f : ℝ → ℝ) (x - t * v) + (f : ℝ → ℝ) (x + t * v)) / 2) ∂ϖ)
        = ∫ x, ∫ v, kar ω φ x * ((f : ℝ → ℝ) x
            - ((f : ℝ → ℝ) (x - t * v) + (f : ℝ → ℝ) (x + t * v)) / 2) ∂ϖ :=
      integral_congr_ae (.of_forall fun x => (integral_const_mul _ _).symm)
    have hstep2 := integral_integral_swap hFint
    have hstep3 : (∫ v, (∫ x, kar ω φ x * ((f : ℝ → ℝ) x
          - ((f : ℝ → ℝ) (x - t * v) + (f : ℝ → ℝ) (x + t * v)) / 2)) ∂ϖ)
        = ∫ v, (1 - Real.cos (t * ω * v)) * (∫ x, kar ω φ x * f x) ∂ϖ := by
      refine integral_congr_ae (.of_forall fun v => ?_)
      have h := integral_kar_mul_secondDifference ω φ (t * v) f
      rw [show ω * (t * v) = t * ω * v by ring] at h
      exact h
    rw [hstep1, hstep2, hstep3, integral_mul_const]
  rw [integral_congr_ae (.of_forall hgen), integral_sub hA hB, hgauss, integral_const_mul, hjump,
    symbol_eq_add P hϖ (t * ω)]
  field_simp
  ring

/-- **`prop:scale-evolution`'s multiplier clause**, the generator at unit scale is the Fourier
multiplier with symbol `-B`, stated through the cosine and the sine transform separately in the
article's own convention.

`Skeleton.scale_evolution_multiplier`'s type verbatim. Both clauses are
`integral_kar_mul_scaleGenerator` at unit scale and at a phase: `φ = 0` for the cosine,
`φ = π/2` for the sine. -/
theorem scale_evolution_multiplier (P : SDProfile) (ϖ : Measure ℝ) (hϖ : HasProfileTail P.k ϖ)
    (f : SignalClass) (ω : ℝ) :
    (∫ x, Real.cos (ω * x) * scaleGenerator P.a ϖ 1 (⇑f) x
        = -(symbol P.a ϖ ω) * ∫ x, Real.cos (ω * x) * f x) ∧
      ∫ x, Real.sin (ω * x) * scaleGenerator P.a ϖ 1 (⇑f) x
        = -(symbol P.a ϖ ω) * ∫ x, Real.sin (ω * x) * f x := by
  constructor
  · have h := integral_kar_mul_scaleGenerator P ϖ hϖ f ω 0 one_pos
    simpa only [kar_zero, inv_one, one_mul] using h
  · have h := integral_kar_mul_scaleGenerator P ϖ hϖ f ω (Real.pi / 2) one_pos
    simpa only [kar_pi_div_two, inv_one, one_mul] using h

end SpatialLine
