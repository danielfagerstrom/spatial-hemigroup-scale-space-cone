/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.MaternCorner
import SpatialLine.ProfileUniqueness
import SpatialLine.Interfaces

/-!
# `thm:matern`: the single exponential, the one-point Thorin measure, and the Matérn kernels

Blueprint: `blueprint/src/parts/10-corners.tex`, `thm:matern`, clauses (1) ⟺ (2) and (1) ⟺ (3).
The remaining two clauses, (3) ⟺ (4) and the gauge, are in `SpatialLine/MaternCorner.lean`.

## The two directions are not the same kind of statement

Forward is arithmetic on the exponent: `SpatialLine.integral_frullani` evaluates the profile's
Lévy integral, and a one-point Thorin measure evaluates `eq:thorin` by `lintegral_dirac`, so
both sides read `γ log(1 + θ²ω²)`.

Backward is where the trust boundary is spent. An exponent determines its pair (ledger **A3**,
`fourier_toolbox_levy_unique`), so the two profile *measures* agree; a measure determines its
density only almost everywhere, and the passage from there to the pointwise `Set.EqOn` of the
reviewed statement is `SpatialLine.eqOn_of_ae_eq_of_antitoneOn` in `ProfileUniqueness.lean` —
the one step R9's annotation named and no measure-theoretic lemma supplies.
-/

namespace SpatialLine

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-! ## The exponent of a profile that is Matérn on `(0,∞)` -/

theorem maternExponent_nonneg {γ θ : ℝ} (hγ : 0 < γ) (ω : ℝ) : 0 ≤ maternExponent γ θ ω := by
  have hlog : 0 ≤ Real.log (1 + θ ^ 2 * ω ^ 2) :=
    Real.log_nonneg (by nlinarith [sq_nonneg (θ * ω)])
  rw [maternExponent]
  positivity

theorem continuousOn_maternProfile (γ θ : ℝ) :
    ContinuousOn (maternProfile γ θ) (Ioi (0:ℝ)) := by
  refine ContinuousOn.congr (f := fun x : ℝ => 2 * γ * Real.exp (-(x / θ))) (by fun_prop)
    fun x hx => ?_
  exact maternProfile_of_pos hx γ θ

theorem exponentL_eq_of_eqOn_matern {P : SDProfile} {γ θ : ℝ} (hγ : 0 < γ) (hθ : 0 < θ)
    (ha : P.a = 0) (hk : Set.EqOn P.k (maternProfile γ θ) (Ioi 0)) (ω : ℝ) :
    P.exponentL ω = ENNReal.ofReal (maternExponent γ θ ω) := by
  rw [SDProfile.exponentL, ha, lintegral_maternProfile hγ hθ hk ω]
  simp

theorem exponent_eq_of_eqOn_matern {P : SDProfile} {γ θ : ℝ} (hγ : 0 < γ) (hθ : 0 < θ)
    (ha : P.a = 0) (hk : Set.EqOn P.k (maternProfile γ θ) (Ioi 0)) (ω : ℝ) :
    P.exponent ω = maternExponent γ θ ω := by
  rw [SDProfile.exponent, exponentL_eq_of_eqOn_matern hγ hθ ha hk ω]
  exact ENNReal.toReal_ofReal (maternExponent_nonneg hγ ω)

/-! ## A one-point Thorin measure -/

/-- **`eq:thorin` at a single atom.** With `U = 2γ δ_{1/θ}` the Thorin exponent is the Matérn
exponent: the `lintegral` against a Dirac evaluates, the folding factor `2` cancels the `½` in
front of the integral, and `log(1 + ω²/(θ⁻¹)²) = log(1 + θ²ω²)`. -/
theorem thorinExponentL_dirac {γ θ : ℝ} (hγ : 0 < γ) (hθ : 0 < θ) (ω : ℝ) :
    thorinExponentL 0 (ENNReal.ofReal (2 * γ) • Measure.dirac θ⁻¹) ω
      = ENNReal.ofReal (maternExponent γ θ ω) := by
  have hlog : 0 ≤ Real.log (1 + θ ^ 2 * ω ^ 2) :=
    Real.log_nonneg (by nlinarith [sq_nonneg (θ * ω)])
  have hmeas : Measurable fun t : ℝ => ENNReal.ofReal (Real.log (1 + ω ^ 2 / t ^ 2)) := by
    fun_prop
  rw [thorinExponentL, lintegral_smul_measure, lintegral_dirac' _ hmeas]
  have hbase : (1:ℝ) + ω ^ 2 / (θ⁻¹) ^ 2 = 1 + θ ^ 2 * ω ^ 2 := by field_simp
  rw [hbase]
  rw [smul_eq_mul, show (0:ℝ) * ω ^ 2 = 0 by ring, ENNReal.ofReal_zero, zero_add,
    ← mul_assoc, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2⁻¹),
    ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 2⁻¹ * (2 * γ))]
  rw [maternExponent]
  congr 1
  ring

theorem thorinExponent_dirac {γ θ : ℝ} (hγ : 0 < γ) (hθ : 0 < θ) (ω : ℝ) :
    thorinExponent 0 (ENNReal.ofReal (2 * γ) • Measure.dirac θ⁻¹) ω = maternExponent γ θ ω := by
  rw [thorinExponent, thorinExponentL_dirac hγ hθ ω]
  exact ENNReal.toReal_ofReal (maternExponent_nonneg hγ ω)

/-! ## The step that spends A3 -/

/-- If an `SDProfile`'s exponent is the Matérn exponent, its Gaussian coefficient vanishes and
its profile is the Matérn profile on `(0,∞)`.

**Spends ledger A3** through `fourier_toolbox_levy_unique`. -/
theorem eqOn_maternProfile_of_exponent {P : SDProfile} {γ θ : ℝ} (hγ : 0 < γ) (hθ : 0 < θ)
    (hexp : ∀ ω : ℝ, P.exponent ω = maternExponent γ θ ω) :
    P.a = 0 ∧ Set.EqOn P.k (maternProfile γ θ) (Ioi 0) := by
  obtain ⟨Q, hQa, hQν, hQe⟩ := profile_integrability_pair P
  obtain ⟨Q', hQ'a, hQ'ν, hQ'e⟩ := profile_integrability_pair (maternDatum γ θ hγ hθ)
  have hsame : ∀ ω, Q.exponent ω = Q'.exponent ω := by
    intro ω
    rw [← hQe, ← hQ'e, hexp ω, maternDatum_exponent γ θ hγ hθ ω]
  obtain ⟨hane, hνe⟩ := fourier_toolbox_levy_unique Q Q' hsame
  have ha : P.a = 0 := by
    rw [← hQa, hane, hQ'a]
    rfl
  refine ⟨ha, ?_⟩
  have hprof : profileMeasure P.k = profileMeasure (maternProfile γ θ) := by
    rw [← hQν, hνe, hQ'ν]
    rfl
  exact eqOn_of_profileMeasure_eq P.k_antitone P.k_nonneg
    (measurable_maternProfile γ θ).aemeasurable
    (fun x _ => maternProfile_nonneg hγ θ x) (continuousOn_maternProfile γ θ) hprof

/-! ## The two clauses of `thm:matern` -/

/-- **`thm:matern`, (1) ⟺ (2).** A single-exponential profile is a one-point Thorin measure —
at the *same* `(γ,θ)` on both sides (fidelity review R26).

**Priced M; paid M.** Forward is the Frullani identity against `lintegral_dirac`; backward is
uniqueness of the pair (**A3**) followed by the almost-everywhere-to-pointwise step of
`ProfileUniqueness.lean`. -/
theorem matern_thorin_atom (P : SDProfile) :
    ∀ γ θ : ℝ, 0 < γ → 0 < θ →
      ((P.a = 0 ∧ Set.EqOn P.k (maternProfile γ θ) (Ioi 0)) ↔
        (P.a = 0 ∧ ∀ ω : ℝ, P.exponent ω
          = thorinExponent 0 (ENNReal.ofReal (2 * γ) • Measure.dirac θ⁻¹) ω)) := by
  intro γ θ hγ hθ
  constructor
  · rintro ⟨ha, hk⟩
    refine ⟨ha, fun ω => ?_⟩
    rw [exponent_eq_of_eqOn_matern hγ hθ ha hk ω, thorinExponent_dirac hγ hθ ω]
  · rintro ⟨ha, hexp⟩
    have hexp' : ∀ ω : ℝ, P.exponent ω = maternExponent γ θ ω := by
      intro ω
      rw [hexp ω, thorinExponent_dirac hγ hθ ω]
    exact ⟨ha, (eqOn_maternProfile_of_exponent hγ hθ hexp').2⟩

/-- **`thm:matern`, (1) ⟺ (3).** A single-exponential profile is the same thing as Matérn
kernels — at the *same* `(γ,θ)` on both sides (fidelity review R26): the smoothness and range
read off the profile are the smoothness and range appearing in the transform, which the
existential reading of the equivalence would not say.

**Priced M; paid M.** The backward direction reads the transform at the canonical scale `t = 1`
and takes logarithms, which turns the hypothesis into the exponent identity
`eqOn_maternProfile_of_exponent` consumes; no other scale is needed, and the hypothesis at the
other scales is not used. -/
theorem matern_kernels (P : SDProfile) (μ : ℝ → Measure ℝ)
    (hprob : ∀ t : ℝ, 0 < t → IsProbabilityMeasure (μ t))
    (hcos : ∀ t ω : ℝ, 0 < t → fourierCos (μ t) ω = Real.exp (-P.exponent (t * ω))) :
    ∀ γ θ : ℝ, 0 < γ → 0 < θ →
      ((P.a = 0 ∧ Set.EqOn P.k (maternProfile γ θ) (Ioi 0)) ↔
        ∀ t ω : ℝ, 0 < t →
          fourierCos (μ t) ω = (1 + θ ^ 2 * t ^ 2 * ω ^ 2) ^ (-γ)) := by
  intro γ θ hγ hθ
  constructor
  · rintro ⟨ha, hk⟩
    refine fun t ω ht => ?_
    have hpos : (0:ℝ) < 1 + θ ^ 2 * t ^ 2 * ω ^ 2 := by positivity
    rw [hcos t ω ht, exponent_eq_of_eqOn_matern hγ hθ ha hk (t * ω), maternExponent,
      Real.rpow_def_of_pos hpos]
    congr 1
    rw [show θ ^ 2 * (t * ω) ^ 2 = θ ^ 2 * t ^ 2 * ω ^ 2 by ring]
    ring
  · intro htr
    have hexp : ∀ ω : ℝ, P.exponent ω = maternExponent γ θ ω := by
      intro ω
      have h := (hcos 1 ω one_pos).symm.trans (htr 1 ω one_pos)
      have hpos : (0:ℝ) < 1 + θ ^ 2 * 1 ^ 2 * ω ^ 2 := by positivity
      rw [Real.rpow_def_of_pos hpos] at h
      have hlog := congrArg Real.log h
      rw [Real.log_exp, Real.log_exp] at hlog
      rw [maternExponent]
      rw [show θ ^ 2 * ω ^ 2 = θ ^ 2 * 1 ^ 2 * ω ^ 2 by ring]
      rw [show (1:ℝ) * ω = ω by ring] at hlog
      linarith [hlog]
    exact eqOn_maternProfile_of_exponent hγ hθ hexp


/-! ## The node, assembled -/

/-- **`thm:matern`**, the four clauses in one declaration.

The node asserts that four conditions on an admissible family are equivalent; the four
declarations above prove them pairwise, and this assembles them over one profile `P` and one
family of kernels `μ`, so that the node has a declaration naming all of its clauses. Nothing
new is proved here.

**The witnesses are shared** (fidelity review R26). Clauses (1) to (3) are stated at a
*given* pair `(γ,θ)` of positive reals and quantified universally, so the `γ, θ` of the two
sides of each equivalence are the same. The existential reading — "there are `γ, θ` making (1)
hold if and only if there are `γ, θ` making (3) hold" — is a one-line consequence, and it is
strictly weaker: it leaves the parameters of the two sides unrelated, which the article cannot
mean, since clause (4) reuses the `θ` of clauses (1) to (3). Both proofs produce the same pair
anyway, so the shared form is free.

**What the bundling does not do.** Clause (4) is stated for **integer** `γ` only, and its
statement is about the two-scale increments `μ_{s,t}` where (3) is about the endpoint kernels
`μ_{0,t}`. So the four are not a single chain of equivalences at one `γ`: (3) ⟺ (4) is stated
at each integer `γ = m` and each range `θ`, which is exactly what the node says. The last conjunct is the theorem's closing sentence, that
`θ` is a change of gauge, and it is stated at the **profile** as well as at the exponent
(fidelity review R23): the frequency-side identity is definitional and says nothing about the
family, while `matern_gauge_profile` says that the `(γ,θ)` member is the `(γ,1)` member with the
displacement axis rescaled, which is what "may be normalised to `1`" means. The residual is
recorded in the node's annotation.

**Clause (4) appears twice.** The third conjunct is the equivalence with clause (3), at the
closed form; the fourth reads that closed form as a **ratio of polynomials** whose denominator
is a power of one quadratic with no real root --- the "rational in `ω` with a single pole pair"
of the node's own words, which the closed form alone does not carry (fidelity review R24). The
natural-number exponent is load-bearing there and inert in the equivalence: at a non-integer
exponent there is no polynomial ratio to state.

**Spends ledger A3** through the first two conjuncts; the third, fourth and fifth are Lean
core. -/
theorem matern_theorem (P : SDProfile) (μ : ℝ → ℝ → Measure ℝ)
    (hprob : ∀ s t : ℝ, 0 ≤ s → s ≤ t → IsProbabilityMeasure (μ s t))
    (hcos : ∀ t ω : ℝ, 0 < t → fourierCos (μ 0 t) ω = Real.exp (-P.exponent (t * ω)))
    (hcas : ∀ s t ω : ℝ, 0 ≤ s → s ≤ t →
      fourierCos (μ 0 t) ω = fourierCos (μ s t) ω * fourierCos (μ 0 s) ω) :
    (∀ γ θ : ℝ, 0 < γ → 0 < θ →
        ((P.a = 0 ∧ Set.EqOn P.k (maternProfile γ θ) (Ioi 0)) ↔
          (P.a = 0 ∧ ∀ ω : ℝ,
            P.exponent ω = thorinExponent 0 (ENNReal.ofReal (2 * γ) • Measure.dirac θ⁻¹) ω))) ∧
      (∀ γ θ : ℝ, 0 < γ → 0 < θ →
        ((P.a = 0 ∧ Set.EqOn P.k (maternProfile γ θ) (Ioi 0)) ↔
          ∀ t ω : ℝ, 0 < t →
            fourierCos (μ 0 t) ω = (1 + θ ^ 2 * t ^ 2 * ω ^ 2) ^ (-γ))) ∧
      (∀ (m : ℕ) (θ : ℝ), 0 < m → 0 < θ →
        ((∀ t ω : ℝ, 0 < t →
            fourierCos (μ 0 t) ω = (1 + θ ^ 2 * t ^ 2 * ω ^ 2) ^ (-(m : ℝ))) ↔
          ∀ s t ω : ℝ, 0 ≤ s → s ≤ t →
            fourierCos (μ s t) ω
              = ((1 + θ ^ 2 * s ^ 2 * ω ^ 2) / (1 + θ ^ 2 * t ^ 2 * ω ^ 2)) ^ (m : ℝ))) ∧
      (∀ (m : ℕ) (θ : ℝ), 0 < θ →
        (∀ s t ω : ℝ, 0 ≤ s → s ≤ t →
            fourierCos (μ s t) ω
              = ((1 + θ ^ 2 * s ^ 2 * ω ^ 2) / (1 + θ ^ 2 * t ^ 2 * ω ^ 2)) ^ (m : ℝ)) →
          ∀ s t : ℝ, 0 < s → s ≤ t →
            ∃ p q : Polynomial ℝ,
              p.natDegree = 2 ∧ q.natDegree = 2 ∧ (∀ ω : ℝ, 0 < q.eval ω) ∧
                ∀ ω : ℝ, fourierCos (μ s t) ω = (p ^ m).eval ω / (q ^ m).eval ω) ∧
      ∀ γ θ : ℝ, 0 < γ → 0 < θ →
        Set.EqOn (maternProfile γ θ) (fun x => maternProfile γ 1 (x / θ)) (Ioi 0) ∧
          ∀ ω : ℝ, maternExponent γ θ ω = maternExponent γ 1 (θ * ω) :=
  ⟨matern_thorin_atom P,
    matern_kernels P (fun t => μ 0 t) (fun t ht => hprob 0 t le_rfl ht.le) hcos,
    fun m θ hm hθ => matern_rational m hm θ hθ μ hprob hcas,
    fun m θ hθ hinc _ _ hs hst => matern_rational_polynomial m θ hθ μ hinc hs hst,
    fun γ θ hγ hθ => ⟨matern_gauge_profile hθ γ, matern_gauge γ θ hγ hθ⟩⟩
end SpatialLine
