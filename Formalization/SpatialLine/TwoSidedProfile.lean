/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.BrownianDensity
import SpatialLine.TwoSidedDefs

/-!
# The two-sided profile, and the folding translation

Blueprint: `blueprint/src/parts/08-cone.tex` — `lem:folding-translation`, the `[T]` lemma that
carries ledger **A10** from Sato's convention into this article's, and
`prop:cin-origin-singularity`, whose three regimes an admitted A10 would then discharge.

## What is here and why

Chapter 2's folding convention says that a symmetric Lévy measure on `ℝ \ {0}` enters
`eq:levy-khintchine` as its image under `x ↦ |x|`, so that a two-sided Lévy density written
`h(|x|)/|x|` has folded profile `k = 2h`. Every source this article cites for the *behaviour* of
a self-decomposable density — ledger A10 is the one at issue — states its results in the
two-sided convention, through the `k`-function of the Lévy density `k(x)/|x|` on `ℝ \ {0}` and
the two one-sided limits `k(0+)`, `k(0−)`. This development has no two-sided profile: `SDProfile`
is folded, carried by `(0,∞)`, and that is all Chapters 7 to 13 quantify over. So the translation
between the two conventions — which A10's ledger entry says in as many words that the entry does
**not** carry — was asserted in prose in three places and checked nowhere.

`TwoSidedProfile` is the source's datum: a nonnegative `k` on `ℝ`, nonincreasing on `(0,∞)`,
nondecreasing on `(−∞,0)`, with Sato's Lévy condition `∫(1 ∧ x²)k(x)|x|⁻¹dx < ∞`. It is a
**vocabulary for citations**, not a class this development's theorems range over; nothing in
`SpatialLine` outside this file, `SpatialLine/MaternThreshold.lean`,
`SpatialLine/OriginSingularity.lean` and the ledger A10 section of `SpatialLine/Interfaces.lean`
mentions it. Since the admission of A10 (2026-09-15) it is declared in
`SpatialLine/TwoSidedDefs.lean` rather than here, together with the three specifications below:
`Interfaces` has to import that vocabulary, and importing a chapter 8 *theorem* module would pull
chapter 8 into the line paper's release closure. The split is the `CornerDefs`/`VariationDefs`
arrangement of R158.

`SDProfile.twoSided` is the translation: `k₂(x) = k(|x|)/2`, the halving that undoes the folding.
The four things it has to supply are

* `twoSided_exponent` — the two-sided exponent of `k₂` is the folded exponent of `k` when the
  Gaussian coefficient is `0`, so a law specified through the folded exponent is the law the
  source speaks about;
* `twoSided_k_add_neg` — `k₂(x) + k₂(−x) = k(x)` for `x > 0`, the pointwise form of the same
  statement, and what carries a source's *formula* in `k` across;
* `twoSided_tendsto_nhdsGT` and `twoSided_tendsto_nhdsLT` — the two one-sided limits exist and
  are each `c/2` when the folded profile has right limit `c`, so the source's constant
  `c = k₂(0+) + k₂(0−)` is the folded `k(0+)` and its antisymmetric constant
  `c′ = k₂(0+) − k₂(0−)` vanishes.

`folding_translation` bundles the four; it is the `\lean{}` tag of `lem:folding-translation`.

## The specifications at Sato's letter

`SatoOriginSingular`, `SatoOriginSmooth` and `SatoOriginThreshold` (`SpatialLine/TwoSidedDefs.lean`)
are ledger A10's three regimes **typed at the source's letter**: quantified over a
`TwoSidedProfile`, with `c` the sum of the two one-sided limits and the threshold's comparison
function written in `k₂(u) + k₂(−u)`. They are `Prop`-valued *definitions*, and the three
`cin_origin_singularity_*_of_sato` theorems below derive the node's folded statements from them
*taken as hypotheses*, on Lean core, through the translation above. That is judgement point 11 of
the charter — a specification is a hypothesis, and a hypothesis can be quantified over — and it is
what let the proposed admission be checked before it was taken.

**They are now inhabited by admitted axioms** (2026-09-15, the author's decision): `A10` is on
`blueprint/trust-boundary.txt` as `sato_origin_singular`, `sato_origin_smooth` and
`sato_origin_threshold`, declared in `SpatialLine/Interfaces.lean`. Everything in *this* file
stays on Lean core, and that is the point of the arrangement: what the axioms carry is the
source's sentence, and the translation into the article's folded convention is proved here, beside
them. The three theorems that spend the axioms are `SpatialLine/OriginSingularity.lean`, each a
single application of one `_of_sato` theorem to one axiom.

## One thing found while writing this

The even-function split `∫_ℝ = 2∫_{(0,∞)}` was already in the library, as
`SpatialLine.lintegral_even_eq_two_mul` in `SpatialLine/BrownianDensity.lean`, written for the
folded Gaussian jump integral. It is used three times here and was not rewritten; the import of
`BrownianDensity` is for that lemma alone, and it costs nothing, that module being below every
chapter this file serves.
-/

namespace SpatialLine

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-! ## The source's datum

`TwoSidedProfile`, its `exponentL` and its `exponent` are in `SpatialLine/TwoSidedDefs.lean`,
which `SpatialLine/Interfaces.lean` imports for the three A10 axioms; see the module docstring
above for why the definitions and the theorems about them are in two files. -/

/-! ## Sato's factor `K` is an honest integral

`TwoSidedProfile.satoK c y = exp[∫_y^1 (c − k(u) − k(−u))u⁻¹du]` (`SpatialLine/TwoSidedDefs.lean`)
is the factor (53.25) that both comparison functions of ledger **A10** carry. Bochner's integral
returns `0` on a non-integrable integrand, and there `satoK` would be `1` identically — which is
exactly the false form the singular regime had before R171 (2026-09-19). So the integrability is
proved, once, for every two-sided profile: the integrand is measurable, `k` being monotone on each
piece, and bounded on `(y,1)` by `(|c| + k(y) + k(−y))/y`. -/

/-- The reflected profile is antitone on the positive ray, `k` being monotone on the negative
one. -/
theorem TwoSidedProfile.antitoneOn_k_neg (K : TwoSidedProfile) :
    AntitoneOn (fun u : ℝ => K.k (-u)) (Ioi (0 : ℝ)) := by
  intro u hu v hv huv
  have hu0 : (0 : ℝ) < u := hu
  have hv0 : (0 : ℝ) < v := hv
  exact K.k_monotoneOn (mem_Iio.mpr (by linarith)) (mem_Iio.mpr (by linarith)) (by linarith)

/-- **The integrand of Sato's `K` is integrable on `(y,1)` for every `y > 0`.** So `satoK` is an
exponential of a genuine integral and not of `integral`'s junk value; see the module note above
for why that is load-bearing. -/
theorem TwoSidedProfile.integrableOn_satoIntegrand (K : TwoSidedProfile) (c : ℝ) {y : ℝ}
    (hy : 0 < y) : IntegrableOn (fun u => (c - (K.k u + K.k (-u))) / u) (Ioo y 1) := by
  have hfin : volume (Ioo y (1 : ℝ)) ≠ ⊤ := by
    rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
  have hsub : Ioo y (1 : ℝ) ⊆ Ioi (0 : ℝ) := fun u hu => mem_Ioi.mpr (lt_trans hy hu.1)
  have hmeas1 : AEMeasurable K.k (volume.restrict (Ioo y 1)) :=
    (aemeasurable_restrict_of_antitoneOn measurableSet_Ioi K.k_antitoneOn).mono_measure
      (Measure.restrict_mono hsub le_rfl)
  have hmeas2 : AEMeasurable (fun u : ℝ => K.k (-u)) (volume.restrict (Ioo y 1)) :=
    (aemeasurable_restrict_of_antitoneOn measurableSet_Ioi K.antitoneOn_k_neg).mono_measure
      (Measure.restrict_mono hsub le_rfl)
  refine Integrable.mono' (g := fun _ : ℝ => (|c| + (K.k y + K.k (-y))) / y)
    (integrableOn_const (hs := hfin))
    ((aemeasurable_const.sub (hmeas1.add hmeas2)).div aemeasurable_id).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
  have hu0 : 0 < u := lt_trans hy hu.1
  have h1 : K.k u ≤ K.k y := K.k_antitoneOn (mem_Ioi.mpr hy) (mem_Ioi.mpr hu0) hu.1.le
  have h2 : K.k (-u) ≤ K.k (-y) :=
    K.k_monotoneOn (mem_Iio.mpr (by linarith)) (mem_Iio.mpr (by linarith)) (neg_le_neg hu.1.le)
  have hnum : |c - (K.k u + K.k (-u))| ≤ |c| + (K.k y + K.k (-y)) := by
    refine abs_le.mpr ⟨?_, ?_⟩
    · linarith [neg_abs_le c, K.k_nonneg u, K.k_nonneg (-u)]
    · linarith [le_abs_self c, K.k_nonneg u, K.k_nonneg (-u)]
  have hB : (0 : ℝ) ≤ |c| + (K.k y + K.k (-y)) :=
    add_nonneg (abs_nonneg c) (add_nonneg (K.k_nonneg y) (K.k_nonneg (-y)))
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hu0, div_le_div_iff₀ hu0 hy]
  nlinarith [abs_nonneg (c - (K.k u + K.k (-u))), hu.1.le, hy.le]

/-! ## The halving that undoes the folding -/

/-- `k₂(x) = k(|x|)/2`, the two-sided profile of a folded one. -/
noncomputable def foldedHalf (P : SDProfile) : ℝ → ℝ := fun x => P.k |x| / 2

theorem foldedHalf_apply (P : SDProfile) (x : ℝ) : foldedHalf P x = P.k |x| / 2 := rfl

theorem foldedHalf_neg (P : SDProfile) (x : ℝ) : foldedHalf P (-x) = foldedHalf P x := by
  rw [foldedHalf_apply, foldedHalf_apply, abs_neg]

theorem foldedHalf_of_pos (P : SDProfile) {x : ℝ} (hx : 0 < x) :
    foldedHalf P x = P.k x / 2 := by
  rw [foldedHalf_apply, abs_of_pos hx]

theorem foldedHalf_nonneg (P : SDProfile) (x : ℝ) : 0 ≤ foldedHalf P x := by
  rcases eq_or_ne x 0 with hx | hx
  · rw [foldedHalf_apply, hx, abs_zero, P.k_zero]; norm_num
  · exact div_nonneg (P.k_nonneg _ (abs_pos.mpr hx)) (by norm_num)

theorem foldedHalf_antitoneOn (P : SDProfile) : AntitoneOn (foldedHalf P) (Ioi (0 : ℝ)) := by
  intro u hu v hv huv
  have h : P.k v ≤ P.k u := P.k_antitone hu hv huv
  have hu' : (0 : ℝ) < u := hu
  have hv' : (0 : ℝ) < v := hv
  rw [foldedHalf_of_pos P hu', foldedHalf_of_pos P hv']
  linarith

theorem foldedHalf_monotoneOn (P : SDProfile) : MonotoneOn (foldedHalf P) (Iio (0 : ℝ)) := by
  intro u hu v hv huv
  have hu' : u < (0 : ℝ) := hu
  have hv' : v < (0 : ℝ) := hv
  have hvu : (0 : ℝ) < -v := neg_pos.mpr hv'
  have huu : (0 : ℝ) < -u := neg_pos.mpr hu'
  have h : P.k (-u) ≤ P.k (-v) := P.k_antitone (mem_Ioi.mpr hvu) (mem_Ioi.mpr huu) (by linarith)
  rw [foldedHalf_apply, foldedHalf_apply, abs_of_neg hu', abs_of_neg hv']
  linarith

/-! ### The two integrals -/

/-- The folded form of Sato's Lévy condition is the two conditions of
`lem:profile-integrability`, read on the two halves of the range. -/
theorem lintegral_Ioi_min_profile_ne_top (P : SDProfile) :
    (∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (min 1 (x ^ 2) * P.k x / x)) ≠ ⊤ := by
  have hdisj : Disjoint (Ioo (0 : ℝ) 1) (Ici (1 : ℝ)) := by
    rw [Set.disjoint_left]
    rintro x ⟨-, hx2⟩ hx3
    exact absurd (mem_Ici.mp hx3) (not_le.mpr hx2)
  rw [← Ioo_union_Ici_eq_Ioi (zero_lt_one (α := ℝ)), lintegral_union measurableSet_Ici hdisj]
  refine ENNReal.add_ne_top.mpr ⟨?_, ?_⟩
  · have h : (∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (min 1 (x ^ 2) * P.k x / x))
        = ∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (x * P.k x) := by
      refine setLIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
      have hx0 : (0 : ℝ) < x := hx.1
      have hx1 : x < 1 := hx.2
      have hmin : min 1 (x ^ 2) = x ^ 2 := min_eq_right (by nlinarith)
      rw [hmin]
      congr 1
      field_simp
    rw [h]
    exact P.integrable_near_zero
  · have hIci : (∫⁻ x in Ici (1 : ℝ), ENNReal.ofReal (min 1 (x ^ 2) * P.k x / x))
        = ∫⁻ x in Ioi (1 : ℝ), ENNReal.ofReal (min 1 (x ^ 2) * P.k x / x) :=
      setLIntegral_congr Ioi_ae_eq_Ici.symm
    rw [hIci]
    have h : (∫⁻ x in Ioi (1 : ℝ), ENNReal.ofReal (min 1 (x ^ 2) * P.k x / x))
        = ∫⁻ x in Ioi (1 : ℝ), ENNReal.ofReal (P.k x / x) := by
      refine setLIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
      have hx1 : (1 : ℝ) < x := hx
      have hmin : min 1 (x ^ 2) = 1 := min_eq_left (by nlinarith)
      rw [hmin, one_mul]
    rw [h]
    exact P.integrable_at_top

theorem foldedHalf_levy_condition (P : SDProfile) :
    (∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2) * foldedHalf P x / |x|)) ≠ ⊤ := by
  have heven : ∀ x : ℝ,
      (fun y : ℝ => ENNReal.ofReal (min 1 (y ^ 2) * foldedHalf P y / |y|)) (-x)
        = (fun y : ℝ => ENNReal.ofReal (min 1 (y ^ 2) * foldedHalf P y / |y|)) x := by
    intro x
    show ENNReal.ofReal (min 1 ((-x) ^ 2) * foldedHalf P (-x) / |(-x)|)
      = ENNReal.ofReal (min 1 (x ^ 2) * foldedHalf P x / |x|)
    rw [neg_sq, foldedHalf_neg, abs_neg]
  rw [lintegral_even_eq_two_mul heven]
  refine ENNReal.mul_ne_top (by norm_num) ?_
  refine ne_top_of_le_ne_top (lintegral_Ioi_min_profile_ne_top P) (lintegral_mono_ae ?_)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : (0 : ℝ) < x := hx
  refine ENNReal.ofReal_le_ofReal ?_
  have hA : (0 : ℝ) ≤ min 1 (x ^ 2) := le_min zero_le_one (sq_nonneg x)
  have hk : (0 : ℝ) ≤ P.k x := P.k_nonneg x hx
  rw [foldedHalf_of_pos P hx0, abs_of_pos hx0,
    show min 1 (x ^ 2) * (P.k x / 2) / x = min 1 (x ^ 2) * P.k x / x / 2 by ring]
  exact half_le_self (div_nonneg (mul_nonneg hA hk) hx0.le)

/-- `2·ofReal(a/2) = ofReal a`, the cancellation of the folding factor. -/
theorem two_mul_ofReal_half (a : ℝ) :
    (2 : ℝ≥0∞) * ENNReal.ofReal (a / 2) = ENNReal.ofReal a := by
  have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
  rw [h2, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  ring

/-- **The exponents agree**: the two-sided exponent of `k₂` is the folded exponent of `k`. -/
theorem lintegral_foldedHalf_one_sub_cos (P : SDProfile) (ω : ℝ) :
    (∫⁻ x, ENNReal.ofReal ((1 - Real.cos (ω * x)) * foldedHalf P x / |x|))
      = ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal ((1 - Real.cos (ω * x)) * P.k x / x) := by
  have heven : ∀ x : ℝ,
      (fun y : ℝ => ENNReal.ofReal ((1 - Real.cos (ω * y)) * foldedHalf P y / |y|)) (-x)
        = (fun y : ℝ => ENNReal.ofReal ((1 - Real.cos (ω * y)) * foldedHalf P y / |y|)) x := by
    intro x
    show ENNReal.ofReal ((1 - Real.cos (ω * -x)) * foldedHalf P (-x) / |(-x)|)
      = ENNReal.ofReal ((1 - Real.cos (ω * x)) * foldedHalf P x / |x|)
    rw [foldedHalf_neg, abs_neg, show ω * -x = -(ω * x) by ring, Real.cos_neg]
  rw [lintegral_even_eq_two_mul heven,
    ← lintegral_const_mul' 2 _ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
  refine setLIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx0 : (0 : ℝ) < x := hx
  show (2 : ℝ≥0∞) * ENNReal.ofReal ((1 - Real.cos (ω * x)) * foldedHalf P x / |x|)
    = ENNReal.ofReal ((1 - Real.cos (ω * x)) * P.k x / x)
  rw [foldedHalf_of_pos P hx0, abs_of_pos hx0,
    show (1 - Real.cos (ω * x)) * (P.k x / 2) / x
      = ((1 - Real.cos (ω * x)) * P.k x / x) / 2 by ring]
  exact two_mul_ofReal_half _

/-! ## The translation -/

/-- **The halving that undoes the folding**, as a `TwoSidedProfile`. -/
noncomputable def SDProfile.twoSided (P : SDProfile) : TwoSidedProfile where
  k := foldedHalf P
  k_nonneg := foldedHalf_nonneg P
  k_antitoneOn := foldedHalf_antitoneOn P
  k_monotoneOn := foldedHalf_monotoneOn P
  levy_condition := foldedHalf_levy_condition P

@[simp]
theorem twoSided_k (P : SDProfile) : P.twoSided.k = foldedHalf P := rfl

/-- **The pointwise form of the folding**: the two one-sided values add up to the folded one. -/
theorem twoSided_k_add_neg (P : SDProfile) {x : ℝ} (hx : 0 < x) :
    P.twoSided.k x + P.twoSided.k (-x) = P.k x := by
  rw [twoSided_k, foldedHalf_neg, foldedHalf_of_pos P hx]
  ring

/-- **The exponents agree**, `ℝ≥0∞`-valued, for a profile with Gaussian coefficient `0`. -/
theorem twoSided_exponentL (P : SDProfile) (ha : P.a = 0) (ω : ℝ) :
    P.twoSided.exponentL ω = P.exponentL ω := by
  change (∫⁻ x, ENNReal.ofReal ((1 - Real.cos (ω * x)) * foldedHalf P x / |x|))
    = ENNReal.ofReal (P.a * ω ^ 2)
      + ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal ((1 - Real.cos (ω * x)) * P.k x / x)
  rw [ha, zero_mul, ENNReal.ofReal_zero, zero_add, lintegral_foldedHalf_one_sub_cos]

/-- **The exponents agree**, real-valued. -/
theorem twoSided_exponent (P : SDProfile) (ha : P.a = 0) (ω : ℝ) :
    P.twoSided.exponent ω = P.exponent ω := by
  change (P.twoSided.exponentL ω).toReal = (P.exponentL ω).toReal
  rw [twoSided_exponentL P ha]

/-- **The right limit**: `k₂(0+) = k(0+)/2`. -/
theorem twoSided_tendsto_nhdsGT (P : SDProfile) {c : ℝ}
    (hk : Tendsto P.k (𝓝[>] (0 : ℝ)) (𝓝 c)) :
    Tendsto P.twoSided.k (𝓝[>] (0 : ℝ)) (𝓝 (c / 2)) := by
  refine Tendsto.congr' ?_ (hk.div_const 2)
  filter_upwards [self_mem_nhdsWithin] with x hx
  rw [twoSided_k]
  exact (foldedHalf_of_pos P hx).symm

/-- **The left limit**: `k₂(0−) = k(0+)/2` too, so the source's antisymmetric constant
vanishes. -/
theorem twoSided_tendsto_nhdsLT (P : SDProfile) {c : ℝ}
    (hk : Tendsto P.k (𝓝[>] (0 : ℝ)) (𝓝 c)) :
    Tendsto P.twoSided.k (𝓝[<] (0 : ℝ)) (𝓝 (c / 2)) := by
  have hneg : Tendsto (fun x : ℝ => -x) (𝓝[<] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h : Tendsto (fun x : ℝ => -x) (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
        simpa using continuous_neg.tendsto (0 : ℝ)
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact mem_Ioi.mpr (neg_pos.mpr hx)
  refine Tendsto.congr' ?_ ((hk.comp hneg).div_const 2)
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x < 0 := hx
  show P.k (-x) / 2 = P.twoSided.k x
  rw [twoSided_k, foldedHalf_apply, abs_of_neg hx0]

/-- **The folding translation** (`lem:folding-translation`). For a symmetric law the source's
two-sided datum is the halved folded profile; its exponent is the folded exponent, its two
one-sided limits at the origin exist and add up to the folded `k(0+)`, and their difference —
the source's antisymmetric constant — is `0`. -/
theorem folding_translation (P : SDProfile) (ha : P.a = 0) {c : ℝ}
    (hk : Tendsto P.k (𝓝[>] (0 : ℝ)) (𝓝 c)) :
    (∀ ω, P.twoSided.exponent ω = P.exponent ω) ∧
      (∀ x, 0 < x → P.twoSided.k x + P.twoSided.k (-x) = P.k x) ∧
      ∃ cp cm : ℝ, Tendsto P.twoSided.k (𝓝[>] (0 : ℝ)) (𝓝 cp) ∧
        Tendsto P.twoSided.k (𝓝[<] (0 : ℝ)) (𝓝 cm) ∧ cp + cm = c ∧ cp - cm = 0 :=
  ⟨fun ω => twoSided_exponent P ha ω, fun _ hx => twoSided_k_add_neg P hx,
    c / 2, c / 2, twoSided_tendsto_nhdsGT P hk, twoSided_tendsto_nhdsLT P hk, by ring, by ring⟩

/-! ## What the admission buys: the node's folded statements, from the specifications

The three theorems below are the translation, and they are on Lean core: each takes the
corresponding specification of `SpatialLine/TwoSidedDefs.lean` *as a hypothesis* and derives the
folded statement of `prop:cin-origin-singularity`. They were written on 2026-09-15 to check that
an admission of ledger A10 would suffice before it was taken; since the admission (the author's
decision, the same day) they are what carries the three axioms of `SpatialLine/Interfaces.lean`
into the article's convention, in `SpatialLine/OriginSingularity.lean`. -/

/-- **The folded form of Sato's factor `K`.** For a symmetric law the two-sided `satoK` is the
article's `K(y) = exp[∫_y^1 (c − k(u))u⁻¹du]`: the inner integrand `(c − k₂(u) − k₂(−u))u⁻¹`
becomes `(c − k(u))u⁻¹` by `twoSided_k_add_neg`, every `u` in the range being positive. -/
theorem twoSided_satoK (P : SDProfile) (c : ℝ) {y : ℝ} (hy : 0 < y) :
    P.twoSided.satoK c y = Real.exp (∫ u in Ioo y 1, (c - P.k u) / u) := by
  rw [TwoSidedProfile.satoK_apply]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
  rw [twoSided_k_add_neg P (lt_trans hy hu.1)]

/-- **The folded integrand of `K` is integrable too**, at every `c` and every `y > 0`: it agrees
on `(y,1)` with the two-sided one, whose integrability is `integrableOn_satoIntegrand`. So the
`K` printed in the blueprint's statement of `prop:cin-origin-singularity` is an exponential of a
genuine integral, in the article's convention as well as in the source's. -/
theorem integrableOn_foldedSatoIntegrand (P : SDProfile) (c : ℝ) {y : ℝ} (hy : 0 < y) :
    IntegrableOn (fun u => (c - P.k u) / u) (Ioo y 1) := by
  refine (P.twoSided.integrableOn_satoIntegrand c hy).congr_fun ?_ measurableSet_Ioo
  intro u hu
  dsimp only
  rw [twoSided_k_add_neg P (lt_trans hy hu.1)]

/-- **`prop:cin-origin-singularity`, the singular regime, from `SatoOriginSingular`.** The
specification is a hypothesis; the proof is the folding translation and nothing else, and it is
on Lean core.

**2026-09-19 (R171):** the comparison function carries the factor `K`, which the axiom was missing
and without which it is false; the two positivity hypotheses of (53.24) are supplied from
`0 < c`, both one-sided limits of a folded profile being `c/2`. -/
theorem cin_origin_singularity_unbounded_of_sato (H : SatoOriginSingular)
    (P : SDProfile) (ha : P.a = 0) {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (hk : Tendsto P.k (𝓝[>] (0 : ℝ)) (𝓝 c))
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hsym : IsSymmetric μ)
    (hcos : ∀ ω : ℝ, fourierCos μ ω = Real.exp (-P.exponent ω)) :
    ∃ p : ℝ → ℝ, μ = volume.withDensity (fun x => ENNReal.ofReal (p x)) ∧
      ∃ c₁ c₂ δ : ℝ, 0 < c₁ ∧ c₁ ≤ c₂ ∧ 0 < δ ∧
        ∀ x : ℝ, 0 < |x| → |x| < δ →
          c₁ * (|x| ^ (c - 1) * Real.exp (∫ u in Ioo |x| 1, (c - P.k u) / u)) ≤ p x ∧
            p x ≤ c₂ * (|x| ^ (c - 1) * Real.exp (∫ u in Ioo |x| 1, (c - P.k u) / u)) := by
  have hsum : c / 2 + c / 2 = c := by ring
  obtain ⟨p, hp, c₁, c₂, δ, hc₁, hc₁₂, hδ, hbound⟩ :=
    H P.twoSided (c / 2) (c / 2) (twoSided_tendsto_nhdsGT P hk) (twoSided_tendsto_nhdsLT P hk)
      (by positivity) (by positivity) (by rw [hsum]; exact hc1)
      μ inferInstance hsym (fun ω => by rw [hcos ω, twoSided_exponent P ha ω])
  refine ⟨p, hp, c₁, c₂, δ, hc₁, hc₁₂, hδ, fun x hx hxδ => ?_⟩
  have hb := hbound x hx hxδ
  rw [hsum, twoSided_satoK P c hx] at hb
  exact hb

/-- **`prop:cin-origin-singularity`, the smooth regime, from `SatoOriginSmooth`.** -/
theorem cin_origin_singularity_smooth_of_sato (H : SatoOriginSmooth)
    (P : SDProfile) (ha : P.a = 0) {c : ℝ} {N : ℕ}
    (hN : 1 ≤ N) (hcN : (N : ℝ) < c) (hcN' : c ≤ N + 1)
    (hk : Tendsto P.k (𝓝[>] (0 : ℝ)) (𝓝 c))
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hsym : IsSymmetric μ)
    (hcos : ∀ ω : ℝ, fourierCos μ ω = Real.exp (-P.exponent ω)) :
    ∃ p : ℝ → ℝ, μ = volume.withDensity (fun x => ENNReal.ofReal (p x)) ∧
      ContDiff ℝ (((N - 1 : ℕ) : ℕ∞) : WithTop ℕ∞) p := by
  have hsum : c / 2 + c / 2 = c := by ring
  exact H P.twoSided (c / 2) (c / 2) N (twoSided_tendsto_nhdsGT P hk)
    (twoSided_tendsto_nhdsLT P hk) hN (by rw [hsum]; exact hcN) (by rw [hsum]; exact hcN')
    μ inferInstance hsym (fun ω => by rw [hcos ω, twoSided_exponent P ha ω])

/-- **`prop:cin-origin-singularity`, the threshold regime, from `SatoOriginThreshold`.** Here the
translation does visible work: the source's comparison function is written in `k₂(u) + k₂(−u)`,
and `twoSided_satoK` rewrites it into the article's `k(u)` under the integral, every `y` in the
outer range being positive. -/
theorem cin_origin_singularity_threshold_of_sato (H : SatoOriginThreshold)
    (P : SDProfile) (ha : P.a = 0)
    (hk : Tendsto P.k (𝓝[>] (0 : ℝ)) (𝓝 1))
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hsym : IsSymmetric μ)
    (hcos : ∀ ω : ℝ, fourierCos μ ω = Real.exp (-P.exponent ω)) :
    ∃ p : ℝ → ℝ, μ = volume.withDensity (fun x => ENNReal.ofReal (p x)) ∧
      ∃ c₁ c₂ δ : ℝ, 0 < c₁ ∧ c₁ ≤ c₂ ∧ 0 < δ ∧
        ∀ x : ℝ, 0 < |x| → |x| < δ →
          c₁ * (∫ y in Ioo |x| 1, Real.exp (∫ u in Ioo y 1, (1 - P.k u) / u) / y) ≤ p x ∧
            p x ≤ c₂ * ∫ y in Ioo |x| 1, Real.exp (∫ u in Ioo y 1, (1 - P.k u) / u) / y := by
  have hgt : Tendsto P.twoSided.k (𝓝[>] (0 : ℝ)) (𝓝 ((1 : ℝ) / 2)) :=
    twoSided_tendsto_nhdsGT P hk
  have hlt : Tendsto P.twoSided.k (𝓝[<] (0 : ℝ)) (𝓝 ((1 : ℝ) / 2)) :=
    twoSided_tendsto_nhdsLT P hk
  obtain ⟨p, hp, c₁, c₂, δ, hc₁, hc₁₂, hδ, hbound⟩ :=
    H P.twoSided (1 / 2) (1 / 2) hgt hlt (by norm_num) (by norm_num) (by norm_num)
      μ inferInstance hsym (fun ω => by rw [hcos ω, twoSided_exponent P ha ω])
  have houter : ∀ x : ℝ, 0 < |x| →
      (∫ y in Ioo |x| 1, P.twoSided.satoK 1 y / y)
        = ∫ y in Ioo |x| 1, Real.exp (∫ u in Ioo y 1, (1 - P.k u) / u) / y := by
    intro x hx
    refine setIntegral_congr_fun measurableSet_Ioo fun y hy => ?_
    rw [twoSided_satoK P 1 (lt_trans hx hy.1)]
  refine ⟨p, hp, c₁, c₂, δ, hc₁, hc₁₂, hδ, fun x hx hxδ => ?_⟩
  have hb := hbound x hx hxδ
  rwa [houter x hx] at hb

end SpatialLine
