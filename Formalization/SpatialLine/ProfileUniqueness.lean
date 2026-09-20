/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.ProfileIntegrability

/-!
# From an equal Lévy measure to an equal profile on `(0,∞)`

Blueprint: the backward directions of `thm:matern`(1) ⟺ (2) and (1) ⟺ (3), and the same step
wherever a node concludes that a *given* profile is a named one.

## Why this file exists, and what R9 found

Uniqueness of the Lévy pair (`prop:fourier-toolbox`(3)) identifies the **measures**
`ν(dx) = k(x)x⁻¹dx`, and a measure identifies its density only almost everywhere. R9 narrowed
`thm:matern`'s profile clauses to `Set.EqOn … (Ioi 0)` for the neighbouring reason — the exponent
says nothing about `k` off the positive half-line — and left the pointwise reading on `(0,∞)`
standing, on the ground that "there it does determine it everywhere, `maternProfile` being
continuous and strictly decreasing and `P.k` antitone". `eqOn_of_ae_eq_of_antitoneOn` is that
sentence, and it is the step no measure-theoretic lemma supplies: an almost-everywhere equality
between an antitone function and a continuous one is a pointwise equality, because the good set
meets every subinterval and the antitone function is squeezed between the continuous one's
one-sided limits.

Strict monotonicity of the continuous side is **not** needed, which the annotation's wording
suggested it might be; continuity of one side and monotonicity of the other are enough.
-/

namespace SpatialLine

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-- **An antitone function almost everywhere equal to a continuous one equals it everywhere.**

The good set `{f = g}` is co-null in `(0,∞)`, so it meets every subinterval; approaching `x`
from the left through it gives `f x ≤ f y = g y → g x`, and from the right `g x ← g z = f z ≤
f x`. -/
theorem eqOn_of_ae_eq_of_antitoneOn {f g : ℝ → ℝ}
    (hf : AntitoneOn f (Ioi (0:ℝ))) (hg : ContinuousOn g (Ioi (0:ℝ)))
    (hae : ∀ᵐ y ∂(volume.restrict (Ioi (0:ℝ))), f y = g y) :
    Set.EqOn f g (Ioi (0:ℝ)) := by
  have hnull : volume {y : ℝ | y ∈ Ioi (0:ℝ) ∧ f y ≠ g y} = 0 := by
    have h := (ae_restrict_iff' measurableSet_Ioi).mp hae
    rw [MeasureTheory.ae_iff] at h
    refine measure_mono_null ?_ h
    rintro y ⟨hy, hne⟩
    exact fun hcon => hne (hcon hy)
  have hmeet : ∀ a b : ℝ, 0 ≤ a → a < b → ∃ y ∈ Ioo a b, f y = g y := by
    intro a b ha hab
    by_contra hcon
    push Not at hcon
    have hsub : Ioo a b ⊆ {y : ℝ | y ∈ Ioi (0:ℝ) ∧ f y ≠ g y} := fun y hy =>
      ⟨lt_of_le_of_lt ha hy.1, hcon y hy⟩
    have hz : volume (Ioo a b) = 0 := measure_mono_null hsub hnull
    rw [Real.volume_Ioo, ENNReal.ofReal_eq_zero] at hz
    linarith
  intro x hx
  have hx0 : (0:ℝ) < x := hx
  have hleft : f x ≤ g x := by
    have hev : ∀ᶠ y in 𝓝[<] x, y ∈ Ioo (0:ℝ) x :=
      (mem_nhdsLT_iff_exists_Ioo_subset' hx0).mpr ⟨0, hx0, subset_rfl⟩
    have hfreq : ∃ᶠ y in 𝓝[<] x, f y = g y := by
      rw [Filter.frequently_iff]
      intro U hU
      obtain ⟨l, hl, hlU⟩ := (mem_nhdsLT_iff_exists_Ioo_subset' hx0).mp hU
      obtain ⟨y, hy, hfy⟩ := hmeet (max l 0) x (le_max_right l 0)
        (max_lt (mem_Iio.mp hl) hx0)
      exact ⟨y, hlU ⟨lt_of_le_of_lt (le_max_left l 0) hy.1, hy.2⟩, hfy⟩
    have hfr : ∃ᶠ y in 𝓝[<] x, f x ≤ g y := by
      refine (hfreq.and_eventually hev).mono ?_
      rintro y ⟨hfy, hy⟩
      rw [← hfy]
      exact hf hy.1 hx hy.2.le
    have hmem : Ioi (0:ℝ) ∈ 𝓝[<] x := mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hx0)
    have hgt : Tendsto g (𝓝[<] x) (𝓝 (g x)) :=
      (hg x hx).mono_left (nhdsWithin_le_iff.mpr hmem)
    by_contra hcon
    push Not at hcon
    obtain ⟨y, hy1, hy2⟩ := (hfr.and_eventually (hgt (Iio_mem_nhds hcon))).exists
    exact absurd hy1 (not_le.mpr hy2)
  have hright : g x ≤ f x := by
    have hxlt : x < x + 1 := by linarith
    have hev : ∀ᶠ y in 𝓝[>] x, y ∈ Ioo x (x + 1) :=
      (mem_nhdsGT_iff_exists_Ioo_subset' hxlt).mpr ⟨x + 1, hxlt, subset_rfl⟩
    have hfreq : ∃ᶠ y in 𝓝[>] x, f y = g y := by
      rw [Filter.frequently_iff]
      intro U hU
      obtain ⟨u, hu, huU⟩ := (mem_nhdsGT_iff_exists_Ioo_subset' hxlt).mp hU
      obtain ⟨y, hy, hfy⟩ := hmeet x u hx0.le (mem_Ioi.mp hu)
      exact ⟨y, huU hy, hfy⟩
    have hfr : ∃ᶠ y in 𝓝[>] x, g y ≤ f x := by
      refine (hfreq.and_eventually hev).mono ?_
      rintro y ⟨hfy, hy⟩
      rw [← hfy]
      exact hf hx (lt_trans hx0 hy.1) hy.1.le
    have hmem : Ioi (0:ℝ) ∈ 𝓝[>] x := mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hx0)
    have hgt : Tendsto g (𝓝[>] x) (𝓝 (g x)) :=
      (hg x hx).mono_left (nhdsWithin_le_iff.mpr hmem)
    by_contra hcon
    push Not at hcon
    obtain ⟨y, hy1, hy2⟩ := (hfr.and_eventually (hgt (Ioi_mem_nhds hcon))).exists
    exact absurd hy1 (not_le.mpr hy2)
  exact le_antisymm hleft hright

/-- **Equal profile measures have almost everywhere equal profiles on `(0,∞)`**, with no
monotonicity on either side.

The hypothesis the argument consumes is *measurability*, and `AntitoneOn` was only ever a way of
getting it (`aemeasurable_restrict_of_antitoneOn`): the two densities are compared through
`withDensity_eq_iff_of_sigmaFinite`, which asks for nothing else. Chapter 13's step 1 needs the
weaker form, its increment profile plus a smoothing tail not being antitone, so the primitive is
stated here at the hypothesis it uses and `ae_eq_of_profileMeasure_eq` below derives the antitone
form in two lines. -/
theorem ae_eq_of_profileMeasure_eq_aemeasurable {k₁ k₂ : ℝ → ℝ}
    (h₁m : AEMeasurable k₁ (volume.restrict (Ioi (0:ℝ)))) (h₁n : ∀ x ∈ Ioi (0:ℝ), 0 ≤ k₁ x)
    (h₂m : AEMeasurable k₂ (volume.restrict (Ioi (0:ℝ)))) (h₂n : ∀ x ∈ Ioi (0:ℝ), 0 ≤ k₂ x)
    (h : profileMeasure k₁ = profileMeasure k₂) :
    ∀ᵐ x ∂(volume.restrict (Ioi (0:ℝ))), k₁ x = k₂ x := by
  have hd₁ : AEMeasurable (fun x : ℝ => ENNReal.ofReal (k₁ x / x))
      (volume.restrict (Ioi (0:ℝ))) := (h₁m.div aemeasurable_id).ennreal_ofReal
  have hd₂ : AEMeasurable (fun x : ℝ => ENNReal.ofReal (k₂ x / x))
      (volume.restrict (Ioi (0:ℝ))) := (h₂m.div aemeasurable_id).ennreal_ofReal
  simp only [profileMeasure] at h
  have hae0 := (withDensity_eq_iff_of_sigmaFinite hd₁ hd₂).mp h
  have hmem : ∀ᵐ x ∂(volume.restrict (Ioi (0:ℝ))), x ∈ Ioi (0:ℝ) :=
    self_mem_ae_restrict measurableSet_Ioi
  filter_upwards [hae0, hmem] with x hx hxm
  have hx0 : (0:ℝ) < x := hxm
  have heq := (ENNReal.ofReal_eq_ofReal_iff (div_nonneg (h₁n x hxm) hx0.le)
    (div_nonneg (h₂n x hxm) hx0.le)).mp hx
  field_simp at heq
  exact heq

/-- Equal profile measures have almost everywhere equal profiles on `(0,∞)`, the first profile
antitone: the form chapters 8 and 10 consume, an antitone function on `(0,∞)` being almost
everywhere measurable there. -/
theorem ae_eq_of_profileMeasure_eq {k₁ k₂ : ℝ → ℝ}
    (h₁a : AntitoneOn k₁ (Ioi 0)) (h₁n : ∀ x ∈ Ioi (0:ℝ), 0 ≤ k₁ x)
    (h₂m : AEMeasurable k₂ (volume.restrict (Ioi 0)))
    (h₂n : ∀ x ∈ Ioi (0:ℝ), 0 ≤ k₂ x)
    (h : profileMeasure k₁ = profileMeasure k₂) :
    ∀ᵐ x ∂(volume.restrict (Ioi (0:ℝ))), k₁ x = k₂ x :=
  ae_eq_of_profileMeasure_eq_aemeasurable
    (aemeasurable_restrict_of_antitoneOn measurableSet_Ioi h₁a) h₁n h₂m h₂n h

/-- **Equal profile measures, continuous comparison profile: equal on `(0,∞)`.** The two lemmas
above, composed; this is the form the corner theorems consume. -/
theorem eqOn_of_profileMeasure_eq {k₁ k₂ : ℝ → ℝ}
    (h₁a : AntitoneOn k₁ (Ioi 0)) (h₁n : ∀ x ∈ Ioi (0:ℝ), 0 ≤ k₁ x)
    (h₂m : AEMeasurable k₂ (volume.restrict (Ioi 0)))
    (h₂n : ∀ x ∈ Ioi (0:ℝ), 0 ≤ k₂ x) (h₂c : ContinuousOn k₂ (Ioi 0))
    (h : profileMeasure k₁ = profileMeasure k₂) :
    Set.EqOn k₁ k₂ (Ioi 0) :=
  eqOn_of_ae_eq_of_antitoneOn h₁a h₂c (ae_eq_of_profileMeasure_eq h₁a h₁n h₂m h₂n h)

end SpatialLine
