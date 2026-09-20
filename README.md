# Spatial scale space from hemigroup axioms: the admissible cone, its corners and their implementation — release cone-v0.1

This repository is the verification artifact of the article of the same name (the PDF is at the
root). It is an export of the development repository at revision `5424a6e`, restricted to what
the article's statements rest on; the development repository also holds the material of other
modules of the same theory and stays private until they are released.

## What is here

- `Formalization/` — the Lean 4 development: the transitive import closure of every module that a
  numbered statement of the article names (123 modules), with the toolchain pinned in-tree
  (`lean-toolchain`, `lake-manifest.json`). `SpatialLine/` is sorry-free; `Skeleton/` holds the
  typed statements of the nodes the article marks as not machine-checked.
- `Formalization/CIAxiomGuard.lean` — prints the axiom usage of every named declaration.
- `blueprint/trust-boundary.txt`, `blueprint/AXIOMS.md` — the fourteen interface names of the full
  development, each with the page-verified citation it rests on and the step it carries beyond its
  source; `blueprint/AXIOMS-verbatim.md`, where it is present, sets the sources' own wording beside
  each entry. The headline theorem, `SpatialLine.matern_theorem`, rests on 1 of them, and section 1.1 of the paper says what the other results rest on.
- `blueprint/src/parts/` — the statements and proofs of record of the article's sections 8, 9, 10, 11, 14 (the
  blueprint's chapters of the same numbers), with the `\lean{}` tag naming the declaration behind
  each statement; a chapter of another module is included where the article transcribes a
  statement from it.
- `paper/`, `figures/` — the article's sources.
- `notes/` — the process account, the external reviews verbatim, and the response plan.

## Verifying

    cd Formalization
    lake exe cache get        # Mathlib's prebuilt oleans
    lake build
    lake env lean CIAxiomGuard.lean

The last command prints, for `SpatialLine.matern_theorem`, Lean's three logical axioms and
`SpatialLine.fourier_toolbox_levy_unique`, and nothing else (the block printed in section 1.1).

## Statements and declarations

| blueprint node (chapter) | declarations |
|---|---|
| `lem:cin-rays (08)` | `SpatialLine.cin_ray`, `SpatialLine.cin_elementary`, `SpatialLine.cin_expansion_zero`, `SpatialLine.cin_expansion_top`, `SpatialLine.cin_superposition`, `SpatialLine.cin_superposition_exists` |
| `prop:choquet-cone (08)` | `SpatialLine.choquet_cone_forward`, `SpatialLine.choquet_cone_surjective`, `SpatialLine.choquet_cone_domain`, `SpatialLine.choquet_cone_linear`, `SpatialLine.choquet_cone_injective`, `SpatialLine.choquet_cone_extreme_gaussian`, `SpatialLine.choquet_cone_extreme_cin`, `SpatialLine.choquet_cone_extreme_only` |
| `lem:cin-delay-equation (08)` | `SpatialLine.cin_delay_equation`, `SpatialLine.cin_delay_equation_deriv` |
| `lem:folding-translation (08)` | `SpatialLine.folding_translation` |
| `prop:cin-origin-singularity (08)` | `SpatialLine.cin_origin_singularity_unbounded`, `SpatialLine.cin_origin_singularity_smooth`, `SpatialLine.cin_origin_singularity_threshold`, `SpatialLine.one_le_satoK`, `SpatialLine.cin_origin_singularity_cin_ray` |
| `cor:origin-boundedness (08)` | `SpatialLine.origin_boundedness`, `SpatialLine.matern_origin_boundedness`, `SpatialLine.matern_origin_constant` |
| `lem:bridge-exponents (09)` | `SpatialLine.bridge_exponents`, `SpatialLine.bridge_exponents_mixture` |
| `prop:bridge-families (09)` | `SpatialLine.bridge_families`, `SpatialLine.bridge_families_delay`, `SpatialLine.bridge_families_gamma`, `SpatialLine.bridge_families_bessel`, `SpatialLine.bridge_families_stable` |
| `prop:bridge-strictness (09)` | `SpatialLine.bridge_strictness_criterion`, `SpatialLine.bridge_strictness_increasing`, `SpatialLine.bridge_strictness_cin`, `SpatialLine.bridge_strictness_stationary`, `SpatialLine.bridge_strictness_cone` |
| `lem:subordinated-members (09)` | `SpatialLine.subordinated_members` |
| `lem:student-subordinated (09)` | `SpatialLine.student_subordinated` |
| `def:delay-data (09)` | `Skeleton.DelayDatum`, `Skeleton.DelayDatum.exponent`, `Skeleton.IsTypeG`, `Skeleton.polarProfile` |
| `lem:filtration-strictness (09)` | `Skeleton.filtration_strictness_typeG`, `Skeleton.filtration_strictness_dimension` |
| `prop:moments-tails (10)` | `SpatialLine.moments_tails_criterion`, `SpatialLine.moments_tails_variance`, `Skeleton.moments_tails_bounded`, `SpatialLine.moments_tails_divergence`, `Skeleton.moments_tails_heavy`, `SpatialLine.moments_tails_completely_monotone` |
| `prop:matern-exponent (10)` | `SpatialLine.matern_exponent`, `SpatialLine.matern_transforms`, `SpatialLine.matern_moments`, `SpatialLine.matern_gamma_mixture` |
| `prop:matern-density (10)` | `Skeleton.matern_density`, `SpatialLine.matern_density_special`, `Skeleton.matern_density_tail`, `SpatialLine.matern_density_gaussian_limit` |
| `thm:matern (10)` | `SpatialLine.matern_theorem`, `SpatialLine.matern_thorin_atom`, `SpatialLine.matern_kernels`, `SpatialLine.matern_rational`, `SpatialLine.matern_rational_polynomial`, `SpatialLine.matern_gauge_profile`, `SpatialLine.matern_gauge` |
| `prop:thorin-subclass (10)` | `SpatialLine.thorin_subclass_representation`, `SpatialLine.thorin_bridge`, `SpatialLine.thorin_bridge_onto`, `SpatialLine.thorin_bridge_measure_injective`, `SpatialLine.thorin_bridge_measure_linear`, `SpatialLine.thorin_strictness` |
| `lem:thorin-two-sided (10)` | `SpatialLine.thorin_pair_mul`, `SpatialLine.neg_log_norm_thorin_factor`, `SpatialLine.thorin_pair_compensator`, `SpatialLine.thorin_two_sided_fold` |
| `prop:student-t (10)` | `SpatialLine.student_density`, `SpatialLine.student_transform`, `SpatialLine.student_thorin`, `Skeleton.student_moments` |
| `prop:stable-family (10)` | `SpatialLine.semigroup_case_profile`, `SpatialLine.semigroup_case_gaussian`, `SpatialLine.stable_family_moments`, `SpatialLine.stable_family_thorin`, `SpatialLine.stable_family_bridge` |
| `def:signal-class (11)` | `SpatialLine.SignalClass` |
| `prop:scale-evolution (11)` | `SpatialLine.scale_evolution_fourier`, `SpatialLine.scale_evolution_absconv`, `SpatialLine.scale_evolution_multiplier`, `SpatialLine.scale_evolution_signal`, `SpatialLine.scale_evolution_conjugation` |
| `prop:corner-generators (11)` | `SpatialLine.corner_generator_gaussian`, `SpatialLine.corner_generator_stable`, `SpatialLine.corner_generator_matern`, `SpatialLine.corner_generator_thorin`, `SpatialLine.corner_generator_cin` |
| `prop:laplace-uniqueness-locally-finite (02)` | `SpatialLine.laplace_uniqueness_locally_finite` |
| `prop:sd-exponents (02)` | `Skeleton.sd_exponents` |
| `lem:profile-integrability (02)` | `SpatialLine.profile_integrability`, `SpatialLine.profile_integrability_mem` |
| `def:cascade-family (03)` | `SpatialLine.PreCascadeCore`, `SpatialLine.IsPositive`, `SpatialLine.IsNondegenerate`, `SpatialLine.CascadeCore`, `SpatialLine.IsScaleCovariant`, `SpatialLine.CascadeFamily` |
| `thm:main-characterization (07)` | `SpatialLine.main_characterization`, `SpatialLine.main_construction`, `SpatialLine.main_analysis_exists`, `SpatialLine.main_analysis`, `SpatialLine.main_uniqueness` |
| `cor:semigroup-case (07)` | `SpatialLine.semigroup_case` |
| `lem:admissible-cone (07)` | `SpatialLine.admissible_cone` |
| `prop:kernel-regularity (07)` | `SpatialLine.kernel_regularity_law`, `SpatialLine.kernel_regularity` |

## Licence

Lean sources under Apache 2.0, text under CC BY 4.0 (`LICENSES/`).
