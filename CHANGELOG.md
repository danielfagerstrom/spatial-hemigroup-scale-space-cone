# Changelog

All releases of this module are recorded here, newest first, with what changed and why, and in
particular which statements were renumbered, strengthened, weakened or withdrawn (hub `RELEASES.md`,
rule 2).

## cone-v0.1 — 2026-09-20 — first release of module B: the admissible cone, its corners and their implementation

The article *Spatial scale space from hemigroup axioms: the admissible cone, its corners and
their implementation*, sections 1–8 with Appendix A, 89 pages, the second article of the spatial
line after v0.1 (the characterization on the line), whose notation, axioms and characterization
theorem it restates in its section 2. What it contains. *The shape of the class:* the admissible
exponents form a convex cone in which every member is a unique superposition of the Gaussian and
the unit-step members (the `Cin` rays), which are its extreme rays; the kernel of a unit-step
member satisfies a delay equation; a kernel with no Gaussian part is bounded at the origin
exactly when its profile starts above 1. *The bridge:* Bochner's subordination maps the
time-causal families of the same axioms injectively and not onto; the image is exactly the
members whose radial extension is self-decomposable in every dimension, and the first two
inclusions of the chain of classes by dimension are strict. *The named members:* the Matérn
family (four descriptions; of integer index exactly the families, in canonical gauge, whose
stages are cascades of identical first-order forward and backward pairs), the Student-t family,
the symmetric stable family, compared by moments, tails and the origin, inside the symmetric
Thorin subclass on which the bridge is a bijection. *The evolution equation* of every member in
generator form. *The algorithm:* the cascade is exact at the knots of any ladder for signals on
the line; the families computed by first-order sections reach, in the limit, exactly the members
whose Thorin measure consists of locally finitely many atoms of even integer mass, possibly with
a Gaussian part, every one of which has an exponential moment, so the stable and Student-t
members are not among them; from the origin their kernels are Schoenberg's symmetric Pólya
frequency functions; an even rational function is an admissible kernel exactly when it has no
real pole or zero and its signed profile is nonnegative and nonincreasing, which the continuous
prototypes of two recursive Gaussians in common use fail; a numerical example checks the
statements on a sampled signal.

What is machine-checked: most of sections 3 to 6, on Lean core plus the cited facts of the line
paper and three more (Bernstein's theorem at its existence clause; the moment criterion and the
tail floor; the behaviour of a self-decomposable density at the origin, three names at Sato's
letter); the trust boundary holds fourteen names, and the headline block printed in section 1.1
is that of `SpatialLine.matern_theorem`, Lean core plus the uniqueness clause of the
Lévy–Khintchine representation. What is proved in prose and not machine-checked: the dimension
filtration and its strictness lemma, the corollary at an unbounded profile, the Matérn
realization corollary, and the whole of section 7. Forty-three numbered statements are the
blueprint's verbatim.

What is deferred, stated as open in section 8 and promised nowhere: locality, the non-creation
of local extrema and the jet (module C, blueprint chapters 12, 13 and 15, ADR-0006); references
to it are prose about further work.

Reviews: the author's section-by-section review; a register pass by eight blind reviewers; a
citation audit with every ledger entry transcribed verbatim beside its paraphrase
(`blueprint/AXIOMS-verbatim.md`); a first external round (OpenAI's GPT-6 Astra, which found a
cited fact admitted in a false form, since restated at the source's letter, and proved the
equality of the image with the intersection of the chain); a second round by five blind
instances of the models that worked on the article, with its limits stated. Both rounds are
archived verbatim with the plans that record the disposition of every finding.

The release form (ADR-0005, ADR-0007): the development repository stays private; the release is
the verification export at
`https://github.com/danielfagerstrom/spatial-hemigroup-scale-space-cone`, written by
`scripts/export-release.py` (the Lean modules the statements rest on, 123 of 155; the trust
boundary and the ledger with its verbatim companion; blueprint chapters 8, 9, 10, 11 and 14; the
paper and the PDF; the process account; both review rounds and the response plans), tagged `v0.1`
there and `cone-v0.1` here, deposited on Zenodo with a DOI reserved before the PDF was built, so
that the PDF prints it. The version DOI and the concept DOI are recorded here at the deposit.
