# PLAN — response to the external reviews of module B (2026-09-19)

Working plan for revising *the admissible cone, its corners and their implementation* in
response to two external reviews of the build at revision `a76a323` (73 pages), both archived
verbatim in `reviews/cone/`:

- **the content review** (`reviews/cone/cone-review-content-a76a323-GPT-6-Astra-Ultra.md`, "the
  review" below), run by the author in GPT-6 Astra at the Ultra setting; verdict *major
  revision*. It confirms the cone representation, the bridge and its strictness, the dimension
  witnesses with their constants, the moment and tail translations, the Thorin representation,
  the Student-t computations, the restricted closure theorem and the elementary cascade
  statements, and it finds false statements: the singular regime at the origin loses a slowly
  varying factor, the Matérn theorem's Thorin clause lacks the hypothesis of no Gaussian part,
  the realization corollary lacks the integer index, the expected converse on rational stages
  has a counterexample, and the rounded-node errors of the numerical example were computed
  with a Gaussian compensation the text does not mention. It also proves that the question the
  paper calls open, whether `𝒜_∞ = 𝒮`, has the answer yes. Fifteen required changes, eight
  suggestions.
- **the presentation review**
  (`reviews/cone/cone-review-presentation-a76a323-GPT-6-Astra-Extra-High.md`), GPT-6 Astra at the
  Extra High setting: twenty ranked located items on the opening, the formalization account,
  the bibliography, the figures and tables, the vocabulary and the section structure.

Assessment session 2026-09-19 (the article session, Fable): every finding was checked
independently against the text, the blueprint and, where it applies, the Lean; the verdicts
below are the session's, and the decisions marked **D** are the author's. In this module the
article session also edits the blueprint (the text of record), so a statement correction is
made there and re-transcribed, with its `% CHANGED` marker and ledger row; each batch is one
commit through the gates (`tectonic`, `linkage check` with every shared statement verbatim,
`check-control-chars.py`, and for Lean changes `lake build` with the axiom guard). Page
references are to the reviewed build.

## Status (2026-09-19, the first round closed)

Everything in this plan is applied: R1a (R170), R1b (R171), R2, R3, R4 with the factor two of
the delay equation's proof confirmed and corrected, D1 (R172), D2, D3 (R173), D4, D5, D6, D7.
The anchor edits of each batch are the `fixes-*.txt` files of `reviews/cone/`. What follows is
the second frozen build and round.

## Status as it stood at the end of the first session of 2026-09-19

*The author agreed to all seven recommendations (D1–D7) on 2026-09-19.* Applied: R1a (R170),
R1b (the axiom, R171, with the paper's § 3 re-transcribed and its prose corrected), R2, R3,
R4a, D1 (R172), D2 except "catalogue", D4, D5. Open: D3, D6, D7, the rest of R4 (Figures 1, 2,
5 and 8; "catalogue"; the factor two in the proof of the delay equation, not yet verified), the
second frozen build and round. Finding Q is confirmed from the source: Sato (2001), Thm. 1.2
with Lemma 3.1, read by the librarian. The anchor edits of each batch are the `fixes-*.txt`
files of `reviews/cone/`.

## Verification of the substantive findings (R0, done 2026-09-19)

| finding | verdict | evidence |
|---|---|---|
| **A** Proposition 3.7's singular regime, `φ₁(x) ≍ |x|^{c−1}` for `c < 1`, drops a slowly varying factor `K(x) = exp∫_x^1 (c − k(u))u⁻¹du` (pp. 19–20) | **confirmed, and it reaches the trust boundary** | The review's profile `k = ½ − 1/log(1/x)` on `(0, e⁻⁴)` is admissible, has `c = ½` and `F(ω) = ½log ω − log log ω + O(1)`, so `e^{−F} ≍ ω^{−1/2} log ω`; a density bounded by `C|x|^{−1/2}` near the origin would give `(φ₁ * g_ε)(0) = O(ε^{−1/2})`, while the positive Fourier integral is at least a multiple of `ε^{−1/2} log(1/ε)`. So the upper half of the comparison is false. The admitted `SatoOriginSingular` (`SpatialLine/TwoSidedDefs.lean`) states exactly that comparison, without `K`: **the axiom `sato_origin_singular` is false as typed.** Its consumers use only the lower bound (unboundedness), which survives because `K ≥ 1`. The source's own formula is being re-read from the page image (librarian); the ledger's A10 entry paraphrased (53.28) and never quoted it. |
| **A′** "Logarithmic" divergence said of the whole threshold regime (pp. 12, 19) | **confirmed** | With `c = 1` and `K ≍ log(1/x)`, `L ≍ log²(1/x)`. The statement's `L` is right; the prose around it is too strong. Logarithmic is right for the `Cin` rays and the Matérn member `γ = ½`. |
| **A″** The `Cin` specialization: "`K ≡ 1` there and `L(x) = log(1/|x|)`" (p. 20) | **confirmed as a proof-text error** | For `τ < 1` and `y < τ`, `K(y) = exp∫_τ^1 du/u = 1/τ`. The Lean (`cin_origin_singularity_cin_ray`) proves the inner integral over `(y, τ)` vanishes, which is right and says only that `K` is constant near the origin; the statement's "`K` constant near the origin" is right; the proof's two identities hold for `τ ≥ 1` only. |
| **B** Theorem 5.4(2), the one-point Thorin measure, admits a Gaussian part (p. 42) | **confirmed, a printed statement weaker than its declaration** | `aω² + γlog(1+θ²ω²)` satisfies (2) as printed and fails (1) and (3). `SpatialLine.matern_theorem` has `P.a = 0 ∧ … thorinExponent 0 …` in that clause. The print dropped the hypothesis; the same kind of fault as R167. Also: (4) is an equivalence for integer `γ` only, which the declaration has as a separate conjunct over `m : ℕ` and the print folds into "the following are equivalent". |
| **C** Corollary 5.5 claims the realization for every `γ > 0` (pp. 1, 3, 37, 43, 67) | **confirmed** | A finite cascade of first-order sections has a rational transfer; `(1+θ²t²ω²)^{−1/2}` is not rational. Proposition 7.2 assumes integer `γ`. R168 narrowed the class of sections and missed the index. The "first-order section" also needs its definition in the statement. |
| **D** Remark 7.5's expected converse is false (pp. 58–59), and with it the reading of Proposition 7.7 as the closure of *all* families with rational stages (pp. 3, 43, 55, 60, 67) | **confirmed** | `k(x) = 2e^{−x}(3 + 2cos x)` is positive with `k′ = −2e^{−x}(3 + 2cos x + 2sin x) < 0` since `3 > 2√2`; its exponent is `3log(1+ω²) + log(1+ω⁴/4)`, so `e^{−F}` and every stage are rational of bounded order; `k⁽⁴⁾(x) = 2e^{−x}(3 − 8cos x) < 0` near the origin, so `k` is not completely monotone and the member is not Thorin. Proposition 7.7 is correct for its defined class `ℛ` (the review checks its proof step by step and agrees); its title and the prose written on 2026-09-19 call `ℛ` "the families with rational stages", which is too wide. Remark 7.3's title has the same fault. |
| **E** `𝒜_∞ = 𝒮` follows from the radial theorem applied to the remainders (pp. 30–33, 68) | **confirmed; a widening, the author's to take (D1)** | For `F ∈ 𝒜_∞` and `0 < c < 1`, `F(|ξ|) − F(c|ξ|)` is the exponent of the remainder law, infinitely divisible in every dimension, so by the radial theorem `f(σ) − f(c²σ)` is a Bernstein function vanishing at the origin, `f(σ) = F(√(2σ))`. Then the law on the half-line with Laplace exponent `f` is self-decomposable, its profile is nonincreasing, and `F ∈ 𝒮`. Needs two anchors the ledger has only on the line: that the remainder of a self-decomposable law on `ℝ^d` is infinitely divisible (Sato Prop. 15.5) and the half-line criterion for self-decomposability (Sato Cor. 15.11). |
| **F** Proposition 7.6: "every quadrature" converges; "every increment rational" with a Gaussian part (p. 59) | **confirmed** | Positivity gives admissibility only; the proof assumes convergence of the exponents, which is the definition of a quadrature that the statement never gives (an atom `1/n` at `e^{−n}` vanishes vaguely and adds `→ 1` to the exponent). With `a > 0` the increment has the factor `e^{−a(t²−s²)ω²}`, not rational. |
| **G** Proposition 7.4(2)'s proof: `ψ = O(ω²)` near the origin "by the quadratic-growth lemma" (p. 58) | **confirmed, a wrong justification of a true step** | That lemma gives `O(1 + ω²)`. The step follows from `R` rational, even, `R(0) = 1`. |
| **H** Definition 6.1: the Schwartz class "is stable under convolution with a finite measure" (p. 51); p. 54: `ϖ` "being infinite near the origin" for a general Thorin member | **both confirmed false** | A Cauchy law gives polynomial tails; `ϖ((0,∞)) = U((0,∞)) = k(0+)`, finite for every finite Thorin measure. Neither is used: the proof of Proposition 6.2 works on the initial signal, and clause (4) is stated for the convergence class. |
| **I** Definition 4.11 calls `𝒢` "the type G exponents" (pp. 32–34) | **confirmed** | The definition allows only mixing laws with Lévy measure `k_I(u)du/u`; a compound Poisson mixing time is type G and is excluded. The witnesses do not depend on the name. |
| **J** Remark 7.8: the Student-t scale space "cannot be computed by stepping in scale" (pp. 61–62) | **confirmed** | Proposition 7.1 is a cascade for every member; the Poisson member steps by `e^{−(t−s)|ω|}`. What is ill-posed is the Cauchy problem of the local elliptic equation. Remark 7.9's "so they cost their kernels" (mine, R169) overreaches in the same way. |
| **K** The rounded-node errors (pp. 63, 65–66, Figure 9) use an unstated Gaussian compensation | **confirmed** | `scripts/make-fig-experiment-b.py` adds `ω²/(π²N)` to the weight-2 exponent ("the same Gaussian remainder") and the text describes the uncompensated product. The review's numbers for both variants are to be reproduced and both reported. |
| **L** The search distances 0.200 and 0.027 are upper bounds on the best distance, not separations (pp. 66–67) | **confirmed** | A positive infimum does follow from Proposition 7.7 (the closure is weakly closed and `L¹` convergence implies weak convergence); its value is not determined by a finite search. |
| **M** The sampled section: exact variance is on the infinite lattice; the bandwidth matching is the continuum member's (p. 62) | **confirmed** | At `γ = 1`, `s = 1` the sampled transfer at `ω = 1/s` is 0.3876 against `1/e`. Wording. |
| **N** Deriche and Young–van Vliet: the exclusions hold for the continuous prototypes with the printed coefficients; the 2000 draws are a sensitivity experiment; the uncancelled pole of the ratio should be shown; the uniqueness of the Lévy pair should be invoked (pp. 64–66) | **confirmed, all four** | The interval bound on the one-sided slope over the rounding box (0.0148 to 0.0206, to be recomputed) proves one zero throughout the box; `2 × 4.21` is not a zero, so the pole of the ratio at `4.21` is not cancelled. |
| **O** The opening: linearity, covariance, positivity and the semigroup "must" give the Gaussian (p. 1) | **confirmed** | The stable semigroups satisfy all four; the Gaussian needs locality or non-creation as well, which the next sentence on Pauwels presupposes. My sentence. |
| **P** "which no semigroup axiomatics reaches" (p. 2) and similar | **confirmed, needs its qualification** | The Bessel kernels form a semigroup in the order parameter (Burgeth, Didas and Weickert); what no semigroup reaches is a dilation-covariant family of them. |
| **Q** Sato (2001), *Subordination and selfdecomposability*, Thm. 1.2, already has a self-decomposable type G law whose mixing law is not self-decomposable (pp. 32–34) | **to be verified from the source (librarian)**; if so, Lemma 4.12(1) is an explicit example of a known phenomenon and "not settled in the held literature" goes |
| **R** Table 1's "used by no proof" for the Matérn closed form, against Corollary 5.5's proof citing Proposition 5.3 (pp. 5, 43); "Nothing in the paper depends on this remark" (p. 49) against the later uses of the Student-t Thorin density | **both confirmed** | The corollary's proof takes the exponential tail from Proposition 5.3; the generator clause, Remarks 7.8–7.9 and Proposition 7.7's annotation read Remark 5.11's density. |
| **S** The AI statement's "Nothing outside § 1.1 comments on the machine checking" (p. 69) | **confirmed false** | Copied proofs and paragraphs on pp. 20, 46, 50 and 68 say which steps are machine-checked. |
| **T** The bibliography prints acquisition notes ([13], [32], [41], [42]) and `&amp;` ([24]) | **confirmed** | The `note` fields came with the hub's export. |
| Smaller, all confirmed: "twice" on p. 18 (a factor two counted twice in the sentence on the transform of (3.2)); "increases strictly" on p. 2 as the explanation of the obstruction (the `Cin` function is strictly increasing too; the obstruction is a stationary point); the tail "of order" wording of Proposition 5.1(2) (an exponential-integrability threshold, not a density asymptotic); the zero profile in "a completely monotone `k` … being positive" (the Gaussian is a Thorin member); Figure 5's caption at `α = 2`; stationary increments of the stable family are in `v = t^α`; "The four statements" before a five-item map (p. 54); "typed and priced" (p. 6). | | |

What the review checked and found sound is listed in its § 3.11 and is not repeated here.

## Standing decisions (the session's, under the repo's rules)

- **The false axiom is repaired before anything else.** `sato_origin_singular` is restated at
  the source's letter, with the factor `K`, once the librarian has read (53.25)–(53.28) from the
  page image; the consumers keep their conclusions (`K ≥ 1`). This is a restatement of an
  interface at its source's letter, which is delegated; it changes a name's type on the trust
  boundary and is reported as such. One Lean-building agent, in the main tree.
- **Statement corrections are narrowings** and are made at the blueprint with their markers and
  ledger rows: Proposition 3.7 (with `K`), Theorem 5.4(2) and its opening sentence, Corollary
  5.5 (integer index, the section defined), Proposition 7.6 (what a quadrature is; the jump
  part), Proposition 7.7's title and the name of its class, Definition 4.11's name for `𝒢`,
  Definition 6.1's false clause.
- **Remark 7.5 is replaced by the counterexample**, credited to the review. It withdraws an
  expectation, so it is the safe direction, and the example is three lines.
- **A widening waits for the author**: `𝒜_∞ = 𝒮` (D1).
- **The reference policy toward the causal article stands** (ADR-0003); Remark 4.13 is that
  section's one relation remark and is cut to what a reader of this paper can follow (D4).

## Decision points — for the author

- **D1. `𝒜_∞ = 𝒮`.** Add it as clause (4) of Proposition 4.9 with the review's proof, on two
  more anchors in Sato read in dimension `d` and on the half-line; drop the open question from
  § 8 and Remark 4.10; redraw Figure 4 with `𝒮 = 𝒜_∞` as one region. *Recommendation: yes.*
  The proof is short, uses the theorem the proposition already cites, and leaving a settled
  question as open would be wrong once we know. The AI statement and the process note say that
  the result is the reviewing system's.
- **D2. The vocabulary.** The presentation review asks to replace "corners" by "classical
  families", "bridge" by "subordination map", "machine" by a description, "record" by
  "smoothed signal", and to stop using "catalogue" for three different objects.
  *Recommendation:* keep "corner" and "bridge" (both are defined, and "corners" is in the
  title), but say at the first use of "corner" that the named families are not extreme rays;
  drop "machine" (§ 7.4 becomes "Finite Thorin approximations and their realization"); define
  "record" where § 1 first needs it; keep "catalogue" for the jump measure `k(x)dx/x` only and
  name `k` and `ϖ = −dk` by their own names.
- **D3. The letter `B`.** The presentation review ranks the collision ninth of twenty and
  proposes `W` for Brownian motion, which is what the macro route of 2026-09-19 would give.
  Decided on 2026-09-19 to leave it; *the recommendation is now to change it in this module*,
  an external reader having tripped on it, at the cost that the blueprint's site and the line
  paper keep `B`.
- **D4. Remark 4.13 ("what else crosses the bridge").** Both reviews call it the sharpest
  break with self-containment (the memory line, the signaling form, the embodied jet).
  *Recommendation:* cut the paper's copy to one short paragraph that names what is deferred;
  the blueprint keeps the full remark.
- **D5. The formalization account.** Move Table 1 and the ledger vocabulary to an appendix,
  keep a half-page scope summary in § 1.1, and strip the "machine-checked" sentences from the
  copied proofs so that the AI statement's sentence becomes true. *Recommendation:* do the
  second now (it is the author's own rule for the body), and decide the first with the journal
  version.
- **D6. Length.** Both reviews ask for a shorter journal version: compress the result
  itineraries (§ 1, the section maps, § 8), move the proof-history paragraphs of § 8 to the
  process note, shorten the folding discussion. The author's position on maps (2026-09-18) is
  that they help where a section's payoff needs many steps; the presentation review agrees for
  §§ 4 and 6 and asks to shorten those of §§ 3, 5 and 7. *Recommendation:* shorten those three
  maps to a question, the answer and a reading route; leave the rest for the journal version.
- **D7. The abstract.** The presentation review wants three contributions and the limits of
  "exact" beside the first computational promise. *Recommendation:* rewrite the abstract after
  R1–R3, since five of its sentences change anyway (integer index, no Gaussian part, the
  realization class, sampling, the closure), and show it to the author as a separate item.

## Batches

- **R1 — the mathematics (statements, interfaces, proofs).** A, A′, A″, B, C, D, F, G, H, I, J
  and the smaller items that touch statements or proofs. Lean: the axiom and its consumers.
  Blueprint and paper together. Ledger rows from R170.
- **R2 — the numerical example.** K, L, M, N: rerun with both rounded-node variants and label
  them; the search as an upper bound with the positive infimum from Proposition 7.7; the
  lattice and continuum qualifications; the prototype scope, the interval bound, the uncancelled
  pole, Lévy–Khintchine uniqueness; a reproducibility paragraph (signal, seed, ladder, periodic
  solver, norms and domains, optimizer), the scripts being part of the export. Figure 9 split
  in two with a gray-scale key; Figure 10 with a signed inset and the zeros marked.
- **R3 — literature and positioning** (after the librarian's report). O, P, Q; the Bessel and
  the relativistic scale spaces of Burgeth, Didas and Weickert; the background driving Lévy
  process behind the symbol `B = ωF′` (Jeanblanc, Pitman and Yor; Sato); Lindeberg's discrete
  kernels against the sampled section; density against covariance for the Matérn name;
  the novelty paragraph of § 1 restated at the level the review finds defensible.
- **R4 — the trust base and the presentation.** R, S, T; "typed and priced" and the other
  development words in § 1.1; the announcements of the presentation review's item 19; the
  counts ("four statements"); the threshold table numbered and captioned; Figures 1, 2, 5, 7
  and 8 as the presentation review asks (a zoom for the echoes, no family labels on the cone
  or a membership diagram instead, the normalization in the caption, "repeat γ times", no
  sample marks); Corollary 5.5's forward reference.
- **Then:** the decisions D1–D7 as the author takes them, the abstract, a second frozen build
  and the second round (part A in another vendor's system), the AI statement's review
  paragraph.

## Not adopted, with reasons

- *A statement-to-declaration table in the paper* (review § 5): the export's generated
  `Formalization/INDEX.md` is that table, per node, and § 1.1 will point to it; printing it
  would add pages the presentation review asks to remove.
- *A permanent URL for this paper's export* (review § 5): supplied by the release checklist,
  not before.
- *Peak live storage against total state count* (suggestion 6): adopted as one sentence in
  Remark 7.9, not as an analysis.
