# Module B, second review round: assessment and response plan

2026-09-19. The round is five blind referees run as subagents of the article session against the
frozen build `2d0a737` (75 pages); its design and its two limits (same vendor as the drafting
model; project instructions possibly in the referees' context) are in
`notes/reviews/cone/README.md`. The reports are archived verbatim as
`notes/reviews/cone/cone-review-round2-2d0a737-{A,B,C,D,E}-*.md`. The first round's plan is
`PLAN-review-response-module-b.md`; this file continues it and uses the same rule: **no finding
is acted on because a referee asked; each is checked against the text, the sources and the Lean,
and the verdict is recorded here.**

## The round in one paragraph

No numbered statement was found false. The two blocks that exist only in print were attacked and
held: `prop:dimension-filtration`(4) (`A_inf = S`) and `lem:filtration-strictness` with every
constant (B), `prop:rational-closure` and the counterexample of `rem:rational-converse` (C), with
Bondesson, Feller, Sato, Sato 2001, Schilling–Song–Vondraček and Halgreen read at the page. The
numerical example was reproduced blind, about forty numbers to the printed digit (D). What the
round found is of four kinds: (i) **one imprecise domain in a statement of record**, the
integrability condition of `eq:thorin`, with a false sentence in a proof beside it (B1);
(ii) **summaries stronger than their statements**, again (the boundedness threshold four times,
the Matérn realization three times, "most results machine-checked" without its scope; A3, E2.1,
E2.2, E2.8, B3), and the Student-t condition not carried uniformly (B4, C8); (iii) **steps that
are true and not on the page** (A4–A6, A8, A9, B5, C2, C4, C6, C12, D7); (iv) **prior work not
cited** (E4.3 Pólya frequency functions, E4.4 Lindeberg's time-causal limit kernel, E4.5 the
state-space Matérn). The lesson of the first round repeats: a statement is narrowed and the
sentences that announce it are not. That is item 9 of `LESSONS-for-article-kit.md`, now with a
second occurrence, and the repair below includes a sweep of every summary sentence against its
statement (batch S4), not only of the ones the referees found.

## Verdicts

Status: **C** confirmed against the text or by recomputation here; **C\*** confirmed in substance,
the repair differs from the referee's; **W** wrong; **V** to be verified by the batch that acts on
it (source or Lean); **P** presentation, taken or declined in batch S5.

### Referee A (sections 1–3, the trust base)

| # | Finding | Verdict |
|---|---|---|
| A1 | DLMF (6.13.3), (6.13.4) cited, which do not exist | **W**: the frozen PDF and the source at `2d0a737` print (6.12.3), (6.12.4), the audit's correction of the same morning; the referee misread the page |
| A2 | § 1.1 "of § 3, everything" against `rem:cin-propagation` (induction not carried out) and the DLMF remark; Table 1's caption | **C**; name the remark among what is not formalized, restrict the caption to statements, give DLMF its orientation line |
| A3 | the boundedness threshold stated without "`k(0+)` finite" (pp. 2, 12, 70), and Table 3's two rows at `k(0+) = ∞` rest on nothing | **C** (= E2.1, E2.6, B8ii); narrow the four sentences now (safe); the clause at `c = ∞` is decision **D1** |
| A4 | Sato's (53.14) form (no drift, finite variation, (53.15)) not matched in `lem:folding-translation` | **V** (text and the Lean specifications `SatoOriginSingular`, `SatoOriginThreshold`): one sentence under `c < ∞`; if the Lean specification lacks the finite-variation hypothesis it is implied by `k ≤ c`, to be said in the annotation |
| A5 | Sato's k-function is the left-continuous version; the lemma does not pass to it | **V**, same batch; three invariances in one sentence |
| A6 | `≍` needs Sato's constant nonzero; it is, by the folding (`sin(cπ/2)/sin(cπ)`, `c' = 0`) | **C**; one clause; check what the Lean's existential representative asserts (a positive constant?) |
| A7 | `c := k(0+) ∈ (0,∞]` asserted, not assumed, in `prop:cin-origin-singularity` | **V** against the Lean hypothesis; safe restatement |
| A8 | § 2 declares four cited results of the line paper and uses at least seven, one (the truncation inequality) inside the proof of `lem:cin-delay-equation` | **C** (= E18); restate the truncation inequality's consequence in § 2, correct the count after a sweep of every `of [14]` |
| A9 | the general Fourier sign convention of that proof is never fixed | **C**; one sentence in § 2.1 |
| A10 | the disclosure of the false axiom does not say what changed in print | **C**; one clause: `prop:cin-origin-singularity`'s statement gained `K` and `L`; the corollary's threshold and every downstream result were unchanged |
| A11 | Table 1: A7 has no row; A3's row is the line statement while 4.9 uses dimension `d` | **C** (= E3.1, B7i); rows for A7, A23's second use, Feller, the `d`-dimensional reading |
| A12 | the constant 5/96 is slack and unexplained | **P**: it is the machine-checked constant (proof of record follows the Lean); say so in half a sentence, do not change it |

### Referee B (sections 4–5)

| # | Finding | Verdict |
|---|---|---|
| B1 | `eq:thorin`'s condition does not control `U` near `θ = 1`; `U = Σ δ_{1−1/n²}` satisfies it with the integral infinite; "term by term" in `lem:thorin-two-sided`'s proof is false against Bondesson (7.1.2); "the two domains" of clause (4) | **C** for the text (the condition is as printed, `paper-b/05-corners.tex` l. 556). **The Lean is not junk-valued here**: `thorinExponentL` is `ℝ≥0∞`-valued and `thorin_subclass_representation` asserts the identity with a finite exponent, which forces local finiteness; so clause (2) is true as typed and as printed, and what is wrong is the description of the *domain* (clause (4), the remark, the proof sentence). Repair in the safe direction: the domain is `∫ log(1+θ^{-2}) U(dθ) < ∞`; **V**: what domain `thorin_bridge_onto` is stated on. Fidelity row R175 |
| B2 | `thm:matern`(4) and `cor:matern-realization` need "in its canonical gauge" | **C**; safe restatement (a hypothesis added); **V** against `matern_theorem`'s typing |
| B3 | abstract, § 1, § 8 claim the realization without the prescribed pair | **C** (= E2.2); narrow now; the wider statement is decision **D2**. B's example `6e^{-x} − 2e^{-2x}` recomputed: admissible, not Matérn, one pole pair from the origin |
| B4 | the Student-t condition is not uniform: `prop:bridge-families`(3), pp. 48, 60, 3, the chain display, Table 3's caption | **C** for the four sentences and the caption; **V** for 4.5(3): what the causal article proves of the inverse-gamma delay law decides whether the clause is conditional (the Lean takes the datum as a hypothesis, R160, so the printed clause should too) |
| B5 | the strictness `A_1 ⊋ A_2 ⊋ A_3` is drawn in a remark and a caption, with two steps missing | **C**; clause (3) of `lem:filtration-strictness` with the two steps is decision **D3** (a statement gains a clause) |
| B6 | Figure 3's bottom row: label `a/V`, plot `2a/V`, proposition `1/V`; panel titles write `B_{T_1}` | **C** (`scripts/make-fig-bridge.py` l. 10 and l. 72); replot at the proposition's scale, `W` in the titles |
| B7 | Table 1: clause (4)'s cited facts; A15, A16 "used by no proof" against the corollary's exponential tails; "four corner identifications" against five items | **C**; (ii) by B's elementary argument (analyticity in a strip), which removes the appeal |
| B8 | Table 3 entries with no carrying statement: the stable tail, "bounded: yes" for stable and Student-t, "lag sections: none", the sense of "Gaussian or lighter tail" | **C** (= E2.6); the stable tail with its classical citation (librarian), the bounded entries by D1 or by their one-line reasons, the last column by C7's argument |
| B9–B11 | citation of Sato Cor. 15.11 at the line, `g_c ≥ 0`, `b^{-1}`; attributions (Bondesson Thm. 7.3.1 at the statement, Sato 2001 (3.3), Halgreen § 3, Sato's witness (3.7)); one sign convention in `lem:thorin-two-sided`; clause numbering of `prop:thorin-subclass` | **C**; the numbering gap was the author's standing decision "until the draft sync", and the draft is frozen (ADR-0008), so renumber now |
| B12 | "catalogue carried by a compact subset" should be the tail measure | **C** |
| B13 | `prop:bridge-families` invokes the causal similarity form and (ND), not restated | **C\***: one sentence restating them, within the Paper I citation rule |

### Referee C (sections 6–7)

| # | Finding | Verdict |
|---|---|---|
| C1 | "a family with rational stages is a finite convolution of gamma laws" (p. 61) and the same slide on p. 68 | **C**, contradicts `rem:rational-converse`; "realized by lag sections" in both |
| C2 | "these are the families realized by lag sections": one inclusion proved | **C**; print the one-line converse in the sense of `prop:matern-cascade` |
| C3 | real poles with a numerator: `k = 4e^{-x} − 2e^{-2x}` is admissible with rational stages, all poles and zeros real, outside the Thorin subclass | **C**, recomputed here (`k > 0`, `k' = −4e^{-x}(1−e^{-x}) ≤ 0`, `F = 2log(1+ω²) − log(1+ω²/4)`); add to `rem:rational-converse`, restate the case split of the recursive-Gaussian remark, amend open question 2 |
| C4 | uniqueness among *signed* densities needs the recombination of `lem:cin-delay-equation` | **C**; one sentence; part of **D4** |
| C5 | the remark's `|P/Q|²` frame does not cover Deriche's sum design | **C** (= E2.7); restate for an even rational `R` with `R(0) = 1` in three steps |
| C6 | `prop:thorin-machine` defines a quadrature by its convergence and never shows one exists; five places rely on existence | **C**; an existence clause with the three-line proof is decision **D3** |
| C7 | every limit in `prop:rational-closure` has an exponential moment, so the stable and Student-t members are excluded without Halgreen | **C**: atoms of mass ≥ 2 cannot accumulate at 0 under `∫ log(1/θ) U < ∞`; decision **D3** (a conclusion strengthened) |
| C8 | `prop:corner-generators`(4): the Student-t clause unconditional and mis-referenced | **C**; conditional, with the right reference |
| C9 | "for a Thorin member other than the Matérn one the tail measure is infinite near the origin" | **C**, false for finite `U` (the proof on the same page says so); "with `U((0,∞)) = k(0+) = ∞`" |
| C10 | "which rational functions are admissible stages is Proposition 7.4" | **C**; "gives a class of them; the general question is open" |
| C11 | the `L¹` realization selected; "two passes" is per knot; `2γ` multiply–adds is `4γ` | **C** |
| C12 | four missing steps in the proof of `prop:rational-increments`(2); an opaque citation | **C**; **V** the citation against the line paper |
| C13 | "the class of limits is closed" is used and is not a clause | **C**; one sentence, with D3 |
| C14 | Table 1 rows (Feller, Sato 17.5, Bondesson's definition); "solves an equation" without the gauge; "variance gauge" is half the variance; Figure 7's labels; `F = 0` in `R`; the first stage's degree | **C**, batch S5 |

### Referee D (the numerical example)

| # | Finding | Verdict |
|---|---|---|
| D1 | the distance 0.507 is the integral cut at `|x| = 400`; on the line it is 0.5086 | **C** (`LC = 400` in the script); compute the two limits' distance in closed form or by quadrature on the line, and say that distances to the Poisson kernel on the window are low by `1.6·10⁻³` |
| D2 | the `γ = 4` tail rate is not the fit the text describes | **C**: the script fits `log k − (γ−1) log x` (l. 266), the text says a log-linear fit; describe the fit, and report the number with its window |
| D3 | the real-weight quadrature is under-described (the mass below the first cell, the node rule) | **C**; D's sentence, checked against the script |
| D4 | Deriche's numbers cannot be recomputed without the four amplitudes; `a₀` has two decimals, which is what makes the interval what it is | **C**; print the amplitudes with their printed precision |
| D5 | Figure 11(d) mixes gauges: Young–van Vliet's prototype has variance 1.177; at matched variance its error is 5.98 % and the cascade passes it at `γ ≈ 7`, not 37 | **V** by recomputation in the script; then state each number with its gauge, and both readings |
| D6 | the signal, the seed and the windows are only in the scripts | **C**; two sentences |
| D7 | the complex-`θ` extension of the exponential-profile identity is asserted | **C**; cross-reference `rem:rational-converse`, where it is proved |
| D8 | "convolution powers" is wrong for the 24-range member | **C** |
| D9 | the key saturates at ±0.056 and the Poisson panel is clipped | **C** |
| D10 | the Young–van Vliet profile is negative already at the first point where the cosine is −1 | **C**; "eventually" goes |

### Referee E (the whole paper)

| # | Finding | Verdict |
|---|---|---|
| E2.1–2.8 | headline claims | = A3, B3, plus: "with a Gaussian part" for "possibly with"; the local-finiteness condition dropped in the summaries; § 1's "lies inside" against the abstract's equality; "a cited theorem" for six cited facts; § 8's "exact at every knot" without the sampling disclaimer; "most results" without "of §§ 3–6" and § 7's status buried. **C**, batch S4 |
| E3 | the trust base: A23's row, Feller's row, "not formalized" against "assumed" (5.1(1) in three categories), `rem:cannot-march` asserting what § 5.4 says is not treated | **C**; the per-statement table replaces the two prose lists; the remark is narrowed to what is proved here plus one sentence marked as announced and not proved (safe) |
| E3-AI | the AI statement: two figures a reader cannot check; the system credited with clause (4) unnamed; say in one sentence that the prose-only items were read by no second human | decision **D6** (the author's text) |
| E4.2 | `A_inf = S` not found in the literature; asks for a check of the Barndorff-Nielsen–Maejima–Sato line and a sentence saying it was searched | **V** by the librarian; then the sentence |
| E4.3 | `prop:rational-closure`'s class is the symmetric Pólya frequency functions of order ∞; Bondesson states the half-line corollary on his p. 36 | **V** at the sources (Bondesson p. 36; Karlin's representation is held, ledger A21/A22). **C\*** in one respect already: the identification is for the *kernels from the origin*; a stage `(1+s²ω²)/(1+t²ω²)` is not of Schoenberg's form (its reciprocal has poles), so "exactly the variation-diminishing members" must not be said of the families, and nothing here may anticipate module C's non-creation theorem. Decision **D4** |
| E4.4 | `prop:rational-increments`(2) is the symmetric twin of Lindeberg's time-causal limit kernel, uncited | **V** by the librarian (Lindeberg 2016, 2023; Lindeberg and Fagerström 1996), then a paragraph; decision **D5** with the rest of the bibliography |
| E4.5 | the classical half of the Matérn realization (state-space, Hartikainen and Särkkä) unattributed | **V**, **D5** |
| E4.6 | Jurek–Vervaat; Barndorff-Nielsen–Kent–Sørensen and Maejima–Rosiński for type G; Matérn 1960, Stein 1999; Triggs–Sdika, van Vliet–Young–Verbeek | **V**, **D5** |
| E5 | exposition: forward references (`cor:origin-boundedness`(2)'s proof uses Proposition 5.2(1), twenty pages ahead; Corollary 5.5's vocabulary; Table 3's last column); nine notation collisions; figures 7, 9, 10; the unnumbered table; [13], [14] without locators; the draft line | **C** mostly; batch S5; the collisions `𝒮` and the letter `a` are decision **D7**; the locators and the date line are the release procedure's |
| E6.20 | cut to about 55 pages | decision **D8** |

## Decisions for the author

**Taken 2026-09-19 (evening): the author agrees with every recommendation, D1 to D8.** On D8:
no cut for its own sake ("I have no intention to send anything to journals anyway"); material
that is *obviously* appendix material may move, for readability; the current focus is to
understand the consequences of the hemigroup axiom, and friendlier, consolidated articles come
after the planned ones are written. On the cross-reference from `rem:cannot-march` into module
C: module C is not published, so the visible text says that further work is needed, and an
invisible comment records the node to cite once it exists. On D5: the librarian acquires what is
missing first, and the author looks for what the librarian cannot find. A correction from the
author to the librarian's report: `lindeberg1996causaltime` is not a duplicate of the ECCV 1996
paper; it is a technical report with more content, which is lost, and its official link now
resolves to the ECCV article.

- **D1. `cor:origin-boundedness` at `k(0+) = ∞`.** A fourth clause, "if `c = ∞` the kernel has a
  `C^∞` representative", on Sato Thm. 28.4(ii) (the librarian transcribes it first). It makes the
  four headline sentences true as written and carries Table 3's two rows. Prose-only and `[A]`
  on ledger A10 extended, no Lean name admitted. *Recommended: yes.* Until then the four
  sentences are narrowed (batch S4).
- **D2. The Matérn realization in its wider form.** "Identical first-order forward–backward
  pairs" with the pair's transfer *not* prescribed: the stage from `0` forces the zero to vanish
  (the kernel is absolutely continuous, so its transform tends to 0) and hence
  `F(tω) = n log(1+q(t)²ω²)`, Matérn. Five lines, prose-only. *Recommended: yes*, since it is
  what the abstract wants to say; otherwise the three summaries are narrowed to the prescribed
  pair.
- **D3. Clauses that the prose already asserts become parts of statements:**
  `lem:filtration-strictness`(3) (`F^(8) ∈ A_1∖A_2`, `F^(4) ∈ A_2∖A_3`, with B's two steps);
  `prop:thorin-machine` gains existence of a quadrature (C6); `prop:rational-closure` gains
  "the class of limits is closed" (C13) and **a clause (4): a member with a missing moment is no
  limit**, which excludes the stable and Student-t members without Halgreen's theorem (C7) and
  lets Table 3, `rem:costs` and `rem:cannot-march` drop the condition. All prose-only.
  *Recommended: yes to all four.*
- **D4. The recursive-filter criterion as a proposition, and the Pólya-frequency reading.** The
  remark on which rational transfers are admissible kernels becomes a numbered proposition with
  its three-step proof (C4, C5, E2.7); and, after the sources are read, a remark attributes the
  limit class of `prop:rational-closure` to Schoenberg's theorem and Bondesson's p. 36, scoped to
  the kernels from the origin. *Recommended: yes*; the proposition stays (its content is the
  statement about families with a Gaussian part on the line), and it stops being listed as a
  contribution without attribution.
- **D5. The bibliography** (Lindeberg's time-causal limit kernel with a relating paragraph; the
  state-space Matérn; Jurek–Vervaat; type G sources; Matérn 1960, Stein 1999; the two recursive
  Gaussian variants): the librarian acquires and verifies, then the text. *Recommended: yes*,
  except the two recursive-Gaussian variants, which get one sentence and no analysis.
- **D6. The AI statement** (yours): name the system credited with clause (4); one sentence that
  the prose-only statements (4.9, 4.12, 7.7, § 7) were read by no second human and by which
  reviewers; whether the word ratio and "five days" stay. *Recommended: name it, add the
  sentence, keep the figures* (they are the hub standard's, and the process note backs them).
- **D7. Notation.** `𝒮` is the subordinated slice and the Schwartz class; `a` is the Gaussian
  coefficient and the Student-t shape. *Recommended:* write the Schwartz class as
  `\mathscr{S}(\mathbb{R})`; leave `a` (it is the causal article's and the literature's letter
  for the shape) with a sentence at Proposition 5.10. The other seven collisions are local and
  are handled in S5 where a sentence suffices.
- **D8. Length.** *Recommended: no cut for the preprint* (as after the first round); E's list of
  what a journal version should lose is recorded for the submission.

## Batches

- **S1, the numerical example** (paper-side and scripts; D1–D10, C1's p. 68 sentence, E's figure
  notes on 9 and 10): the article session.
- **S2, statements and proofs of record, safe direction** (one opus mathematician, blueprint
  first, then the verbatim copies; ledger rows from R175): B1, B2, B4, B9–B12, C2, C3, C8–C12,
  A4–A7, A12, E3's narrowing of `rem:cannot-march`, the renumbering of `prop:thorin-subclass`;
  with the Lean read (not built, unless a docstring changes) at B1, B2, A4–A7.
- **S3, sources** (sonnet librarians): Sato Thm. 28.4(ii) verbatim; Bondesson p. 36 and the
  Schoenberg–Karlin representation; the stable tail's classical anchor; D5's list; E4.2's search.
- **S4, the summary sweep** (the article session, after S2): every sentence of the abstract,
  § 1, the section maps, Table 3 with its caption, § 8 and the AI statement that restates a
  result, set against its statement in a table kept in this file; A3, B3, B4ii, C1, C10, E2.
- **S5, presentation**: Table 1 rebuilt per statement (A2, A11, B7, C14i, E3), § 2's count and
  the truncation inequality (A8, A9), forward references, Figures 3, 7, 9, 10, the unnumbered
  table, the collisions.
- **After the decisions:** D1–D5 as one blueprint batch with their ledger entries and verbatim
  blocks; then the AI statement's review paragraph, a new frozen build, and the release
  procedure.

## Status

- 2026-09-19: reports archived; verdicts above; B1 checked against the Lean (not junk-valued);
  A1 found wrong; C3 and B3's examples recomputed; D1, D2 and B6 confirmed in the scripts.
- 2026-09-19, **batch S2 is done** (one opus mathematician; `Formalization/SKELETON.md` § 35,
  fidelity rows **R175–R188**). Blueprint first, then the verbatim copies; no `.lean` file changed
  and no gate moved (77 nodes, 57 `\leanok`, fourteen names, guard at 675 lines, both headline
  `#print axioms` blocks byte-identical). Items closed: B1, B2, B4(i), B9, B11, B12, C2, C3, C8,
  C9, C10, C11, C12, A4–A7, A12, E3's narrowing of `rem:cannot-march`, and the renumbering of
  `prop:thorin-subclass` (1, 2, 3, 4). Two findings of the batch itself: `lem:thorin-ggc`'s
  **statement had a sign error** (`½cσ² + ∫(…)V` where the article's convention wants both minus
  signs, so that at `σ = iω` it was minus `eq:thorin`'s right-hand side), and the left-continuity
  normalisation of Sato's `k`-function is a **fourth** step the three A10 names carry beyond their
  pages, now at the head of `trust-boundary.txt`. Left for S4 as promised: the four unconditional
  Student-t sentences (pp. 3, 45, 48, 60), Table 3's caption, and open question 2 of § 8, which
  should record C3's example.
- 2026-09-19, **batch S1 done** (`notes/reviews/cone/fixes-s1-example.txt`, eleven anchored
  edits and three by hand; 76 pages). D1: the distance between the two limits is 0.5086 on the
  line and 0.5070 on the window `|x| ≤ 400` (recomputed by quadrature; the script prints both),
  and the example now says that its `L¹` distances are on the window and what that does to a
  distance from the Poisson kernel. D2: the text describes the fit the script makes
  (`log h − (γ−1) log x` over `12 < x/t < 20`) and says that the excess 0.02 is the window's
  bias. D3: the real-weight quadrature is described as the script builds it (`N` cells, the
  first from 0, midpoints, Gaussian coefficient `1/(2πN)`). D4: Deriche's four amplitudes are
  printed with their precision, and the slope formula. **D5 confirmed and sharper than the
  referee's numbers:** Young and van Vliet's prototype has variance `1.177σ²`; its error is
  1.04 % at its own parameter, 8.5 % at matched variance (the referee's 5.98 % did not
  reproduce; the conclusion is the same), 0.86 % at its best dilation; the cascade at its best
  dilation is 4.1 % at `γ = 4`, 0.48 % at `γ = 32`, `0.15/γ`, and passes the design at
  `γ = 19` best against best (16 against the own-parameter reading), not 37. The script
  computes the three readings, panel (d) draws the cascade in both gauges, the text gives each
  number with its gauge. D6: the signal and the seed are in the text. D7–D10 and C1's p. 68
  sentence: as the referees proposed. B6: Figure 3's bottom row redrawn at
  `prop:student-t`'s scale (`T_1 = 1/V`, density `(2/π)(1+x²)^{-2}`), `W` in the panel titles.
  Not rerun: `make-fig-experiment-b.py` (five minutes; its figures are unchanged, its new
  printed line was computed separately and agrees with the referee to six digits).
- 2026-09-19, **batch S3 done** (`notes/reviews/cone/SOURCES-round2-2026-09-19.md`, the
  librarian's report, page images read). *Sato Thm. 28.4* (p. 191) verbatim: clause (ii), "If
  `c = ∞`, then `μ` has a `C^∞` density on `ℝ`", so A3's repair and decision D1 stand on the
  page; the theorem's k-function is "left-continuous and decreasing on `(0,∞)`" (A5 confirmed)
  and its hypothesis is "selfdecomposable" with `c > 0`, no drift condition. *Bondesson p. 36*:
  E's quotation confirmed, with one correction: the class named there is Thorin's class of
  generalized gamma convolutions on the half-line under Bondesson's script letter for it, not
  "`𝒢`". *Karlin Thm. 3.2(a), p. 345* with the class of p. 336: the Pólya-frequency
  representation with its exact hypotheses, attributed by Karlin to Schoenberg (1951, J.
  d'Analyse Math. 1, 331–374); ledger A21 already holds these pages. *The stable tail*: Sato
  Remark 14.18, pp. 87–88, with the constant `π⁻¹Γ(α+1) sin(πα/2)` (B8i, E2.6). *Sato 2001*
  held in full: Theorems 1.1, 1.2 and the witness (3.7) transcribed (B10iii). *Lindeberg's
  time-causal limit kernel*: `lindeberg2016time` § 5, eq. (38), p. 62,
  `∏_k (1 + i c^{-k}√(c²−1)√τ ω)^{-1}`, held, as are the 2023 paper, the ECCV 1996 paper and
  Jurek–Vervaat; its two-sided version is `prop:rational-increments`(2) at the one-pole `R`, so E4.4 is
  confirmed and the paragraph can be written from held copies. Not held: Hartikainen–Särkkä,
  Särkkä–Solin, Barndorff-Nielsen–Kent–Sørensen, Maejima–Rosiński, Matérn, Stein, Triggs–Sdika,
  van Vliet–Young–Verbeek (records with DOIs in the report; acquisition waits for D5). *The
  novelty search* (E4.2): none of the sources reachable states the dimension-free
  biconditional; the closest is Barndorff-Nielsen–Pedersen–Sato 2001, a sufficiency result in
  fixed dimension; read from abstracts only, the sources not being held, so the sentence in the
  article must say "we have not found", with what was searched. A library note for the
  librarian's next dispatch: the ECCV 1996 paper is held pinned and also sits in the
  acquisition queue under a second citekey.
- 2026-09-19, S2 reviewed by the article session and committed: gates rerun (`linkage check` OK
  with 74 of 74 shared statements verbatim, 14 interface axioms grounded, 78 pages), no `.lean`
  file changed. **Left by S2:** B10's attributions (the pages are now read: S3 holds Sato 2001
  (3.3), (3.7) and Bondesson; Halgreen section 3 is in the round's referee B report and in the
  held copy), the unconditional Student-t sentences and Table 3's caption (S4), open question 2
  of the conclusions (C3's example), and one question: whether `rem:cannot-march` should keep
  its `\ref` into module C's chapter 12, which a repository split would break.
- 2026-09-19, **the author's decisions D1-D8 are taken: every recommendation is accepted.**
- 2026-09-19, **the decisions batch is done** (the "D1–D5 as one blueprint batch" of the batch
  list above, at D1–D4 and D7; one opus mathematician; `Formalization/SKELETON.md` § 36,
  fidelity rows **R189-R202**): the widenings **D1-D4** and the notation half of **D7**, plus the
  three items S2 left (B10's attributions, the module-C references, the novelty sentence). All of
  it prose: **no `.lean` file changed, no interface name was admitted, the trust boundary holds
  fourteen names and both headline `#print axioms` blocks are byte-identical.** Two new nodes,
  both prose-only - `cor:origin-smooth` (D1, `[A]` on A10 extended at Sato Thm. 28.4(ii), with the
  verbatim block added to `AXIOMS-verbatim.md`) and `prop:rational-criterion` (D4, `[T]`, the
  recursive-filter criterion with the complex-rate Frullani identity and the signed-density
  recombination written out) - and one new remark, `rem:polya-limits` (D4, the Schoenberg-Karlin
  attribution of the limit class, scoped to the kernels from the origin). Three nodes gained
  clauses, all prose-only: `cor:matern-realization` is the three-clause equivalence with the pair
  no longer prescribed (D2), `lem:filtration-strictness` gains the strictness of the chain and
  becomes `[A]` on A7 and A3 (D3), `prop:thorin-machine` gains the existence of a quadrature with
  its Gaussian variant (D3), and `prop:rational-closure` gains closure under limits and the
  light-tail clause (D3) - the last of which **removes the Halgreen hypothesis from every
  statement of the Student-t exclusion**, in `rem:cannot-march`, `rem:costs`, the paragraph after
  the proposition and Table 3, and only there. **79 statement nodes, 57 `\leanok`, 24 ledger
  entries, fourteen names;** `linkage check` OK with 76 of 76 shared statements verbatim and the
  one permitted advisory; `paper-b` builds to 86 pages.
- 2026-09-19 (night), **the decisions batch reviewed and committed** (`afc79f1`; rows R189 to R202,
  `SKELETON.md` section 36; 79 nodes, 57 `leanok`, 24 entries, fourteen names, no Lean file
  changed; the docs CI passed with the script letter for the Schwartz class). What changed against
  the recommendations: `cor:origin-smooth` does not pass through `lem:folding-translation`
  (whose hypothesis is a finite value) and does not claim the Student-t members as instances
  (their profile is not computed in this article; that row of Table 3 is carried by the explicit
  density); referee B's example refutes dropping the word *identical*, not dropping the
  prescribed pair; there were four references into module C, not one.
- 2026-09-19 (night), **batch S4 done** (`notes/reviews/cone/fixes-s4-summary-sweep.txt`, twenty
  anchored edits in the introduction, section 1.1 with Table 1, the conclusions and the
  abstract; 87 pages): the threshold cites both corollaries; the image *is* the intersection of
  the chain; the Matern realization as D2 states it; the closure with local finiteness, "possibly
  with a Gaussian part" and the unconditional exclusion by moments; "machine-checked" scoped to
  sections 3 to 6 in the abstract and the introduction; section 1.1 no longer claims all of
  section 3, counts the bridge proposition's five clauses, names the fourth step of the three
  origin names and what the repair of the false fact changed in print; Table 1 has rows for the
  facts used by prose-only statements (A10's further clause, A13 again, A3 and A7 in dimension
  d, A23 in two clauses, A24 with Feller) and its caption lists what is cited in remarks; the
  conclusions carry the sampling disclaimer and the half-answered open question 2. **D6:** the AI
  statement names the first round's system, describes this round with its limits, and says who
  has read the statements that are not machine-checked; it is the author's text, to be read by
  the author. Two long formulas in `prop:rational-increments`(1) are displayed (blueprint and
  paper alike).
- 2026-09-20, **D5, the presentation items and D8 done** (`fixes-d5-literature.txt`; commits
  `dac526e`, `b22a537`, `58be482` and the one after). Written from held copies read at the page:
  Lindeberg's time-causal limit kernel beside the pyramid clause (its two-sided form is the
  Matern pyramid; the clause differs by symmetry, by the general rational `R` with its
  admissibility criterion, and by uniqueness), the state-space Matern with what the realization
  corollary adds to it, Matern 1960 (2.4.7), Stein 1999 (14) p. 31 for the name, the stable tail
  at Sato Remark 14.18, the two later recursive-Gaussian designs, Jurek and Vervaat, Schoenberg
  1951 Theorem I as the primary source beside Karlin. **Type G** is attributed to Maejima and
  Rosinski 2002 (who attribute it to Marcus and to Rosinski) and Aoyama and Maejima 2007, with
  Steutel and van Harn kept for the one-dimensional mixture form. **The novelty sentence for
  `A_inf = S`** now rests on papers read in full, which the author acquired on 2026-09-20
  (`SOURCES-round2-new-papers-2026-09-20.md`): the sufficiency half is in print three times
  (Halgreen and Sato 2001 on the line; Barndorff-Nielsen, Kent and Sorensen 1982, pp. 147 and
  149, in a dimension that does not enter the hypothesis, with the words "self-decomposable in
  any dimension" for the generalized hyperbolic family; Barndorff-Nielsen, Pedersen and Sato
  2001, Theorem 6.1, in fixed dimension for an operator-stable subordinand, with Example 6.2
  against the unrestricted form), none states a converse, and the type G literature fixes the
  dimension and takes an infinitely divisible mixing law. Fifteen bibliography entries added.
  Presentation: Figure 7's labels, Figure 9's square-root gray scale, Figure 10's annotation,
  the threshold table numbered, three long formulas displayed, the forward reference of the
  boundedness corollary explained. **D8:** the proof of `lem:filtration-strictness` is Appendix A
  with an outline in its place; the delay-equation subsection stays (the first figure and the
  introduction rest on it). Left: two overfull lines of 24 and 29 pt inside copied proofs.
  89 pages; `linkage check` OK, 76 shared statements verbatim.
- **Next:** the author reads the AI statement and the release candidate; then
  `notes/RELEASE-procedure.md` (the `CHANGELOG.md` entry headed `cone-v0.1`, the reserved DOI, the
  date line, the export to `spatial-hemigroup-scale-space-cone`, the deposit).
