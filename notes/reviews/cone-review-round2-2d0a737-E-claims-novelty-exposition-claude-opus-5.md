<!-- Archive header (not part of the review): second round, referee E, the whole paper (headline
claims, trust base, novelty, exposition); Claude Opus 5 as a blind subagent of the article session,
2026-09-19, against the frozen build 2d0a737 (75 pages). The subagent could not write files, so this
is its final message, copied verbatim by the article session. 263,071 tokens, 24 tool uses,
18.7 minutes. See README.md for the round's design and limits. -->

The Write tool blocked the report file (harness policy: subagents return findings as text). Here is the full report.

---

# Referee report E — claims, novelty, exposition

**Manuscript.** *Spatial scale space from hemigroup axioms: the admissible cone, its corners and their implementation.* 75 pages, 48 references. Read in full; page numbers are the printed ones (= PDF pages).

**Remit.** The paper as a whole. Where I say a claim is wrong I mean the statement cited does not support the words used, not that the mathematics is false.

---

## 1. Overall assessment and recommendation

**Major revision.**

The paper does something worth doing and mostly does it well. Given the companion classification, it works out the geometry of the class (Choquet structure, Cin rays as the non-Gaussian extreme rays, §3), maps the time-causal theory in by Bochner subordination and proves the map injective and not onto (§4), locates three classical families (§5), writes the evolution equation of every member (§6), and turns the hemigroup axiom into an algorithm (§7). The organising idea — that the composition axiom *is* the algorithm, so the "approximation of the Gaussian by recursive filters" literature is better read as an *exact* computation of a different, non-Gaussian scale space — is genuinely good, and Remark 7.3 with Example 7.10 makes it sharp and falsifiable. The honesty about what rests on what is above the norm.

Three things stand between the manuscript and acceptance.

**First, several headline claims are strictly stronger than the statements that carry them.** The boundedness threshold is asserted without the hypothesis Corollary 3.9 requires and which Proposition 3.7 says cannot be dropped (§§1, 3, 8); the Matérn realization is announced in three places in a form wider than Corollary 5.5 — the very over-claim the AI statement says a review found and the corollary was narrowed for; and the abstract's "most of the results are machine-checked" drops the scope "of §§3–6" that §1.1 carries, when §7 (one of three announced contributions) has no machine-checked proof at all.

**Second, §7.4–§7.5 rest on a classical theory the paper does not cite.** The class in Proposition 7.7 is, if I read Schoenberg's theorem correctly, exactly the symmetric Pólya frequency functions of order ∞, and its closure is the classical closedness of PF∞. Bondesson — whose closure theorem the paper cites (Thm 3.1.5, pp. 34–35) — states the half-line version of precisely this corollary two pages later, on p. 36. Separately, §7.3's pyramid is the reflection-symmetric twin of Lindeberg's time-causal limit kernel; Lindeberg's time-causal papers are absent from the bibliography.

**Third, 75 pages is too long**; about twenty are appendix or supplementary material.

None of this is irreparable and I expect to recommend acceptance on a revision. Major rather than minor because the prior-art point touches the framing of a whole section, and because the claim/statement mismatches are numerous enough that the author should re-read *every* summary sentence against its statement, not only the ones I found.

---

## 2. Headline claims against what is proved

### 2.1 The boundedness threshold — claim stronger than the statement (severe)

- p. 2: "An admissible kernel with no Gaussian part is bounded at the origin exactly when its profile starts above 1 (Corollary 3.9)."
- p. 12: "the kernel is bounded exactly when that value exceeds 1".
- p. 19: "The answer, **for every admissible kernel without a Gaussian part**, rests on two theorems of Sato".
- p. 70: same claim again.

Corollary 3.9 (p. 21) begins "*suppose c := k(0+) is finite and positive*", and Proposition 3.7 (p. 20) is explicit: "nothing is claimed when k(0+) = ∞, which is the case for the stable profiles and for every completely monotone profile with an unbounded Thorin measure." So the case c = ∞ — which includes the stable and Student-t families, i.e. two of the three corner families — is outside the corollary, and four sentences claim it anyway. The claim happens to be true there, but the paper does not prove it and says so. Clearest case in the manuscript of a headline stronger than its result, repeated four times. Fix with one clause, or dispose of c = ∞ (the singular regime read at a finite truncation of the profile looks as though it would give it) and widen the corollary — the better paper.

### 2.2 The Matérn theorem and the realization corollary — claim wider than the corollary

Corollary 5.5 (p. 44): "…the stage from s to t is a cascade of γ identical forward–backward pairs of first-order sections, **the pair having the transfer function (1+θ²s²ω²)/(1+θ²t²ω²)**." The prescribed transfer function ties pole and zero to the two scales; with it the converse is Theorem 5.4(4) restated and the corollary is near-tautological. All three summaries drop it: abstract p. 1 ("exactly those whose stages are cascades of identical first-order recursive filters, run forward and backward"), §1 p. 3, §8 p. 70. Each therefore asserts a characterization strictly wider than what is proved. The AI statement (p. 71) records that a blind review found "a uniqueness claim in the Matérn corollary made against too wide a class of realizations" — the repair landed in the corollary and not in the three places that announce it.

Two things needed: (i) make the summaries match; (ii) say whether the wider statement is *true* — if the stage from s to t is γ identical pairs with transfer (1+a(s,t)²ω²)/(1+b(s,t)²ω²) and the family is admissible, the hemigroup axiom forces the exponents to telescope, which I would expect to force a = θs, b = θt. If that works it is short, belongs in the corollary, and the summaries become correct as written. Theorem 5.4 itself I have no complaint about.

### 2.3 What first-order sections can and cannot reach — broadly accurate, two slips

Propositions 7.6, 7.7 and Remark 7.5 are stated carefully; the abstract's "do not reach the stable members even in the limit" is exactly 7.7(3). But pp. 3 and 70 say "atoms of even integer mass, **with a Gaussian part**" where 7.7 says the Gaussian coefficient *may* be positive; and both omit 7.7(1)'s local-finiteness condition ("finitely many θᵢ in every compact subset of (0,∞)"), without which the description is of a strictly larger set.

### 2.4 "The image consists of the members whose radial extension is self-decomposable in every dimension"

Abstract and §8 state 𝒜∞ = 𝒮, which is Proposition 4.9(4) — correct. But §1's own result paragraph (p. 3) says only that the image "lies inside a chain of classes"; §1 is weaker than the abstract and §8 and should be brought into line (the AI statement says clause (4) was added late). And both the abstract and §8 state it flatly, while 4.9 is not machine-checked and is proved in prose from six cited facts in dimension d (radial theorem, Lévy–Khintchine on ℝᵈ with converse and uniqueness, the polar criterion, negative definiteness, infinite divisibility of ρ_b, Bernstein — all listed pp. 31–32). §1 and §8 both call this "proved in prose on **a cited theorem**", singular. That understates the trust account sixfold.

### 2.5 "Exact", and for which signals

Handled well: Proposition 7.1 is exactness in the *scale* direction on the line; §7's opening, the abstract, §7.6's preamble and Example 7.10's check 1 (9.7×10⁻³ between sampled cascade and continuum member at s = 1) all disclaim the sampling. One slip: §8's algorithm paragraph (p. 70) — "Over any finite ladder of scales the cascade is exact at every knot" — is the one summary without the disclaimer, and the sentence a reader will quote.

### 2.6 Table 3 (p. 38) — two entries not supported

The caption says the tail entries are made precise by Propositions 5.1, 5.3, 5.10 and 5.12, and §5 says the table "collects what the section and the two around it establish".

- **Stable row, tail |x|^{-1-α}.** Proposition 5.12 (p. 51) states the exponent, profile, Thorin density, identification of the kernels, moment count and semigroup uniqueness — **no tail**. Figure 5's caption (p. 39) makes the same false attribution. The order is classical and easy to cite; as it stands two places cite a proposition for something it does not say.
- **Stable row, "bounded at 0: yes".** The stable profile has k(0+) = ∞, where 3.7 and 3.9 are silent, and nothing else in the paper establishes it (2.8 gives unimodality, not boundedness).

Everything else checks: Gaussian tail e^{-x²/4at²} ✓; Matérn "iff γ > 1/2" ✓ and "iff γ integer" ✓ (subject to §2.2); Student-t n < 2a, |x|^{-2a-1}, bounded ✓ (5.10); unit step ✓; "none, not a limit" ✓ in all three cases against 7.7(3); Gaussian "a limit only" ✓ against 7.7(2). Presentational: the profile column gives 2γe^{-x}, i.e. range θ = 1, while the caption says "at canonical scale t" — the profile depends on θ, not t. Say so.

### 2.7 The two published recursive Gaussians (Example 7.10) — sound, but Remark 7.3 misclassifies one

Both exclusions are argued honestly and with the right disclaimers ("statements about the continuous prototypes with the published coefficients"; the 2000-draw sensitivity check "proves nothing more"). The Young–van Vliet argument (profile negative from x = 1.46σ, signed density the only candidate Lévy density) is correct in form; the Deriche argument (three real zeros; the transform of an infinitely divisible law has none) is correct and the more elementary.

But Remark 7.3 (p. 58) frames the test for a transfer R(ω) = |P(iω)/Q(iω)|², i.e. a forward–backward *cascade*, then says "Both are therefore decided by this test". Deriche's design is a *sum* of causal and anticausal halves (p. 69), so its transfer is not a modulus squared at all — indeed the paper's own argument is that it goes negative. Also: Remark 7.3's headline sentence ("is the kernel of an admissible family exactly when R = e^{-F} for an admissible F") is circular; the usable criterion is the pole/zero one two sentences later. And that criterion is, for a practitioner, the most directly useful thing in the paper — yet it is an unnumbered remark, not separately proved and (like all of §7) not machine-checked. Promote it.

### 2.8 "Most of the results are machine-checked" — scope dropped

Abstract p. 1 unscoped; §1.1 p. 4 scopes it to §§3–6; §1's Scope paragraph p. 4 unscoped again. Of five announced result groups, the fifth — §7, eleven numbered items plus the example — is entirely unverified, and it carries the abstract's engineering pitch. §1.1's bullet "The implementation section, where no machine-checked proof is scheduled" is buried sixth of seven and reads as a minor exclusion. It is not one.

---

## 3. The trust base (§1.1, Table 1, AI statement)

**What is good.** Better than I usually see: "proved" / "rests on a named cited fact at a named page" / "not formalized" is drawn per statement; Table 1 gives the *clause* of each cited fact actually used; the narrowings are stated ("Bernstein's theorem, the existence equivalence only"; the tail floor "at its divergence branch alone and at a lower bound for the radius"); the printed `#print axioms` block makes the claim falsifiable; and the disclosure that an earlier version "had admitted the singular regime without the slowly varying factor, which made the admitted fact false; an external review found it" (p. 5) is exactly the disclosure that ought to be made and usually is not. This part of the paper is a model.

**Defects.**

1. **Table 1's A23 row is incomplete** — "used directly by Prop. 4.9(3)". The proof of 4.9(4) uses it too (p. 33: "By the radial theorem, applied as in clause (3), g_c is a Bernstein function"). Since 4.9(4) is what the abstract headlines, this is not cosmetic.
2. **No Table 1 row for the Feller continuity theorem**, which §1.1 names as the second cited fact behind 7.7 ([15], Vol. 2, §XIII.1, Thm 2, p. 431) and which the proof of 7.7(1) uses (p. 62). A24's row covers only Bondesson.
3. **"Not formalized" and "assumed as an interface" are conflated.** §1.1's first not-formalized bullet lists "the moment criterion … (Proposition 5.1, two clauses)"; the what-is-proved bullet lists "the moments-and-tails proposition, the variance formula…"; Table 1's A13 row says of 5.1(1) that it "**is** the fact". So 5.1(1) is not a theorem of the development at all, and no reader can extract that from the three places that mention it. Replace the two prose lists with one per-statement table: proved on Lean core / proved spending named interfaces / not formalized. That would also shrink §1.1 from three pages to one.
4. **Remark 7.8 (p. 63) asserts what the paper says it does not treat.** §5.4 ends (p. 50): "Which principle cuts the Student-t family out of the cone … is the subject of the next module. Nothing is stated about it here." Remark 7.8 then states, unproved and on the strength of an unwritten module, that the Student-t scale space solves an elliptic boundary-value problem, that the Cauchy problem in t is ill-posed, and that at a = ½ this is Hadamard's instability. Mark it conjectural or cut it to the two facts proved here.

**The AI statement (pp. 71–72)** is consistent with the rest and is more forthcoming than §1.1 — the two errors it reports found in blind review are the origin of the mismatch in §2.2, and I would not have located it so fast without it. Four points:

1. **Two figures a reader cannot check and does not need**: "the agents' words outnumber mine by about twenty-four to one" and "took five days". Lower bounds on an unpublished archive; a word ratio measures nothing a referee can use. Move to the process note.
2. **An unnamed system is credited with a theorem** — "the argument is the reviewing system's" for Proposition 4.9(4), a headline claim. Name it and its version, as one would a computer-algebra system that produced a case analysis.
3. **"No human reader beyond me has yet reviewed the article"**, with "none of the proof terms are mine", locates the risk exactly where §1.1 says the checking stops: Propositions 4.9, 4.12, 7.7 and all of §7 are prose proofs, agent-written, never machine-checked, never read by a second human. Say it in one sentence — and the editor should weight the block-by-block referees towards those items.
4. Minor: the standing rule that "corrections that make the article claim less are delegated to the agents" evidently narrows statements without propagating to the summaries (§§2.1, 2.2, 2.6). Worth saying the revision fixed the propagation.

---

## 4. Novelty and relation to prior work

**What the positioning gets right.** Pauwels et al. [32] is correctly the foil and correctly described; Duits et al. [12] and Felsberg–Sommer [16, 17] are correctly placed, and the observation that the Cauchy kernel is where the stable and Student-t corners meet is a nice touch; Burgeth–Didas–Weickert's Bessel scale space [5] is correctly distinguished (composed along the *order* at fixed range, not along the range) — the crux of what the hemigroup adds and the most important comparison in the paper; the relativistic scale spaces [6] are correctly set aside; the Matérn histories ([46], [20], [35], [30], [31], [18]) are right and well apportioned; Halgreen [21] and [2] are correctly used and correctly flagged as hypotheses (Remark 5.11); Sato [37, 36, 38] is used accurately, and the use of Sato 2001 at Remark 4.10 matches what that paper is known for; Deriche, Young–van Vliet and Burt–Adelson are the right three for §7; Lindeberg's discrete scale space [27] is used correctly and in the right place (p. 64). Remark 4.10 is a model of saying what is known, what is not, and whose the question is.

**4.2 𝒜∞ = 𝒮 (Proposition 4.9(4)) — I could not find it in the literature.** I looked for the equivalence under any name and did not find one. The nearest things are the easy direction (standard; the paper's clause (2)) and Sato 2001, which shows the one-dimensional converse fails and which the paper cites for exactly that. The equivalence is a short consequence of Schoenberg's radial theorem once one takes the limit in d, and the paper says as much; "short given the right tool" is not "known". Two requests: check it against the Barndorff-Nielsen–Maejima–Sato line on nested classes of multivariate infinitely divisible laws defined by stochastic integral representations (if it is anywhere, it is there); and say in Remark 4.10 that the author searched and did not find it, in the voice already used for the second question. At present clause (4) arrives with no novelty claim attached, which is odd for a result the abstract headlines.

**4.3 Proposition 7.7 is classical, and the paper is the poorer for not saying so.** (My main prior-art finding; the author should check Schoenberg's exact statement himself.) 7.7's limit class is e^{-F(ω)} = e^{-aω²}Πᵢ(1+ω²/θᵢ²)^{-nᵢ}, nᵢ positive integers, locally finite. Schoenberg: a density is PF∞ exactly when the reciprocal of its bilateral Laplace transform is Ce^{-γs²+βs}Π(1+α_k s)e^{-α_k s}, γ ≥ 0, Σα_k² < ∞. For symmetric f, β = 0 and the α_k pair as ±θ⁻¹, so at s = iω the product collapses to Π(1+ω²/θ²) — **exactly** 7.7's class, with Σnᵢ/θᵢ² < ∞ playing the role of local finiteness plus admissibility. So: *the members computable by first-order forward–backward sections, and their limits, are exactly the admissible members whose kernels are symmetric Pólya frequency functions.* Three consequences:

- **Attribution.** 7.7 is the symmetric line version of Schoenberg's PF∞ theorem, its closure half the classical closedness of PF∞. The half-line corollary is stated *in the source the paper cites*: Bondesson [4], p. 36 — "Obviously the PF∞-class equals the subclass of 𝒢 for which the U-measure is discrete with atoms with integral mass. The closure theorem for GGC's guarantees in particular that also the PF∞-class is closed with respect to weak limits; note that atoms with mass 1 cannot be split in the limit." (I read pp. 30, 34, 36 in a held copy.) The paper cites Theorem 3.1.5 on pp. 34–35 and not the remark two pages later that gives it the statement it wants.
- **The paper gains a better statement.** PF∞ kernels are precisely the variation-diminishing convolution kernels. The paper defers non-creation of local extrema to "the next module" (pp. 4, 55, 63, 70) — but the PF identification says, *within this paper*, that the members realizable by first-order sections and their limits are exactly the variation-diminishing ones. That is a far more satisfying answer to "which members can be computed this way" than a parity condition on Thorin atoms; it connects §7 to the discrete scale-space literature already cited ([27], whose generating-function classification is the discrete PF theory); and it makes Remark 7.8's frustration about the Student-t corner structural rather than accidental.
- **Bibliography.** Schoenberg on Pólya frequency functions, Hirschman & Widder's *The Convolution Transform*, Karlin's *Total Positivity* — none of the three appears. For a paper whose §7 is about cascades of exponential factors, conspicuous.

**4.4 §7.3's pyramid is the twin of Lindeberg's time-causal limit kernel.** Proposition 7.4(2) and Figure 8: e^{-F(ω)} = Π_{m≥1}R(q^{-m}ω), folded profile k(x) = Σ_{m≥1}k_R(qᵐx) — an infinite cascade of a fixed filter over a geometric ladder, self-similar under dilation by q, interpolating a pyramid. On the time-causal side this is Lindeberg's *time-causal limit kernel*: an infinite cascade of truncated exponential kernels with time constants in geometric progression with ratio c, built precisely for scale covariance under that ratio and truncated to K layers by the convergence of the geometric series (Lindeberg, JMIV 2016; Biol. Cybern. 2023; earlier Lindeberg & Fagerström 1996). The manuscript cites [27], [28], [29] but none of the time-causal work, and presents the construction and the pyramid interpolation as its own. The results do not coincide — the manuscript's is the symmetric case for general rational R, with uniqueness and admissibility proved, which is more — but a reader who knows that literature recognises the object immediately and wants to be told where it differs. It is also the most natural bridge to the imaging readership the paper is aimed at.

**4.5 The Matérn realization's classical half must be attributed.** That the Matérn with half-integer ν = γ − ½ is the covariance of a continuous-time AR(γ) — a γ-th order SDE, exactly realizable by a γ-th order state-space model, and on the line by the spectral factorization (1+t²ω²)^{-γ} = |(1+itω)^{-γ}|² into causal and anticausal first-order cascades — is standard in the Gaussian-process and geostatistics literature (Hartikainen & Särkkä 2010; Särkkä & Solin; and in the SPDE reading Lindgren–Rue–Lindström [30], cited only for the Green's-function link). Remark 5.6 lists where the Matérn *kernels* have appeared but not where their *realization* has. The paper's own contribution should then be stated as what it is: not that the integer-index member factors into first-order sections, which is classical, but that the factorization is exact *between every pair of scales* under the hemigroup axiom, and that within the cone the property singles the family out. That makes the novelty claim both more modest and more credible.

**4.6 Smaller points.** *Jurek*: the integral representation of self-decomposable laws is Jurek & Vervaat (1983), uncited; §1 says "the random integral representation of [3] is the closest in shape to the bridge", and Becker-Kern [3] is a descendant of Jurek–Vervaat, which should be the primary citation. *Type G*: attributed to Steutel & van Harn (2.7), p. 345; the standard sources are Barndorff-Nielsen, Kent & Sørensen (1982) on normal variance-mean mixtures and Maejima & Rosiński on type G on ℝᵈ — and since Definition 4.11 and Remark 4.10 turn on the class in every dimension, the ℝᵈ source is the one needed. *Matérn*: Matérn (1960) and Stein (1999) are absent; [20] and [35] are histories, not sources. *Recursive Gaussians*: if two published designs are to be tested, Triggs & Sdika (2006) and van Vliet–Young–Verbeek (1998) belong in the discussion — not because they change the verdict but because a reader will ask whether it survives the variants.

---

## 5. Exposition and structure

**Where it becomes hard to follow.** §1.1 (pp. 4–7): three pages of formalization bookkeeping between §1's results and §2, announcing itself as skippable — an admission that it is misplaced. §3.2, the proof of 3.3 (pp. 15–16): a page and a half of tail-versus-measure manipulation with three nested "two steps carry that to ϖ itself" layers and the extreme-ray classification in the same undivided block; the paragraph beginning "That there are no other extreme rays" is what a reader will want to find again and has no signpost. §4.5–§4.6 (pp. 30–37) is the hardest stretch: 4.9's four clauses over two pages from six cited facts, then two pages of Remark 4.10, then Definition 4.11 restating the vocabulary a third time, then three pages of explicit numerical inequalities ("6912/3125 ≤ π", "400 > 392"). Example 7.10 (pp. 64–69): six pages of numbers in running prose, which want to be a table.

**Definitions used before given; load-bearing forward references.** Corollary 5.5 (p. 44) is stated in "knot ladder" and "first-order forward–backward section", defined pp. 56–57 — a corollary the abstract headlines should be readable where it stands. Table 3 (p. 38) uses "lag sections" (p. 57) in its last column and the caption explains only the other term. **Corollary 3.9(2)'s proof (p. 22) uses Proposition 5.2(1) (p. 41)** — a genuine forward dependence inside a proof, twenty pages ahead, unflagged. Lemma 4.8 (p. 30) is stated via "the inverse-gamma law of shape a of Proposition 5.10" (p. 49); Proposition 3.7's non-emptiness remark (p. 20) uses "the Matérn profile of §5 at γ = 1". Remark 4.10 (p. 33) discusses "the type G laws" before Definition 4.11 (p. 35). Proposition 5.7 → Lemma 5.9 is handled well.

**Leaning on the line paper in spite of §2.** Mostly no; §2 is a well-judged five pages. Two residues: the proofs cite at least seven further numbered results of [14] beyond the four §2 announces ("Four further results are used and only cited", p. 7) — either extend §2 or correct the sentence. And **[13] has no venue, DOI, arXiv id or URL**, and [14] has only a GitHub link to a verification export, not to the paper. A sequel whose §2 is five pages of restatement can afford that only if both predecessors are locatable.

**Notation collisions**, in rough order of severity:

1. **𝒮 is both the subordinated exponents (p. 28ff.) and the Schwartz class** — Definition 6.1 (p. 52): "𝒟 := 𝒮(ℝ)", and two pages later "the scale space is not a Schwartz function". Rename one.
2. **a** is the Gaussian coefficient everywhere and the Student-t shape in Lemma 4.8, Proposition 5.10, Remark 5.11 and Table 3 — both live in the same subsection, since the Student-t members have a = 0 as exponents. Also the interval endpoint in Lemma 4.12 and lim f(σ) in the proof of 4.9(3). Use ν or p for the shape.
3. **c**: the contraction ratio (p. 9; proof of 4.9(4)); the value k(0+) (§3.4 on); the constant of Lemma 3.1; the cosine transform in the proof of Lemma 3.5; the bump weight of Lemma 4.12; c(λ) = S_λ1 (Table 2); and a generic constant in half a dozen tails.
4. **K**: the slowly varying factor (3.7), the modified Bessel function (5.3, 5.10), and the operators K_t (p. 1).
5. **g**: a Bernstein function (4.4; g_c in 4.9(4)), the Gaussian density g_u, the stage exponent g_{s,t} (Table 2), and the test signal in (6.2).
6. **ϖ against ω** at 10pt, adjacent in almost every generator display — (2.3), (6.1)–(6.2). Distinguishable but not at a glance.
7. **P**: regularized incomplete gamma (4.12), the distribution function P_τ (3.5), the numerator P(iω) (7.3).
8. **u**: the scale space u(t,x) (§6), the delay variable in (4.2) and §4, a generic integration variable in §3.
9. **𝒢** (type G exponents) against G(t,ω) (Table 2) and G(σ) in the proof of 7.7.

**Figures and tables.** Fig. 1 does its job; the right-panel inset is too small to read at print size and the caption should say *which* taper. Fig. 2 is a good schematic, honest about what it cannot show. Fig. 3 clear. **Fig. 4 is the best figure in the paper** — it draws the chain and says in the caption what is *not* known about it (ℬ against 𝒜_d for finite d > 1). Fig. 5: false attribution of the stable tail (§2.6); otherwise good, and the bandwidth warning is right. Fig. 6 nice and legible. **Fig. 7: the "repeat γ times" labels collide with the boxes; "backward section" is overlapped.** Fig. 8 clear. **Fig. 9: the second panel (the scale space itself) is almost uniformly black and conveys nothing in print** — renormalize or drop in favour of the three difference panels; the bottom-left legend covers curves near the peak. **Fig. 10: the red annotation overlaps the red series and the frame.** Fig. 11 good; panel (d) is the practitioner's takeaway and deserves a sentence in §8. Table 2's third column serves readers of [13] only. **The unnumbered table on p. 68 should be numbered and captioned.**

**What a journal version should lose** (target ≈ 55 pp.): §7.6 with Figs 9–11 (≈ 7 pp.) → supplementary with the two scripts, keeping the difference panels, a five-row check table, and the verdict on the published designs, which is a result and belongs in §7.5; §4.6 with Lemma 4.12's proof (≈ 3 pp.) → appendix; §1.1 (≈ 3 pp.) → half a page plus Table 1; **§3.3 with Lemma 3.5 and Remark 3.8 (≈ 3 pp.) → appendix or cut — the paper says twice that nothing depends on it** (charming, the Dickman connection is the nicest incidental observation in the paper, but not load-bearing and the proof is two pages); Lemmas 5.8–5.9 (≈ 2 pp.) → appendix; Table 2's third column and Remark 4.13 → appendix. ≈ 20 pages, at no cost a referee would miss.

---

## 6. Required changes

1. **pp. 2, 12, 19, 70** — add "with k(0+) finite" to every statement of the boundedness threshold, or widen Corollary 3.9 to k(0+) = ∞. As written the paper asserts four times what Proposition 3.7 explicitly declines to claim, for a case including two of its three corner families.
2. **pp. 1, 3, 70** — narrow the three summaries of Corollary 5.5 to what it says (the pair's transfer function is prescribed), or prove the wider statement and widen the corollary.
3. **p. 1** — restore the scope: "most of the results **of §§3–6**". §7 has no machine-checked proof.
4. **pp. 38, 39** — the stable tail |x|^{-1-α} is attributed to Proposition 5.12, which does not state it. Add it there with the classical citation, or drop the attribution.
5. **p. 38** — "bounded at 0: yes" for the stable row is established nowhere; 3.9 is silent at k(0+) = ∞.
6. **p. 61, §7.4, p. 3, p. 70** — attribute Proposition 7.7: symmetric PF∞ (Schoenberg), with the half-line corollary stated by Bondesson himself at [4], p. 36, two pages after the theorem cited. Shorten the proof and stop listing it among the paper's own contributions.
7. **§7.3, pp. 58–59** — cite Lindeberg's time-causal limit kernel (2016, 2023; Lindeberg & Fagerström 1996) and add a paragraph relating Proposition 7.4(2) to it.
8. **Remark 5.6, p. 44** — attribute the classical half of the realization (half-integer Matérn as CAR(γ)/state-space, spectral factorization; Hartikainen & Särkkä 2010; Särkkä & Solin; [30]) and state precisely what the hemigroup adds.
9. **p. 6, Table 1** — add 4.9(4) to the A23 row; give the Feller continuity theorem a row or say A24 bundles it.
10. **p. 5, §1.1** — separate "not formalized" from "assumed as a named interface"; replace the two prose lists with one per-statement table. Proposition 5.1(1) currently appears in all three categories at once.
11. **pp. 3, 70** — "proved in prose on a cited theorem" understates Proposition 4.9's account; six cited facts in dimension d are listed on pp. 31–32.
12. **p. 3** — §1 says the image "lies inside" the chain while the abstract and §8 state 𝒜∞ = 𝒮.
13. **p. 63, Remark 7.8** — the elliptic-equation and Hadamard assertions are unsupported and contradict p. 50's "Nothing is stated about it here". Mark conjectural or cut to the two facts proved.
14. **p. 58, Remark 7.3** — Deriche's design is a sum, not a forward–backward cascade, so "Both are therefore decided by this test" is wrong; restate the test for a symmetric rational transfer, and promote the remark to a numbered proposition with a proof.
15. **[13], [14]** — supply a venue, DOI or arXiv id for both.
16. **p. 1** — remove "Working draft — not yet released".
17. **Definition 6.1, p. 52** — resolve the 𝒮 collision; separate the two meanings of *a*.
18. **p. 7** — §2 promises four cited results of [14]; the proofs use at least eleven.
19. **pp. 71–72** — name the system credited with the argument for 4.9(4), and state in one sentence that the prose-only items (4.9, 4.12, 7.7, all of §7) are neither machine-checked nor read by a second human.
20. **Length** — cut to ≈ 55 pages of main text along the lines of §5.6.

## 7. Suggestions

1. **pp. 3, 38** — "corners" fights with "extreme rays", and Remark 3.4 has to explain that the corners are *not* extreme. Consider "distinguished families".
2. **p. 26** — split Proposition 4.5's gauge clause off as a remark; the other four are family identifications.
3. **p. 15** — label the three parts of the proof of 3.3 (surjectivity, injectivity, extremality) with run-in headings.
4. **p. 20** — display Proposition 3.7's three regimes as a three-row table.
5. **pp. 64–68** — turn Example 7.10's five checks into a "what it tests / what it found / against what" table.
6. **p. 67** — the 0.38/γ decay and the γ = 37 crossover is the practitioner's takeaway; put it in §8's algorithm paragraph, which currently ends on the Poisson distance.
7. **p. 34** — Remark 4.10 is excellent and too long; the c_d numerics go with Lemma 4.12 to the appendix.
8. **p. 12** — since Euler's constant is not used, Remark 3.2 can be one sentence inside the proof.
9. **p. 50** — Remark 5.11 is the paper's one genuinely conditional result and is a remark; display it as "Hypothesis (H)" so its two consumers can name it, rather than "the hypothesis of Remark 5.11", which appears six times.
10. **pp. 70–71** — open question 1 (how large the complement of the slice is) would be sharper if it named the PF∞ / variation-diminishing reading, if that survives checking.
11. **p. 44** — the Bessel-K-forms distinction ([33]) is right and could carry one more sentence; an imaging reader is most likely to have met these kernels there.
12. **p. 55** — say once, at the head of §7, that no statement of the section is machine-checked; §1.1 says it on p. 5 and the reader will have forgotten.

---

## 8. Which prior work I checked at the source, and which from memory

**At the source.** Bondesson (1992) — pp. 30, 34, 36 read in a held copy: Closure Theorem 3.1.5 as cited, and the PF∞ remark on p. 36 that §4.3 turns on. Lindeberg's time-causal limit kernel — construction and geometric progression of time constants, checked against the arXiv versions of the 2016 JMIV and 2023 Biol. Cybern. papers and related preprints. Hartikainen & Särkkä / state-space Matérn — through secondary sources and the Särkkä group's own exposition, not the 2010 paper itself. Schoenberg's PF∞ representation — the form of the representation checked through recent survey literature, not Schoenberg's papers; **the author should verify the exact statement before acting on required change 6.** Sato, *Subordination and self-decomposability* (2001) — abstract and secondary descriptions only (ScienceDirect refused the full text).

**From memory.** Pauwels–Van Gool–Fiddelaers–Moons (1995); Duits–Florack–de Graaf–ter Haar Romeny (2004); Felsberg & Sommer (2001, 2004); Burgeth–Didas–Weickert (both 2005); Whittle (1954); Lindgren–Rue–Lindström (2011); Steutel & van Harn (2004); Thorin (1977, both); Halgreen (1979) and Barndorff-Nielsen & Halgreen (1977); Jurek & Vervaat (1983); Barndorff-Nielsen–Kent–Sørensen (1982); Sato's monograph (1999); Deriche (1993); Young & van Vliet (1995); Burt & Adelson (1983); Lindeberg (1990, 2011); Phelps; Feller vol. 2. I did **not** check any page anchor of the manuscript's cited facts against its sources — that is the interface referees' job — with the single exception of the Bondesson pages above, which I needed for the attribution question.

**Sources consulted on the web:** [Lindeberg, time-causal/time-recursive scale-covariant scale space (arXiv:2202.09209)](https://arxiv.org/pdf/2202.09209); [Lindeberg, time-causal and time-recursive spatio-temporal receptive fields (arXiv:1504.02648)](https://arxiv.org/pdf/1504.02648); [Sato, *Subordination and self-decomposability*](https://www.sciencedirect.com/science/article/abs/pii/S0167715201001109); [Hartikainen & Särkkä, Kalman filtering and smoothing for temporal GP regression](https://www.researchgate.net/publication/224178777_Kalman_filtering_and_smoothing_solutions_to_temporal_Gaussian_process_regression_models); [Khare et al., totally positive kernels, Pólya frequency functions and their transforms (arXiv:2006.16213)](https://arxiv.org/pdf/2006.16213).
