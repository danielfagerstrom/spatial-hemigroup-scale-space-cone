# Prompt for the second external review of module B

Attach the PDF of the second reviewed build (repo revision `2d0a737`, 75 pages; the file is
`cone-review-build-2d0a737.pdf` in this directory, untracked). Run it in a system of a
different vendor from the first round's, set to its highest reasoning effort. Save the output
verbatim into this directory as `cone-review-content-2d0a737-<system>-<setting>.md`. The first
round's reviews are NOT attached: the second reader should meet the text as a new referee does.
If the system stops before the end, run the prompt once per block of sections (§§ 1–3, §§ 4–5,
§§ 6–8) with the sentence "Review sections N to M in detail and the rest for consistency with
them" added at its head, and save each output.

---

You are a referee for a mathematical-imaging journal (JMIV class), reviewing the attached
manuscript, *Spatial scale space from hemigroup axioms: the admissible cone, its corners and
their implementation*. It is the second paper of a series. The first (cited as the line paper)
classifies the kernels; this one describes the class. Section 2 restates what it uses of the
first paper, and the manuscript is meant to be readable on its own: say where it is not. The
manuscript has been revised once after a referee report; you have not seen that report, and
you should not assume that anything has already been checked. Write a detailed referee report.
Be specific, cite pages of the PDF, and separate what is wrong from what is merely improvable.

1. **Overall assessment and recommendation** (accept, minor revision, major revision, reject),
   with the reasons in a paragraph.

2. **The headline claims against what is proved.** The abstract, the result paragraphs of
   section 1, Table 3 and the concluding section make claims; check each against the statements
   and proofs that are supposed to carry it. Say where a claim is stronger than its result,
   where a qualification made in the body is missing from the headline, and where a scope
   statement leaves a wrong impression. In particular: what is claimed to be "exact" and for
   which signals; the Matérn theorem and the realization corollary (Theorem 5.4, Corollary
   5.5); what the families computed by first-order sections can and cannot reach (Propositions
   7.6 and 7.7, Remark 7.5); every entry of Table 3; and the claims about two published
   recursive Gaussian filters (Example 7.10).

3. **Mathematical correctness.** Read the statements and proofs. Report every gap, error or
   unjustified step, with the page. Pay particular attention to what section 1.1 says is not
   machine-checked, where the printed argument is all there is, and to what is new in this
   version:
   - Proposition 3.7 and Corollary 3.9 (the behaviour of a kernel at the origin): the
     comparison function with its slowly varying factor `K`, the claim `K ≥ 1`, the three
     regimes and their hypotheses as cited from Sato's Theorems 28.4 and 53.8, the `Cin`
     specialization at the end of the proof, and whether the corollary's threshold follows;
   - Proposition 4.9, especially its new clause (4), `𝒜_∞ = 𝒮`: the use of the remainder
     laws of self-decomposability in every dimension, the second application of Schoenberg's
     radial theorem, the passage to a self-decomposable law on the half-line, and the
     identification of its exponent as causally admissible; and Lemma 4.12 with its constants;
   - Proposition 7.7 (the closure of the families realized by first-order sections): the
     passage to the half-line, the continuity theorem for Laplace transforms, Bondesson's
     closure theorem, the step that a vague limit of integer-valued point measures is one, and
     the passage back, including mass that escapes to infinity;
   - Remark 7.5's counterexample (an admissible family with rational stages and a complex
     pole pair), and whether anything else in the paper is inconsistent with it;
   - the whole of section 7 (Propositions 7.1, 7.2, 7.4, 7.6, Remarks 7.3, 7.8, 7.9) and
     Corollary 5.5;
   - the conditional clauses on the Student-t family (Proposition 5.10(3), Remark 5.11), and
     whether every later use, Table 3 included, respects the condition;
   - the cited facts of Table 1 and whether each is used within its stated hypotheses;
   - the statements that carry the structure: Proposition 3.3, Lemma 3.5 (with the factor two
     in its proof), Propositions 4.5 and 4.6, Proposition 5.7, Propositions 6.2 and 6.4.

4. **The numerical example (section 7.6, Example 7.10, Figures 9 to 11).** Are the checks
   well designed, do the reported numbers support what the text concludes, and is anything
   concluded that a computation cannot show? If you can, reproduce: the `L¹` distances of the
   rounded-node members from the kernel `½ sech(πx/2)`, for the finite product and for the
   variant with a Gaussian remainder; the first negative point and the minimum of the folded
   profile of the Young–van Vliet prototype; the zeros of Deriche's fourth-order transfer
   function and the interval bound on its one-sided slope. Is the sampled section described
   well enough to be reproduced, and are the statements about it (exact telescoping, exact
   variance on the infinite lattice, the comparison with Lindeberg's discrete kernels) right?

5. **The trust base.** Section 1.1 and Table 1 state what the machine-checked development
   assumes and what is not formalized, and say that an earlier version had admitted one cited
   fact in a false form. Is the account clear, complete and honest as a reader would judge it?
   Is anything claimed as verified that the text elsewhere qualifies?

6. **Novelty and relation to prior work.** Check the positioning against Pauwels, Van Gool,
   Fiddelaers and Moons; the alpha, Poisson, Bessel and relativistic scale spaces (Duits et
   al., Felsberg and Sommer, Burgeth, Didas and Weickert); the Matérn family and its SPDE
   reading; self-decomposable laws, generalized gamma convolutions, type G laws and the
   background driving Lévy process (Sato, Steutel and van Harn, Thorin, Bondesson, Halgreen;
   Sato's 2001 paper on subordination and self-decomposability); recursive Gaussian filters
   (Deriche; Young and van Vliet); pyramids (Burt and Adelson); Lindeberg's discrete scale
   space. Is anything claimed as new that is known, attributed wrongly, or missing?

7. **Exposition and structure.** Where does the argument become hard to follow, where is a
   definition used before it is given, where is a forward reference load-bearing, where does
   the paper lean on the line paper in spite of section 2, and what should a journal version
   of 75 pages lose?

8. **A numbered list of required changes** and a separate **numbered list of suggestions**,
   each item with a page reference and one sentence of reason.

Do not summarize the paper back to the author beyond what the assessment needs. Do not
soften findings; a wrong claim should be called wrong. If you are unsure whether something is
an error, say so and say what would settle it.
