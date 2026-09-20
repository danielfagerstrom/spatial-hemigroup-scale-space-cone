# Prompt for the external review of module B

Attach the PDF of the reviewed build (repo revision `a76a323`, 73 pages; the file is
`cone-review-build-a76a323.pdf` in this directory, untracked). Run part A in a system set to its
highest reasoning effort; part B may be run in the same or another system. Save each output
verbatim into this directory, under a filename that carries the system and its setting, on the
pattern `cone-review-content-<revision>-<system>-<setting>.md` and
`cone-review-presentation-<revision>-<system>-<setting>.md`.

The manuscript is long. If a system stops before the end of part A, run part A once per block
of sections (§§ 1–3, §§ 4–5, §§ 6–8) with the same prompt and the sentence "Review sections N
to M in detail and the rest for consistency with them" added at its head, and save each output.

---

## Part A — journal-style review

You are a referee for a mathematical-imaging journal (JMIV class), reviewing the attached
manuscript, *Spatial scale space from hemigroup axioms: the admissible cone, its corners and
their implementation*. It is the second paper of a series. The first (cited as the line paper)
classifies the kernels; this one describes the class. Section 2 restates what it uses of the
first paper, and the manuscript is meant to be readable on its own: say where it is not. Write
a detailed referee report. Be specific, cite pages of the PDF, and separate what is wrong from
what is merely improvable.

1. **Overall assessment and recommendation** (accept, minor revision, major revision, reject),
   with the reasons in a paragraph.

2. **The headline claims against what is proved.** The abstract, the result paragraphs of
   section 1 and the concluding section make claims; check each against the statements and
   proofs that are supposed to carry it. Say where a claim is stronger than its result, where
   a qualification made in the body is missing from the headline, and where the scope
   statements leave a reader with a wrong impression. In particular: the Matérn theorem and its
   corollary on exact recursive realization (Theorem 5.4, Corollary 5.5); the claims about
   which members the recursive cascades reach (Propositions 7.6 and 7.7); and the claims made
   about two published recursive Gaussian filters in Example 7.10.

3. **Mathematical correctness.** Read the statements and proofs. Report every gap, error, or
   unjustified step you find, with the page. Pay particular attention to the parts that
   section 1.1 says are not machine-checked, where the printed argument is all there is:
   - Proposition 4.9 (the dimension filtration) and its use of Schoenberg's radial theorem and
     of the polar criterion for self-decomposability in dimension d, and Lemma 4.12 (the
     witnesses, with its explicit constants);
   - Proposition 7.7 (the closure of the families with rational stages): the passage to the
     half-line, the use of the continuity theorem for Laplace transforms and of Bondesson's
     closure theorem, the step that a vague limit of integer-valued point measures is one, and
     the passage back, including what happens to mass that escapes to infinity;
   - the whole of section 7 (Propositions 7.1, 7.2, 7.4, 7.6, Remark 7.3), and Corollary 5.5;
   - the conditional clauses on the Student-t family (Proposition 5.10(3), Remark 5.11), and
     whether every later use respects the condition;
   - the cited facts of Table 1 and whether each is used within its stated hypotheses,
     especially the behaviour of a self-decomposable density at the origin (Proposition 3.7,
     Corollary 3.9) and the moment and tail criteria (Proposition 5.1);
   - the statements that carry the structure: Proposition 3.3 (the Choquet structure of the
     cone), Lemma 3.5 (the delay equation), Propositions 4.5 and 4.6 (the bridge and its
     strictness), Proposition 5.7 (the Thorin subclass), Propositions 6.2 and 6.4 (the
     generator form).

4. **The numerical example (section 7.6, Example 7.10, Figures 9 and 10).** Are the checks
   well designed, do the reported numbers support what the text concludes from them, and is
   anything concluded that a computation cannot show? Check the derivation of the folded
   profile of a rational filter from its poles, the conclusion that the design of Young and
   van Vliet is not infinitely divisible, and the argument that Deriche's fourth-order
   transfer function vanishes on the real axis. Is the sampled recursive section described
   well enough to be reproduced?

5. **The trust base.** Section 1.1 and Table 1 state what the machine-checked development
   assumes and what is not formalized. Is the account clear, complete and honest as a reader
   would judge it? Is anything claimed as verified that the text elsewhere qualifies?

6. **Novelty and relation to prior work.** The article positions itself against Pauwels, Van
   Gool, Fiddelaers and Moons (1995); the alpha and Poisson scale spaces (Duits et al.,
   Felsberg and Sommer, Pedersen et al.); the Matérn family in spatial statistics and its SPDE
   reading (Lindgren, Rue and Lindström); the probability literature on self-decomposable
   laws, generalized gamma convolutions and type G laws (Sato, Steutel and van Harn, Thorin,
   Bondesson, Halgreen); recursive Gaussian filters (Deriche; Young and van Vliet); pyramids
   (Burt and Adelson); and Lindeberg's discrete scale space. Is the positioning accurate? Is
   anything claimed as new that is known, or attributed wrongly? Is relevant work missing,
   in particular on variance-gamma or Bessel-kernel smoothing, on rational or recursive
   scale-space filters, and on infinitely divisible kernels in image processing?

7. **Exposition and structure.** Where does the argument become hard to follow, where is a
   definition used before it is given, where is a forward reference load-bearing, where does
   the paper lean on the line paper in spite of section 2, and which remarks, paragraphs or
   figures could be cut without loss? The manuscript is 73 pages; say what a journal version
   should lose.

8. **A numbered list of required changes** (what must change for acceptance) and a separate
   **numbered list of suggestions** (what would improve the paper). Each item with a page
   reference and one sentence of reason.

Do not summarize the paper back to the author beyond what the assessment needs. Do not
soften findings; a wrong claim should be called wrong. If you are unsure whether something is
an error, say so and say what would settle it.

---

## Part B — presentation review

Read the attached manuscript as an experienced reader of mathematical-imaging papers, not as
a referee of its mathematics. Report on presentation only:

- the abstract and introduction: does a reader of the field know after three pages what the
  paper shows, why it matters for someone who computes scale spaces, and what it does not
  claim?
- the register: sentences that are hard to parse, metaphors or coined terms that a reader
  would not follow (the paper uses "stage", "record", "profile", "catalogue", "corner",
  "bridge", "lag section", "machine"), places where the text announces rather than states, and
  any passage that reads as written for the author's own project rather than for the field;
- the maps at the heads of the sections: which help, and which only repeat the section;
- the figures and tables: is each one earning its place, is any hard to read at print size,
  and is anything missing a figure;
- the notation: collisions (the letter B is used both for the symbol of the generator and for
  Brownian motion, by a decision recorded in the notation table), symbols used before they are
  introduced, and the notation table's usefulness;
- the section structure: does each section open with what it is for, and do the section
  ends land on content rather than on a flourish.

Give located items (page and quoted phrase) and, where you can, the plainer alternative. Keep
the list short and ranked; twenty located items are worth more than a hundred.
