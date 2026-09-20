# How this article was made — the process account (module B)

This is the account that the "Author contribution and use of AI" section of *the admissible
cone, its corners and their implementation* points to. That section is short by design: roles,
verification and review status, the record, responsibility. This note has the chronology, the
division of labour in numbers, the reviews, and the caveats the numbers travel with. It is
written in the first person, from the session archive; the sources and their limits are in the
last section. The line paper's account (`notes/PROCESS.md` in the development repository, and
in that paper's own export) covers the campaign that produced the mathematics and the formal
development of both articles, and this note does not repeat it.

*Status: drafted 2026-09-18, before the external review rounds and before my final reading.
The section on reviews and the figures are to be brought up to date before the release.*

## How the work went

The three modules come from one working draft. I asked the question on 10 August 2026: what
does the hemigroup weakening give on the line? The agent's reply the same day already named
what this article is about: the symmetric cone with the cosine-integral functions as its
extreme rays, the subordination that carries every causal family to a symmetric one, and the
Matérn family as the corner with rational spectra, implementable by forward–backward
first-order filtering. The sustained work of 5 to 14 September produced the draft, the
blueprint, the Lean development and the line paper, which was released as v0.1 on 15 September.
Chapters 8 to 11 and 14 of the blueprint, which are this article, were written, typed in Lean,
proved and reviewed in that campaign beside the chapters of the line paper.

The work that is this article's own began on the morning of the release, 15 September. An
agent, asked to read the released paper as a postdoctoral colleague would, returned five
proposals. Three of them are in this article: the boundedness threshold of a kernel at the
origin, the dimension filtration read through Schoenberg's radial theorem, and the question
whether the Thorin section needs a new interface, which it turned out not to need. The same
day the export script was given the module as a parameter, three agents formalized what the
proposals needed, I took three decisions on their recommendations (admit the three interface
names for the origin behaviour, make the two constructions of the filtration statements, keep
the one advisory of the linkage check as the honest count), and all eight sections were
drafted from the blueprint with the statements transcribed verbatim.

From 16 to 18 September I read the article section by section and gave my comments in the
session, about forty-five of them in ten messages. They changed the article's form more than
its content. The first draft cited the line paper and moved fast; I asked that it restate what
it uses, so that it can be read alone, and section 2 was rewritten with the notation, the
axioms, the profile and the characterization theorem. I asked for a map at the head of each
technical section, for every term to be introduced where it is first used, with its
literature, for the commentary on machine checking to leave the body and live in section 1.1,
for results to be described before their proofs are discussed and the details after, and for
figures wherever an object could be made concrete. One comment changed the mathematics of
record: the remark on the dimension filtration read as a proof, and became a proposition with
a proof and a ledger entry of its own.

On 18 September the register pass ran, and at my request a numerical experiment on the model
of the causal article's was designed, built and written up. Both are described below, because
both found errors.

## What the agents did, in detail

The prose, the code, the figures and the numerical experiments were written by AI agents
throughout, in dialogue with me; I worked from the conversation and from the built PDF. The
Lean 4 development, now about 44,000 lines in 155 files for the three modules together, is
theirs essentially in full, and none of the proof terms are mine. This article's statements
rest on 123 of those modules, 53 more than the line paper's release.

Mathematical content is theirs as well, and the record dates it. The cone, the bridge and the
Matérn corner were in the reply of 10 August, in answer to an open question of mine that named
none of them. The reading of a gamma cascade as a quadrature of the Thorin measure is older
and comes from the causal article's side, first on 7 August and refined on 31 August, again
in the agent's turns; my part that day was a question about what the quadrature meant. The
boundedness threshold and the dimension filtration were the postdoctoral agent's proposals of
15 September. The design of the numerical run was the agent's, in answer to my request.

During the article stage the agents found and repaired errors in the statements of record:

- two while transcribing the statements into the article (ledger rows R164 and R165);
- the dimension-filtration proposition, written out with its proof and its cited theorem read
  from a held copy at my request (R166);
- two by the blind reviewers of the register pass: a hypothesis that a restating clause had
  dropped from the stationary-point criterion of the bridge and, through it, from the
  proposition of two days before (R167), and the Matérn realization corollary, whose
  uniqueness was claimed against "first-order forward–backward sections", which other members
  have too, and now reads "a cascade of identical" such sections (R168);
- the numerical run, which showed that the article's prose claimed in five places that every
  member of the Thorin subclass is approximated by families with rational stages. The
  proposition says that for quadratures with real weights, and says of the rounding to integer
  weights only that it stays in the class. On the Poisson scale space the rounded families
  converge to another member and stay at a fixed distance. The prose was corrected.

Corrections that make the article claim less are delegated to the agents by a standing rule of
the project (the development repository's `CLAUDE.md`, my decision of 11 September): each is
recorded with a marker and a ledger row and reported to me, and I keep the veto. Widenings and
new interface names wait for me. The technical decisions of the formalization were, as for the
line paper, the agents' recommendations, which I read with their consequences and followed.

Twice I overruled the agents, and both times the matter was the writing and not the
mathematics. The first draft's policy of not restating the line paper was the agent's
inference and not a rule of mine, and it went. And I do not agree with the hub's writing
standard where it rules out per-section roadmaps: they help when a section's payoff needs many
technical steps, and they are noise in a short section with a natural path. I also found a gap
the agents had missed, that neither this repository's instructions nor the framework's agent
definitions actually refer to the writing standard the drafting was supposed to follow.

## What the formalization changed in the mathematics

*(Moved here from the article's concluding section on 2026-09-19, at the external reviews'
request that the development's history leave the body.)* Several of the printed proofs follow
the machine-checked route and differ from the ones first written. Five are worth recording.

- The injectivity of the Choquet map passes from tails equal almost everywhere to equal
  measures through a finite restriction. The Choquet measure of an unbounded profile puts
  infinite mass near the origin, so no exhausting sequence of half-lines of finite measure
  exists before the restriction.
- The delay equation of the `Cin` kernels is proved with the two halves of a signed weight kept
  positive until the last step, because the uniqueness of the transform is available for
  positive measures.
- The tail measure `ϖ` of a member of the Thorin subclass is identified as a mixture of
  exponential laws by comparing tails, since `ϖ` is given only by its tails and the profile
  need not be differentiable.
- The bridge onto the Thorin subclass constructs the causal datum and computes its exponent.
  The first version compared integrability conditions term by term.
- The passage between the two-sided convention of the probabilistic sources and the folded one
  of the article was asserted in prose until this article. It is now a lemma (the folding
  translation), and that is what allowed the cited facts on the density at the origin to be
  admitted at the letter of their source.

In two places the formalization changed a statement, in the direction of claiming less. The
Student-t family's membership of the subordinated slice and of the Thorin subclass is stated
under the hypothesis that its delay law has the representation the literature gives it. In the
boundedness threshold, the identification of the Matérn kernel at `γ = ½` with the Bessel
function `K₀` moved from the statement to the text after it, because the closed form is cited
and not proved.

## The reviews

Review by agents that had no part in the writing was a working method, as for the line paper.
The register pass of 18 September used eight reviewers, one to a section, each given the
section and the writing standard and nothing of the drafting. Each returned a ranked list of
findings with verbatim anchors, about 170 of which were applied by exact replacement. The part
of their brief that paid was the scope audit: restate each claim from its statement, then
compare with the prose. The summaries written during my review had dropped hypotheses in the
abstract and in five sections, and two statements of record were themselves at fault (above).
Twenty-three findings inside statements, proofs and copied remarks are listed for the
blueprint in `notes/reviews/register-b/README.md` of the development repository.

The numerical run is a review of another kind, of the statements against a computation. Its
five checks passed; what it found is above and in the article's section 7.6. It also settled a
question the article had left open about the two recursive Gaussians in common use, from their
published coefficients, read from held copies.

At the date of this note the article has not been read by an AI system of another vendor, and
no human reader beyond me has reviewed it. The external rounds are the next step.

## By the numbers

The work specific to this article, from 15 September to the evening of 18 September 2026, is
one long session with its subagents: about 9.7 hours of recorded active time, about 1,900
words from me in 15 turns against about 45,500 words from the agents, a ratio of about
twenty-four to one, and about 1,250 subagent turns. My review is ten of those turns.

Those figures were computed on 18 September 2026 from an archive synced through 20:00 UTC that
day, and they are lower bounds. Active time is capped at fifteen minutes of idleness per gap,
so the hours I spent reading the built article between my messages are mostly not in it. My
words are what I typed into the prompt; reading on paper and thinking away from the keyboard
leave no trace. The writing of this note and of the statement, my final reading, and the
external reviews and the revision they will drive are after the sync and are counted nowhere.
A session of under an hour in the framework's repository, which made a second paper directory
possible, is not counted either. The archive still does not join this repository's commits to
its sessions, and the session that anchored the September campaign is still tagged to the hub,
so the archive's own per-repository table undercounts this repository by a factor of nearly
three.

For the whole of the Paper V work in this repository, from 5 September through the same sync,
the archive now holds about 93 hours of active time, 14,600 words from me against 290,000 from
the agents, a ratio near twenty to one, about 13,900 subagent turns and 174 turns of mine. The
line paper's article stage, which its own note could not yet count, is in these totals. The
ratio has come down from the twenty-two to one of the line paper's note because a review adds
more of my words than of the agents'.

## What this article would otherwise have been

It would not exist, for the reasons the line paper's note gives, and it would not have the
corrections the reviews and the run found.

## Sources for this account, and where the record qualifies it

The account was written from the archivist's report of 18 September 2026 (computed from
`chronicler`, canonical tier synced 18 September 20:00 UTC, research conversations only,
scoped to this repository by the sessions' repository tags with the hub-tagged anchor session
added by hand, as in the line paper's note), from the repository's git log, changelog and
ADRs, and from the fidelity ledger. The count of my review comments is a manual reading of the
session and an estimate; no tool computes it. The first appearances of the ideas were found by
full-text search of the archive, oldest first. The figures are not to be restated without
re-deriving them.

A simple account, that the agents wrote and I reviewed, is wrong in both directions, and the
record shows where. The agents did more than write: the ideas of the article are dated to
their turns, and they corrected the mathematics of record five times in four days, twice
in text that I had already read without seeing the fault. And I did more than
review: the form of the article is mine, against the agents' first draft, and one of my
comments turned a remark into a proposition.
