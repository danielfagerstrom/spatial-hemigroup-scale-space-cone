# External reviews of module B

Referee-style reviews of *the admissible cone, its corners and their implementation* solicited
by the author from AI systems other than those that wrote it, against a frozen PDF build, and
archived here verbatim as provenance. The procedure is the line paper's (`../README.md`): the
author runs the prompt in `PROMPT-external-review.md` in each system's own interface with the
PDF attached, saves the output here unedited under a filename carrying the attribution (the
system, and its reasoning-effort setting where one was chosen), and the article session then
assesses every finding independently, against the text and the formal development, and records
the disposition in `../../PLAN-review-response-module-b.md`.

**The reviewed build** is the article at repo revision `a76a323` (2026-09-19, 73 pages: the
end of the author's own review, the register pass, the numerical run, the AI statement and the
closure proposition), built with `tectonic paper-b/main.tex`. The PDF is
`cone-review-build-a76a323.pdf` in this directory; PDFs are ignored by git, so it is a local
file, reproducible from the revision. Page references inside the reviews are to that build;
section and statement numbers may shift in the revisions the reviews drive.

The reviews are inputs to the revision process, not statements by the author; where a
review's claim is found wrong or out of scope, the response plan says so. No finding is acted
on because a reviewer asked for it alone.

## Files

- `PROMPT-external-review.md` — the prompt, in two parts: the journal-style review and the
  shorter presentation review. It differs from the line paper's in what it points the referee
  at: the statements that are proved in prose and not machine-checked (the dimension
  filtration and its witnesses, the closure of the families with rational stages, the whole
  implementation section), the conditional clauses on the Student-t family, the numerical
  example with its claims about two published recursive Gaussians, whether the paper reads on
  its own, and what a journal version of 73 pages should lose.

- `cone-review-content-a76a323-GPT-6-Astra-Ultra.md` — part A, run by the author on 2026-09-19 in
  OpenAI's GPT-6 Astra at the Ultra setting (the output's own header says the setting was not
  exposed to the system; the attribution is the author's); verdict *major revision*. This is
  *the review* that `../../PLAN-review-response-module-b.md` responds to, finding by finding.
- `cone-review-presentation-a76a323-GPT-6-Astra-Extra-High.md` — part B, run the same day in
  GPT-6 Astra at the Extra High setting; twenty ranked presentation items.
- `fixes-r1-prose.txt` — the paper-side anchor edits of batch R1a, applied with
  `scripts/apply-anchors.py`.

Both reviews are verbatim as uploaded by the author; they were run remotely, and the uploaded
files were copied here unchanged apart from their names.

**Second round.** After the response to the first two reviews (batches R1–R4, the seven
decisions and ledger rows R170–R173 of `../../PLAN-review-response-module-b.md`, 2026-09-19), a
second build was frozen at revision `2d0a737` (75 pages; `cone-review-build-2d0a737.pdf`,
untracked) for a referee-style review in another vendor's system. Its prompt is
`PROMPT-external-review-round2.md`: the same eight questions, pointed at what changed (the
origin proposition with its slowly varying factor, clause (4) of the dimension filtration, the
closure proposition and the counterexample beside it, Table 3, the two variants of the
numerical example) without telling the reader what the first referee found. Page references in
that review are to the second build.

**How the second round was run, and what that does to its independence (2026-09-19).** No other
vendor's frontier system was usable: the author's attempts with Grok timed out repeatedly, and
the Gemini models within reach were flash or old reasoning models. At the author's decision the
round was run inside the article session as five blind referees, each a fresh subagent given the
frozen PDF and a text dump of it and nothing else, forbidden to open the repository, the hub,
the earlier reviews or the author's scripts, and allowed the held library (read-only) and web
search to check cited facts at their sources: `A` sections 1–3 with the trust base (Claude
Opus 5), `B` sections 4–5 and `C` sections 6–7 (Claude Fable 5.1, where the proofs that exist
only in print are: clause (4) of the dimension filtration and the closure proposition), `D` a
reproduction of the numerical example from its printed description with code of its own
(Opus 5), `E` the headline claims, the trust base, novelty and exposition over the whole paper
(Opus 5). The prompts are the round-2 prompt cut by block, with the classification ERROR / GAP
/ IMPRECISE / PRESENTATION asked for. **Two limits, to be stated wherever the round is cited:**
the referees are models of the vendor whose model drafted the text, two of them the same model,
so their blind spots are correlated with the draft's in a way the first round's were not; and a
subagent started in this repository may have its project instructions in context, which name
what the first round found. The reports are archived verbatim as
`cone-review-round2-2d0a737-<block>-<model>.md`.

## For the release

`scripts/export-release.py --reviews notes/reviews/cone` exports the files of this directory as
the export's `notes/reviews/`, and `--response-plan notes/PLAN-review-response-module-b.md`
the plan, so that module B's export carries its own rounds and not the line paper's.
