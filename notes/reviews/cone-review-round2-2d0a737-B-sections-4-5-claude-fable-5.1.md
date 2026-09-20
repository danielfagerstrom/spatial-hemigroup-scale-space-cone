<!-- Export note: 1 file path(s) on the author's machine were replaced by <local path> in this public copy; nothing else was changed. -->
<!-- Archive header (not part of the review): second round, referee B, sections 4-5; Claude Fable 5.1
as a blind subagent of the article session, 2026-09-19, against the frozen build 2d0a737 (75 pages).
The subagent could not write files, so this is its final message, copied verbatim by the article
session. 280,428 tokens, 35 tool uses, 19.9 minutes. See README.md for the round's design and limits. -->

I could not write the report file: the harness refused `report-B-sections-4-5.md` ("subagents should return findings as text"). The full report is below instead. My numerical checks are in `<local path>`.

**Summary.**
- The main mathematics of §§4–5 holds. I could not break Proposition 4.9(4) (`A_∞ = S`). Lemma 4.12 is correct in every constant, and I reproduced `c_1 = 12.606`, `c_2 = 5.242`, `c_3 = 3.206`. Halgreen's theorem carries Remark 5.11; I checked it at the source and numerically.
- The integrability condition printed in (5.1) does not control `U` near `θ = 1`. `U = Σ δ_{1−1/n²}` satisfies it and makes (5.1) infinite. Lemma 5.9's "term by term" against Bondesson (7.1.2) is therefore false, and so are the "two domains" of Proposition 5.7(4).
- Theorem 5.4(4) and Corollary 5.5 are false as printed for an admissible family that is not in its canonical gauge.
- The abstract and introduction claim a stronger Matérn characterization than Corollary 5.5 proves. The corollary prescribes the transfer function; the stronger claim looks true but is unproved. `F = 3log(1+ω²) − log(1+ω²/4)` shows the stages with `s > 0` are needed.
- The Student-t conditionality is not uniform: Proposition 4.5(3), p. 48, p. 60 and the Table 3 row assert it without the hypothesis.
- The strictness `A_1 ⊋ A_2 ⊋ A_3` appears only in a remark and a caption; two steps are missing.
- The label of Figure 3's bottom row says `T_1 = a/V`, the plot is `2a/V`, and Proposition 5.10 has `1/V`.
- Tables 1 and 3 have bookkeeping holes; attribution and presentation points are findings 9–13.

---

# Referee report B — sections 4 and 5 (pp. 22–50)

**How statements were judged.**

*Checked at the source* (held copies, read-only through the author's library):
- Schilling–Song–Vondraček: Thm. 1.4 p. 3, Def. 3.1/Thm. 3.2 p. 21, Thm. 3.7 p. 27, Def. 4.3/Prop. 4.4 p. 36, Thm. 13.14 p. 212.
- Sato's book: Def. 15.1 p. 90, Prop. 15.5 p. 93, Thm. 15.10/Cor. 15.11 p. 95, Thm. 24.11 p. 153, Thm. 25.3 p. 159, Thm. 26.1 p. 168.
- Sato 2001: Thm. 1.1, Thm. 1.2, Lemma 3.1, eqs. (3.3), (3.7), (4.2).
- Halgreen 1979 in full.
- Bondesson: (7.1.1)–(7.1.2) p. 105 (page image) and Thm. 7.3.1 pp. 115–116.
- Steutel–van Harn: (2.7) p. 345.

*Judged from memory or by my own computation*:
- the Fourier pair behind Prop. 5.3 and the Student-t transform;
- Grosswald's formula (tested numerically);
- Sato Thm. 8.1, Thm. 30.1 and Thm. 28.4/53.8, Barndorff-Nielsen–Halgreen, and Feller.

*Computed* (`refB_checks.py`):
- the thresholds `c_d`;
- the closed form (4.7) against quadrature of (4.6);
- the five monotonicity claims of Lemma 4.12(2);
- (4.2) against (4.6) at `d = 1`;
- the exponent identity for `F^(4)`;
- Halgreen's Thorin density against `K_{a−1}(z)/(zK_a(z))` and against (5.2);
- the counterexample of finding 1.

## (a) Verdict

The mathematics of the block holds up. I tried to break Proposition 4.9(4) and could not. The argument runs through the remainder laws, a second application of Schoenberg's theorem, the passage to a self-decomposable law on the half-line, and the identification of its exponent with Definition 4.1. It is complete. Each cited fact says what it is used for. The degenerate cases (`F ≡ 0`, the pure Gaussian, the constant `a` of the Bernstein triplet) are covered.

Lemma 4.12 is correct in every constant, and Remark 4.10's thresholds reproduce. Lemma 4.2, Propositions 4.5, 4.6, 5.1, 5.2, 5.7, 5.10, 5.12 and Lemma 5.8 are correct as far as I can check.

What is wrong sits at the edges of statements:
- the integrability condition of (5.1) (finding 1);
- the missing canonical gauge in Theorem 5.4 and Corollary 5.5 (finding 2);
- an abstract and introduction that claim more than Corollary 5.5 proves (finding 3);
- the non-uniform conditional status of the Student-t corner (finding 4);
- strictness of the dimension chain asserted but nowhere proved as a statement (finding 5);
- Figure 3's scale (finding 6);
- bookkeeping holes in Tables 1 and 3 (findings 7, 8).

None of these needs new mathematics to repair.

## (b) Findings

**1. ERROR in the proof of Lemma 5.9; IMPRECISE in (5.1), Prop. 5.7(2),(4) and the remark on p. 47.**

The condition printed in (5.1) is `∫_(0,1] log(1/θ)U(dθ) + ∫_(1,∞) θ^{-2}U(dθ) < ∞`. It does not control the mass of `U` near `θ = 1` from below, since `log(1/θ) → 0` there.

Counterexample: `U = Σ_{n≥2} δ_{1−1/n²}`. Here `Σ log(1/θ_n) = log Π n²/(n²−1) = log 2` and `U((1,∞)) = 0`, so the condition holds. Yet `∫e^{−θx}U(dθ) = ∞` for every `x`, and the right side of (5.1) is `+∞` at every `ω ≠ 0`. I checked this numerically.

Consequences:
- (i) Lemma 5.9's proof says "Thorin's integrability condition on V is (5.1)'s on U term by term". It is not. Bondesson's (7.1.2), read from the page image, is `∫(1+t²)^{-1}U(dt) < ∞` over all of `ℝ∖{0}` plus `∫_{|t|≤1}|log t²|U(dt) < ∞`. The first integral bounds `U` on every compact subset. The printed (5.1) replaced it by an integral over `(1,∞)` only.
- (ii) In (2)⇒(1), "which the same three regimes make finite for every x > 0" is not justified by the printed condition. What makes `k'` finite is that `F(1)` is finite and equals the Thorin integral, with `e^{−θx} ≤ C_x log(1+θ^{-2})`. The equivalence (1)⇔(2) survives, because (2) asserts an identity with a finite `F`.
- (iii) "The two domains of Thorin measures" in clause (4), and the remark "up to the harmless shift of the cut", are wrong for the domain as printed. The causal condition used in Remark 5.11, `∫log(1+θ^{-1})U_I < ∞`, implies local finiteness; the printed symmetric one does not. Remark 5.11 shows the author knows this ("for a measure finite on the compact subsets of (0,∞)"). The qualifier is missing where it matters.

*Repair:* state the domain as `∫log(1+θ^{-2})U(dθ) < ∞`, which is what the proofs use, or add "finite on compact subsets of (0,∞)". Correct the sentence in Lemma 5.9.

**2. IMPRECISE, p. 43, Theorem 5.4 (and Corollary 5.5, p. 44).**

The theorem is stated "for an admissible family", and by §2.2 an admissible family may be in any gauge. Clause (1) is about the exponent. Clause (4) is about the family's own stages.

Take a Matérn family in a gauge `χ ≠ id`, for instance `Φ'_{s,t} := Φ_{s²,t²}`, which satisfies (A1)–(A8) and (ND). Clause (1) holds, and clause (4) as printed fails: the stage is `((1+θ²χ(s)²ω²)/(1+θ²χ(t)²ω²))^γ`. The proof of (3)⇔(4) silently takes `φ_t = μ_{0,t}`. The same applies to the forward half of Corollary 5.5.

Proposition 4.5 says "the coordinate t is its canonical gauge" where it needs it. Theorem 5.4 must say so too.

**3. IMPRECISE, abstract, p. 3, pp. 42–44: the headline reading is stronger than Theorem 5.4(4) and Corollary 5.5.**

Corollary 5.5 prescribes the pair's transfer function `(1+θ²s²ω²)/(1+θ²t²ω²)`, including how pole and zero depend on `(s,t)`. With that prescription the converse is clause (4)⇒(1) and nothing more. "Exactly" holds in both directions only because the statement has already fixed the answer.

The abstract and introduction do not prescribe the transfer function:
- "exactly those whose stages are cascades of identical first-order recursive filters";
- "stages that are rational filters with a single pole pair";
- "exactly the admissible families whose stages, over every finite ladder of scales, are cascades of identical first-order recursive sections".

That stronger statement is proved nowhere. It appears true, by a short argument. If the stage from `0` to `t` is `((1+p²ω²)/(1+q²ω²))^n`, then `p = 0`, because the kernel from the origin is absolutely continuous (Prop. 2.8) and its transform tends to 0. Hence `F(tω) = n log(1+q²ω²)`.

The stages with `s > 0` cannot be dropped from the hypothesis. Take `F(ω) = 3log(1+ω²) − log(1+ω²/4)`, with profile `k = 6e^{−x} − 2e^{−2x}`. Then `k ≥ 0` and `k' = −2e^{−x}(3 − 2e^{−x}) < 0`, so `F` is admissible and not Matérn. Its kernel has `e^{−F(tω)} = (1+t²ω²/4)/(1+t²ω²)³`: one pole pair from the origin, two pole pairs between `0 < s < t`.

*Repair:* weaken the abstract and introduction to what the corollary says, or state and prove the stronger form.

Two smaller points:
- "For some θ and some γ" sits inside "at every knot ladder", so as printed they may depend on the ladder. This is harmless, since the ladders `{0,t}` force them constant, but the proof does not say so.
- The restriction of clause (4) to integer `γ` is needed only for the word "rational".

**4. IMPRECISE, the conditional status of the Student-t corner is not uniform.**

The condition is stated in Prop. 5.10(3), Lemma 4.8, Remark 3.4, Figure 4's caption, p. 44, p. 47 and §§7.4–7.5. The cited fact carries it. I read Halgreen §2 at `λ = −a`, `χ = 1`, `ψ = 0`: his (5) gives `u(y) = g_a(2y)` on `(0,∞)` with no drift, and his (3) is as the remark says. Numerically `∫u(y)/(σ+y)dy = K_{a−1}(√2σ)/(√2σ K_a(√2σ))` and (5.2) hold to 12 digits at `a = ½, 3/2, 2.3`.

Places that do not respect the condition:
- (i) **Proposition 4.5(3)** asserts unconditionally that the causal Bessel family with inverse-gamma kernels is a time-causal family satisfying the causal axioms. Its proof says "self-decomposability of the image is Lemma 4.2", which needs exactly Lemma 4.8's hypothesis. Either [13] proves the inverse-gamma law is a causal delay law, and then Lemma 4.8's hypothesis is a theorem and only the Thorin half of 5.10(3) is conditional. Or [13] cites it, and then 4.5(3) is conditional too. The reader cannot tell which.
- (ii) Four unconditional sentences:
  - p. 48: "The causal Bessel family, being Thorin, maps to a Student-t family that is Thorin too."
  - p. 60: "They are all members of the Thorin subclass."
  - p. 3: "the Student-t and stable families among them".
  - The chain display on p. 45 places "stable, Student-t" under the Thorin subclass with no qualifier; the stable family alone makes that step strict.
- (iii) **Table 3's** caption conditions only "not a limit". The row's presence in the table, and its profile "a Gaussian mixture", rest on the weaker half of the same hypothesis (self-decomposability of `T_1`), which the caption does not mention. The entries "n < 2a", "|x|^{−2a−1}" and "bounded: yes" are unconditional properties of the explicit density.

In the other direction, "not a limit" looks provable without Halgreen. By Prop. 7.7(1) a limit has finitely many atoms in `(0,1]`, so its exponent is analytic near `ω = 0`. `|ω|^aK_a(|ω|)` is not.

**5. GAP, pp. 34–35 and Figure 4: the strictness `A_1 ⊋ A_2 ⊋ A_3` is not a proved statement.**

Lemma 4.12(2) is about the functions `k_d^{(c)}`. The conclusion about the classes is drawn in Remark 4.10, Figure 4's caption, §4.6's introduction and p. 3. Two steps are missing:
- (i) That `k_d^{(c)}` *is* the polar profile of the law with exponent `F^{(c)}(|ξ|)` on `ℝ^d`. Proposition 4.9(2) proves this for a causally admissible datum. For a delay datum without monotonicity, the proof of Lemma 4.12 re-reads the computation at `d = 1` only. The `d`-dimensional computation does not read monotonicity before its last line, but this has to be written.
- (ii) The "only if" inference from "this radial density is not nonincreasing" to "not self-decomposable". Beside uniqueness of the Lévy measure, one needs that Sato's (15.8), with some `λ` and `k_ξ`, forces the radial density of a rotation-invariant Lévy measure to be nonincreasing. Average (15.8) over the orthogonal group, then use continuity of `k_d`.

*Repair:* add a clause (3) to Lemma 4.12, "`F^{(8)} ∈ A_1∖A_2`, `F^{(4)} ∈ A_2∖A_3`", with these two sentences.

**6. ERROR in a figure, p. 27, Figure 3, bottom row.**

Three scales disagree:
- The label reads "`T_1 = a/V, V ~ χ²_{2a}`".
- Proposition 5.10 has `T_1 = 1/V`.
- What is plotted is `T_1 = 2a/V`, the standard `t_3`.

The delay density peaks at about 0.61 near `u = 0.6`, the mode of `3/χ²_3`. The kernel peaks at about 0.37 `= 2/(π√3)`, whereas the kernel of Prop. 5.10(1) at `a = 3/2` peaks at `2/π ≈ 0.64`. So the row is at canonical scale `√(2a)`, not at "canonical scale 1" as the caption says.

The panel titles write `B_{T_1}`, against Table 2 (`W` is Brownian motion, `B` the symbol). Figure 5's middle panel is at the proposition's scale and is consistent.

**7. IMPRECISE, Table 1 and §1.1 against the proofs of the block.**

- (i) The A23 row lists only "Prop. 4.9(3)" as the direct user of the radial theorem. Clause (4) applies it a second time, to `g_c`. It also uses Bernstein's existence theorem (A11), Sato Prop. 15.5, Thm. 24.11 with Remark 21.6, SSV Thm. 3.7 and Sato Cor. 15.11. None of these is listed for 4.9(4), though the caption says the table "lists every cited fact with the results that use it directly".
- (ii) The caption says A15 and A16 (the Matérn closed form and the Bessel asymptotics) are "used by no proof". Corollary 5.5's "exponential tails" is proved "by Proposition 5.3", which is those two facts. Table 3's Matérn tail entry rests on the same. *Repair:* list them, or replace the appeal by the elementary one: `e^{−F}` is analytic in `|Im ω| < 1/t`, so `E e^{β|X_t|} < ∞` for `β < 1/t`, and Prop. 5.1(2) gives the other side.
- (iii) §1.1 counts "four corner identifications" in Proposition 4.5, which has five items. If the one left out is (3), say so (see finding 4).

**8. GAP, Table 3 (p. 38): entries with no carrying statement.**

- (i) Stable row, tail "`|x|^{−1−α}`": the caption sends the reader to Prop. 5.12 "for the sense", and Figure 5's caption attributes the order to it. Prop. 5.12 states the moment count only. No tail order of the stable density is stated or cited anywhere in the paper.
- (ii) "Bounded at 0: yes" for the stable and Student-t rows: Corollary 3.9 and Proposition 3.7 explicitly claim nothing when `k(0+) = ∞`, which holds for both. For Student-t, Halgreen's density is `~ 1/(π√(2y))` at infinity, so `U_I` has infinite mass. The entries are true for one-line reasons (integrable transform; explicit density), which should be given.
- (iii) "Lag sections: none" for the unit-step row is carried by nothing. For the Student-t and stable rows it is carried by an unnumbered sentence of §7.4 ("as their transforms show"). All three are easy: the stage transforms decay faster than any rational function, or are nonconstant entire functions bounded on the real axis. But the table says it collects what the sections establish.
- (iv) Prop. 5.1(2), "no kernel other than the Gaussians has a Gaussian or lighter tail": the sense (`E e^{αX²} = ∞` for every `α > 0`) is fixed only in the proof.

**9. PRESENTATION, p. 33, proof of 4.9(4).**

- "By the one-dimensional characterization" is not the paper's Proposition 2.2, which is for symmetric laws. `T` is one-sided, and the fact used is Sato Cor. 15.11. Cite it at that line.
- The radial theorem is stated for `f : (0,∞) → [0,∞)`. That `g_c ≥ 0` deserves a half-sentence.
- Sato's Def. 15.1 quantifies over `b > 1`. The paper's `c ∈ (0,1)` is `b^{-1}`; say so once.

**10. PRESENTATION, attribution.**

- (i) Proposition 5.7(4) is Bondesson's Theorem 7.3.1, both directions, with the measure map `t ↦ √(2t)`, in the paper's folded normalization. The paper says so only in Remark 4.10. At the statement it reads as new.
- (ii) Formula (4.3) and the monotonicity argument of Lemma 4.2 are Sato 2001 (3.3) and Halgreen §3. Remark 4.4 is Halgreen's pp. 15–16 argument.
- (iii) Remark 4.10 says that beside Sato's Theorem 1.2 "what this paper adds is an explicit family with its constants". Sato's witness is explicit too: his (3.7) is `2s^{-1/2}` with a rising piece on `[1/(a+b), 1/a)`. Lemma 4.12(1) is the same design with a jump in place of a slope. What is new is the crossing of the dimensions and `A_∞ = S`.

**11. PRESENTATION.**

- Lemma 5.9's statement writes the two-sided exponent as a log-mgf, `½cσ² + ∫(…)V`. Its proof writes minus a log-mgf, `−bσ − ½cσ² − ∫(…)V`. Use one sign convention.
- Proposition 5.7 numbers its clauses 1, 2, 4, 5.

**12. IMPRECISE, p. 30, remark after Lemma 4.8.**

"An admissible F whose catalogue is carried by a compact subset of (0,∞)": by Remark 2.4 the catalogue is `ν = k dx/x`. For a nonincreasing `k ≢ 0` its support contains a neighbourhood of 0, so no catalogue is carried by a compact subset of `(0,∞)`. What is meant is the tail measure `ϖ`, that is, `k` of bounded support. The argument that follows is right for that reading.

**13. IMPRECISE, p. 26, Proposition 4.5.**

The proof invokes "the causal similarity form in the canonical gauge" and the causal (ND). Neither is restated in this paper. The proof also does not note that `F_I ≢ 0` is what gives (ND) for the image. A reader of this paper alone can verify Lemma 4.2 and everything downstream of Definition 4.1, but not the hypothesis of Proposition 4.5.

## (c) Checked and found sound

- **Proposition 4.9:**
  - (1) Nesting by projection.
  - (2) The Lévy measure `ν_d`, the bound `1∧du`, the Lévy–Khintchine identity with covariance `b_0I`, and the polar formula (4.5) with its constant and its reduction to (4.2) at `d = 1` (also numerically).
  - (3) `A_∞ ⊆ B`, `a = f(0+) = 0`, `f' > 0`.
  - (4) In full. The load-bearing citation is that the remainder `ρ_b` is *infinitely divisible* (Sato Prop. 15.5), and the paper says so. The uniqueness used (no zeros of `μ̂_d`; a Laplace transform determines a law) is supplied.
  - Among the `F^{(c)}` I found the expected behaviour: each leaves `A_d` at `c = c_d`, and `c_d` decreases to 0.
- **Lemma 4.12:**
  - (4.7) and (4.8); both elementary bounds; the maximizer `p = (mλ+1)/(m+1)`.
  - `6+4√2 = 1/(3/2−√2)` and `6912/3125 < π`.
  - Both failure points (`14/25 > √π/4`; `4·351/2500 > ½`).
  - The no-ancestor argument through Prop. 2.9.
  - Thresholds `c_1 = 12.606`, `c_2 = 5.242`, `c_3 = 3.206`.
- **Lemma 4.2, Remarks 4.3, 4.4, Prop. 4.5(1),(2),(4),(5), Prop. 4.6, Lemma 4.7:** all constants, the first-passage identity, `k = 2γe^{−√2x}`, `c_β = β/Γ(1−β)`.
- **Prop. 5.1** against Sato Thm. 25.3 and Thm. 26.1 as printed in the source; the variance argument; the last sentence of (2).
- **Prop. 5.2, 5.3:** the normalization, `γ = 1`, `γ = ½`, the tail constant `2^{−γ}/Γ(γ)·t^{−γ}`, the Gaussian limit.
- **Theorem 5.4** in canonical gauge, all directions.
- **Prop. 5.7:** (1)⇔(2) subject to finding 1; uniqueness through Prop. 2.9; clause (4) both ways, including `uθ'²/2 − uθ'/2 + u/2 ≥ 0` and the factor 2; clause (5), including the `erfc` profile and the contradiction.
- **Lemma 5.8.**
- **Prop. 5.10**(1),(2),(4) and the conditional (3).
- **Prop. 5.12**, including the Thorin density and its Jacobian.
- Table 3's remaining entries agree with the statements named for them.

## (d) Not settled

- Whether `A_∞ = S` is new. Sato 2001 and Halgreen do not contain it. I did not search Barndorff-Nielsen–Pedersen–Sato 2001 or the type-G literature in `ℝ^d` (Maejima–Rosiński), where such a statement would be if it exists.
- Everything that leans on [13]:
  - that Definition 4.1 is "exactly" the causal class;
  - the hypotheses of Proposition 4.5;
  - what [13] establishes about the inverse-gamma law (finding 4(i)).
- Not read at the source: Sato Thm. 8.1 and Thm. 30.1, Barndorff-Nielsen–Halgreen pp. 309–311, Feller XIII.4, and the Fourier pair of Prop. 5.3. I have no doubt about any of them.
- What §1.1 reports as machine-checked could not be examined in a blind review of the PDF. This report judges the printed arguments only.
