<!-- Export note: 1 file path(s) on the author's machine were replaced by <local path> in this public copy; nothing else was changed. -->
<!-- Archive header (not part of the review): second round, referee C, sections 6-7; Claude Fable 5.1
as a blind subagent of the article session, 2026-09-19, against the frozen build 2d0a737 (75 pages).
The subagent could not write files, so this is its final message, copied verbatim by the article
session. 233,877 tokens, 21 tool uses, 14.6 minutes. See README.md for the round's design and limits. -->

I could not write the report file: the Write tool refuses report files from a subagent, so nothing exists at `.../scratchpad/review2/report-C-sections-6-7.md`. I did not route around the refusal through the shell. The full report is below, ready to save at that path.

**Summary.**
- No numbered statement in sections 6–7 is false as far as I can find.
- Proposition 7.7 is correct. I checked Bondesson Thm 3.1.5 (pp. 29, 34–35, page images) and Feller XIII.1 Thm 2 (p. 431) at the source, and every attempt to break it failed.
- Remark 7.5's counterexample is correct in every printed detail, verified by hand and numerically.
- Section 6 is sound line by line. Sato Thm 17.5 was checked at the source.
- One false sentence of commentary: p. 55 says non-Matérn Thorin members have an infinite tail measure. That is false for any finite U.
- p. 61 says "a family with rational stages is a finite convolution of gamma laws", which contradicts Remark 7.5.
- Four gaps:
  - Proposition 7.6 never shows that a convergent quadrature exists for a given Thorin measure.
  - "These are the families realized by lag sections" is proved in one direction only.
  - The signed-density uniqueness in Remark 7.3 needs a recombination step.
  - The proof of 7.4(2) is missing steps.
- Proposition 6.4(4)'s Student-t clause is unconditional and mis-referenced, at odds with §1.1 and Table 1.
- New example: k = 4e^{-x} − 2e^{-2x} gives an admissible family with rational stages and only real poles and zeros, outside the Thorin subclass. Remark 7.3's case split misses it.
- Strengthening: every limit in Proposition 7.7 has an exponential moment, so the stable and Student-t members are excluded without Halgreen's theorem.

---

# Referee report C — sections 6 and 7 (pp. 51–64), blind

Manuscript: *Spatial scale space from hemigroup axioms: the admissible cone, its corners and their implementation* (75 pp., "working draft"). Block: Propositions 6.2, 6.4, 7.1, 7.2, 7.4, 7.6, 7.7, Remarks 7.3, 7.5, 7.8, 7.9, with Corollary 5.5 and the Thorin material of §5.3 as far as the block uses it. Read from the rendered pages. Pages 1–21, 38–50 and 51–71 were read; §4 was not.

## (a) Verdict on the block

No numbered statement in the block is false as far as I can find.

Proposition 7.7 is the one result whose printed argument is all there is, and it rests on two cited theorems. It is correct. I checked both theorems at the source, the normalizations between the one-sided and the two-sided Thorin measure, the integer-valued vague-limit step, and the converse. I failed to break it in either direction.

Remark 7.5's counterexample is correct in every printed detail, verified by hand and numerically. Section 6 is sound line by line.

What is wrong sits around the statements, not in them:
- One false sentence of commentary after Proposition 6.4.
- One sentence before Proposition 7.7 that says "rational stages" where only "lag sections" is true, and so contradicts Remark 7.5.
- An approximation property (every Thorin member is a limit of finite quadratures) that the introduction, §7.4, Remark 7.8 and §8 attribute to Proposition 7.6. That proposition defines a quadrature by its convergence and never proves that one exists.
- An identification ("these are the families realized by lag sections") of which only one inclusion is proved.
- A uniqueness step among *signed* densities in Remark 7.3 that the cited uniqueness (positive pairs) does not literally give.
- An unconditional Student-t clause in Proposition 6.4(4) that sits badly with §1.1 and Table 1.

All are repairable in a few lines each. One substantive improvement is also available: every limit in Proposition 7.7 has an exponential moment, which excludes the stable and Student-t members without Halgreen's theorem.

## (b) Findings

**1. IMPRECISE — p. 61, paragraph before Proposition 7.7: "Under the bridge a family with rational stages is a finite convolution of gamma laws with integer shapes."**
- This is false as written, by the paper's own Remark 7.5 (p. 60). That family has rational stages and is not in the Thorin subclass, so under no reading is it a finite gamma convolution.
- The sentence is true of the families *realized by lag sections* (the set R of Proposition 7.7).
- The same slide from "lag sections" to "rational stages" occurs on p. 68 ("How close a member with rational stages comes to a given member…"). There the run only measures members of the closure of R.
- Repair: write "a family realized by lag sections" in both places.

**2. GAP — p. 61, Proposition 7.7, preamble: "These are the families realized by lag sections".**
- Only the inclusion R ⊂ {families every increment of which is a cascade of lag sections} is justified, by Proposition 7.4(1).
- The proposition's title, Table 3's last column, Remark 7.9 and §8 all use the converse: that no admissible family outside R is so realized.
- The converse is true, but the argument depends on what "lag section" means.
  - (i) In the sense of Propositions 7.2 and 7.4(1), with pole and zero at the common ratio s/t. Read the stage from 0 to t. The zeros disappear and e^{-F(tω)} = ∏(1+t²ω²/θ_j²)^{-1}, so F ∈ R. This is one line and should be printed.
  - (ii) In the wider sense the prose suggests: any convex combination of the identity and a one-sided exponential, with transfer (1+izω)/(1+ipω), 0 ≤ z < p. Then F(ω) = Σ log(1+p_j²ω²) − Σ log(1+z_j²ω²) after cancellation. Each zero of a stage must be paired with a strictly larger pole range. Let s ↑ t and count at the range t·z_j of any zero. A family with any z_j > 0 then has stages with s close to t that are not such cascades.
- So the converse holds in both senses as far as I can tell, but neither is on the page.
- Repair: fix the sense of "lag section" in Proposition 7.7 and print argument (i).

**3. IMPRECISE — p. 58, Remark 7.3, the case split "If Q has only real roots and P ≡ 1 … If Q has complex roots …"; and Remark 7.5.**
- The split omits real poles with a nontrivial numerator. That is the generic case for a stage, and it is not harmless for a kernel from the origin.
- Example: k(x) = 4e^{-x} − 2e^{-2x}.
  - It is positive, k′ = −4e^{-x}(1−e^{-x}) ≤ 0, and both integrability conditions hold.
  - F(ω) = 2 log(1+ω²) − log(1+ω²/4), so e^{-F} = (1+ω²/4)/(1+ω²)². I checked this numerically against the integral (2.2) at four frequencies.
  - So this is an admissible family with rational stages (order 6) whose poles *and* zeros are all real, that is, on the imaginary ω-axis.
  - It is not in the Thorin subclass (k″(0+) = −4 < 0) and not in R.
  - Its kernel from the origin is a cascade of positive first-order forward–backward sections: (1+ω²/4)/(1+ω²) times 1/(1+ω²).
  - Its stage from s to t has pole ranges {t, t, s/2} and zero ranges {t/2, s, s}. The pole s/2 has no smaller zero to pair with. So the stage is a cascade of real first-order sections of which one necessarily has a negative coefficient.
  - The stage kernel itself is still positive. Numerically, at s = 1, t = 2: atom s²/t² = 1/4, continuous part ≥ 0, mass 3/4.
- Consequences:
  - (a) "Real poles" implies neither "Thorin" nor "lag sections". Remark 7.5's moral ("monotonicity does not exclude oscillating terms") is only half of what fails in the converse of 7.4(1).
  - (b) Remark 7.3's "real-pole case" should be stated as "real poles, no zeros".
  - (c) Open question 2 of §8 should record that the admissible rational transforms exceed the Thorin subclass already among real-pole transfers.
- Repair: add the example to Remark 7.5.

**4. GAP — p. 58, Remark 7.3: "That criterion is the uniqueness of the Lévy pair (Proposition 2.3 of [14](3)) read at a rational transfer, which leaves the signed density as the only candidate". Repeated on p. 69: "the signed density is the only candidate, the Lévy pair of a law being unique".**
- The cited uniqueness is among pairs (a, ν) with ν a *positive* measure.
- The step needed is this. Suppose ψ = −log R is the exponent of an infinitely divisible law with pair (a, ν), and also ψ(ω) = ∫(1−cos ωx)ρ(x)dx with ρ a signed density, ∫(1∧x²)|ρ| < ∞. Then a = 0 and ν = ρ dx.
- It follows by the recombination the paper itself uses in Lemma 3.5 (p. 18). Write ψ + ∫(1−cos)ρ⁻ = ∫(1−cos)ρ⁺. Both sides are exponents with positive Lévy measures ν + ρ⁻dx and ρ⁺dx. Uniqueness gives a = 0 and ν = ρ dx, which is impossible if ρ⁻ ≠ 0.
- That is one sentence. At present the exclusion of the Young–van Vliet prototype rests on an unstated step.
- Proposition 7.4(2) uses the same uniqueness for its "exactly when". Table 1 lists neither it nor the remark under A3.

**5. IMPRECISE — p. 58, Remark 7.3, opening: "A forward–backward recursive filter with transfer R(ω) = |P(iω)/Q(iω)|²".**
- The remark then declares both standard designs "decided by this test".
- Deriche's design, as described on p. 69, is a causal half plus an anticausal half *added*. Its transfer changes sign on the real axis (Figure 11(a) inset). No |P/Q|² does that.
- The test the paper actually applies there is the prior one: an infinitely divisible transform has no real zero. It is not the signed-density criterion of the remark.
- Repair: state the remark for an even rational R with R(0) = 1, in three steps: R > 0 on the real axis, the signed density nonnegative, the profile nonincreasing.

**6. GAP — p. 60, Proposition 7.6.**
- Proposition 7.6 *defines* a quadrature as a sequence with F_N → F pointwise, and then applies Lévy's continuity theorem. It never shows that a quadrature exists for a given U satisfying (5.1).
- The existence is relied on in five places:
  - p. 3: "are limits of members with finitely many ranges (Proposition 7.6)";
  - p. 56;
  - p. 60: "The proposition says … that the kernels of the quadrature converge weakly to those of the given member";
  - Remark 7.8: "The Thorin quadrature of Proposition 7.6 with the Bessel spectral density and real weights converges to it";
  - §8: "every member of the subclass is a limit of members with finitely many ranges".
- The claim is true. Restrict U to [1/N, N]. Lump the mass of cells of width δ_N at a point of each cell, with U([1/N,N])·N·δ_N → 0, using |∂_θ log(1+ω²/θ²)| ≤ 2/θ. The two tails vanish by the integrability conditions of (5.1) and dominated convergence.
- Bondesson p. 35 asserts the half-line version without proof: "An arbitrary GGC … is certainly a limit of a sequence of finite convolutions of Gamma distributions".
- Repair: add existence as a clause with the three-line proof.
- Related: the run of §7.6 uses quadratures that carry the mass above the last cell as a Gaussian coefficient. Proposition 7.6 ("with the same Gaussian coefficient") does not cover that as stated.

**7. IMPRECISE (and an available strengthening) — p. 61, Proposition 7.7(1): "with finitely many θ_i in every compact subset of (0,∞)".**
- This is true, but weaker than what the proposition's own representation forces.
- Atoms of mass ≥ 2 cannot accumulate at 0, because ∫_{(0,1]} log(1/θ)U(dθ) < ∞ in (5.1).
- So the atoms are finitely many in every (0, M], accumulate only at infinity, and Σ n_i/θ_i² < ∞.
- Hence θ_min > 0 exists, and k(x) = Σ 2n_i e^{-θ_i x} ≤ Ce^{-θ_min x} for x ≥ 1.
- Every limit therefore has all moments finite (Proposition 5.1(1)) and E e^{λ|X_1|} < ∞ for λ < θ_min.
- This gives a second, elementary form of clause (3): *an admissible family with a missing moment is no limit of families realized by lag sections.*
- It excludes the stable members and the Student-t members unconditionally.
- At present the Student-t exclusion (Table 3, the remark after 7.7, Remarks 7.8 and 7.9) is conditional on Halgreen's theorem, through "its Thorin measure has a density". With the moment argument that condition can be dropped everywhere it appears in §7 and in Table 3.

**8. IMPRECISE — p. 54, Proposition 6.4(4), last clause: "the Student-t family is the case of the Bessel Thorin measure of Proposition 5.7(4)."**
- (i) Proposition 5.7(4) is the bridge on Thorin subclasses and contains no Bessel measure. The measure is in Remark 5.11.
- (ii) That the Student-t family is a Thorin member at all is conditional on the hypothesis of Remark 5.11, by Proposition 5.10(3). Here it is asserted unconditionally inside a proposition.
- (iii) §1.1 says of §6 that "everything" is machine-checked on the Lévy–Khintchine uniqueness and Lean's foundations alone. Table 1's caption says Halgreen's theorem is "used by no proof". An unconditional Student-t clause is inconsistent with both.
- Repair: "under the hypothesis of Remark 5.11, the Student-t family is the case U = twice the image of U_I under θ ↦ √(2θ)".

**9. ERROR (commentary) — p. 55, first paragraph after Proposition 6.4: "It is needed because for a Thorin member other than the Matérn one the tail measure is infinite near the origin".**
- This is false. ϖ((0,∞)) = U((0,∞)) = k(0+), so ϖ is finite for every Thorin member with finite U: two atoms, all of R, every finite quadrature of Proposition 7.6.
- The proof on the same page says so: "as it does whenever U is finite".
- Repair: "for a Thorin member with U((0,∞)) = k(0+) = ∞, such as the stable and Student-t members".

**10. IMPRECISE — p. 43, commentary to Theorem 5.4: "Which rational functions in general are admissible stage transfer functions is Proposition 7.4."**
- Proposition 7.4 gives a sufficient class and a pyramid construction. It does not say which rational functions are admissible stages.
- Remark 7.5 shows its first clause has no converse, and §8 lists the question as open (item 2).
- Repair: "Proposition 7.4 gives a class of them; the general question is open (§8)."

**11. IMPRECISE — p. 57, Proposition 7.2, the realization and the cost.**
- (i) The state equation w′ = (y − w)/t_{k+1} has the solutions E₊∗y + Ce^{−x/t}. The realization is the one in L¹ (or with w(−∞) = 0), and its mirror for the backward pass. For L¹ signals on the line this selection is what "exact" means, and it should be in the statement. On a finite or periodic record it is the initialization problem, which the text mentions only inside the example ("the periodic solution of each recursion").
- (ii) "In two passes" is per knot. Each record u_{k+1} needs its own forward and backward pass, so 2M passes for M knots.
- (iii) Remark 7.9 gives "2γ multiply–adds" per sample and knot. The printed section needs one multiplication for the state and one for the output, and there are 2γ sections per knot, so the count is 4γ. Proposition 7.2's O(γM) is right; the constant in the remark is not.

**12. GAP — p. 59, proof of Proposition 7.4(2).**
- The statement is true as far as I can tell. Four steps are missing.
- (i) ψ = −log R has no Gaussian coefficient, because ψ = O(log ω) for rational R. Its Lévy measure also needs to have a density. Without both, "folded Lévy profile k_R" and the substitution u = cx are not available.
- (ii) The exchange of Σ_m with the integral is Tonelli, since k_R ≥ 0.
- (iii) That the sum F is itself of the form (2.1), with Lévy density k(x)/x satisfying Lemma 2.3, follows from the finiteness of F(1). This should be said.
- (iv) "Admissible exactly when this k is nonincreasing": the "only if" is the uniqueness of the Lévy pair (finding 4), and it holds up to a null set.
- The citation "Theorem 2.5 through Lemma 7.1 of [14]" for admissibility is opaque. On p. 53 Lemma 7.1 of [14] is the differentiability of F with ωF′ = B, which is not what is needed here.

**13. GAP — p. 68 (the example, in support of Proposition 7.7): "the class of limits is closed under weak convergence".**
- This is not a clause of Proposition 7.7.
- It is true. A sequential closure in a metrizable topology is closed. It also follows directly from the converse half of Bondesson's theorem with the integer-valued limit step.
- One sentence in the proposition would carry it.

**14. PRESENTATION.**
- (i) Table 1 claims to list every cited fact, but:
  - Feller's continuity theorem, used by 7.7(1), has no row.
  - Sato Thm 17.5 (p. 52) and Bondesson's definition (3.1.1)–(3.1.2) are not among the "cited for orientation" items.
  - The uses of A3-uniqueness in §7 (findings 4 and 12) are not listed.
- (ii) Proposition 6.2 is a statement in the canonical gauge and for t > 0 only. The sentences on p. 3 and p. 70 ("every member's scale space solves an equation") omit the gauge. In a gauge χ that is only a continuous bijection, the scale space need not be differentiable in t.
- (iii) Proposition 6.4(1): v = at² is half the variance (the variance is 2at², p. 10), so "variance gauge" is a misnomer.
- (iv) p. 53: the pairing ⟨κ_φ, h⟩ suppresses its dependence on ω.
- (v) Figure 7: the labels "repeat γ times" overprint the section boxes.
- (vi) Proposition 7.7: R includes F = 0 (N ≥ 0), which (ND) excludes as a family.
- (vii) p. 57: "a ratio of two polynomials in ω² of the same degree" fails for the first stage, from t₀ = 0.

## (c) Checked and found sound

**Proposition 7.7, all three clauses.**
- The passage to the half-line is made on exponents: G_n(σ) = F_n(√(2σ)) = ∫log(1+σ/t)V_n(dt), with V_n = Σ n_i δ_{θ_i²/2}. So no subordination of the limit is assumed.
- e^{−G_n} is the transform of a finite gamma convolution with integer shapes.
- G is continuous with G(0) = 0, so Feller's theorem gives weak convergence to a proper law. Bondesson's theorem then gives membership and vague convergence.
- **Both theorems were checked at the source**: Bondesson pp. 29, 34 and 35 (page images), and Feller Vol. 2 p. 431 (text layer).
- Bondesson's theorem is printed for the measures ν_n = log(1+1/t)U_n on the compact [0,∞], with ν({∞}) = a. The paper's paraphrase ("U_n → U vaguely on (0,∞)") is his reformulation (i) on p. 35.
- His (ii) and (iii) confirm the paper's account of where the drift comes from (mass escaping to infinity) and of mass near zero (the limit would be defective, which the hypothesis excludes).
- The integer-valued step is correct: V_n(I) → V(I) for relatively compact I with V(∂I) = 0, and integers decreasing to V({x}).
- The return to the line, a = b/2 and U = twice the image of V under t ↦ √(2t), agrees with (5.1) and with Proposition 5.7(4). This includes the factor 2 that makes the masses *even*.
- Clause (2): N log(1+aω²/N) is in R and tends to aω². Clause (3) follows from uniqueness of U.
- Attempts to break it, none of which succeeded:
  - mass accumulating at zero (this gives a defective limit or a violation of (5.1));
  - dilation of the sequence (R is dilation-invariant);
  - F = 0;
  - infinitely many atoms (the Matérn pyramid of 7.4(2), with U = Σ 2δ_{q^m}, is a consistent instance of a limit outside R).

**Remark 7.5.**
- Verified: k > 0 and k′ < 0.
- Verified: the complex-rate identity and the choice of branch (1 ∓ iω²/2 has positive real part).
- Verified: F = 3log(1+ω²) + log(1+ω⁴/4), also numerically against (2.2) at four frequencies.
- Verified: order ten.
- Verified: k⁗ = 2e^{−x}(3 − 8cos x).
- Verified by hand: the transform pair e^{−|x|}(cos x + sin|x|) ↔ 2/(1+ω⁴/4).
- Its existence is consistent with Theorem 5.4, Corollary 5.5 and Proposition 7.7. The inconsistent sentences are findings 1 and 10.

**Corollary 5.5 from the implementation side.**
- It is consistent with 7.2, 7.4(1) and 7.6.
- It is also robust to the looser wording of the abstract, where the pair transfer is unspecified. At s = 0 a zero z > 0 would give k(0+) = 0 with k increasing near 0, so z = 0 and F is Matérn.
- θ and γ cannot vary with the ladder, because the stage from 0 to 1 fixes F.

**Proposition 6.2.**
- Verified: (6.1).
- Verified: the symbol computation and both bounds of min(2‖g‖_∞, ½t²v²‖g″‖_∞).
- Verified: the inversion formula with κ, where the odd part integrates to zero against the even ν̂.
- Verified: the dominating function on (t/2, 3t/2) with the (1+ω²)^{−2} decay.
- Verified: the move of A_t off u onto f by Fubini, which is needed because u(t,·) ∉ S.
- Verified: the conjugation A_t = t^{−1}D_tA_1D_t^{−1} and ∂_θ = t∂_t.
- Sato Thm 17.5 was **checked at the source** (p. 108, text layer). (17.11)–(17.12) with c = 1 give F(ω) = ∫_0^ω ψ(u)du/u, so ψ = ωF′ = B in the paper's sign. Sato's log-moment condition is the paper's ∫_1^∞ k(x)dx/x < ∞.

**Proposition 6.4.**
- Verified: clauses (1)–(3) and (5) by symbols.
- Verified: clause (4), including the identification of ϖ by its tails and the Fubini step.
- Verified: the norm bound 4γ/t on L¹ and L^∞, and the compound-Poisson reading.

**Propositions 7.1, 7.2, 7.4(1).**
- Verified: the telescoping, the transfer identity of the section, and (7.2).
- Verified: pole i/t_{k+1} in the upper half-plane ↔ causal, under the convention e^{−iωx}.
- Verified: stability for every t_{k+1} > 0, and positivity and unit mass per section.
- **7.4(2)**: uniqueness, telescoping, the profile sum, the Matérn pyramid and Figure 8's "2 per octave" all check. The O(ω²) behaviour is the analyticity of the rational R at 0, so no lemma is needed. The statement explicitly involves no subsampling.

**The sampled section (p. 64)**, read for consistency only: p(τ), the transfer (1+s²Ω²)/(1+t²Ω²), the impulse response, and the exact variance 2γt² on the lattice all check.

**Remarks 7.8 and 7.9**, apart from findings 6, 7 and 11: the Laplace-equation reading at a = ½ and Hadamard instability are classical. The O(1/γ) accuracy in the exponent is right.

## (d) Not settled

- The line paper's Lemmas 2.10, 4.2, 5.1 and 7.1 and Propositions 2.7 and 2.8 are used as paraphrased here. I have not seen that paper. The paraphrases are standard facts. Finding 12's remark on Lemma 7.1 needs that paper to settle.
- Judged from memory, not checked:
  - Lindeberg's classification of discrete scale-space kernels (p. 64). The exclusion of a zero on the positive real axis agrees with my memory of the generating function.
  - The pole counts of the Young–van Vliet and Deriche designs, and their page references.
  - [12] p. 288 (66).
  - Phillips' formula in [39] Ch. 13.
  - Halgreen's measure in Remark 5.11.
  - The printed coefficients on p. 69 were not recomputed; that is another referee's task.
- The pole–zero matching argument of findings 2(ii) and 3 is mine and is a sketch. A written Hall-type proof would settle it. Nothing in the paper depends on it except the choice of wording in finding 2.
- Whether the elliptic equation of Remark 7.8 for general a is as described is deferred by the paper to the next module. It cannot be judged from this manuscript.

---

Scratch files are in `<local path>`:
- bondesson1992generalized_printed29.png
- bondesson1992generalized_printed34.png
- bondesson1992generalized_printed35.png
- check.py
