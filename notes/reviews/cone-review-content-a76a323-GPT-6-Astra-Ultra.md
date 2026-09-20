# Part A: referee report

**Manuscript:** *Spatial scale space from hemigroup axioms: the admissible cone, its corners and their implementation*  
**Build reviewed:** `a76a323`, 73 PDF pages  
**Reviewer system:** Codex (GPT-6 family); the session's exact model variant and reasoning setting were not exposed to the reviewer.  
**Date:** 19 September 2026

Page references below are to the supplied PDF; its printed page numbers agree with the PDF page numbers. This report covers Part A only. It is based on the printed statements and proofs, inspection of the relevant figures, independent mathematical checks, selected numerical reproductions, and primary-source literature checks. The Lean development and the authors' experiment scripts were not supplied as review attachments and were not audited or executed. The full cited passages in Sato's book, Bondesson's book, and Halgreen's article were not independently accessible for a line-by-line source audit; the report distinguishes checks of their application from verification of their exact source wording. Consequently, statements about discrepancies with formal verification concern the manuscript's claims and mathematical interfaces, not an inspection of proof terms.

## 1. Overall assessment and recommendation

**Recommendation: major revision.** The organization of symmetric self-decomposable smoothing families by their profiles is useful, and substantial parts of the cone representation, subordination calculation, generator formula, and restricted real-pole closure theorem withstand examination. However, this version contains false mathematical statements, not merely presentation problems: the subcritical origin asymptotic loses a slowly varying factor; the main Matérn equivalence omits a Gaussian-part hypothesis; the realization corollary drops the integer-index restriction; and an explicit admissible rational family contradicts the proposed converse that underlies several broad implementation claims. The reported approximation errors also appear to involve an unstated Gaussian correction. Moreover, an advertised open problem has a short solution using the paper's own cited framework, and a closely related claimed literature gap was settled by Sato. These issues affect the abstract, the novelty argument, and the assurance that the headline theorem is verified as printed. The paper could become publishable after correction and a substantial tightening of its contribution; it is not ready for acceptance in its present form.

## 2. Headline claims against the results

| Claim and location | Assessment |
| --- | --- |
| The Gaussian and Cin rays uniquely generate the admissible exponent cone, pp. 1–2, 67. | Supported by Proposition 3.3, subject to the stated integrability conditions and identification of profiles almost everywhere. This is a representation of exponents; it must not be described as a probability mixture of kernels. |
| Boundedness at the origin is equivalent to the profile starting above one, pp. 1–2, 67. | The threshold is sound for a nondegenerate zero-Gaussian law, but Corollary 3.9 explicitly assumes finite positive $k(0+)$. Either put that qualification in the headlines or add the straightforward infinite-limit extension. The stronger pure-power assertion in Proposition 3.7 is false. |
| Subordination is injective and not onto, and Cin rays have no causal ancestor, pp. 1–2, 67. | Supported. The obstruction is $F'(\omega)=0$ at some positive frequency, versus strictly positive derivative for a nonzero subordinated exponent. Cin is itself strictly increasing, despite these stationary points: “increases strictly” on p. 2 is an inadequate explanation of the obstruction. |
| The dimension filtration has strict first inclusions, pp. 2, 67. | Supported by the explicit witnesses. But the claimed uncertainty about its intersection, pp. 30, 33, 68, is unnecessary: $\mathcal A_\infty=\mathcal S$ follows by applying Schoenberg to the self-decomposability remainders. |
| Four equivalent descriptions characterize the Matérn family, pp. 3, 37, 42. | False as printed: Theorem 5.4(2) also allows an independent Gaussian component. Clause (4) additionally needs to be separated as an integer-index equivalence. |
| Matérn is the exactly implementable family, pp. 1, 3, 37, 43, 67. | Overstated. Finite cascades of identical first-order sections give the integer-index Matérn subfamily. Noninteger indices are not covered, and generic “first-order section” must be replaced by the specific normalized lag section whose pole and zero follow the endpoint scales. |
| Every member is computed exactly on any finite scale ladder, pp. 1, 3, 54–56, 67. | Proposition 7.1 proves an exact operator identity. It is a numerical algorithm only once each stage has an implementable realization; the sampled recursion is a different spatial operator. The body acknowledges this, but the abstract should do so too. |
| Rational-stage families have exactly the closure in Proposition 7.7, pp. 3, 43, 55, 60, 67. | False at this breadth. Proposition 7.7 proves the closure of its explicitly defined finite real-pole, integer-weight class $\mathcal R$, not of all admissible rational-stage families. The distinction is substantive, with a counterexample below. |
| Thorin quadratures converge and rounded weights give rational increments, p. 59. | A consistent quadrature with appropriate endpoint control converges. Arbitrary positive quadratures do not automatically converge; a retained Gaussian component also prevents the full increment from being rational. |
| Student-t belongs to the relevant subclasses, pp. 3, 43, 48–49, 59–62, 67. | The probabilistic facts are credible and classical, but the checked assertions are conditional. Some later sentences fail to retain or discharge those conditions explicitly. |
| Neither of the two published recursive Gaussians is an exact admissible cascade, pp. 3, 66. | The analytic exclusion is supported for the particular continuous prototypes with the quoted coefficients. It does not, without further analysis, establish the same result for every discrete implementation or every variant sold under those design names. |
| Most results, including the headline theorem as printed, are machine-checked, pp. 1, 4–6. | The listed exceptions are helpful, but the false printed equivalence and the incorrect density interface require an audit of the correspondence between source theorem, admitted fact, formal declaration, and printed statement. |

## 3. Mathematical correctness

### 3.1 A false subcritical origin asymptotic — Proposition 3.7, pp. 19–20

The assertion

$$
\varphi_1(x)\asymp |x|^{c-1},\qquad 0<c<1,
$$

is false for a general nonincreasing profile with $k(0+)=c$. A slowly varying factor is missing. In the notation already used for the critical case, that factor is

$$
K(x)=\exp\!\left\{\int_x^1\frac{c-k(u)}u\,du\right\}.
$$

It need not be bounded. For a concrete admissible example, set

$$
k(x)=\begin{cases}
\frac12-\dfrac1{\log(1/x)},&0<x<e^{-4},\\
0,&x\ge e^{-4}.
\end{cases}
$$

This is nonnegative, nonincreasing, and satisfies both profile integrability conditions. Its limit is $c=1/2$, while $K(x)$ is a positive constant times $\log(1/x)$ near zero. Directly in the exponent one obtains

$$
F(\omega)=\tfrac12\log|\omega|-\log\log|\omega|+O(1),
\qquad |\omega|\longrightarrow\infty.
$$

Thus its characteristic function has order $|\omega|^{-1/2}\log|\omega|$, rather than order $|\omega|^{-1/2}$. This already contradicts the claimed density upper bound: convolving a density bounded above by $C|x|^{-1/2}$ near zero with a Gaussian of width $\varepsilon$ gives $O(\varepsilon^{-1/2})$ at zero, whereas the positive Fourier integral here is bounded below by a constant times $\varepsilon^{-1/2}\log(1/\varepsilon)$.

Restore the slowly varying factor, or impose a condition such as

$$
\int_0^1(c-k(u))\,\frac{du}{u}<\infty
$$

that makes it comparable to a constant. Merely replacing an exact source asymptotic by two-sided comparison does not justify deleting an unbounded factor. This directly challenges the description of the admitted Sato interface on pp. 4–5, 19–20.

The boundedness conclusion of Corollary 3.9 need not be abandoned. The corrected subcritical statement still gives unboundedness, and the critical proof uses $K\ge1$. The threshold and the asserted exact singularity order are different claims.

The unqualified logarithmic description of the entire critical regime on pp. 12 and 19 also needs correction. Replacing the constant $1/2$ in the example above by one gives $c=1$, $K(x)$ comparable to $\log(1/x)$, and the proposition's own $L(x)$ comparable to $(\log(1/|x|))^2$. The critical formula printed in Proposition 3.7 accommodates this; the surrounding prose does not. Logarithmic divergence is correct for the Cin and critical Matérn examples, not universally.

There is also a definite constant error in the Cin specialization on p. 20. For $0<\tau<1$, $k=1_{(0,\tau)}$, and $0<y<\tau$,

$$
K(y)=\exp\!\left(\int_\tau^1\frac{du}{u}\right)=\tau^{-1},
$$

not one. In fact

$$
L(x)=\tau^{-1}\log(\tau/|x|)+\tau^{-1}-1
\quad(0<|x|<\tau<1).
$$

The conclusion of logarithmic divergence survives. The two exact identities said to be machine-checked on p. 20 do not survive for arbitrary $\tau$.

### 3.2 The Matérn equivalence is missing a hypothesis — Theorem 5.4, p. 42

Take

$$
F(\omega)=a\omega^2+\gamma\log(1+\theta^2\omega^2),
\qquad a,\gamma,\theta>0.
$$

It belongs to the Thorin subclass and has the one-point Thorin measure $U=2\gamma\delta_{1/\theta}$. It therefore satisfies clause (2) exactly as written. It fails clause (1), which requires $a=0$, and clause (3), whose transform has no Gaussian factor. The converse proof silently drops $a\omega^2$ from (5.1).

Add $a=0$ to clause (2). Also state (1)–(3) for arbitrary positive $\gamma$, then separately state the equivalence with (4) when $\gamma$ is a positive integer. The explanatory paragraph partly does this, but the theorem's opening blanket equivalence remains imprecise. For $s=t$, the transfer is one and has no pole pair, so “single pole pair” should concern nontrivial stages.

### 3.3 The realization corollary is false for noninteger index — Corollary 5.5, p. 43

Every finite composition of first-order rational sections has a rational transfer function. For $\gamma=1/2$, for example, the initial Matérn stage is

$$
(1+\theta^2t^2\omega^2)^{-1/2},
$$

which is not rational. Proposition 7.2 assumes integer $\gamma$; it cannot prove the corollary for all $\gamma>0$. The same omission occurs in the abstract, introduction, section map, and conclusion.

The converse also needs a definition. A generic first-order pole-zero section is not automatically the particular section with transfer $(1+i\theta s\omega)/(1+i\theta t\omega)$. State the permitted realization, normalization, common range, and repetition count. Under that definition, the integer-index characterization is elementary and sound; moments and exponential tails are consequences, as the proof itself observes.

### 3.4 Rational stages need not be Thorin — Remark 7.5 and broad claims on pp. 3, 43, 55, 58–60, 67–68

The proposed converse is false even with uniformly bounded rational order. Consider

$$
k(x)=2e^{-x}(3+2\cos x),\qquad a=0.
$$

It is strictly positive and

$$
k'(x)=-2e^{-x}(3+2\cos x+2\sin x)<0,
$$

because $3>2\sqrt2$. The integrability requirements are immediate. Its admissible exponent is

$$
F(\omega)=3\log(1+\omega^2)+\log(1+\omega^4/4),
$$

obtained by combining the two exponential terms with rates $1+i$ and $1-i$. Consequently

$$
e^{-F(\omega)}=\frac1{(1+\omega^2)^3(1+\omega^4/4)}
$$

is rational, and every stage is the ratio of this rational function at the two endpoint dilations. Numerator and denominator degrees are uniformly bounded by ten. Admissibility follows from the positive decreasing Lévy profile, not from any assumption about signs of partial fractions.

But

$$
k^{(4)}(x)=2e^{-x}(3-8\cos x)<0
$$

for sufficiently small positive $x$. Hence $k$ is not completely monotone and this family is not Thorin. It lies outside the closure described in Proposition 7.7, despite having rational stages itself.

This refutes the proposed exclusion of oscillating terms by monotonicity on p. 59. It also makes the title of Remark 7.3 misleading: admissible rational filters are not exhausted by real-pole Matérn products. The remark's body already allows a dominant real contribution to overcome a complex pair; the counterexample shows that even monotonicity can survive.

Retain Proposition 7.7 for its defined class $\mathcal R$, but call that class finite real-pole integer-weight Thorin products throughout. Do not infer a theorem about all rational-stage families from it. The above example does not have the paper's realization by individually positive first-order real lag sections; that is precisely the distinction the prose needs to preserve.

### 3.5 The intersection of the dimension filtration is determined — pp. 30–33, 68

The equality presented as open follows from the same radial theorem already invoked in Proposition 4.9. Let $F\in\mathcal A_\infty$, and put $f(\sigma)=F(\sqrt{2\sigma})$. Proposition 4.9(3) already makes $f$ a Bernstein function with $f(0)=0$, hence the Laplace exponent of a nonnegative infinitely divisible law. For each $0<c<1$, self-decomposability in every dimension implies that

$$
\xi\longmapsto F(|\xi|)-F(c|\xi|)
$$

is a continuous negative definite function in every dimension. The infinitely divisible remainder can be seen directly from the polar criterion: subtract the contracted Lévy measure, whose radial profile difference is nonnegative, and subtract the corresponding Gaussian covariance.

Schoenberg's theorem, now applied to these remainders, says that

$$
f(\sigma)-f(c^2\sigma)
$$

is a Bernstein function vanishing at zero. Hence its negative exponential is the Laplace transform of a probability law on the half-line. Since $c^2$ ranges over all contraction factors, the nonnegative law with Laplace exponent $f$ is self-decomposable. The half-line self-decomposability criterion gives the nonincreasing delay profile required by Definition 4.1. Thus $F\in\mathcal S$.

The reverse inclusion is Proposition 4.9(2). Therefore

$$
\boxed{\mathcal A_\infty=\mathcal S.}
$$

This does not invalidate the finite-dimensional witnesses. It removes the first open question in the conclusion and requires updating Figure 4 and Remark 4.10. No approximate-identity limit in the dimension is needed.

### 3.6 Proposition 7.6 needs a convergence hypothesis and a Gaussian qualification — p. 59

Positive weights ensure admissibility, not convergence to the intended measure or exponent. “Every quadrature” needs a definition and a convergence requirement for

$$
\frac12\int\log(1+\omega^2/\theta^2)\,U_N(d\theta).
$$

Even vague convergence of positive measures is insufficient: an atom of mass $1/n$ at $e^{-n}$ vanishes vaguely on $(0,\infty)$, but contributes a quantity tending to one to this integral at every fixed $\omega\ne0$. Endpoint mass matters. A clean proof would first truncate $U$ to compact intervals, control the two tails with the integrability weights in (5.1), and then approximate the continuous integrand on each compact interval.

Further, if $a>0$, the increment contains

$$
e^{-a(t^2-s^2)\omega^2},
$$

which is not rational. Rounding the Thorin weights only makes the jump factor rational. The phrase about realizing the Gaussian separately does not make the full increment rational. Either assume $a=0$ for that assertion or explicitly separate the two factors.

### 3.7 A repairable justification in the pyramid construction — Proposition 7.4(2), pp. 57–58

The product construction and uniqueness argument are sound. However, the reason given for $\psi(\omega)=O(\omega^2)$ near zero is wrong: an arbitrary symmetric Lévy exponent need not have that behavior, as $\psi(\omega)=|\omega|$ shows. The usual quadratic-growth bound is $O(1+\omega^2)$, not a second-order zero at the origin.

Here the needed estimate follows from the additional rationality assumption: $R(0)=1$, $R$ is even and analytic near zero after removable cancellations, and it is positive there, so $-\log R(\omega)=O(\omega^2)$. Use that argument. Also say explicitly why the sum defines a Lévy measure with the required integrability; rationality supplies finite second moment and the geometric dilations make the second moments summable. If admissibility is meant to include nondegeneracy, exclude $R\equiv1$ when claiming a nontrivial family.

### 3.8 Two incorrect generator statements, although the main formula survives — pp. 51–54

Definition 6.1 says that the Schwartz class is stable under convolution with a finite measure. This is false. Convolving a nonnegative nonzero Schwartz function with a Cauchy law produces polynomial tails. The proof on pp. 52–53 correctly recognizes this and moves the generator onto the initial Schwartz signal, so the opening assertion should simply be removed.

The final explanation of Proposition 6.4 on p. 54 treats a general Thorin member's tail measure $\varpi$ as necessarily infinite near zero. It need not be: by Tonelli,

$$
\varpi((0,\infty))=U((0,\infty))=k(0+).
$$

For $a=0$, every finite Thorin measure, including two-atom and finite non-atomic measures, gives a bounded generator, with norm at most $2U((0,\infty))/t$ on $L^1$ or $L^\infty$. Replace the universal assertion by “may be infinite.” Boundedness of the generator does not characterize Matérn.

The generator formula, its factors of $t$, the dilation conjugation, and the individual corner calculations otherwise agree with the Fourier symbols. To complete the analytic justification on p. 53, insert the $L^1$ analogue of the displayed bounded-function estimate:

$$
\|A_tf\|_1\le 2at\|f''\|_1+
\frac1t\int\min\{2\|f\|_1,\tfrac12t^2v^2\|f''\|_1\}\,\varpi(dv).
$$

This explicitly supplies the integrability used when Fourier inversion is applied to $A_tf$.

### 3.9 “Type G” is broader than Definition 4.11 — pp. 32–34

Definition 4.11 permits only delay Lévy measures of the form $k_I(u)du/u$. General infinitely divisible mixing laws can have atomic or singular Lévy measures. Thus the set called $\mathcal G$ there is not, by that definition alone, all type G exponents. For a simple unrestricted example, a compound-Poisson mixing time has exponent $1-e^{-\sigma}$, with an atomic Lévy measure, and its Gaussian variance mixture is type G.

This defect remains even if attention is restricted to admissible spatial exponents. For example, $F(\omega)=|\omega|+1-e^{-\omega^2/2}$ has folded profile

$$
k(x)=\frac2{\pi x}+\sqrt{\frac2\pi}\,x e^{-x^2/2}.
$$

It is positive and strictly decreasing: for $x\ge1$ both derivative contributions are nonpositive, and for $0<x<1$, multiply the derivative by $x^2$ and use $x^2(1-x^2)e^{-x^2/2}\le1/4$. Its uniquely determined mixing exponent is $\sqrt{2\sigma}+1-e^{-\sigma}$, whose Lévy measure has an atom at one. It is therefore admissible and type G but excluded by Definition 4.11.

Restrict the terminology to the specified absolutely continuous subclass, or define general type G exponents using an arbitrary subordinator Lévy measure and then specialize to the profiles used in Lemma 4.12. The witness calculations do not depend on treating the subclass as exhaustive.

### 3.10 The claim that Student-t cannot be stepped in scale is wrong — Remark 7.8, pp. 61–62

Ill-posedness of an elliptic Cauchy problem does not imply that the selected scale-space family cannot be evaluated successively in scale. Proposition 7.1 itself supplies such a cascade for every admissible member. Most plainly, the Cauchy/Poisson member of Student-t has

$$
\widehat\mu_{s,t}(\omega)=e^{-(t-s)|\omega|},
$$

and a well-defined forward evolution generated by $-|D|$. One can step exactly by this multiplier, or use suitable numerical methods for that evolution.

Distinguish an unstable Cauchy formulation of the second-order elliptic equation from the well-posed nonlocal evolution selecting its decaying solution. The absence of the particular real-pole realization does not imply that a method must “cost its kernel,” nor does it exclude Fourier methods or other approximations.

### 3.11 Results and proof steps that do withstand the checks

**Cone coordinates and delay equation, pp. 12–18.** The layer-cake representation and the integrability weight in Proposition 3.3 are appropriate; uniqueness through the Lévy pair and the Stieltjes tail measure supports the extreme-ray claim. “Choquet structure” is justified here as a concrete unique representation over rays, without relying on an unstated compact-base Choquet theorem. Lemma 3.5's distributional/weak calculation is consistent with the Cin Fourier transform. There is a local factor-two typo on p. 18: delete “twice” from the sentence identifying the transform of the left side of (3.2), which already contains the factor two. The propagation narrative in Remark 3.8 is correctly labeled unproved; keep it separate from the lemma.

**Bridge and its strictness, pp. 22–29.** The Gaussian variance convention, folded factor two, and relation between causal and spatial scales are consistent. Injectivity follows from the surjectivity of $\omega^2/2$ onto the nonnegative Laplace variable. For a nonzero causal exponent, the positive derivative rules out the stationary points arising from lattice-supported $\varpi$. The compact-support obstruction through a Gaussian mixture is also valid. These statements do not require the false rational-family converse.

**Dimension filtration and witnesses, pp. 30–36.** Restriction from dimension $d+1$ to $d$, the polar Lévy criterion, and Schoenberg's theorem are applied in suitable settings. In (4.5),

$$
|S^{d-1}|r^df_d(r)=\frac2{\Gamma(d/2)}
\int_0^\infty v^{d/2-1}e^{-v}k_I(r^2/(2v))\,dv
$$

has the correct constant, and its monotonicity follows pointwise under the positive integral. In Lemma 4.12, the differentiation leading to (4.8) and the bounds using $6+4\sqrt2$, $c=4$, and $c=8$ check out. The explicit failures in dimensions two and three occur with strict inequalities; no numerical plot is being substituted for a proof. The identification of a hypothetical causal ancestor by Laplace-transform uniqueness is also justified. The requested changes concern the stronger intersection result and the literature/terminology, not these witness constants.

**Moments and tails, pp. 38–39.** The large-jump moment criterion, the folded factor in the variance, and the second-difference/Fatou argument are consistent. The exponential-integrability threshold at bounded jump radius is the appropriate content of the cited tail result, for positive scale and a nonzero jump part. Its informal paraphrase as a “tail of order” is too strong if read as a pointwise density asymptotic or a constant-factor comparison of tail probabilities; state exactly which logarithmic or integrability notion is intended. A nonzero completely monotone profile has unbounded support; the zero profile must be excluded from that sentence, because the Thorin class also includes Gaussians. Do not suggest that Gaussian exclusion applies to arbitrary non-infinitely-divisible smoothing kernels.

**Thorin representation and bridge, pp. 43–47.** The factor $1/2$ in the symmetric exponent and the mapping $\theta\mapsto\theta^2/2$ to causal rates are consistent. The integrability conditions, Tonelli exchanges, and uniqueness of the mixing measure justify Proposition 5.7. This proposition explicitly allows a Gaussian component, which is why Theorem 5.4(2) needs correction.

**Student-t, pp. 48–49.** The inverse-gamma Gaussian mixture, Student density, Bessel transform, and moment cutoff are mutually consistent. The conditional formulation of Proposition 5.10(3) is legitimate. Core later statements such as Proposition 7.7's Student-t application on p. 60 explicitly acknowledge the condition. However, the named generator on p. 53 and implementation discussion on pp. 59–62 use the cited representation/density; “Nothing in the paper depends on this remark” on p. 49 is misleading unless narrowed to dependence of formal declarations. Mathematical use of a cited theorem is acceptable; it must be recorded as such.

**Restricted closure theorem, Proposition 7.7, pp. 60–61.** The proof's central steps are sound for the defined $\mathcal R$. Weak convergence on the line gives convergence of the strictly positive characteristic functions and hence of $F_n$. Setting $G_n(\sigma)=F_n(\sqrt{2\sigma})$ produces gamma-convolution Laplace transforms; continuity at zero permits the half-line continuity theorem. Bondesson closure then supplies a GGC limit, its drift, and vague convergence of Thorin measures. On relatively compact intervals whose endpoints are not atoms, vague convergence gives convergence of integer masses. Shrinking such intervals forces every sufficiently small neighborhood either to contain a single integer atom or to have zero measure; local finiteness rules out a diffuse remainder. The argument is valid.

The passage back has the right constants: $a=b/2$ and $U$ is twice the pushforward of the causal Thorin measure under $t\mapsto\sqrt{2t}$. Mass escaping to high causal rates can contribute drift, hence a Gaussian part, rather than a finite-rate Thorin atom. It can also make no contribution; not every escaped atom produces positive drift. Positive integer atoms cannot persistently escape to rate zero in a convergent probability sequence here: at a fixed positive Laplace argument their contribution would force the exponent to diverge. Finally, the construction $N\log(1+a\omega^2/N)$ correctly restores any Gaussian part in the converse. These checks support the theorem's narrow statement, not its broader title and surrounding claims.

**Stable family, pp. 3, 38, 50, 53.** The profile, Thorin density, moment cutoff, and endpoint Gaussian in Proposition 5.12 are consistent. Stationary increments occur in the scale coordinate $v=t^\alpha$, not in the canonical length coordinate $t$ unless $\alpha=1$; carry this qualification into the introductory semigroup description. Figure 5's power-tail caption must exclude its Gaussian endpoint $\alpha=2$.

**Elementary cascade statements, pp. 55–58.** Proposition 7.1 is a correct induction on the hemigroup identity. Proposition 7.2's continuous first-order realization and positive mixture formula are correct for integer index; allow $r=0$ for the initial stage. Proposition 7.4(1) is a valid sufficient construction, not an exhaustive classification.

## 4. Numerical example, recursive Gaussian filters, and reproducibility

### 4.1 What the pole calculation establishes

For $\Re\theta>0$, the identity

$$
2\int_0^\infty(1-\cos\omega x)e^{-\theta x}\,\frac{dx}{x}
=\log(1+\omega^2/\theta^2)
$$

extends from positive real rates by analytic continuation, with the logarithm chosen continuously from $\omega=0$. Conjugate rates combine to a real expression. Poles contribute positive multiplicities and zeros negative multiplicities to the resulting exponential sum. A complete criterion needs normalization at zero, absence of real-frequency zeros, and the Lévy integrability requirements as well as the signs. Infinite divisibility requires the resulting Lévy measure to be nonnegative; admissibility in this paper further requires the folded profile to be nonincreasing. These two tests must not be conflated.

For Young–van Vliet's quoted continuous prototype, p. 66 gives

$$
k(x)=2e^{-1.1668x}+4e^{-1.10783x}\cos(1.40586x).
$$

The oscillatory term decays more slowly. At sufficiently large points where the cosine is minus one, the profile is negative. This is an analytic obstruction to infinite divisibility, not a conclusion drawn only from a finite grid. Independent evaluation also reproduces the first negative interval near $1.46\sigma$, the minimum near $1.97\sigma$, and the negative increment lobe to the stated precision. The signed representation cannot be replaced by a different positive Lévy measure, by Lévy–Khintchine uniqueness; that last step should be stated.

For Deriche's quoted fourth-order continuous approximation, an even kernel $h$ with the stated regularity has

$$
\widehat h(\omega)=-2h'(0+)/\omega^2+O(\omega^{-4}).
$$

Using the printed coefficients gives $h'(0+)=0.0176693$ before normalization and leading Fourier coefficient $-0.0353386$. The fitted function has total integral approximately $2.50705278$; after unit-mass normalization the coefficient becomes approximately $-0.01409567$. Keep the normalization explicit: the manuscript's $-0.035$ refers to the unnormalized fitted function. Positive value at zero and negative values at large frequency force a real zero. Direct evaluation also reproduces roots approximately $4.2082,5.0763,9.8149$, close to the paper's reported $4.21,5.08,9.82$; state coefficient precision before comparing the last digit. The nonvanishing property of infinitely divisible characteristic functions therefore gives the claimed exclusion. For the ratio taking scale $\sigma$ to $2\sigma$, demonstrate that at least one denominator zero is not cancelled; the reported root locations make this easy. A real pole precludes a bounded convolution operator of the required kind.

The 2,000 coefficient perturbations are a sensitivity experiment, not proof over the whole rounding box. A conservative interval calculation using half a unit of each displayed coefficient's last digit bounds the slope between $0.014778875$ and $0.020559275$, proving persistence of at least one zero throughout that box; it does not certify three zeros. Also, these are continuous prototype calculations in the variable $\omega$. Published sampled recursions have transfer functions in $z$; periodization and discretization can change the zero and Lévy-profile analysis. Name exactly what has been excluded. The source designs are [Young and van Vliet, 1995](https://repository.tudelft.nl/record/uuid:6fea1bc9-de9c-450f-8e34-a33c1129589a) and [Deriche, INRIA RR-1893](https://inria.hal.science/inria-00074778); the latter source link was access-blocked during this review, so the calculation checks the supplied coefficients rather than independently certifying their transcription from the original report.

### 4.2 The rounded-node errors do not match the stated finite product — pp. 65–66, Figure 9

For the stated nodes $\theta_i=\pi(i-1/2)$, define

$$
F_N(\omega)=\sum_{i=1}^N\log(1+\omega^2/\theta_i^2).
$$

The infinite product does give $e^{-F_\infty}=1/\cosh\omega$, with density $\tfrac12\operatorname{sech}(\pi x/2)$. But independent Fourier inversion of the finite products does not reproduce the printed errors:

| $N$ | Finite product: approximate $L^1$ error to the sech density | After adding $\omega^2/(\pi^2N)$ to $F_N$ | Reported, p. 66 |
| --- | ---: | ---: | ---: |
| 4 | $4.20\times10^{-2}$ | $4.70\times10^{-4}$ | $4.7\times10^{-4}$ |
| 256 | $6.22\times10^{-4}$ | $1.89\times10^{-9}$ | $1.9\times10^{-9}$ |

These checks used double-precision Fourier inversion on $2^{19}$ spatial points, spacing $0.002$, period $1048.576$, angular frequencies $2\pi\,\mathrm{fftfreq}$, and the spacing-weighted sum of absolute density differences. The rapidly decaying sech comparisons have negligible period tails at this length; the large discrepancies between the first and last columns are not rounding effects. The agreement of the middle and last columns strongly indicates an unstated Gaussian tail compensation $a_N=1/(\pi^2N)$. That is an inference from independently reproduced numbers, not a claim to have inspected the authors' script.

Such compensation is mathematically reasonable, but the compensated finite member no longer has a fully rational transfer or a realization solely by the finite lag cascade. The 24-range run's quoted variance, approximately $0.9916t^2$, is consistent with the uncompensated finite product. The report therefore appears to use two different approximants under insufficiently distinguished descriptions. Print both definitions, identify which curve uses which, and recompute or relabel the comparison. This is a required correction, not cosmetic exposition.

### 4.3 What the remaining numbers do and do not show

The ladder-refinement and direct-versus-cascade comparisons on p. 65 are sensible implementation checks, and roundoff-sized differences are consistent with the exact telescoping algebra. Euler's approximately halved error is likewise consistent with first-order stepping error. These numerical observations illustrate the theorem; they do not establish exactness independently of it.

The observed range and mean preservation are useful checks on the implementation. Positivity and unit mass for all signals come from the positive section coefficients and their sum, not from inspecting one signal. Similarly, a few fitted tail slopes and three frequency cutoffs illustrate the selected families; they do not prove an asymptotic or repair the missing slowly varying factor in Proposition 3.7. All the displayed threshold examples have especially well-behaved profiles near zero and fail to probe that issue.

The finite search giving distances $0.200$ and $0.027$ on p. 66 supplies **upper bounds on the best achievable distances**, namely distances achieved by candidates. It gives no positive lower bound for the full class, no certificate of a global optimum, and no proof that three nodes suffice. The restricted closure theorem proves a qualitative obstruction to convergence to the excluded target, but it does not identify the numerical separation. The claim in the conclusion that the run finds the class “at a fixed distance” should be narrowed to the tested approximation scheme and tested optimization family. State the domain and norm used for every numerical distance.

The matched-variance Gaussian approximation errors are consistent with the Matérn central-value asymptotic $3/(8\gamma)$, explaining the quoted $0.38/\gamma$. The rounded-coefficient comparisons support an accuracy-versus-realization tradeoff for these examples, not a global optimality theorem for either design.

### 4.4 The sampled section is algebraically clear but the experiment is not fully reproducible — p. 62

The relation $p/(1-p)^2=\tau^2$, the pole-zero section, and the substitution $\Omega^2=4\sin^2(\omega/2)$ are correct. They specify a positive normalized lattice filter whose scale factors telescope. The exact variance $2\gamma t^2$ is a statement on the infinite lattice. After periodization onto 4,096 sites, ordinary centered-coordinate variance is affected by wrapping; very small errors at the chosen scales are possible, but the unqualified exact statement should not be transferred to the finite circle.

Likewise, $F(c)=1$ gives transfer $1/e$ at $\omega=1/s$ for the continuum member, not exactly for the sampled one. For $\gamma=1,s=1$, the sampled transfer is about $0.38763$, versus $e^{-1}\approx0.36788$. Describe the bandwidth matching as continuum matching or use a lattice-specific calibration. The measured continuum discrepancy reflects the spatial operator discretization, not just sampling the input signal.

For independent reproduction, provide the signal formula and noise seed; the exact knot sequence including the first stage from zero; periodic state initialization or the exact circular solver; normalization and transforms used for Gaussian and Poisson comparisons; quadrature endpoints, weights, and Gaussian compensation; tail-fit intervals; the integration domain and mesh for $L^1$ distances; and the optimizer, bounds, starts, and stopping criteria. Naming two scripts without a pinned, accessible artifact containing them is insufficient. A compact supplement can carry these details. Figures 9 and 10 are useful and should remain, with clarified captions and an explicit difference-image color scale.

## 5. The trust base

The manuscript makes a serious effort to distinguish admitted classical facts, formally checked deductions, and prose-only results. The separate treatment of Proposition 4.9, Lemma 4.12, Section 7, and Corollary 5.5 is welcome. The integer-point-measure closure argument and witness inequalities must indeed be assessed as ordinary proofs; I did so above.

Nevertheless, the account is not reliable enough in its present wording. The decisive examples are:

1. The equivalence involving Theorem 5.4(2), p. 42, is false, while pp. 4 and 6 describe its assembled declaration as verifying the printed headline theorem.
2. Proposition 3.7, p. 20, drops a generally unbounded slowly varying factor, while pp. 5 and 19 say the source regimes are admitted at the source's own mathematical content.
3. The exact Cin identities on p. 20 fail for $\tau<1$, despite the adjacent claim that both are checked using only the logical foundations.
4. Definition 6.1, p. 51, contains a false preservation assertion, while the actual proof correctly works around its failure; the blanket statement that every other numbered statement is checked needs more precise granularity.

None of this implies a failure of Lean. A verified declaration can have stronger hypotheses, weaker conclusions, or different definitions than the printed sentence. An admitted false interface can also invalidate the mathematical interpretation of downstream checked results. A dependency list is evidence about formal assumptions; it is not evidence that those assumptions correctly transcribe a cited theorem.

The revised submission needs a statement-to-declaration table showing complete hypotheses for these results, together with corrected source-interface statements and an updated dependency audit. Table 1 should distinguish mathematical use of an external result from direct use of an admitted declaration: the Student-t density used in later applications depends on Remark 5.11 even if the corresponding formal theorem takes the representation as an argument. Likewise, the p. 5 claim that the Matérn closed form and tail are used by no proof conflicts with Corollary 5.5's explicit use of Proposition 5.3 on p. 43. List the Laplace continuity theorem alongside Bondesson for Proposition 7.7, and make the polar criterion, multidimensional Lévy representation, and inherited density regularity/unimodality dependencies readily visible rather than relying on the reader to combine the table caption and surrounding prose.

Finally, give an explicit permanent URL, revision, and executable verification instructions for **this** paper's export. Page 6 refers to an accompanying repository, while the identifiable repository in reference [13] is the companion line paper. A review of the PDF cannot establish that the promised export reproduces the claims.

## 6. Novelty and relation to prior work

**The opening Gaussian claim needs correction (p. 1).** The listed properties of linearity, covariance, positivity, and semigroup composition do not by themselves select the Gaussian: positive stable semigroups supply immediate counterexamples. State the additional locality or non-enhancement assumption where the Gaussian conclusion is first made. Also describe Pauwels et al. as the broader scale-invariant recursive classification and identify the positivity restriction under which the stable range $0<\alpha\le2$ is recovered; their paper also discusses sign-changing kernels beyond that range. [Pauwels et al., 1995](https://dev.ipol.im/~reyotero/bib/bib_all/1995_Pauwels_VanGool_extended_scale_space_PAMI.pdf).

**The Bessel/variance-gamma identification is already acknowledged, but the contrast is too broad (pp. 2–4, 37, 40–43).** Burgeth, Didas, and Weickert explicitly give the Bessel convolution semigroup in the order parameter and also discuss varying the range at fixed order. The manuscript may distinguish its exact range-increment hemigroup from that earlier treatment; it should not imply that range-based smoothing was absent. Statements that no semigroup can contain these kernels are false without the qualification of dilation covariance along the fixed-shape range orbit. The order-parameter semigroup is itself a counterexample. [The Bessel Scale-Space, §§2.2, 2.4 and 3](https://www.mia.uni-saarland.de/Publications/burgeth-dsscv05.pdf).

**The probability literature contains a directly relevant missing result (pp. 32–34).** Sato's *Subordination and selfdecomposability*, Theorem 1.2, constructs a self-decomposable type G law whose unique nonnegative mixing law is not self-decomposable. Lemma 3.1 there also identifies the mixing law from the Gaussian mixture. Thus the strict distinction motivating this part of Lemma 4.12 and the question described as unsettled in the held literature are not new phenomena. The explicit profile and dimension-crossing constants may still be useful, but position them as an explicit refinement/example. [Sato, Theorem 1.2 and §3](https://webdoc.gwdg.de/ebook/e/2002/maphysto/publications/mps-rr/2000/40.pdf).

**Related non-Gaussian imaging work is missing.** The relativistic scale spaces of Burgeth, Didas, and Weickert use the exponent $\sqrt{|\omega|^2+m^2}-m$ and provide an established imaging example connected to infinitely divisible kernels with a non-Gaussian, exponentially decaying regime. A short comparison would prevent a mistaken impression that finite-moment non-Gaussian smoothing enters imaging only through the present hemigroup construction. Their scale covariance differs from the one required here, which should be the comparison's point. [Relativistic Scale-Spaces](https://www.mia.uni-saarland.de/burgeth/pub/burgeth-scsp05.pdf).

The citations to Duits et al., Felsberg–Sommer, and Pedersen et al. are appropriate for the stable/Poisson and image-statistical background. The Matérn, variance-gamma, GGC, Halgreen, and SPDE connections are also substantially appropriate. However, distinguish a Matérn covariance function from an integrable Bessel/variance-gamma kernel: on the line the covariance interpretation requires $\gamma>1/2$, whereas the probability density exists for every $\gamma>0$. The narrower condition is acknowledged on pp. 21 and 41 but lost in some blanket descriptions on pp. 2, 37 and 43. Likewise, identify whether the SPDE operator is being used as a smoothing Green operator or as a stochastic field construction; their exponents should not be conflated.

The recursive-filter discussion should give Lindeberg's discrete theory a more substantive comparison. Its structure-preservation requirements and spatial lattice are different from this paper's positivity and continuum dilation assumptions; satisfying the present hemigroup conditions does not establish the stronger no-new-extrema property. The sampled resolvent construction should be situated relative to discrete diffusion and classical cascaded recursive smoothing. [Lindeberg, Scale-Space for Discrete Signals](https://people.kth.se/~tony/papers/cvap66.pdf).

The pyramid analogy with Burt–Adelson is appropriately qualified in Figure 8, but the proposition addresses convolution ladders and their continuum interpolation, not decimation, reconstruction, or coding performance. Preserve that boundary.

The generator discussion also needs the background-driving Lévy-process connection. The symbol $B(\omega)=\omega F'(\omega)$ and its relation to dilation are classical within the random-integral and self-similar-additive-process representations of self-decomposable laws. Explain what Section 6 adds in signal-operator form beyond that background. A useful primary reference is [Jeanblanc, Pitman and Yor, *Self-similar processes with independent increments associated with Lévy and Bessel processes*](https://math.maths.univ-evry.fr/jeanblanc/pubs/jpy_self.pdf).

The defensible novelty is an organized consequence of the particular measurement axioms, the concrete profile geometry and comparisons, explicit examples, and a carefully delimited implementation classification. It is not the discovery of Matérn smoothing, variance-gamma kernels, subordination preserving self-decomposability, or general first-order recursive smoothing. The standard self-decomposable/self-similar-additive-process connection is already cited to Sato and should remain background. With the Matérn characterization reduced to the correctly specified integer-section realization, its novelty should be assessed at that narrower level.

## 7. Exposition, self-containment, and a shorter journal version

Section 2 gives enough definitions to follow most of Sections 3–6 without the line paper. It does not make the article wholly independent: the representation theorem, regularity theorem, symbol identity, growth estimate, and continuity theorem remain imported results. That is acceptable if their exact statements and hypotheses are available locally. The near-zero growth mis-citation in Proposition 7.4 shows why precise restatement matters.

The most load-bearing forward reference is Corollary 5.5, p. 43, which announces an implementation characterization before defining its permitted sections; move it after Proposition 7.2 or define the realization fully before stating it. Theorem 5.4's Thorin formulation also points forward to Proposition 5.7; introduce the representation before using it in the main characterization.

Section 4.7, pp. 36–37, is not self-contained. Its memory line, signaling form, embodied jet, and locality theorem belong to the causal article and a future module. Remark 7.8 then uses the future locality discussion to make an incorrect computational impossibility claim. Remove most of this material or replace it by one short, explicitly prospective paragraph.

The journal version should lose repeated announcements rather than essential arguments. In particular:

- Compress the introduction's result itinerary, the section-opening itineraries, and the conclusion's repeated itinerary (pp. 2–4, 11–12, 21–22, 37, 54–55, 67).
- Move the development-specific proof-history discussion, including the five-item account on p. 68, to a formalization appendix or companion document; retain the corrections to mathematical statements in the main text.
- Shorten the folding discussion and its routine proof on p. 19 while keeping the factor-two convention prominent; retain the corrected density theorem with its hypotheses.
- Remove or greatly shorten Section 4.7 and the unsupported cost/impossibility rhetoric in Remarks 7.8–7.9.
- Keep Figures 9–10, which test substantive implementation distinctions; consolidate some of the repeated schematic cone/cascade diagrams and their long captions.
- Reduce the process narrative on pp. 69–70 to a concise contribution, AI-use, and responsibility statement, with the fuller record in a supplement.
- Delete acquisition notes, sandbox-search history, and OCR instructions from references [13], [32], [41], and [42] on pp. 71–73; these are internal records, not bibliographic content.

The manuscript can lose substantial length without sacrificing a proof. It should not retain 73 pages merely to repeat an already stated distinction in the language of “catalogues,” “corners,” and “machines.” Use conventional terminology where it removes ambiguity, especially “convolution product” versus “mixture,” and “exact operator composition” versus “numerical realization.”

## 8. Required changes and suggestions

### Required changes for acceptance

1. **Correct Proposition 3.7 and its trust interface (pp. 4–5, 19–21):** restore the slowly varying factor or add a hypothesis that bounds it and qualify the critical-regime logarithmic prose, because the printed pure-power comparison and unqualified logarithmic description are false.
2. **Correct the Cin specialization (p. 20):** retain the dependence on $\tau$ in $K$ and $L$, because the claimed exact identities fail for $\tau<1$.
3. **Repair Theorem 5.4 (p. 42):** add zero Gaussian coefficient to the one-atom clause and separate the integer-index rational statement, because the current equivalence has an explicit counterexample.
4. **Restrict and define the realization characterization (pp. 1, 3, 37, 43, 56, 67):** specify positive integer index and the permitted lag sections, because a finite first-order cascade cannot realize a noninteger Matérn transform.
5. **Correct the claimed scope of rational-stage results (pp. 3, 43, 55, 57–61, 67–68):** withdraw Remark 7.5's proposed converse and restrict Proposition 7.7's surrounding claims to its defined real-pole class, because admissible non-Thorin rational-stage families exist.
6. **State a valid approximation theorem (p. 59):** define consistent quadratures with endpoint control and distinguish a rational jump factor from a retained Gaussian factor, because positivity alone proves neither convergence nor rationality of the full stage.
7. **Reconcile the rounded-node numerical comparison (pp. 63, 65–66):** disclose any Gaussian tail compensation and identify each finite approximant, because the reported errors do not match the stated uncompensated product.
8. **Make numerical claims reproducible and appropriately scoped (pp. 62–67):** provide the pinned experiment artifact and the missing signal, boundary, quadrature, norm, and optimization details, because one signal and a finite search cannot establish universal positivity, tail laws, or optimal separation distances.
9. **Correct the Student-t marching claim (pp. 61–62):** distinguish elliptic Cauchy instability from the valid nonlocal forward cascade, because the Poisson member directly contradicts the claimed impossibility.
10. **Correct the generator preliminaries (pp. 51–54):** remove Schwartz preservation under arbitrary finite convolution and the assertion that every general Thorin tail measure is infinite, because both statements have elementary counterexamples.
11. **Resolve the filtration intersection and terminology (pp. 30–34, 68):** include the remainder-based proof of $\mathcal A_\infty=\mathcal S$ and distinguish general type G mixing measures from the absolutely continuous subclass, because the current open-question and class descriptions are inaccurate.
12. **Repair proof justifications and source qualifications (pp. 38–39, 48–49, 53, 58–61):** use rational analyticity for the pyramid estimate, state the precise tail notion, and track the Student-t representation hypothesis, because the current exposition sometimes substitutes a stronger claim for the available result.
13. **Audit printed statements against formal declarations and admitted facts (pp. 4–6, 19–20, 42, 51):** supply corrected full hypotheses and a reproducible export, because the assertion that the headline theorem is verified as printed is contradicted by the mathematics in this version.
14. **Revise the historical and novelty claims (pp. 1–4, 32–34, 37, 40–43):** correct Gaussian uniqueness and the unrestricted semigroup language, add Sato's directly relevant result, and acknowledge earlier range-based Bessel and relativistic smoothing, because the present contrasts overstate the contribution.
15. **Revise the abstract and conclusion after these corrections (pp. 1–3, 67–69):** propagate the integer, Gaussian-part, realization-class, conditional, and sampling qualifications, because several current headlines are stronger than their valid supporting statements.

### Suggestions that would improve the paper

1. **Present a compact theorem map (pp. 2–6):** distinguish new consequences, classical inputs, and implementation corollaries in one place so the novelty is visible without several repeated itineraries.
2. **Move Corollary 5.5 after its realization theorem (pp. 42–43, 56):** this would remove a load-bearing forward reference and make its exact engineering hypotheses natural.
3. **Give the dimension witnesses a concise table (pp. 34–36):** recording which $c,d$ pairs have decreasing profiles would make the explicit constants easier to verify.
4. **Add a slowly varying origin example (pp. 20, 65):** it would test the corrected general density statement rather than only the special cases with pure-power or logarithmic behavior.
5. **Add a signed Deriche transfer inset and label the prototype domain (pp. 64, 66):** the current modulus plot conceals the sign information on which the exclusion argument relies.
6. **State peak live storage separately from total per-scale work (pp. 56, 62):** stages can be processed sequentially, so aggregate state counts need not describe the memory of every implementation.
7. **Use probability terminology consistently (pp. 43–47, 59):** superposition of exponents corresponds to convolution of independent components, whereas “mixture” usually means a different operation on laws.
8. **Carry out the structural cuts and bibliography cleanup above (pp. 2–6, 36–37, 54–55, 67–73):** they would shorten the journal article while retaining the actual mathematical evidence.
