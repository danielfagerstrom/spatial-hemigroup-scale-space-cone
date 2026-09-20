# Citation audit -- blueprint/AXIOMS.md, spatial-hemigroup-scale-space

Librarian pass, 2026-09-19. Every anchor below was opened from the held copy (page image
where the text layer is unreliable) and transcribed independently of the ledger's own
paraphrase, then compared against the ledger's "Statement as used" and, where an axiom
exists, against Formalization/SpatialLine/Interfaces.lean and
Formalization/SpatialLine/TwoSidedDefs.lean. Page images and any intermediate text are in
this same scratchpad directory, named <citekey>_printed<N>.png; none were written into the
repository. Priority order followed the task: the fourteen admitted-axiom entries first, then
the rest. Entries flagged in the task as already transcribed in the last three days (A7's
2026-09-19 bullet, A10, A23, A24) were confirmed present in the ledger's own text rather than
re-imaged.

Overall finding: of 24 entries, 22 are MATCH (several with an already-documented, honest
NARROWER-OK reading), one is a disclosed, currently-harmless DIFFERENCE (A20's uniqueness
citation), and none reproduces A10's original defect -- no entry's "statement as used" claims
*more* than its cited pages state. The closest calls (A19 clause (c), A9/A8's origin
behaviour, A10, A21/A22) are all narrowings the ledger already got right.

---

## A1 -- Bochner: continuous positive definite with value 1 at 0 iff a probability transform

**Cite:** sato1999levy -- Prop. 2.5, pp. 8-9 (as in the ledger); feller2009introduction Vol. 2,
Section XIX.2, p. 622.

**Source, verbatim (Sato, p. 8-9).**
> (i) (Bochner's theorem) We have that mu-hat(0) = 1 and |mu-hat(z)| <= 1, and mu-hat(z) is
> uniformly continuous and nonnegative-definite... Conversely, if a complex-valued function
> phi(z) on R^d with phi(0) = 1 is continuous at z = 0 and nonnegative-definite, then phi(z)
> is the characteristic function of a distribution on R^d.
> (ii) If mu-hat_1(z) = mu-hat_2(z) for z in R^d, then mu_1 = mu_2.
> (v) Suppose that mu-tilde is the dual of mu and mu-sharp is the symmetrization of mu. Then
> mu-tilde-hat(z) = mu-hat(-z) = conj(mu-hat(z)) and (mu-sharp)^(z) = |mu-hat(z)|^2.

**Source, verbatim (Feller, p. 622).**
> Theorem. (Bochner.) A continuous function omega is the characteristic function of a
> probability distribution iff it is positive definite and omega(0) = 1.

**Ledger, statement as used:** "A function phi : R -> C is the Fourier transform of a
probability measure on R iff it is continuous, positive definite and phi(0) = 1; it is the
transform of a symmetric probability measure iff moreover it is real, equivalently even."

**Lean:** fourier_toolbox_bochner_symm admits only the forward implication -- continuous,
positive definite, phi 0 = 1, therefore the cosine transform of a symmetric probability
measure -- with continuity asked everywhere (source: only at 0) and of a real phi (source:
allows complex). The reverse direction is proved, not admitted.

**Verdict: MATCH** (Lean: NARROWER-OK, safe direction). The (i)/(ii)/(v) cited pages are
exactly as paraphrased; the symmetric rider correctly runs through (v)'s conjugate identity
plus (ii)'s uniqueness. The admitted axiom asks strictly more of its hypotheses than the
source requires and delivers only one direction of the source's equivalence.

**Note:** none.

---

## A2 -- Schoenberg: the kernel form of negative definiteness equals the exponential form

**Cite:** schilling2012bernstein -- Def. 4.3 and Prop. 4.4, p. 36. Corroboration:
berg1975potential Thm. 7.8, p. 41 (not re-read this pass; already flagged in the ledger as not
independently checked); jacob2001pseudo Def./Thm. 3.6.5-3.6.11.

**Source, verbatim (Schilling-Song-Vondracek, p. 36).**
> Definition 4.3. A function f : S -> C is negative definite if it is hermitian ... and if
> sum (f(s_j) + conj(f(s_k)) - f(s_j+s_k*)) c_j c-bar_k >= 0 holds for all n in N, all
> s_1,...,s_n in S and all c_1,...,c_n in C.
> Proposition 4.4 (Schoenberg). For a function f : S -> C the following assertions are
> equivalent. (i) f is negative definite. (ii) f(0) >= 0, f(s*) = conj(f(s)) and -f is
> conditionally positive definite ... (iii) f(0) >= 0 and s -> e^(-tf(s)) is positive definite
> for all t > 0.

**Ledger, statement as used:** "For continuous even psi >= 0 with psi(0) = 0: psi in NDs (that
is, e^(-tau*psi) positive definite for every tau > 0) iff psi is negative definite in the
kernel sense."

**Lean:** none (not stated).

**Verdict: MATCH.** Prop. 4.4(i) iff (iii) is exactly the cited equivalence, specialised to
S = R with f = psi real, even, psi(0) = 0.

**Note:** the Berg-Forst corroboration (p. 41) was not opened this pass; the primary anchor
(Schilling, p. 36) fully supports the statement on its own.

---

## A3 -- The symmetric Levy-Khintchine representation, with a unique pair

**Cite:** sato1999levy -- Thm. 8.1(i)-(iii), pp. 37-38.

**Source, verbatim (p. 37-38).**
> Theorem 8.1. (i) If mu is an infinitely divisible distribution on R^d, then
> mu-hat(z) = exp[-half<z,Az> + i<gamma,z> + integral(e^(i<z,x>) - 1 - i<z,x>1_D(x))nu(dx)],
> z in R^d, where A is a symmetric nonnegative-definite dxd matrix, nu is a measure on R^d
> satisfying nu({0}) = 0 and integral(|x|^2 ^ 1)nu(dx) < infinity, and gamma in R^d.
> (ii) The representation of mu-hat(z) in (i) by A, nu, and gamma is unique.
> (iii) Conversely, if A is a symmetric nonnegative-definite dxd matrix, nu is a measure
> satisfying (8.2), and gamma in R^d, then there exists an infinitely divisible distribution
> mu whose characteristic function is given by (8.1).

**Ledger, statement as used:** "Every psi in NDs is a*omega^2 + integral(1-cos omega x)nu(dx)
with a>=0 and integral(1 ^ x^2)nu(dx)<infinity; the pair (a,nu) is unique; and conversely
every such pair defines a member of NDs." Explicitly disclosed as NOT carrying the folding of
the punctured-line measure onto (0,infinity) -- that reduction is the article's own, proved
elsewhere.

**Lean:** fourier_toolbox_levy_converse and fourier_toolbox_levy_unique both quantify over the
already-folded SymLevyPair, so the folding sits inside the axioms' statements (disclosed at
length in the ledger and in Interfaces.lean's docstring).

**Verdict: MATCH**; existence is (iii) not (ii), as the ledger correctly notes. The folding
step is disclosed and proved elsewhere, not hidden inside the citation.

**Note:** none beyond what the ledger already records.

---

## A4 -- The class is a convex cone, closed under pointwise limits (with the continuity proviso)

**Cite:** jacob2001pseudo -- Lemma 3.6.7A, p. 123; sato1999levy -- Prop. 2.5(viii), p. 9.

**Source, verbatim (Jacob, p. 123).**
> Lemma 3.6.7 A. The set N(R^n) is a convex cone which is closed under pointwise convergence.
> B. For psi in N(R^n) it follows that psi-bar and Re psi belong to N(R^n) too. ...

**Source, verbatim (Sato, p. 9, already fetched for A1/A6).**
> (viii) If mu-hat_n(z) converges to a function phi(z) for every z and phi(z) is continuous at
> z = 0, then phi(z) is the characteristic function of some distribution.

**Ledger, statement as used:** "NDs is a convex cone; in the kernel form it is closed under
pointwise limits with no proviso; and if psi_n in NDs with psi_n -> psi pointwise and psi
continuous at 0, then psi in NDs."

**Lean:** none.

**Verdict: MATCH.** Jacob's Lemma 3.6.7A is precisely "convex cone, closed under pointwise
convergence, no proviso"; Sato (viii) is exactly the continuity-at-0 proviso.

**Note:** none.

---

## A5 -- A finite measure on the line is determined by its Fourier transform (RETIRED)

**Cite:** sato1999levy -- Prop. 2.5(ii), p. 8.

**Source, verbatim (already fetched for A1):** "(ii) If mu-hat_1(z) = mu-hat_2(z) for z in
R^d, then mu_1 = mu_2."

**Ledger, statement as used:** "If mu-hat = rho-hat pointwise on R for finite Borel measures
mu, rho, then mu = rho." Retired 2026-09-09; proved from Mathlib, grounds no node.

**Lean:** none (proved, not axiomatized).

**Verdict: MATCH.** Verbatim identical to the cited clause.

**Note:** none.

---

## A6 -- Levy's continuity theorem (RETIRED)

**Cite:** sato1999levy -- Prop. 2.5(vii)-(viii), p. 9.

**Source, verbatim (already fetched for A1):**
> (vii) If mu_n -> mu, then mu-hat_n(z) -> mu-hat(z) uniformly on any compact set.
> (viii) If mu-hat_n(z) converges to a function phi(z) for every z and phi(z) is continuous at
> z = 0, then phi(z) is the characteristic function of some distribution.

**Ledger, statement as used:** "Pointwise convergence of the transforms of probability
measures to the transform of a probability measure implies weak convergence; and if the limit
function is continuous at 0, it is a transform and the convergence is weak." Retired
2026-09-09; the article's consumed clause is proved from Mathlib.

**Lean:** none (proved, not axiomatized).

**Verdict: MATCH.**

**Note:** none.

---

## A7 -- The one-dimensional characterization of self-decomposable Levy measures

**Cite:** sato1999levy -- Cor. 15.11, p. 95, with Thm. 15.10, p. 95, Def. 15.1, p. 90, Prop.
15.5, p. 93; Thm. 24.11, p. 153; Remark 21.6, p. 138.

**Confirmed present, not re-imaged** (already transcribed 2026-09-19, R172, in the ledger
itself). The ledger's 2026-09-19 bullet gives, verbatim: Def. 15.1 (the self-decomposability
functional equation); Prop. 15.5 (self-decomposable implies infinitely divisible, rho_b
unique and infinitely divisible); Cor. 15.11's full displayed formula with its hypotheses
(A>=0, gamma in R, k>=0, the integrability condition, k increasing on the negative axis,
decreasing on the positive axis); Thm. 24.11 (subordinator criterion); Remark 21.6 (the
Laplace-exponent identity). All four are present as blockquoted text in blueprint/AXIOMS.md.

**Ledger, statement as used:** "A symmetric infinitely divisible law is self-decomposable iff
its Levy measure is k(x)x^-1 dx on (0,infinity) with k nonincreasing; self-decomposability
imposes no restriction on the Gaussian part." Node is cited-and-not-consumed on the main proof
path (disclosed).

**Lean:** none (not stated; this entry is cited but not on the main proof path).

**Verdict: MATCH.** The one-dimensional specialisation of Cor. 15.11 to a symmetric law's
profile on (0,infinity) is an immediate, disclosed elementary consequence, not claimed
verbatim at the anchor.

**Note:** none new; the caveat about the specialisation is already recorded and correct.

---

## A8 -- A nondegenerate self-decomposable law is absolutely continuous

**Cite:** sato1999levy -- Thm. 27.13, p. 181.

**Source, verbatim (p. 181).**
> Theorem 27.13. Any nondegenerate selfdecomposable distribution on R^d is absolutely
> continuous.

**Ledger, statement as used:** "A self-decomposable law on R that is not a point mass has a
density." Explicitly disclosed as NOT carrying any bound on the density (the closed-half-line
AntitoneOn conjunct was found false at finding F6-1 and narrowed to the open ray).

**Lean:** kernel_regularity_law (shared with A9) concludes mu absolutely continuous, an even
density, AntitoneOn on the open ray (0,infinity), nothing about the value at 0.

**Verdict: MATCH.** Thm. 27.13 states absolute continuity alone, exactly as the ledger uses
it; the once-false "bounded density" reading has already been found and corrected
(2026-09-10) and the current Lean type asks only for open-ray monotonicity.

**Note:** none.

---

## A9 -- A law of class L is unimodal

**Cite:** yamazato1978unimodality -- Thm. 1, p. 523.

**Source, verbatim (p. 523).**
> A distribution function F(x) is said to be unimodal with mode m if F(x) is convex for x < m
> and concave for x > m. F(x) is said to be unimodal if, for some m, it is unimodal with mode
> m. ... Theorem 1. All distribution functions of the class L are unimodal.

**Ledger, statement as used:** "Every self-decomposable law on R is unimodal; in the symmetric
case the mode is at the origin. Yamazato's own reading ... is that the distribution function
is convex for x<m and concave for x>m -- with no value asserted at m."

**Lean:** shared kernel_regularity_law as at A8; nothing asserted at the origin.

**Verdict: MATCH**, verbatim. The "class L" = self-decomposable identification is standard
(Sato names it explicitly) and is not itself asserted at this anchor, but is not in dispute.

**Note:** none.

---

## A10 -- The behaviour of a self-decomposable density at the origin

**Cite:** sato1999levy -- Thm. 28.4, p. 191 (smooth regime); Thm. 53.8, pp. 410-411 with
(53.24)-(53.28) and (53.30) (singular regime and threshold).

**Confirmed present, not re-imaged this pass** (re-read from the page image on 2026-09-19,
per the ledger's own R171 entry, the freshest transcription in the whole file). The ledger
already blockquotes Thm. 53.8 verbatim in full, including (53.24)-(53.31), and records that
the librarian's 2026-09-07 paraphrase of (53.28) had dropped the slowly-varying factor K(x),
making the originally admitted axiom sato_origin_singular FALSE from its admission
(2026-09-15) until the restatement (2026-09-19) -- this is the "next A10" the audit was
commissioned to look for, and the ledger itself already found and fixed it.

**Lean, read directly from TwoSidedDefs.lean this pass:** SatoOriginSingular,
SatoOriginSmooth, SatoOriginThreshold are typed over TwoSidedProfile, with the source's
c = k(0+) + k(0-) as a hypothesis sum of two Tendsto limits, both required positive (matching
(53.24)), and conclude an EXISTENTIAL two-sided comparison c1*g(x) <= p(x) <= c2*g(x) with g
built from the shared satoK definition, which is (53.25) read at the letter. No constant of
(53.28)/(53.30) and no cosine factor is asserted -- confirmed by reading the Prop definitions
directly, matching the ledger's own "what is not admitted" bullet.

**Verdict: MATCH, now** (previously the next A10, already found and fixed by this repository
on 2026-09-19, same day as this audit). NARROWER-OK: existential representative and
comparison-only conclusion, dropping the source's exact asymptotic constant and cosine factor.

**Note:** this is the one entry where the ledger's own history IS the finding the audit was
asked to look for. Recommend no further action; the fix is dated the same day as this audit
and the restated Props were read directly from the Lean source in this pass and agree with
Sato's letter.

**Added 2026-09-19 (R189): Theorem 28.4, p. 191, verbatim**, read from the page image by the
librarian the same day (`notes/reviews/cone/SOURCES-round2-2026-09-19.md`, Part 1.1) for the
extension of this entry to `c = ∞` (`cor:origin-smooth`). Transcribed from the image, not from
the text layer; `mu-hat`, `gamma`, `infinity` are the report's transliterations of the printed
symbols.

> THEOREM 28.4. Let mu be a selfdecomposable distribution on R with
>
> (28.3)  mu-hat(z) = exp[ integral_R (e^{izx} - 1 - izx*1_[-1,1](x)) k(x)/|x| dx + i*gamma*z ],
>
> where k(x) is a nonnegative function right-continuous and increasing on (-infinity,0), and
> left-continuous and decreasing on (0,infinity). Let c = k(0+) + k(0-) > 0.
>
> (i) Suppose c < infinity. Define N in Z_+ by N < c <= N + 1. Let gamma_0 be the drift of mu.
> Then mu has a density f(x) continuous on {x != gamma_0} and the function g(x) defined by
>
> (28.4)  g(x) = (x - gamma_0) f(x) for x != gamma_0, and g(gamma_0) = 0,
>
> is continuous on R. If c <= 1, then f(x) cannot be extended to a continuous function on R. If
> c > 1, then f(x) is extended to a C^{N-1} function on R and g(x) is a C^N function on R.
>
> (ii) If c = infinity, then mu has a C^infinity density on R.
>
> Note that (28.3) is a general form of a purely non-Gaussian selfdecomposable distribution on R
> (Corollary 15.11).

**Hypotheses, as printed**: "a selfdecomposable distribution on R" of the form (28.3) — no
nondegeneracy qualifier in this theorem's own statement, no finite-variation condition, and no
condition on the drift, which is simply named in clause (i). The asymmetric continuity convention
for `k` (right-continuous and increasing on the negative half-line, left-continuous and decreasing
on the positive one) is the normalisation whose modification step this entry's names carry beyond
their pages.

**Added 2026-09-19 (R180, R181), after the second external review round.** Two hypotheses of the
source that the three Props do NOT carry, and that hold for the data this article feeds them: the
(53.14) driftless finite-variation form with (53.15) `∫_{|x|<1}k(x)dx < ∞`, which follows from
`k ≤ c < ∞` (the drift from the cosine-transform specification, the Gaussian part from `a = 0`);
and the source's normalisation of the `k`-function to the version left-continuous on `(0,∞)` and
right-continuous on `(−∞,0)` (p. 403, repeated at Thm. 28.4, p. 191), which `TwoSidedProfile` does
not ask for — the Props therefore quantify over a *monotone* `k`, and the justification is a
modification on a countable set, under which the Lévy measure, the exponent, the two one-sided
limits and both comparison functions are unchanged. That modification step is now listed at the
head of `blueprint/trust-boundary.txt` as a fourth item the three names carry beyond their pages.
And the "NARROWER-OK" verdict above is correct **only because the source's constant is nonzero**,
which for symmetric data it is: `κ > 0`, `sin(cπ/2)/sin(cπ) = 1/(2cos(cπ/2)) > 0` for `0 < c < 1`
and `cos(c'π/2) = 1` at `c' = 0`. Had the constant vanished, the source's asymptotic would give
`f = o(g)` and no two-sided comparison at all, so the existential form would be *stronger* rather
than weaker. No transcription changes; the source's wording as quoted in `AXIOMS.md` already
contains (53.14), (53.15) and (53.24).

---

## A11 -- Bernstein's theorem: completely monotone iff the Laplace transform of a measure

**Cite:** schilling2012bernstein -- Thm. 1.4, p. 3 (2nd ed.); corroboration
feller2009introduction Vol. 2, Section XIII.4, Thm. 1 p. 439, Thm. 1a p. 440.

**Source, verbatim (Schilling, p. 3).**
> Theorem 1.4 (Bernstein). Let f : (0,infinity) -> R be a completely monotone function. Then
> it is the Laplace transform of a unique measure mu on [0,infinity) ... Conversely, whenever
> L(mu;lambda) < infinity for every lambda > 0, lambda -> L(mu;lambda) is a completely
> monotone function.

**Source, verbatim (Feller, pp. 439-440).**
> Theorem 1. A function phi on [0,infinity] is the Laplace transform of a probability
> distribution F, iff it is completely monotone, and phi(0) = 1.
> Theorem 1a. The function phi on [0,infinity] is completely monotone iff it is of the form
> phi(lambda) = integral_0^infinity e^(-lambda x)F(dx), lambda>0, where F is not a necessarily
> finite measure on [0,infinity].

**Ledger, statement as used:** "f is completely monotone iff f(sigma) = integral
e^(-sigma u)F(du) for a positive measure F, unique; and f is the transform of a probability
measure iff moreover f(0+) = 1." Three clauses used, one (uniqueness) deliberately not
admitted.

**Lean:** bernstein_completely_monotone states the existence equivalence only, uniqueness
dropped (proved separately by laplace_uniqueness_locally_finite).

**Verdict: MATCH** (Lean: NARROWER-OK). Both anchors state exactly the cited theorems; the
ledger's own account of the uniqueness narrowing is accurate and safe.

**Note:** none.

---

## A12 -- The exponential of a Bernstein function is completely monotone

**Cite:** schilling2012bernstein -- Thm. 3.7, p. 27 (2nd ed.), clause (iii).

**Source, verbatim (p. 27).**
> Theorem 3.7. Let f be a positive function on (0,infinity). Then the following assertions are
> equivalent. (i) f in BF. (ii) g composed with f in CM for every g in CM. (iii) e^(-uf) in CM
> for every u > 0.

**Ledger, statement as used:** "For g a Bernstein function, e^(-tau*g) is completely monotone
for every tau > 0."

**Lean:** none (unadmitted, no consumer -- the delay-law clause it would have served was
dropped 2026-09-10).

**Verdict: MATCH**, exactly clause (i) implies (iii) of the cited theorem.

**Note:** none.

---

## A13 -- The moment criterion for infinitely divisible laws

**Cite:** sato1999levy -- Thm. 25.3, p. 159.

**Source, verbatim (p. 159).**
> Definition 25.2. A function g(x) on R^d is called submultiplicative if it is nonnegative and
> there is a constant a > 0 such that g(x+y) <= a g(x)g(y) for x,y in R^d. ...
> Theorem 25.3 (g-Moment). Let g be a submultiplicative, locally bounded, measurable function
> on R^d. Then, finiteness of the g-moment is not a time dependent distributional property in
> the class of Levy processes. Let X_t be a Levy process on R^d with Levy measure nu. Then, X_t
> has finite g-moment for every t > 0 if and only if the restriction of nu to |x|>1 has finite
> g-moment.
> Proposition 25.4. ... (iii) Let 0 < beta <= 1. Then the following functions are
> submultiplicative: |x| or 1 (max), |x_j| or 1, x_j or 1, exp(|x|^beta), ...

**Ledger, statement as used:** "For an infinitely divisible law with Levy measure nu_2 and a
submultiplicative, locally bounded, measurable weight g, E g(X) < infinity iff the integral of
g over |x|>1 against nu_2 is finite; used with g(x) = max(|x|,1)^n." (Corrected 2026-09-10
from an earlier, non-submultiplicative |x|^n.)

**Lean:** moments_tails_criterion states the left side directly as Integrable of |x|^n against
mu t (the moment itself, not the submultiplicative weight), matching the docstring's own note
that this is "the right thing to say."

**Verdict: MATCH.** Thm. 25.3 and Prop. 25.4(iii) confirm both the theorem and that
max(|x|,1)^n is a legitimate submultiplicative weight, validating the 2026-09-10 correction
exactly as recorded.

**Note:** none.

---

## A14 -- The tail floor for a Levy law with bounded jump support

**Cite:** sato1999levy -- Thm. 26.1, p. 168.

**Source, verbatim (p. 168).**
> Theorem 26.1. Let X_t be a Levy process on R^d with Levy measure nu. Let c = inf of a>0
> such that the support of nu is inside |x|<=a. If nu = 0, then let c = 0. If the support of
> nu is unbounded, then let c = infinity. We understand 1/infinity = 0 and 1/0 = infinity in
> the following. (i) For any alpha with 0<alpha<1/c and for any t>0,
> E[e^(alpha|X_t|log|X_t|)] < infinity and P(|X_t|>r) = o(e^(-alpha r log r)), r->infinity.
> (ii) For any alpha with alpha>1/c and for any t>0, E[e^(alpha|X_t|log|X_t|)] = infinity and
> P(|X_t|>r)/e^(-alpha r log r) -> infinity, r->infinity.

**Ledger, statement as used:** narrows clause (ii) to a LOWER BOUND on c (if the profile is
nonzero at or beyond tau, the radius is at least tau, and divergence holds for every
alpha>1/(tau*t)) -- explicitly not the false original ("k vanishes beyond tau implies
divergence for alpha>1/(tau*t)"), which the ledger records was caught as false at k=0 (pure
Gaussian) and for tau larger than the true radius.

**Lean:** moments_tails_divergence hypothesises existence of mass at or beyond tau, concludes
divergence for alpha > 1/(tau*t). This is exactly the safe direction of clause (ii) as the
ledger states it.

**Verdict: MATCH.** The theorem is transcribed correctly, including the c = inf convention and
the 1/0 = infinity, 1/infinity = 0 reading; the narrowing to a lower bound is the right fix
for the false original.

**Note:** none.

---

## A15 -- The variance-gamma density and its characteristic function

**Cite:** fischer2025variance -- density (1.1), characteristic function (2.12),
self-decomposability Section 2.3.

**Source, verbatim (p. 1, eq. 1.1).**
> p(x) = (1/(sigma sqrt(pi) Gamma(r/2))) e^(theta(x-mu)/sigma^2)
> (|x-mu|/(2 sqrt(theta^2+sigma^2)))^((r-1)/2)
> K_((r-1)/2)(sqrt(theta^2+sigma^2)/sigma^2 * |x-mu|), x in R.

**Source, verbatim (p. 5, eq. 2.12).** phi(t) = E[e^(itX)] = e^(i mu t)(1 - 2i theta t +
sigma^2 t^2)^(-r/2).

**Source, verbatim (p. 6, Section 2.3).** "A distribution Q on the real line is
self-decomposable (Sato, Definition 15.1, p. 90) ... it is immediate from the representation
(2.15) (see Sato, Corollary 15.11) that the VG(r,theta,sigma,mu) distribution is
self-decomposable."

**Ledger, statement as used:** "The symmetric variance-gamma law VG(2gamma,0,t,0) has density
(sqrt(pi) Gamma(gamma) t)^(-1) (|x|/2t)^(gamma-1/2) K_(gamma-1/2)(|x|/t) and characteristic
function (1+t^2 omega^2)^(-gamma)."

**Lean:** none (unadmitted; the two Lean-reaching clauses of prop:matern-density are proved
directly on besselK's own definition and print Lean core, not this entry).

**Verdict: MATCH, exactly.** Substituting r = 2 gamma, theta = 0, sigma = t, mu = 0 into (1.1)
and (2.12) reproduces the ledger's displayed density and transform term for term.

**Note:** none.

---

## A16 -- Asymptotics of the modified Bessel function of the second kind

**Cite:** dlmf2026 Section 10.25(ii) (10.25.3), corroborated by abramowitz1964handbook
Section 9.7 (9.7.2).

**Source, verbatim (Abramowitz-Stegun, p. 378, 9.7.2).**
> K_nu(z) ~ sqrt(pi/2z) e^(-z) [1 + (mu-1)/(8z) + (mu-1)(mu-9)/(2!(8z)^2) + ...]
> (|arg z| < 3pi/2), with mu = 4 nu^2.

**Ledger, statement as used (narrowed 2026-09-11, R119):** "K_nu(z) ~ sqrt(pi/2z) e^(-z) as
z -> +infinity, for fixed real nu" -- no uniformity in nu claimed, since 9.7.2 does not state
any.

**Lean:** none (unadmitted; chapter 12's need for a Bessel transform turned out to be met on
Lean core without any asymptotic, per the ledger's own wave-6/wave-7 correction).

**Verdict: MATCH.** The leading term and the absence of any uniformity-in-nu claim on the page
are both confirmed directly from the image; the 2026-09-11 narrowing (dropping a "uniformly
for nu" clause that was never on the page) is validated.

**Note:** none.

---

## A17 -- Thorin: the extended generalized gamma convolutions

**Cite:** bondesson1992generalized -- Ch. 7 Def./(7.1.1)-(7.1.2), p. 105; Thm. 3.1.1, p. 30.

**Source, verbatim (p. 105).**
> Definition. An extended generalized Gamma convolution (EGGC) is a probability distribution
> on R such that the mgf phi(s) = integral e^(sx)F(dx), defined at least for Re s = 0, has the
> form (7.1.1) phi(s) = exp[bs + cs^2/2 + integral(log(t/(t-s)) - st/(1+t^2))U(dt)], where
> b in R, c>=0, and U(dt) is a nonnegative measure on R minus {0} such that (7.1.2)
> integral 1/(1+t^2) U(dt) < infinity and the integral over |t|<=1 of |log t^2| U(dt) < infinity.

**Source, verbatim (p. 30).**
> Theorem 3.1.1. A probability distribution on R+ is a GGC iff it is ID and the Levy measure
> has a density l such that y l(y), y>0, is completely monotone. In fact,
> y l(y) = integral e^(-yt) U(dt).

**Ledger, statement as used:** "The extended generalized gamma convolutions are the laws with
mgf exp[b sigma + c sigma^2/2 + integral(log(theta/(theta-sigma)) -
sigma theta/(1+theta^2)) U(d theta)], U>=0 on R minus {0}; the symmetric members are those
with b=0 and U symmetric."

**Lean:** none (unadmitted by design).

**Verdict: MATCH**, exactly (theta/sigma notation swap only).

**Note:** the Levy-density form of the class (Bondesson Section 7.1) was not sought this pass
either; the mgf form used by the article is fully confirmed.

---

## A18 -- The generalized inverse Gaussian laws are generalized gamma convolutions

**Cite:** halgreen1979self -- Section 2 "The GIGDs are Generalized Gamma-Convolutions",
pp. 14-15.

**Source, verbatim (pp. 14-15).** Confirmed to be an unnumbered prose section, exactly as the
ledger records ("no numbered statements"). Its concluding sentence: "Comparing (5) and (2) we
see, that the GIGDs with lambda<=0 are generalized Gamma-convolutions." -- via the constructed
Thorin measure U with an explicit density on (psi/2, infinity).

**Ledger, statement as used:** "The inverse-gamma laws, being generalized inverse Gaussian,
are generalized gamma convolutions and hence self-decomposable; so the causal Bessel family is
causally admissible."

**Lean:** none (unadmitted by design; both statement nodes that would have consumed it are
restated as conditionals on the representation and proved on Lean core instead, per R160).

**Verdict: MATCH.** Section heading and the section's conclusion both confirmed at the letter.

**Note:** none.

---

## A19 -- The modified Bessel equation: solution basis, behaviour at 0, and oscillation

**Cite:** dlmf2026 Section 10.25/Section 10.30/Section 10.21/(10.32.9); corroborated by
abramowitz1964handbook Section 9.6, Section 9.5.

**Source, verbatim (A&S, p. 375).**
> 9.6.1 z^2 d^2w/dz^2 + z dw/dz - (z^2+nu^2)w = 0. Solutions are I_(+-nu)(z) and K_nu(z). ...
> 9.6.6 I_(-n)(z) = I_n(z), K_(-nu)(z) = K_nu(z).
> 9.6.7 I_nu(z) ~ (z/2)^nu / Gamma(nu+1) (nu not -1,-2,...). 9.6.8 K_0(z) ~ -ln z.
> 9.6.9 K_nu(z) ~ (1/2) Gamma(nu) (z/2)^(-nu) (Re nu > 0).

**Source, verbatim (A&S, p. 370).**
> When nu is real, the functions J_nu(z), J'_nu(z), Y_nu(z) and Y'_nu(z) each have an infinite
> number of real zeros, all of which are simple with the possible exception of z=0. ... The
> positive zeros of any two real distinct cylinder functions of the same order are interlaced,
> as are the positive zeros of any real cylinder function C_nu(z) ... and the contiguous
> function C_(nu+1)(z).

**Ledger, statement as used (clause b-prime):** the covariant-equation solution basis,
restated as "the bounded, normalised solution is the normalised K_nu, existing only for
nu>0" -- confirmed by 9.6.1/9.6.6-9.6.9 above, exactly as the ledger's own passes found.
**(clause c):** "every nontrivial solution of the ordinary Bessel equation has infinitely many
positive zeros" -- the page states infinitude ONLY for J_nu, J'_nu, Y_nu, Y'_nu individually,
and states interlacing (not infinitude) for a general real cylinder function; the ledger
already discloses that the general-cylinder-function infinitude is "a one-line deduction from
two stated sentences," not a verbatim page statement.

**Lean:** joint_locality_bounded_solution (clause b-prime) and joint_locality_hyperbolic
(clause c), both admitted only in the narrowed forms above.

**Verdict: MATCH**, given the ledger's own disclosed narrowing at clause (c). This is the
second-closest call in the ledger after A10: a reader who only checked the primary page for
"infinitely many zeros of a general cylinder function" would not find it stated in those
words. The ledger already flags this and the one-line deduction is genuinely elementary, so
this is not a hidden strengthening.

**Note:** confirms the ledger's own finding; no new discrepancy.

---

## A20 -- The half-plane Dirichlet problem of generalized axially symmetric potential theory

**Cite:** weinstein1953generalized Section 10, p. 34, eq. (43); huber1954uniqueness Thm. 2,
p. 356.

**Source, verbatim (Weinstein, p. 34, eq. 43).**
> z(k) = A y^(1-k) integral over the whole line of f(xi)d(xi) divided by
> [(x-xi)^2+y^2]^((2-k)/2), which solves the Dirichlet problem for the half-plane y>=0, for
> given bounded continuous boundary values f(xi). ... Green's function does not exist for
> k >= 1.

**Source, verbatim (Huber, p. 356).**
> Theorem 2. Let u be a solution of L_k(u) = 0, defined in a region G, the boundary of which
> contains an open subset S of D. If u assumes the boundary value 0 on S, we may conclude
> (a) for k >= 1: u = 0 throughout G, (b) for k < 1: u can be represented in the form
> u = x_n^(1-k) v(x_1,...,x_n), where v is analytic on G union S and satisfies
> L_(2-k)(v) = 0. ...

**Ledger, statement as used:** "the bounded solution is unique, unbounded null solutions
y^(1-k) v existing." The ledger's own caveat, already recorded 2026-09-07: "Huber's Theorem 2
as displayed carries no explicit boundedness qualifier for the uniqueness clause, the k>=1
case reading u=0 unconditionally; the 'bounded solutions' language may be a standing
hypothesis of his Sections 1-2, to be reread before the entry is called settled."

**Lean:** none for the uniqueness clause (not admitted, no consumer -- the ledger records the
existence clause is proved directly on Lean core, student_scaleSpace_gaspt, and does not touch
uniqueness).

**Verdict: DIFFERENCE (disclosed, currently harmless).** As printed, Theorem 2(a) states
u = 0 unconditionally for k >= 1, with NO boundedness hypothesis in the displayed theorem,
while the ledger's Cite line and "Statement as used" describe it as "uniqueness among bounded
solutions." This is a genuine gap between the displayed page and the paraphrase; it is not
dangerous only because (i) it is already disclosed in the ledger rather than hidden, and
(ii) rem:gaspt-uniqueness is the only place this entry's uniqueness clause is cited and no
declaration reads it. Huber Sections 1-2 (only Thm. 2 itself, p. 356, was opened this pass)
were not read, so I cannot confirm or rule out a standing boundedness hypothesis stated
earlier in the paper; this is exactly the reread the ledger already says is owed.

**Note:** recommend, before anything ever cites rem:gaspt-uniqueness as load-bearing, that
Huber Sections 1-2 (the setup preceding Theorem 2) be read to settle whether "bounded" is a
standing hypothesis; until then this citation should be treated as unconfirmed for its
uniqueness half.

---

## A21 -- Schoenberg's representation of Polya frequency densities on the line

**Cite:** karlin1968total -- Ch. 7, Thm. 3.2(a), p. 345, Remark 3.1, p. 346; Ch. 7 Section 2,
p. 336; Ch. 7 Section 1, Prop. 1.4, p. 333.

**Source, verbatim (p. 345).**
> Theorem 3.2. (a) A necessary and sufficient condition that a density function f(u)
> (-infinity<u<infinity) be PF is that the reciprocal of its Laplace transform be an entire
> function of class E2* with gamma + the sum of a_i^2 > 0.

**Source, verbatim (p. 336).**
> (2.2) psi(s) = e^(-gamma s^2 + delta s) s^k times the product of (1+a_i s) e^(-a_i s), where
> gamma>=0, delta real, k a nonnegative integer, the a_i are real, and the sum of a_i^2 is
> finite, is fundamental in the theory of general PF functions on the line. We define E2* as
> the subclass of E2 for which psi(0)=1. ... phi(s) = 1/psi(s) for psi(s) in E2* is the
> Laplace transform of a PF density, provided gamma plus the sum of a_i^2 is greater than 0.

**Source, verbatim (p. 333).**
> Proposition 1.4. If f is a PF2 density, then its Laplace transform exists in an open strip
> containing the imaginary axis.

**Ledger, statement as used:** "phi is a Polya frequency density iff the reciprocal of its
two-sided Laplace transform is e^(-gamma sigma^2 + delta sigma) times the product of
(1+lambda_i sigma) e^(-lambda_i sigma), with gamma>=0, real lambda_i, the sum of lambda_i^2
finite, the identity holding at complex sigma on an open strip containing the imaginary
axis." No constant (correctly, since psi(0)=1 forces k=0 in (2.2)).

**Lean:** the two named axioms are restated at Karlin's letter since the 2026-09-12 discharge,
dropping the article's own extra hypotheses that were once needed for a symmetry-reduction
step believed to be an analytic continuation.

**Verdict: MATCH, exactly.** Every displayed clause (the class E2* form, the "provided
gamma plus sum of a_i^2 > 0" producing sentence, and Prop. 1.4's open strip) is confirmed word
for word.

**Note:** this pair's once-open "analytic continuation" debt is independently confirmed
resolved by Prop. 1.4 alone: the identity is stated at complex s on a strip already containing
the imaginary axis, so s = i omega needs no continuation -- exactly the ledger's 2026-09-12
finding.

---

## A22 -- Variation diminution and total positivity coincide for translation kernels

**Cite:** karlin1968total -- Ch. 5, Thm. 3.1(i), p. 233 (sufficiency); Thm. 4.2, pp. 242-243
(necessity).

**Source, verbatim (p. 233, Section 3, "VD properties of sign-regular functions").**
> Theorem 3.1. (i) If K(x,y) is SR_r (r>=2), and if f has n (n<=r-1) relevant sign changes
> with respect to mu, then the essential negative-sign-change count of g(x) is at most n, for
> x in X. Equivalently, that count is at most the count of f(y) whenever the count of f is at
> most r-1, for x in X, y in Y.

**Source, verbatim (p. 243, Thm. 4.2).**
> Theorem 4.2. Let k(u) be a density function on (-infinity,infinity); i.e., k(u) is
> nonnegative and has total integral 1. If the transformation (4.4) enjoys property (4.6),
> then k(u-v) is TP_r almost everywhere in -infinity<u,v<infinity.

**Ledger, statement as used:** "Convolution by a kernel is variation-diminishing iff the
kernel is totally positive, that is a Polya frequency density. Both directions are used." The
"density on the whole line, nonnegative, total integral 1" hypothesis of Thm. 4.2 is exactly
what the ledger records the Lean axiom's absolute-continuity hypothesis (supplied from A8) is
for.

**Lean:** same two names as A21 (spent jointly); the essential-versus-ordinary sign-change
narrowing and the integrable-versus-bounded-Borel extension are both already disclosed and,
per the ledger, the sign-change gap was closed by a proof in 2026-09-11.

**Verdict: MATCH, exactly**, including the precise page (233, Section 3, within Ch. 5's
numbering -- confirmed as Ch. 5 material, not Ch. 7, matching the Cite line).

**Note:** none.

---

## A23 -- Schoenberg's radial theorem, with the representation of a Bernstein function

**Cite:** schilling2012bernstein -- Thm. 13.14, p. 212; Def. 3.1, Thm. 3.2, p. 21.

**Confirmed present, not re-imaged** (read from the held copy 2026-09-17, per the ledger's own
entry). The ledger already blockquotes Thm. 13.14 verbatim (a function on (0,infinity) is a
Bernstein function iff, for all d, its radial extension to R^d is continuous and negative
definite) and Def. 3.1/Thm. 3.2 verbatim (the smoothness and alternating-derivative-sign
definition, and the representation with a unique triplet).

**Ledger, statement as used:** matches the blockquoted text exactly; the entry is disclosed as
prose-only, not admitted, grounding prop:dimension-filtration (clause 3) alone.

**Lean:** none (none scheduled).

**Verdict: MATCH.**

**Note:** none.

---

## A24 -- The closure of the generalized gamma convolutions, with the continuity theorem for Laplace transforms

**Cite:** bondesson1992generalized -- Thm. 3.1.5, pp. 34-35, with (3.1.1)-(3.1.2), p. 29;
feller2009introduction Vol. 2, XIII.1, Thm. 2, p. 431.

**Confirmed present, not re-imaged** (read from the held copies, page images, 2026-09-19 --
the same day as this audit). The ledger already blockquotes, verbatim: the GGC definition
(p. 29); Thm. 3.1.5 (pp. 34-35, the closure theorem, plus its (i)-(iii) reformulation on p. 35
including the defective-limit caveat for (iii)); and Feller's Thm. 2 (p. 431, the
two-directional continuity theorem for Laplace transforms with the "defective iff phi
approaches 1" clause).

**Ledger, statement as used:** matches the blockquoted text; explicitly disclosed as not
carrying Bondesson's two-sided closure theorem (read but not spent) and not carrying Feller's
own convention for weak convergence of possibly-defective distributions (the page defining it
was not read).

**Lean:** none (chapter 14 has no Lean scheduled).

**Verdict: MATCH.**

**Note:** the ledger's own disclosure that Feller's convergence convention was not
independently read is accurate and should stay open if this entry is ever pressed harder.

---

## Summary table

| Entry | Verdict | Note |
|---|---|---|
| A1 | MATCH (Lean: NARROWER-OK) | Forward-implication-only axiom, stronger hypotheses; safe. |
| A2 | MATCH | Berg-Forst corroboration not independently re-checked (as already flagged). |
| A3 | MATCH | Folding step disclosed and proved elsewhere, not hidden inside the citation. |
| A4 | MATCH | Jacob "Lemma 3.6.7A" confirmed to be part A of Lemma 3.6.7, exactly as cited. |
| A5 | MATCH | Retired; proved from Mathlib; verbatim identical to Prop. 2.5(ii). |
| A6 | MATCH | Retired; proved from Mathlib; verbatim identical to Prop. 2.5(vii)-(viii). |
| A7 | MATCH | Verbatim quotes already in ledger (2026-09-19), confirmed present. |
| A8 | MATCH | Thm. 27.13 gives absolute continuity only, exactly as used; the once-false bound is already fixed. |
| A9 | MATCH | Yamazato Thm. 1 and the convex/concave definition confirmed verbatim. |
| A10 | MATCH now (was the "next A10," already found and fixed 2026-09-19) | The dropped-K defect the audit was commissioned to find; ledger's own R171 fix, same day. |
| A11 | MATCH (Lean: NARROWER-OK) | Uniqueness deliberately dropped from the axiom, proved separately. |
| A12 | MATCH | Thm. 3.7(iii) confirmed verbatim. |
| A13 | MATCH | Thm. 25.3 and Prop. 25.4(iii) confirm the corrected max(|x|,1)^n weight. |
| A14 | MATCH | Thm. 26.1 confirmed verbatim; the lower-bound narrowing of clause (ii) is the right fix. |
| A15 | MATCH, exactly | Density and characteristic function reproduce term for term under r=2gamma, sigma=t. |
| A16 | MATCH | 9.7.2 confirms leading term and the absence of any uniformity-in-nu claim. |
| A17 | MATCH | EGGC mgf and GGC class theorem both confirmed verbatim. |
| A18 | MATCH | Confirmed unnumbered prose section and its stated conclusion. |
| A19 | MATCH (disclosed narrowing at clause (c)) | General-cylinder-function infinitude is a one-line deduction, not a verbatim page statement; already flagged in the ledger. |
| A20 | DIFFERENCE (disclosed, currently harmless) | Huber's printed Theorem 2 has no boundedness qualifier; Sections 1-2 (a possible standing hypothesis) were not read this pass either. Not dangerous only because no proof consumes the uniqueness clause. |
| A21 | MATCH, exactly | Thm. 3.2(a), the p. 336 producing sentence, and Prop. 1.4's open strip all confirmed verbatim; the once-open "analytic continuation" debt is independently confirmed unnecessary. |
| A22 | MATCH, exactly | Thm. 3.1(i) (p. 233) and Thm. 4.2 (p. 243) confirmed verbatim, including the density hypothesis the Lean axiom's hypothesis supplies. |
| A23 | MATCH | Verbatim quotes already in ledger (2026-09-17), confirmed present. |
| A24 | MATCH | Verbatim quotes already in ledger (2026-09-19), confirmed present. |
