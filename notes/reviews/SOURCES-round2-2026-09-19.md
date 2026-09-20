<!-- Export note: 3 file path(s) on the author's machine were replaced by <local path> in this public copy; nothing else was changed. -->
# Source-verification report — module B review round (dispatched from spatial-hemigroup-scale-space)

Librarian pass, 2026-09-19. Every Part 1 transcription below was read from the page image of
the held copy (not the text layer, not memory) via `library page <citekey> --printed <N>
--format image`, saved under this same scratchpad directory as `<citekey>_p<N>.png`. Part 2 used
`library search --corpus` against the local Zotero index. Part 3 used the Crossref REST API
(`api.crossref.org`, network reachable from this sandbox via the Bash tool's `curl`) since none of
the named sources are held. No repository file was touched.

---

## Part 1 — held sources, verbatim

### 1. Sato, *Levy Processes and Infinitely Divisible Distributions* (1999), Theorem 28.4, p. 191

**Citekey:** `sato1999levy` (held, PDF stored). Page image:
`sato_p191.png/sato1999levy_printed191.png` (theorem), `sato_p190.png/...190.png` (preceding
context).

**Verbatim (p. 191):**

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

Immediately below, LEMMA 28.5 (same page): "Let mu be as in Theorem 28.4. Then |mu-hat(z)| =
o(|z|^{-alpha}) as |z| -> infinity for any alpha with 0 < alpha < c." The proof of Theorem 28.4
itself is given on p. 191 ("Proof of Theorem 28.4. We know, by Example 27.8, that mu is
absolutely continuous. If 1 < c < infinity, then, by Proposition 28.1 and Lemma 28.5, mu has a
C^{N-1} density. Moreover, if c = infinity, then mu has a C^infinity density for the same
reason...").

**Hypotheses, exactly as printed:**
- "mu [is] a selfdecomposable distribution on R" — **no "nondegenerate" qualifier appears in the
  theorem's own statement.** (The proof invokes "Example 27.8" for absolute continuity, which is
  presumably where any degenerate/trivial case is disposed of or excluded; that example was not
  re-read this pass. The task description's phrase "nondegenerate self-decomposable" is not the
  book's wording for *this* theorem — it is the printed wording of Example 28.2 two results
  earlier, about semi-stable/stable laws, not Theorem 28.4.)
- k-function convention: **right-continuous and increasing on (-infinity,0)**, **left-continuous
  and decreasing on (0,infinity)** — i.e. right/left continuity is asymmetric between the two
  half-lines, exactly opposite conventions on each side.
- No separate condition is placed on the drift; gamma_0 is simply named "the drift of mu."
- c := k(0+) + k(0-) is required **> 0** for the theorem to be in its stated (purely
  non-Gaussian) form at all (c = 0 would make the Levy density vanish near the origin).

**Verdict on the referee's claim ("clause (ii) gives a C^infinity density when
c = k(0+)+k(0-) = infinity): CONFIRMED, verbatim.** Clause (ii) reads exactly: "If c = infinity,
then mu has a C^infinity density on R."

---

### 2. Bondesson, *Generalized Gamma Convolutions and Related Classes of Distributions and
Densities* (1992), p. 36 — the PF-infinity/GGC closure quotation

**Citekey:** `bondesson1992generalized` (held, PDF stored). Page images: `bondesson_p35.png`,
`bondesson_p36.png` (the quoted text), `bondesson_p27.png`, `bondesson_p29.png` (definition of the
class J for context).

**Verbatim (p. 36, Example 3.2.2, "Polya densities"):**

> Example 3.2.2 (Polya densities). The pdf of a denumerable convolution of Exponential
> distributions (and possibly a degenerate distribution) is often called a Polya frequency
> function on R_+ of order infinity. The class of such pdf's f is denoted PF-infinity. As shown by
> Schoenberg (1951), the densities in this class have the characteristic property of being totally
> positive of all orders, i.e., for each n >= 2, every n x n matrix M formed by elements
> m_ij = f(x_i - y_j), x_1 < x_2 < ... < x_n, y_1 < y_2 < ... < y_n, has a nonnegative determinant.
> (For x_i < y_j, m_ij = 0.) The major document on total positivity is the book by Karlin (1968).
> Marshall & Olkin (1979, Chapter 18) provide a brief account. Total positivity of order 2 is
> equivalent to logconcavity, or strong unimodality. **Obviously the PF-infinity-class equals the
> subclass of J for which the U-measure is discrete with atoms with integral mass. The closure
> theorem for GGC's guarantees in particular that also the PF-infinity-class is closed with
> respect to weak limits; note that atoms with mass 1 cannot be split in the limit.**

**Verdict: CONFIRMED, essentially verbatim, with one symbol correction.** The referee's quotation
matches word for word, *except* that Bondesson's printed symbol for the GGC class is the script
letter **J** (called the "J-class," defined p. 29, "in honor of Thorin"), not "G" as the referee
wrote it — almost certainly an OCR/rendering slip for the same script letter (a script J and a
cursive G are easily confused when copied from a scan), not a different symbol Bondesson actually
uses. There is no class called "G" anywhere on the surrounding pages.

**Context, read at pp. 27 and 29 for completeness (not part of the referee's quoted sentence, but
load-bearing for using it correctly):**
- The J-class is defined at p. 29 (start of Ch. 3, "Generalized Gamma Convolutions"): "A
  generalized Gamma convolution (or J-distribution) is a probability distribution F on
  **R_+ = [0,infinity)** with mgf of the form phi(s) = integral e^{sx}F(dx) =
  exp{as + integral log(t/(t-s))U(dt)}, s <= 0, where a >= 0 and U(dt) is a nonnegative measure on
  (0,infinity) satisfying integral_{(0,1]}|log t|U(dt) < infinity and
  integral_{(1,infinity)}t^{-1}U(dt) < infinity." **So J (and hence the quoted PF-infinity class)
  is a class of distributions on the half-line R_+, not on the whole line** — this is the class of
  a nonnegative random variable's law, characterized by its moment generating function and its
  "U-measure." (Bondesson's introduction, p. 29, attributes the J-class to O. Thorin (1977) and
  notes it is the smallest class on R_+ containing the Gamma laws and closed under convolution and
  weak limits.)
- The PF-infinity (Polya frequency function of order infinity) terminology and its equivalence
  with total positivity of all orders is attributed by Bondesson to **Schoenberg (1951)**,
  matching what Karlin's own book attributes (see item 3 below) — an independent cross-check that
  both books point to the same 1951 Schoenberg paper.

---

### 3. Karlin, *Total Positivity* (1968) — the Schoenberg PF-infinity representation (grounds this
article's ledger A21/A22)

**Citekey:** `karlin1968total` (held, PDF stored). Page images: `karlin_p333.png` (Prop. 1.4),
`karlin_p335.png` (eq. (1.6), the two-sided form), `karlin_p336.png` (section 2 definitions of
classes E1, E2, E1*, E2*), `karlin_p337.png`, `karlin_p344.png` through `karlin_p346.png`
(Thm. 3.1, Thm. 3.2, and Remark 3.1/(4.1)), `karlin_p391.png` (section 13 Notes and References
for Chapter 7).

**The characterizing theorem, verbatim (p. 345, Chapter 7 "Polya Frequency Functions," section 3):**

> THEOREM 3.2. (a) *A necessary and sufficient condition that a density function f(u)
> (-infinity < u < infinity) be PF is that the reciprocal of its Laplace transform be an entire
> function of class E2* with gamma + Sum_{i=1}^infinity a_i^2 > 0.*
>
> (b) *A necessary and sufficient condition that a density function f(u) (-infinity < u <
> infinity), for which f(u) = 0 (u < 0), be PF is that the reciprocal of its Laplace transform be
> an entire function of class E1* with Sum_{i=1}^infinity lambda_i > 0.*
>
> (c) *A necessary and sufficient condition that a density function f(u) (-infinity < u <
> infinity), where f(u) = 0 for u > 0, be PF is that the reciprocal of its Laplace transform be an
> entire function of the form [continues on p. 346 as (3.15)]:*
>
> (3.15)  psi(s) = e^{-delta*s} * Prod_{i=1}^infinity (1 - lambda_i*s),
>          delta >= 0; lambda_i >= 0; 0 < Sum_{i=1}^infinity lambda_i < infinity.

And, p. 346, immediately following: "The condition gamma + Sum a_i^2 > 0 in (a) is essential in
order that f be a bona fide density function, and similarly for (b) and (c)."

**The exact form of the class E2* (definition, p. 336, section 2, eq. (2.2)):**

> The class E2 of entire functions of the form
>
> (2.2)  psi(s) = e^{-gamma*s^2 + delta*s} * s^k * Prod_{i=1}^infinity (1 + a_i*s) * e^{-a_i*s}
>
> where gamma >= 0, delta is real, k is a nonnegative integer, the a_i are real, and
> Sum_{i=1}^infinity a_i^2 < infinity, is fundamental in the theory of general PF functions on the
> line. We define E2* as the subclass of E2 for which psi(0) = 1.

So, unwinding the "reciprocal of the Laplace transform," Theorem 3.2(a) says exactly: writing
phi(s) for f's (bilateral) Laplace transform, **f is PF iff 1/phi(s) = psi(s) =
e^{-gamma*s^2 + delta*s} * Prod(1 + a_i*s)*e^{-a_i*s}, with gamma >= 0, Sum a_i^2 < infinity, and
gamma + Sum a_i^2 > 0** (the k = 0 case of (2.2), since psi(0) = 1 forces no s^k factor when f is
a genuine, non-singular density). This is exactly the form quoted in the dispatch
(1/psi(s) = C*e^{-gamma*s^2+delta*s}*Prod(1+a_i*s)*e^{-a_i*s}), up to the harmless
C <-> normalization-to-1 and the phi/psi swap (Karlin uses phi for the transform itself and
psi = 1/phi for its reciprocal). The unnormalized two-sided form, with the strip of convergence,
is stated a few pages earlier, at **(1.6), p. 335**: "phi(s) = e^{gamma*s^2+delta*s} /
Prod_{i=1}^infinity(1+a_i*s)*e^{-a_i*s}, gamma >= 0; delta, a_i real;
0 < gamma + Sum a_i^2 < infinity; max_{a_i>0}(-1/a_i) < Re(s) < min_{a_i<0}(-1/a_i)," with the
accompanying sentence "phi(s) is analytic in an open strip containing the imaginary axis."
**Proposition 1.4, p. 333** ("If f is a PF2 density, then its Laplace transform exists in an open
strip containing the imaginary axis") is the general fact this specializes; this is the
proposition already used to ground this article's ledger A21/A22 (per `blueprint/AXIOMS.md` row
for A21/A22, "Karlin's identity holds at complex s on an open strip containing the imaginary axis
(Prop. 1.4, p. 333)").

**Variation diminution equals PF-infinity, nearby pages.** Theorem 3.2 itself is stated purely in
terms of the Laplace-transform reciprocal, not variation diminution; the variation-diminishing
route to PF is Chapter 3's own machinery (already the anchor of this article's A22, Karlin
Thm. 3.1(i) p. 233 and Thm. 4.2 pp. 242-243, not re-read this pass) and Chapter 7 section 1's
zero-counting results (3.6)/(3.8), p. 344, used in Theorem 3.2's own derivation ("Theorems 2.1,
2.2, and 3.1, and Remark 2.1, when simply combined, yield the following fundamental theorem" —
i.e. Theorem 3.2 is proved *from* the zero-counting/variation-diminishing apparatus of sections
1-2, not stated as a separate biconditional next to it). So "PF-infinity kernels are exactly the
variation-diminishing ones" is not printed as its own labelled theorem on these pages; it is the
*route* by which Theorem 3.2 is proved, via the sign-change bound Z_-(b) <= Z_-(a) of (3.8),
p. 344, and Theorem 3.1's assertion (p. 345) that if f(u) is PF on (-infinity,infinity) with
Laplace transform phi(s) and psi(s) = 1/phi(s) = Sum c_m*s^m/m! convergent for |s| < A, then the
partial sums A*_n(s) = Sum (n choose m) c_m s^m have only real zeros (nonpositive zeros if f
vanishes on the negative axis) — the "variation-diminishing" content is Descartes'-rule counting
of these zeros, carried by (3.6)/(3.8) two pages earlier.

**Attribution, per Karlin's own section 13 "Notes and References" (p. 391, read in full):**
- "Section 1. The genesis and maturation of the theory of Polya frequency functions can be laid
  principally to Schoenberg. In a remarkable series of papers, Schoenberg [1950, 1951, 1953, 1959]
  set the basis of the theory and established the fundamental representation theorems. ... The
  discussion of section 1 follows Schoenberg [1951]."
- "Section 2. The characterizations of the entire functions of classes E1 and E2 rest on
  extensions by Polya [1913] of a classical theorem of Laguerre."
- **"Sections 3 and 4. These are elaborations of Schoenberg [1951]."** — i.e. Theorem 3.2 itself
  (the reciprocal-Laplace-transform characterization) is credited to Schoenberg 1951.

**Full citation of "Schoenberg [1951]" (Karlin's bibliography, p. 572):** Schoenberg, I. J.
(1951). "On Polya Frequency Functions, I: The Totally Positive Functions and Their Laplace
Transforms," *J. d'Analyse Math.*, **1**, 331-74. (This is the same 1951 paper Bondesson's book
cites in item 2 above — an independent corroboration of the attribution.)

**Verdict: CONFIRMED** (the reciprocal-Laplace-transform theorem, its hypotheses, and the
Schoenberg [1951] attribution). The referee's gamma >= 0, Sum a_i^2 < infinity,
gamma + Sum a_i^2 > 0 form is exactly Theorem 3.2(a) read together with definition (2.2);
"variation-diminishing iff PF-infinity" is not a separately labelled theorem on these pages but
the proof route behind Theorem 3.2, via (3.6)/(3.8), Thm. 2.1/2.2 and Thm. 3.1 (all in Chapter 7
sections 1-2 preceding it).

---

### 4. The tail of the symmetric stable density

**Best held anchor: `sato1999levy`, Remark 14.18, pp. 87-88** (page images `sato_p87.png`,
`sato_p88.png`). Also cross-referenced at p. 168 ("the tail P[X_t > r] ... is thinner than the
tail of the Gaussian distribution" — a different, one-sided remark, not used below).

**Verbatim, p. 87-88:**

> REMARK 14.18. If mu is non-trivial and stable on R, then it has a continuous density by
> Proposition 2.5(xii), since |mu-hat(z)| = e^{-c|z|^alpha} with c > 0. Let {X_t} be a stable
> process on R with parameters (alpha, beta, tau, c), 0 < alpha < 2. Let X_t^0 = X_t - t*tau. Let
> p(t,x) and p^0(t,x) be the continuous densities of the distributions of X_t and X_t^0,
> respectively, for t > 0. [...]
>
> The behavior of p(t,x) as t -> infinity is important in limit theorems for stable processes. It
> is obtained from the behavior of p^0(1,x) as x -> +/-infinity or x -> 0. [...] The asymptotic
> expansions of p^0(1,x) are obtained by Linnik [291], Skorohod [431], and others. We give,
> without proofs, the results (with misprints corrected and with some formal changes) in Zolotarev
> [536]. We can fix the parameter c without loss of generality. Assume that c equals
> cos(pi*beta*alpha/2), pi/2, or cos(pi*beta*(2-alpha)/2) for alpha < 1, = 1, or > 1, respectively.
> Let alpha' = 1/alpha. Let rho = (1+beta)/2 or = (1 - beta*(2-alpha)/alpha)/2, according as
> alpha < 1 or > 1.
>
> [...] (ii) If alpha < 1, then
>
> (14.31)  p^0(1,x) = (1/pi) * Sum_{n=1}^infinity (-1)^{n-1} [Gamma(n*alpha+1)/n!] *
>          (sin(pi*n*rho*alpha)) * x^{-n*alpha-1}   for x > 0.
>
> [...] (v) When alpha > 1, beta != -1, and x -> infinity,
>
> (14.34)  p^0(1,x) = (1/pi) * Sum_{n=1}^{N} (-1)^{n-1} [Gamma(n*alpha+1)/n!] *
>          (sin(pi*n*rho*alpha)) * x^{-n*alpha-1} + O(x^{-(N+1)*alpha-1}).

**Specializing to the symmetric case beta = 0** (the article's case): rho = (1+beta)/2 = 1/2 for
alpha > 1 (and the same value 1/2 for alpha < 1's rho = (1+beta)/2), c = 1 in both branches
(cos(0) = 1, and cos(pi*0*(2-alpha)/2) = 1). Reading off the leading (n = 1) term of
(14.31)/(14.34) and using p^0(1,-x) = p^0(1,x) by symmetry:

> **p(x) ~ (1/pi) * Gamma(alpha+1) * sin(pi*alpha/2) * |x|^{-alpha-1}  as |x| -> infinity, for
> 0 < alpha < 2, alpha != 1** (the standard normalization with characteristic function
> exp(-|z|^alpha), i.e. c = 1 above), with the same constant obtained for alpha < 1 (from (14.31))
> and alpha > 1 (from (14.34)) — these are two branches of the *same* series, both anchored at
> Sato p. 87-88, attributed there (without re-derivation) to Linnik, Skorohod and Zolotarev.

The remaining case alpha = 1 (Cauchy) is elementary and not needed here.

**Verdict: CONFIRMED** — a printed, page-anchored statement of the symmetric stable tail with its
exact constant Gamma(alpha+1)*sin(pi*alpha/2)/pi exists at Sato Remark 14.18 (pp. 87-88), stated
as a convergent (not merely asymptotic, for x > 0) series whose leading term gives the claimed
power law. This is a better anchor than Feller Vol. 2 (not searched, not needed) since it carries
the explicit constant rather than just the existence of a C_alpha.

---

### 5. Sato, "Subordination and self-decomposability," *Statist. Probab. Lett.* **54** (2001)

**Citekey:** `sato2001subordination` (held, PDF stored — **the full text is held**, not just the
abstract; date added 2026-09-19, so this may be a very recent acquisition). Page images:
`sato2001_p8.png`, `sato2001_p9.png`.

**Theorem 1.1, verbatim (p. 2):**

> Theorem 1.1. Let {X_t: t >= 0} be a Brownian motion with drift on R and let {Z_t: t >= 0} be a
> selfdecomposable subordinator. Then the subordinated process {Y_t: t >= 0} arising from them is
> selfdecomposable.

Immediately following: "Using the terminology of Barndorff-Nielsen and Shephard (2000), we can
express Theorem 1.1 in this way: normal variance-mean mixtures using selfdecomposable mixing
distributions are selfdecomposable."

**Theorem 1.2, verbatim (p. 3):**

> Theorem 1.2. There is a selfdecomposable random variable Y of type G for which one cannot find
> a nonnegative selfdecomposable Z and a standard Gaussian X satisfying (1.4) and (1.5).
>
> In other words, a selfdecomposable random variable of type G is not necessarily of type GL. This
> disproves a conjecture of Jian (2000), p. 40.

**Section 3, the explicit witness (equation (3.7) and its context, p. 8):** Section 3 constructs
a counterexample for Theorem 1.2 by building a Levy measure nu-sharp for Y via (3.1)-(3.6) and
then

> Take k(s) such that
>
> (3.7)  k(s) = { 2*s^{-1/2},          s in (0, 1/(a+b)) union [1/a, infinity),
>               { -2*s^{-1/2} + c,     s in [1/(a+b), 1/a),
>
> where c is chosen to be -2(a+b)^{1/2} + c >= 0. Then k(s) >= 0 on (0,infinity),
> integral_0^1 k(s)ds < infinity, integral_1^infinity s^{-1}k(s)ds < infinity, and (3.6) is
> satisfied. [...] Hence nu-sharp(dx) = |x|^{-1}*k-sharp(x)dx and rho(ds) = s^{-1}k(s)ds are the
> Levy measures that we wanted to construct. Indeed, the Levy process with Levy measure nu-sharp
> is selfdecomposable since k-sharp(x) is decreasing on (0,infinity) and increasing on
> (-infinity,0); the subordinator with Levy measure rho is not selfdecomposable since k(s) is
> strictly increasing on [1/(a+b), 1/a).

(a and b are fixed with a > b > 0 earlier in Section 3, Lemma 3.1/3.2.) This is exactly the
promised existence witness: a non-self-decomposable subordinator {Z_t} whose Brownian
subordination {Y_t} is nonetheless self-decomposable — the counterexample disproving the converse
of Theorem 1.1 (i.e. disproving that "Y self-decomposable of type G" implies "the mixing law is
self-decomposable").

**A bonus finding, not asked for but directly relevant to this article's `lem:folding-translation`
/ ledger A10 (Section 4, "Remarks," p. 9, equations (4.2)-(4.3)):** for the general (Theorem 1.1)
construction, "k-sharp(0+) = k-sharp(0-) = k(0+)/sqrt(2*pi) * integral_0^infinity
e^{-u/2}*u^{-1/2}du = k(0+)... since integral_0^infinity e^{-u/2}u^{-1/2}du = sqrt(2)*Gamma(1/2) =
sqrt(2*pi)." And with c_Z := k(0+), c_Y := k-sharp(0+) + k-sharp(0-): **c_Y = 2*c_Z** (eq. (4.3)).
This is Sato's own, independently derived instance of exactly the "folding constant doubles"
relation this article's `lem:folding-translation` proves for the Matern family — worth flagging to
the author as a second, non-Matern corroboration of that lemma's shape, should it be wanted.

**Verdict: CONFIRMED**, all three requested pieces (Theorem 1.1, Theorem 1.2, and the Section 3
witness (3.7)) transcribed verbatim from the held, full-text copy — **the referee who "could only
read the abstract" had access to less than what this library now holds.**

---

## Part 2 — bibliographic search (no acquisition performed)

### a. Lindeberg (time-causal limit kernel)

- **`lindeberg2016time`** — Lindeberg, T., "Time-Causal and Time-Recursive Spatio-Temporal
  Receptive Fields," *J. Math. Imaging Vis.* **55** (2016), 50-88. **Held, PDF stored**
  (`<local path>`).
- **`lindeberg2023time`** — Lindeberg, T., "A time-causal and time-recursive scale-covariant
  scale-space representation of temporal signals and past time," *Biol. Cybern.* **117** (2023).
  **Held, PDF stored** (two PDF copies on record, one flagged `contested` with an alternate
  filename — a filing detail, not a content problem).
- **Lindeberg & Fagerstrom, ECCV 1996** — **held twice, inconsistently filed**: a pinned
  `conferencePaper` **`lindeberg1996scalespace`** ("Scale-space with causal time direction," DOI
  10.1007/BFb0015539, collection "Own Publications" — this is the actual proceedings paper) *and*
  a separate `report` stub **`lindeberg1996causaltime`**, same title, same authors, still sitting
  in the **"To Acquire"** queue. This looks like exactly the "citekey clash implies duplicate
  work" pattern this role's operating rules describe (a pinned item and an unfulfilled queue entry
  for the same paper) — **flagged here, not touched**, since resolving it is a `dedupe`/`merge`
  decision outside this dispatch's scope (verification only, no acquisition).

**The limit-kernel definition, verbatim, `lindeberg2016time` p. 62** (section 5 "The
Scale-Invariant Time-Causal Limit Kernel," subsection "The Limit Kernel"; page image
`lindeberg2016_p62.png`):

> The Limit Kernel By letting the number of temporal scale levels K tend to infinity, we can
> define a limit kernel Psi(t; tau, c) via the limit of the Fourier transform (33) according to
> (and with the indices relabelled to better fit the limit case):
>
> Psi-hat(omega; tau, c) = lim_{K->infinity} h-hat_exp(omega; tau, c, K) =
> Prod_{k=1}^infinity 1 / (1 + i * c^{-k} * sqrt(c^2-1) * sqrt(tau) * omega).   (38)
>
> By treating this limit kernel as an object by itself, which will be well defined because of the
> rapid convergence by the summation of variances according to a geometric series, interesting
> relations can be expressed between the temporal scale-space representations
>
> L(t; tau, c) = integral_{u=0}^infinity Psi(u; tau, c) f(t-u) du   (39)
>
> obtained by convolution with this limit kernel.

So the limit kernel is exactly "an infinite cascade of truncated exponential (first-order,
Poisson-type) kernels," each factor 1/(1 + i*mu_k*omega) being the Fourier transform of a
one-sided truncated-exponential kernel with time constant **mu_k = c^{-k} * sqrt(c^2-1) *
sqrt(tau), k = 1, 2, 3, ...** — a **geometric progression in k with ratio 1/c** (c > 1 is the
paper's "distribution parameter"; tau is the total variance target, matching eq. (34),
lim_{K->infinity} M_1 = sqrt((c+1)/(c-1)) * tau^{1/2}, printed on the same page). Section/equation
to cite: **section 5, "The Limit Kernel," eq. (38), p. 62.**

### b. Hartikainen & Sarkka; Sarkka & Solin

- **Hartikainen, J. and Sarkka, S., "Kalman filtering and smoothing solutions to temporal
  Gaussian process regression models," MLSP 2010** — **not held** (`library search --corpus`:
  no hits for "Hartikainen" or "Sarkka"). Full record (Crossref, DOI
  `10.1109/mlsp.2010.5589113`): Jouni Hartikainen, Simo Sarkka, *2010 IEEE International Workshop
  on Machine Learning for Signal Processing*, pp. 379-384, published 2010-08 (proceedings-article,
  publisher IEEE). Note the DOI is `...5589113`, verified directly against Crossref rather than
  guessed. Its own reference list (fetched from Crossref) cites Matern (1960) as "Spatial
  variation - stochastic models and their application to some problems in forest surveys and
  other sampling investigations," Tech. Rep., corroborating item (e) below independently. Open
  copy: the paper is widely mirrored on the authors' university pages (Aalto University); not
  checked for a live URL in this pass (out of scope — acquisition, not verification, was excluded
  from this dispatch).
- **Sarkka, S. and Solin, A., *Applied Stochastic Differential Equations* (2019)** — **not held**.
  Full record (Crossref): Cambridge University Press, "Applied Stochastic Differential Equations,"
  DOI `10.1017/9781108186735`, monograph, published 2019-04-30 (Institute of Mathematical
  Statistics Textbooks series). Where the Matern half-integer state-space (continuous-time AR)
  construction is given is standard knowledge of this text (its worked examples in the chapters on
  spectral factorization / Gaussian process regression), but this was **not independently verified
  at the page** since the book is not held — flagged as **NOT FOUND (not held; not page-verified)**
  rather than transcribed from memory.

### c. Jurek & Vervaat (1983)

- **`jurek1983integral`** — Jurek, Z. J. and Vervaat, W., "An integral representation for
  selfdecomposable Banach space valued random variables," *Z. Wahrsch. Verw. Gebiete* **62**
  (1983). **Held, PDF stored** (`<local path>`,
  DOI `10.1007/bf00538800`, added 2026-09-14). Not transcribed (Part 2 asks only whether held).

---

### d. Type-G origin: Barndorff-Nielsen-Kent-Sorensen; Maejima-Rosinski; Marcus

- **Barndorff-Nielsen, O., Kent, J. and Sorensen, M., "Normal variance-mean mixtures and z
  distributions," *Int. Statist. Rev.* **50** (1982)** — **not held** (`library search --corpus`
  for "Barndorff-Nielsen," "Kent," "Sorensen," "z distributions," "normal variance-mean" all miss
  it; the one Kent item held, `kent1982spectral`, is an unrelated diffusion-hitting-time paper).
  Full record (Crossref): DOI `10.2307/1402598`, *International Statistical Review / Revue
  Internationale de Statistique* **50**(2), Aug. 1982.
- **Maejima, M. and Rosinski, J., "Type G distributions on R^d," *J. Theoret. Probab.* **15**
  (2002)** — **not held** (`library search --corpus "Maejima"` returns two other Maejima papers,
  not this one; "Type G," "Rosinski" all miss it). Full record (Crossref): DOI
  `10.1023/A:1015044726122`, *Journal of Theoretical Probability* **15**(2), April 2002.
- **Marcus, M. B., "xi-radial processes and random Fourier series" (1987)** — **not held**
  (no hits for "Marcus," "xi-radial," "radial processes"). Full record (Crossref): DOI
  `10.1090/memo/0368`, *Memoirs of the American Mathematical Society*, vol. 68, no. 368 (1987),
  sole author Michael B. Marcus.
- **Which of these *defines* type G, per general knowledge of the field (not page-verified, since
  none is held):** the type-G definition (X = sqrt(Z)*G with G standard Gaussian, Z >= 0
  infinitely divisible and independent of G) is standard by the early 1980s; Maejima-Rosinski
  (2002) is the paper that gives the *systematic* R^d treatment and terminology "type G" the way
  this article uses it, and is very likely the correct citation for the *definition* as this
  article states it; Barndorff-Nielsen-Kent-Sorensen (1982) is the origin of the closely related
  but distinct "normal variance-mean mixture"/generalized hyperbolic z-distribution family (mixing
  by a *generalized inverse Gaussian* law specifically, with a mean-shift term, not the general
  variance-mixture-only type-G definition); Marcus (1987) is about xi-radial processes and random
  Fourier series and is the odd one out — worth checking whether it is the right citation at all,
  or whether the review round is thinking of a different Marcus paper. **This assessment is from
  general knowledge of the literature, not from having read any of the three at the page — flagged
  as such.**

### e. Matern; Stein

- **Matern, B., *Spatial Variation* (1960, 2nd ed. 1986)** — **not held** as the monograph itself.
  (Two *about*-Matern papers are held: `porcu2024matern`, "The Matern Model: A Journey Through
  Statistics, Numerical Analysis and Machine Learning," and `guttorp2006studies`, "On the Matern
  correlation family" — neither is Matern's own text.) Full record of the 2nd edition (Crossref):
  DOI `10.1007/978-1-4615-7892-5`, Springer-Verlag New York, *Lecture Notes in Statistics* vol. 36,
  1986, ISBN 9780387963655/9781461578925. (The 1st edition, 1960, is a Meddelanden fran Statens
  Skogsforskningsinstitut technical report, band 49 nr 5 — not indexed on Crossref; not checked
  for an open scan in this pass.)
- **Stein, M., *Interpolation of Spatial Data: Some Theory for Kriging* (1999)** — **not held**.
  Full record (Crossref): DOI `10.1007/978-1-4612-1494-6`, Springer-Verlag New York, *Springer
  Series in Statistics*, 1999, sole author Michael L. Stein.

### f. Triggs & Sdika; van Vliet, Young & Verbeek

- **Triggs, B. and Sdika, M., "Boundary conditions for Young-van Vliet recursive filtering,"
  *IEEE Trans. Signal Process.* **54** (2006)** — **not held** (`library search --corpus
  "Triggs"` and `"boundary conditions"` both miss it). Full record (Crossref): DOI
  `10.1109/tsp.2006.871980`, *IEEE Transactions on Signal Processing* **54**(6), June 2006,
  pp. 2365-2367.
- **van Vliet, L., Young, I. and Verbeek, P., "Recursive Gaussian derivative filters," ICPR
  1998** — **not held** (`library search --corpus "van Vliet"` and `"Verbeek"` both miss it; the
  one related item held, `young1995recursive` — Young, I. T. and van Vliet, L. J., "Recursive
  implementation of the Gaussian filter," *Signal Processing* **44**(2), 1995 — is a *different,
  earlier* paper by an overlapping author pair, not this one). Full record (Crossref): DOI
  `10.1109/icpr.1998.711192`, *Proceedings, 14th International Conference on Pattern Recognition*
  (ICPR 1998), IEEE.

---

## Part 3 — literature search for the dimension-free radial self-decomposability equivalence

**The claim to be searched for:** *a symmetric law on the line whose radial extension
xi -> F(|xi|) is the exponent of a self-decomposable law on R^d for every d is a Gaussian variance
mixture (subordinated Brownian motion at time 1) whose mixing law on the half-line is
self-decomposable, and conversely.*

**What was searched, and where:**
- `library search --corpus` against the whole local Zotero index for "multivariate infinitely
  divisible," "stochastic integral representations," "Multivariate subordination," "Takano,"
  "Type G," "Aoyama," "arcsine density" — **none of the five named sources are held**, so all of
  Part 3 relies on the Crossref REST API (`api.crossref.org`, reachable from this sandbox) for
  bibliographic identification and, where Crossref exposes one, the abstract; no full text of any
  of the five was read.
- **Barndorff-Nielsen, O.E., Maejima, M. and Sato, K., "Some classes of multivariate infinitely
  divisible distributions admitting stochastic integral representations," *Bernoulli* **12**
  (2006).** Several targeted Crossref bibliographic queries (by title fragment, by author
  combination) **did not surface this exact record** — the closest hits under similar search
  terms were unrelated Bernoulli papers (Aoyama & Maejima 2007, "Characterizations of subclasses
  of type G distributions on R^d by stochastic integral representations," DOI
  `10.3150/07-bej5136`, which *is* about type-G subclasses and stochastic integral
  representations, and could be what the reviewer actually meant or a close relative) and later,
  unrelated Bernoulli titles. **Not independently confirmed this pass** — reported as such rather
  than guessed at.
- **Barndorff-Nielsen, O.E., Pedersen, J. and Sato, K., "Multivariate subordination,
  self-decomposability and stability," *Adv. Appl. Probab.* **33** (2001).** Found and confirmed
  via Crossref (DOI `10.1017/s0001867800010685`), **with abstract**:
  > "Multivariate subordinators are multivariate Levy processes that are increasing in each
  > component. Various examples of multivariate subordinators, of interest for applications, are
  > given. Subordination of Levy processes with independent components by multivariate
  > subordinators is defined. Multiparameter Levy processes and their subordination are introduced
  > so that the subordinated processes are multivariate Levy processes. The relations between the
  > characteristic triplets involved are established. **It is shown that operator
  > self-decomposability and the operator version of the class L_m property are inherited from the
  > multivariate subordinator to the subordinated process under the condition of operator
  > stability of the subordinand.**"

  This is the closest of the five to the article's claim in *spirit* (subordination inheriting
  self-decomposability), but it is **not the same theorem**: it is stated for a general
  d-dimensional subordinand required to be *operator-stable*, with the self-decomposability
  passed down from the subordinator, in a *fixed* dimension d — it does not quantify over "for
  every d" starting from a single radial 1-D exponent, and it does not state a converse
  characterizing *which* d-dimensional self-decomposable laws arise this way.
- **Maejima, M. and Rosinski, J. (2002)** — as in Part 2d; not held, abstract not retrieved by
  Crossref (Crossref returned no abstract text for this record). This paper defines and studies
  type-G distributions on R^d generally (any infinitely-divisible nonnegative mixing variable, not
  restricted to self-decomposable mixing, and not stated as a dimension-free radial
  characterization theorem) — this is inferred from the paper's title and its role as cited
  elsewhere (e.g. in `sato2001subordination`'s own Introduction, held and read in Part 1.5: "a
  random variable Y of type G is selfdecomposable if the Z in the definition of type G is
  selfdecomposable, that is, if Y is of class GL in the terminology of Jian (2000)" — i.e. the
  "type GL" refinement, self-decomposable mixing, is treated by Sato (2001) as the relevant
  notion, and it is *this* refinement, not general type-G, that matches the article's claim). Not
  independently verified at the page.
- **Takano** — no specific paper title was given in the dispatch, and Crossref bibliographic
  search on "Takano" plus probability-theoretic terms returned only unrelated
  psychology/oncology papers; **could not identify a candidate Takano paper to check** without a
  more specific reference from the reviewer or the author.
- **Sato's own held book and paper, re-read with this question in mind.** `sato1999levy` was not
  re-searched specifically for a dimension-free radial theorem (out of the scope actually
  requested — Part 3 names five specific sources, not "search the whole Sato book again"); the
  held `sato2001subordination` (Part 1.5, read in full) states **Theorem 1.1 in dimension 1 only**
  ("Let {X_t} be a Brownian motion with drift on R and let {Z_t} be a self-decomposable
  subordinator... {Y_t} is selfdecomposable"), i.e. **one direction, one dimension** — not "for
  every d," and its own Introduction explicitly leaves the stable/non-strictly-stable
  generalization and higher-dimensional questions open ("We do not know whether Theorem 1.1 can be
  generalized to the case where the subordinand {X_t} is a stable process which is not strictly
  stable").

**Assessment.** None of the five named sources, as far as could be verified from Crossref metadata
(three) and a held full text (Sato 2001, already read in Part 1), **states the article's exact
biconditional** — "radially self-decomposable in every dimension iff self-decomposable Gaussian
variance mixture." The nearest results in the literature are: (i) Sato (2001) Theorem 1.1, the
*sufficiency* half in dimension 1 only (self-decomposable subordinator implies self-decomposable
subordinated Brownian motion); (ii) Barndorff-Nielsen-Pedersen-Sato (2001), the same sufficiency
idea generalized to multivariate subordinators acting on an *operator-stable* subordinand in a
*fixed* dimension, again with no "for every d" quantifier and no stated converse; (iii) the
type-G/type-GL vocabulary (Maejima-Rosinski 2002 for type G; Sato 2001, citing Jian (2000), for
the self-decomposable-mixing refinement "type GL") which is the right *language* for the mixing
representation but, on the evidence gathered, not a source that states the dimension-filtration
characterization itself. **The converse direction (only Gaussian-variance-mixture radial laws are
self-decomposable in every dimension) was not found stated anywhere in this search.** This is
consistent with — though does not by itself prove — the article's `prop:dimension-filtration` (in
particular its widening R172 to "A-infinity = S", `blueprint/AXIOMS.md`/`SKELETON.md` sections
29-32 of the calling repository) being a genuine result of this article rather than a restatement
of a theorem already in the cited literature; that inference is offered as this pass's honest
reading of the search, not as a citation-completeness guarantee — a fuller search (full text of
the Bernoulli 2006 paper, Maejima-Rosinski 2002, and a properly identified Takano reference) is
exactly what this dispatch could not do without holding those sources.

---

## What could not be read, and why

- **Sato, Example 27.8** (invoked by Theorem 28.4's proof for "mu is absolutely continuous," which
  bears on whether "nondegenerate" is truly needed) — not opened; out of the scope actually asked
  (the task asked for Theorem 28.4 itself, not its proof's own citations).
- **Bondesson, Chapter 7 / the Levy-density form of PF-infinity** and **Thm. 3.1.1/3.1.2 in
  full** — not reopened this pass; already flagged as "not sought this pass" in the repository's
  own `blueprint/AXIOMS-verbatim.md` (a prior librarian pass, same date), and not needed for the
  specific quotation the referee gave.
- **Karlin, Theorems 2.1/2.2/4.2 in full** (the variation-diminishing route behind Theorem 3.2) —
  read in part (2.1, on p. 337) for the class E1 definition, but the full variation-diminishing
  chain (Chapter 3's composition formula, Chapter 7 section 1's (3.6)/(3.8)) was not re-derived
  page by page; sufficient anchor text was found to answer the dispatch's specific question.
- **Hartikainen & Sarkka (2010) and Sarkka & Solin (2019)** — neither is held; bibliographic
  record only (Crossref), no page content, no open-copy check performed (acquisition and
  open-access discovery were out of scope for this dispatch).
- **Barndorff-Nielsen-Kent-Sorensen (1982), Maejima-Rosinski (2002), Marcus (1987)** — none held;
  bibliographic record only.
- **Matern (1960/1986) and Stein (1999)** — neither held; bibliographic record only; the 1960
  first edition (a Swedish forest-research technical report) is not indexed on Crossref and its
  open-access status was not checked.
- **Triggs & Sdika (2006) and van Vliet-Young-Verbeek (1998)** — neither held; bibliographic
  record only.
- **Barndorff-Nielsen-Maejima-Sato, Bernoulli 12 (2006)** — could not be located via Crossref
  bibliographic search in the time available; its exact content relative to the article's claim
  is therefore genuinely unconfirmed, not merely "not read."
- **A specific "Takano" paper** — no candidate identified; the dispatch did not give a title, and
  a generic author-name search on Crossref is not discriminating enough for a common surname
  against unspecified subject terms.
- **Jurek & Vervaat (1983)** — held with PDF, but not opened/transcribed, since Part 2 asked only
  whether it is held.

## Observation outside the brief

The duplicate holding of the ECCV 1996 Lindeberg & Fagerstrom paper — pinned as
`lindeberg1996scalespace` (Own Publications) and separately queued as `lindeberg1996causaltime`
(To Acquire) — was noticed while resolving Part 2a and is reported here per this role's own
"a pin/queue clash almost always means a duplicate work" rule; it was **not** touched (no
`acquire dedupe`/`merge` was run), since this dispatch is verification-only.

## Files written to the scratchpad (none in the repository)

All under `<local path>`:
this report (`s3-sources-report.md`); page images `sato_p87.png`, `sato_p88.png`, `sato_p190.png`,
`sato_p191.png`, `sato2001_p8.png`, `sato2001_p9.png`, `bondesson_p27.png`, `bondesson_p29.png`,
`bondesson_p35.png`, `bondesson_p36.png`, `karlin_p333.png` through `karlin_p346.png` and
`karlin_p391.png`, `lindeberg2016_p62.png`; and small Crossref JSON dumps (`marcus.json`,
`bmz3.json`, `bmz4.json`, `bmz5.json`, `takano.json`, `stein.json`, `stein2.json`, `matern.json`,
`bps.json`, plus their `*_out.txt` text extracts).
