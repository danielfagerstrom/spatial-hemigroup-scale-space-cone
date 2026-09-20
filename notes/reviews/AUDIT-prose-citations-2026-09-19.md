# Citation audit -- paper-b/ prose (spatial-hemigroup-scale-space, module B)

Scope: the 53 page/theorem/formula-anchored citations extracted from paper-b/0*.tex into
prose-citations.md. Per instructions, a citation that is only a restatement of a
blueprint/AXIOMS.md ledger anchor -- with the ledger entry independently audited by
another librarian in parallel -- is skipped and marked so below, to avoid duplicated work.
Everything else is checked against a held copy (text or page image where the text layer is
unreliable).

Verdicts used: OK, OK (note) (matches, with a small nuance worth recording),
WEAKER/STRONGER, NOT FOUND, NOT HELD / COULD NOT READ.

---

## Section 1 -- Introduction (01-introduction.tex)

### 1. sato1999levy, Def. 15.1, p. 90 -- self-decomposability, informal gloss
Our sentence: the admissible kernels are the symmetric self-decomposable laws: those of
a random displacement that is, for every contraction ratio, a contracted copy of itself plus an
independent remainder.
Source, verbatim (p. 90): mu on R^d is selfdecomposable if, for any b > 1, there is a
probability measure rho_b with mu-hat(z) = mu-hat(b^-1 z) rho_b-hat(z).
Verdict: OK. The prose is an accurate informal paraphrase (contraction by b^-1, independent
remainder rho_b).

### 2-3, 18-19. dlmf2026, Section 6.2 (the entire cosine integral Cin) -- four separate citations
(01-introduction.tex, the Cin exponent and its growth; 03-cone.tex, the integral definition and
growth rates; 03-cone.tex again, the Euler-constant identity Cin(z) = gamma_E + log z - Ci(z)).
Verdict: NOT HELD. The librarys only DLMF artifacts are
dlmf2026-ch10-sec10.30.md and dlmf2026-ch10-secs10.21-10.25-10.32.md -- both Chapter 10
(Bessel functions). Nothing for Chapter 6 (Exponential, Logarithmic, Sine and Cosine
Integrals) is held, under this citekey or any other in the library. I could not read Section 6.2
to check the Cin definition, its small-z behaviour (z^2/4), its large-z behaviour (log z),
or the Euler-constant identity. This affects every dlmf2026 Section 6.2 occurrence in
01-introduction.tex and 03-cone.tex (the Section 10.25(ii)/10.30 citations in 05-corners.tex are
a different section and are held -- see item 44 below). Not a math error, just an unheld
source; flagged for the maintainer/next acquisition rather than for the author to fix.

### 4. deriche1993recursively, young1995recursive -- general historical mention
No specific formula attributed; the kind of filter long used to approximate the Gaussian.
Verdict: OK (general framing, both items held and consistent with their abstracts).

### 5-10, 21. Section 1.1 "What it rests on" (trust-base table) and 03-cone.tex restatement of
the origin-singularity regimes -- schilling2012bernstein Thm. 1.4 p. 3; sato1999levy Thm. 25.3
p. 159 and Thm. 26.1 p. 168; sato1999levy Thm. 28.4 p. 191 and Thm. 53.8 pp. 410-411 (incl.
(53.25)/(53.28)/(53.30)); schilling2012bernstein Thm. 13.14 p. 212; bondesson1992generalized
Thm. 3.1.5 pp. 34-35; feller2009introduction Vol. 2 Section XIII.1 Thm. 2 p. 431.
SKIPPED -- ledger duplicates. Each is the entrys own statement, word for word, of ledger
entries A11, A13/A14, A10, A23, A24 respectively (blueprint/AXIOMS.md), which the other
librarians pass covers, including the page-anchor fix to A10 recorded there on 2026-09-19
(row R171, the slowly-varying factor). I independently re-read Sato pp. 159, 168, and the A10
passage anyway while chasing other citations (see items 41-42, 51 below) and found nothing
inconsistent with the ledgers account.

### 11. burgeth2005bessel -- the Bessel scale space, dilate the kernels at a fixed order
Source, verbatim (abstract, p. 84): the family of inhomogeneous pseudodifferential
equations (I - tau*Delta)^(t/2) u = f with tau >= 0 and scale parameter t >= 0 ... R^n_{t,tau}.
Verdict: OK. Two-parameter family (order t, range tau) matches dilate the kernels at a
fixed order.

### 12. burgeth2005relativistic -- exponent sqrt(omega^2+m^2) - m
Source, verbatim (abstract, p. 1): the linear parabolic pseudodifferential operator
sqrt(-Delta+m^2) - m, ... {Q^m_t | 0<=m,t} ... a continuous transition from the Poisson
scale-space (m=0) to the identity operator (m -> infinity).
Verdict: OK. Exact match (the operator symbol is sqrt(omega^2+m^2) - m).

### 13, 49. duits2004axioms; felsberg2004monogenic -- Poisson/alpha-scale-space framing, general
Verdict: OK (both held and consistent with the specific checks in items 44-46 and 53-54 below).

## Section 2 -- the line paper restated (02-line-paper.tex)

### 15. sato1999levy, Cor. 15.11, p. 95 -- the folding factor of two
Our sentence: a two-sided Levy density written h(|x|)/|x|, the form of Sato Cor. 15.11,
p. 95, has folded profile k = 2h.
Source, verbatim (p. 95): mu on R is s.d. iff
mu-hat(z) = exp[-(1/2)Az^2 + i*gamma*z + int(e^{izx}-1-izx*1_{[-1,1]}(x)) k(x)/|x| dx], k
increasing on (-infinity,0), decreasing on (0,infinity).
Verdict: OK. For a symmetric law the two-sided k is k(x)=h(|x|) for a single
h:(0,infinity)->[0,infinity); folding the two half-line contributions of the sources two-sided
measure k(x)dx/|x| onto (0,infinity) doubles the density, giving folded profile 2h. This is
exactly the factor of two the article itself flags (the one place a constant is easily lost)
-- checked independently here and it is the right factor. (Cross-check: sato2001subordination,
p. 9, (4.3), states the same doubling, c_Y = 2*c_Z, for an analogous folding -- see item 40.)

### 16-17. sato1999levy Thm. 27.13 p. 181; yamazato1978unimodality Thm. 1 p. 523
SKIPPED -- ledger duplicates (A8, A9); the restatement here is word-for-word the ledgers.

## Section 3 -- the cone (03-cone.tex)

### 20. fagerstrom2026hemigroup -- comparison to the causal cone, general
Verdict: OK (general framing against the authors own prior article; not independently
re-derived here).

## Section 4 -- the bridge (04-bridge.tex)

### 22. sato1999levy, Theorem 30.1, p. 197 -- Bochners subordination
Source, verbatim (p. 197): THEOREM 30.1. Let {Z_t} be a subordinator ... Let {X_t} be a
Levy process on R^d ... Define Y_t = X_{Z_t}. Then {Y_t} is a Levy process, with (30.5)-
(30.9) (spilling onto p. 198) giving the transform and triplet of Y.
Verdict: OK. The theorem opens on p. 197 as cited; that some of its display equations
(including (30.8), which the task singled out) print on p. 198 is normal -- a theorem is cited
at its opening page. The construction described (run a Brownian motion for a random causal
delay) is exactly (30.1)-(30.4), and since Brownian motion has a symmetric law at every t, the
subordinate Y_t is a symmetric mixture and hence symmetric, matching the sentence that follows.

### 24-27, 29, 34. schilling2012bernstein -- Def. 3.1 and Thm. 3.2 p. 21 (Bernstein function,
gloss and representation); Thm. 3.7(iii) (no page) and Thm. 3.7 p. 27 (e^{-f} completely
monotone); Thm. 1.4 p. 3 (Bernstein theorem); Thm. 13.14 p. 212 (the radial theorem, given in
full).
Verdict: OK, all verified verbatim against the held copy.
- p. 21: A function f:(0,infinity)->R is a Bernstein function if f is C^infinity, f(lambda)>=0
  ... and (-1)^(n-1) f^(n)(lambda)>=0 (Def. 3.1), and Thm. 3.2 representation
  f(lambda)=a+b*lambda+int(1-e^{-t*lambda})mu(dt), unique triplet -- matches the paper gloss
  and its "conversely every Bernstein function vanishing at the origin has such a
  representation" (with a=0 for vanishing at the origin, b folded into the drift).
- p. 27: Thm. 3.7, f in BF iff e^{-uf} in CM for every u>0 -- matches (iii) cited without
  page, and with page for the general statement.
- p. 3: Thm. 1.4 (Bernstein) -- matches exactly, word for word, the paper statement.
- p. 212: Thm. 13.14 (Schoenberg; Bochner), f:(0,infinity)->[0,infinity) is a Bernstein
  function iff, for all d in N, xi -> f(|xi|^2) on R^d is continuous and negative definite --
  the paper own display of the radial theorem is this sentence essentially verbatim.

### 28, 37. halgreen1979self, Section 2, pp. 14-16 -- inverse-gamma delay is self-decomposable
(pure variance-mixture case)
Source, verbatim (p. 14): As the second result of the present note it is shown that for a
variance mixture, i.e. for beta=0, self-decomposability of the distribution of sigma^2 implies
self-decomposability of the mixture. (p. 15-16): for beta=0 the proof is four lines (the
self-decomposability of phi follows simply from the self-decomposability of zeta) appearing on
p. 15; the harder, unrestricted-beta case (needing the GGC hypothesis) is proved across pp. 15-16.
Verdict: OK, with a small precision note: the announcement is on p. 14 as cited, and the
proof of the pure-mixture case the paper actually uses is self-contained on p. 15 (four lines);
"proves on pp. 15-16" folds in the harder general-beta case that follows immediately after,
which is not wrong but is slightly more generous than strictly needed. Not misleading.

### 30-33, 35. sato1999levy Thm. 8.1 pp. 37-38; Def. 15.1/Prop. 15.5/Thm. 15.10 pp. 90/93/95;
Prop. 15.5 p. 93 (again); Thm. 24.11 p. 153 and Remark 21.6 p. 138.
SKIPPED -- ledger duplicates (A3, A7; the last pair matches word for word the addendum the
other librarians ledger pass added to A7 on 2026-09-19).

### 32. schilling2012bernstein, Prop. 4.4, p. 36 -- negative definite in the kernel sense
SKIPPED -- ledger duplicate (A2); independently re-read anyway (p. 36: f negative definite
iff f(0)>=0 ... iff e^{-tf} positive definite for all t>0) -- matches.

### 36. steutel2004infinite, (2.7), p. 345 -- the type G criterion
Source, verbatim (p. 345): phi(u) = int_{R+} exp[-(1/2)theta*u^2] dG(theta) =
G-hat((1/2)u^2) ... a variance mixture of normal distributions ... infinitely divisible if the
mixing function G is infinitely divisible. (Prop. 2.2, eq. (2.7).)
Verdict: OK, exact match to the Gaussian variance mixtures with an infinitely divisible
mixing law, the type G laws.

### 38. barndorffnielsen1977infinite, pp. 309-311 -- infinite divisibility of the mixture, R^r
Source, verbatim (p. 311): if the normal distribution is r-dimensional (r=1,2,...) ...
and if sigma^-2 is endowed with an arbitrary distribution ... this is infinitely divisible
provided the distribution of sigma^-2 is infinitely divisible.
Verdict: OK, exact match, and the general-r claim is genuinely on p. 311 (p. 309 gives the
setup and the r-dimensional variation domain).

### 39. bondesson1992generalized, Thm. 7.3.1, pp. 115-116 -- symmetric EGGC equals GGC via s^2/2
Source, verbatim (p. 115): Theorem 7.3.1. If phi is the mgf of a GGC, then
psi(s)=phi(s^2/2) is the mgf of a symmetric EGGC. Conversely, if psi(s) is the mgf of a
symmetric EGGC, then psi(s)=phi(s^2/2) for some phi in T [the GGC class].
Verdict: OK, exact match, proved in both directions as stated.

### 40. sato2001subordination, Theorem 1.2 and Lemma 3.1
Source, verbatim (p. 3): Theorem 1.2. There is a selfdecomposable random variable Y of
type G for which one cannot find a nonnegative selfdecomposable Z and a standard Gaussian X
satisfying (1.4) and (1.5). (p. 7): Lemma 3.1. Suppose that Y satisfies (1.4) and (1.5)
with ... Z. Then the distribution of Z is determined by the distribution of Y.
Verdict: OK, both exact matches -- constructs a self-decomposable law of type G that is the
Gaussian mixture of no self-decomposable law on the half-line, the mixing law being determined
by the mixture (his Lemma 3.1) is precise.

## Section 5 -- the corners (05-corners.tex)

### 41-42. sato1999levy Theorem 25.3 p. 159 (submultiplicative-weight form), Theorem 26.1
p. 168 (tail order, both directions)
Source, verbatim (p. 159): THEOREM 25.3 (g-Moment). Let g be a submultiplicative, locally
bounded, measurable function... (p. 168): with c = inf{a>0 : S_nu subset {|x|<=a}}, for a<1/c,
P[|X_t|>r] = o(e^{-ar*log(r)}), and for a>1/c the same probability, divided by e^{-ar*log(r)},
diverges.
Verdict: OK. Both theorems match the section description exactly, including the second at
its divergence branch and the borderline order e^{-|x|log|x|/tau} (tau the jump radius,
a=1/tau the critical rate).

### 43. fischer2025variance -- density (1.1), char. fn. (2.12), self-decomposability Section
2.3, p. 6
Source, verbatim: (1.1) p(x) = 1/(sigma*sqrt(pi)*Gamma(r/2)) e^{theta(x-mu)/sigma^2}
(|x-mu|/(2*sqrt(theta^2+sigma^2)))^{(r-1)/2} K_{(r-1)/2}(sqrt(theta^2+sigma^2)/sigma^2 |x-mu|);
(2.12) phi(t)=e^{i*mu*t}(1-2i*theta*t+sigma^2*t^2)^{-r/2}; p. 6: It is immediate from the
representation (2.15) (see Sato Cor. 15.11) that the VG(r,theta,sigma,mu) distribution is
self-decomposable.
Verdict: OK, exact match on all three sub-citations. Setting theta=0, mu=0, r=2*gamma,
sigma=t in (1.1) reproduces the paper own Matern density formula exactly; the same
substitution in (2.12) gives (1+t^2*omega^2)^{-gamma}; the self-decomposability sentence is on
p. 6 as cited.

### 44. dlmf2026, Section 10.25(ii), (10.25.3) -- Bessel K_nu large-z asymptotic
Source, verbatim (held, dlmf2026-ch10-secs10.21-10.25-10.32.md): (10.25.3)
K_nu(z) ~ sqrt(pi/(2z)) e^{-z} as z -> infinity.
Verdict: OK, and held (unlike Section 6.2 -- see item 2 above). Plugging this into the Matern
density K_{gamma-1/2}(|x|/t) factor reproduces the stated tail
phi_t(x) ~ c_gamma * t^{-gamma} * |x|^{gamma-1} * e^{-|x|/t} exactly (checked by direct
substitution).

### 45. abramowitz1964handbook, Section 9.7, 9.7.2, p. 378
Source, verbatim (page image, since the scan text layer is garbled): 9.7.2
K_nu(z) ~ sqrt(pi/2z) e^{-z}{1 + (mu-1)/(8z) + ...}.
Verdict: OK. Same leading term as DLMF (10.25.3), held and correctly cited.

### 46-47. schilling2012bernstein Theorem 1.4 p. 3; feller2009introduction Vol. 2 Section
XIII.4 Theorems 1 and 1a, pp. 439-440 -- Bernstein theorem, again
Source, verbatim (p. 439-440): Theorem 1. A function phi on (0,infinity) is the Laplace
transform of a probability distribution F, iff it is completely monotone, and phi(0)=1.
Theorem 1a. The function phi ... is completely monotone iff it is of the form
phi(lambda)=int e^{-lambda*x} F(dx), F not necessarily finite.
Verdict: OK, both theorems are on pp. 439-440 exactly as cited.

### 48. bondesson1992generalized, Chapter 7, p. 105, (7.1.1)-(7.1.2) -- EGGC definition
Source, verbatim (p. 105): phi(s) = int e^{sx} F(dx) = exp{bs + c*s^2/2 +
int(log(t/(t-s)) - s*t/(1+t^2))U(dt)}, b in R, c>=0, U a nonnegative measure with the stated
integrability -- labelled (7.1.1)-(7.1.2) in the source (OCR renders the labels as (9.1.1)
but the surrounding numbering and the chapter own cross-references confirm (7.1.1)-(7.1.2)).
Verdict: OK.

### 50. halgreen1979self, Section 2, pp. 14-15, at lambda=-a<0, chi=1, psi=0; his (5) and
Grosswald function
Source, verbatim (p. 15): Grosswald g_nu(x) = 2{pi^2*x*(J_nu^2(sqrt(x))+Y_nu^2(sqrt(x)))}^-1,
and the canonical-measure density from (5) via the integral representation
zeta_nu(t) = int (t+x)^-1 g_nu(x) dx.
Verdict: OK. The Grosswald function is transcribed correctly (matches character for
character against the page image); the parameter reading lambda=-a, chi=1, psi=0 correctly
targets the inverse-gamma boundary case of the GIG family (per the variation domain stated in
Barndorff-Nielsen and Halgreen 1977, p. 309: lambda<0 allows psi=0, giving the reciprocal of a
[gamma] variate).

### 51. sato1999levy, Theorem 14.14, p. 86 -- the symmetric stable laws
Source, verbatim (p. 86): THEOREM 14.14. A non-trivial probability measure mu on R^d is
rotation invariant and alpha-stable with 0<alpha<2 if and only if mu-hat(z)=e^{-c|z|^alpha}
with c>0. ... If mu is rotation invariant and 2-stable, then Theorem 14.1 combined with
[rotation invariance] leads to (14.23) with alpha=2.
Verdict: OK (note). The article range 0 < alpha <= 2 is correct for the page, but the
numbered theorem own boxed statement is 0 < alpha < 2; the alpha=2 (Gaussian) case is folded
in by the proof, one paragraph down, via a cross-reference to Theorem 14.1, not by Theorem
14.14 itself. Harmless -- the citation lands on the right page and the full range is genuinely
established there -- but a reader checking Theorem 14.14 alone would find only 0<alpha<2
boxed.

### 52. pedersen2005alpha -- general citation, stable Levy motions and natural images
Verdict: OK (general; consistent with the paper title and abstract, not independently
re-derived in depth).

## Section 6 -- the generator (06-generator.tex)

### 53. sato1999levy, Theorem 17.5, pp. 108-109 -- the background driving process
Our sentence: A self-decomposable law is the limit law of a process of Ornstein-Uhlenbeck
type, its exponent being int_0^infinity psi(e^{-s}*omega)ds for the exponent psi of a Levy
process ... and differentiating that representation gives psi = omega*F-prime = B.
Source, verbatim (p. 108): THEOREM 17.5. Fix c>0. (i) If mu [the BDLP law] satisfies (17.11),
the process of O-U type ... generated by (G,nu,beta,c) has a limit distribution p with
(17.12) p-hat(z) = exp[int_0^infinity psi(e^{-c*s}*z)ds].
Verdict: WEAKER/STRONGER (a sign, worth the author eye). Writing the paper kernel at
scale 1 as mu-hat(omega)=e^{-F(omega)} and matching it to (17.12) at c=1 (the paper own
canonical gauge): -F(omega) = int_0^infinity psi(e^{-s}*omega)ds. Substituting u=e^{-s}*omega
gives int_0^infinity psi(e^{-s}*omega)ds = int_0^omega psi(u)/u du, so
F(omega) = -int_0^omega psi(u)/u du, hence omega*F-prime(omega) = -psi(omega), i.e.
psi = -omega*F-prime = -B, NOT psi = omega*F-prime = B -- if psi in the sentence denotes
Satos own exponent exactly as printed in (17.12) (the convention E[e^{izX_1}]=e^{psi(z)}, so
psi<=0 for a real symmetric zero-drift process, matching -B<=0). The stated identity psi=B is
correct only under the opposite sign convention for the exponent psi of a Levy process (i.e.
if the paper silently means -psi_Sato, matching its own habit of writing every kernel exponent
with a leading minus, e^{-F}). That reading is plausible and probably intended -- but the
sentence never states the sign convention for this one, unlabelled use of psi, so a reader
checking (17.12) literally will find the opposite sign. Worth a one-clause fix (for the exponent
psi such that the background driving process has transform e^{-psi}, or similar), not a
substantive error in the mathematics (the operator symbol B itself, and everything downstream
of it, is unaffected -- this is purely about which sign is written next to a symbol psi that is
never used again in the paper).

### 54. duits2004axioms, p. 288, (66) -- the alpha-scale-space equation
Source, verbatim (p. 288): (66) du/ds = -(-Delta)^alpha u (0<alpha<1),
lim_{s->0+} u(x,s)=f(x).
Verdict: OK (note). The paper generator -(-Delta)^{alpha-prime}, 0<alpha-prime<=1 includes
the closed endpoint alpha-prime=1; the cited equation (66) is stated for the open interval
0<alpha<1 only (alpha=1 is the ordinary Laplacian/heat equation, treated by the source as the
trivial case outside this family, not part of (66) itself). Minor and inconsequential -- the
paper own alpha-prime=1 case is the Gaussian, established independently, not read off (66)
-- but the endpoint does not match if (66) alone is what is being cited.

## Section 7 -- the algorithm (07-implementation.tex)

### 55-56. bondesson1992generalized Theorem 3.1.5 pp. 34-35 with def. (3.1.1)-(3.1.2) p. 29;
feller2009introduction Vol. 2 Section XIII.1 Theorem 2 p. 431 -- the closure/continuity
theorems, again
Verdict: OK, verified verbatim (as for items 8-9 above, but here independently re-read in
context): p. 29 gives the GGC definition (3.1.1)-(3.1.2); pp. 34-35 give Theorem 3.1.5 (Closure
theorem: weak limits of GGCs are GGCs, Thorin measures converge vaguely on (0,infinity) per the
reformulation clause (i)); p. 431 gives Feller Vol. 2 continuity theorem for Laplace
transforms.

### 57, 61. deriche1993recursively, eq. (38), p. 12 -- the fourth-order design
Note on the held copy: the PDF own page numbers do not match the printed ones for this
scan (printed p. 12 is at PDF index 14, an offset of 2; "library page --printed 12" without an
explicit --offset lands on the PDF page whose printed header reads 10). Re-fetched at the
correct offset.
Source, verbatim (printed p. 12, eq. (38)):
g_a(x) = (1.68*cos(0.6318*x/sigma) + 3.735*sin(0.6318*x/sigma))*e^{-1.783*x/sigma}
 - (0.6803*cos(1.997*x/sigma) + 0.2598*sin(1.997*x/sigma))*e^{-1.723*x/sigma}, the 4th order
IIR.
Verdict: OK. Matches fits a sum of two damped oscillations and the poles the paper quotes
in Section 7.6, 1.783 +/- 0.6318i and 1.723 +/- 1.997i (read directly off the two exponential
rates and the two angular rates in (38)).

### 58. lindeberg1990scalespace -- the generating-function classification, excluded factor
Note on the held copy: the text layer is letter-spaced/garbled (unusable for grep); read from
page images instead.
Source, verbatim (p. 11, Theorem 2): An infinite sequence {K(n)} is a normalized Polya
frequency sequence iff its generating function phi_K(z) = sum K(n)z^n is of the form
phi_K(z) = c*z^k*e^{(q_{-1}z^{-1}+q_1*z)} * prod_i (1+alpha_i*z)(1+delta_i*z^{-1}) /
[(1-beta_i*z)(1-gamma_i*z^{-1})], with alpha_i,beta_i,gamma_i,delta_i >= 0 and
beta_i,gamma_i<1.
Verdict: OK. The paper claim that the classification allows the factors 1/(1-beta*z) and
1/(1-gamma*z^-1) is exactly the denominator of (16); and a numerator factor (1-p_s*z^{-1})
(positive real zero) is indeed excluded, since the theorem numerator factors are only of the
form (1+alpha*z)(1+delta*z^{-1}) (zeros at negative reals only).

### 59. burt1983laplacian -- a pyramid in the sense of multiresolution practice, general
Verdict: OK (general; not independently re-derived).

### 60. young1995recursive, Table 1, p. 141 -- the poles
Note on the held copy: this scan has no text layer at all (text quality: none) and uses raw
PDF index for printed pages; printed p. 141 is at PDF index 3 (printed p. 139 = PDF index 1).
Source, verbatim (Table 1, p. 141): poles of G_L(s): s_0=-1.1668/q,
s_1=(-1.10783+1.40586j)/q, s_2=(-1.10783-1.40586j)/q (and the mirrored signs for G_R).
Verdict: OK, exact match to the poles 1.1668 and 1.10783 +/- 1.40586 i, in units of
1/sigma (q plays the role of sigma). The paper derived profile
2*e^{-1.1668*x} + 4*e^{-1.10783*x}*cos(1.40586*x) follows correctly from these poles via the
k(x)=2*sum(e^{-theta_i*x}) identity used elsewhere in the same section (Eulers formula on the
complex pair).

## Section 8 -- conclusions (08-conclusions.tex)

### 62. fagerstrom2026hemigroup -- Bochner subordination maps the causal theory into the
spatial one, general
Verdict: OK (general; restates the bridge already checked in Section 4).

---

## Summary table

| # | File | Citekey | Anchor | Verdict |
|---|------|---------|--------|---------|
| 1 | 01-intro | sato1999levy | Def. 15.1 p.90 | OK |
| 2 | 01-intro | dlmf2026 | Section 6.2 | NOT HELD |
| 3 | 01-intro | deriche1993recursively, young1995recursive | (general) | OK |
| 4-9,21 | 01-intro/03-cone | schilling2012bernstein / sato1999levy / bondesson1992generalized / feller2009introduction | (trust-base table entries) | SKIPPED (ledger dup) |
| 10 | 01-intro | sato1999levy | (53.25),(53.28) p.411 | SKIPPED (ledger dup; spot-checked, OK) |
| 11 | 01-intro | burgeth2005bessel | (general) | OK |
| 12 | 01-intro | burgeth2005relativistic | (general) | OK |
| 13 | 01-intro | duits2004axioms | (general) | OK |
| 14 | 01-intro | felsberg2004monogenic | (general) | OK |
| 15 | 02-line-paper | sato1999levy | Cor. 15.11 p.95 | OK |
| 16-17 | 02-line-paper | sato1999levy / yamazato1978unimodality | Thm.27.13 p.181 / Thm.1 p.523 | SKIPPED (ledger dup) |
| 18-19 | 03-cone | dlmf2026 | Section 6.2 (x2) | NOT HELD |
| 20 | 03-cone | fagerstrom2026hemigroup | (general) | OK |
| 22 | 04-bridge | sato1999levy | Thm. 30.1 p.197 | OK |
| 23 | 04-bridge | fagerstrom2026hemigroup | Thm. 7.3 | OK (not deep-checked) |
| 24-27,29,34 | 04-bridge | schilling2012bernstein | Def.3.1/Thm.3.2 p.21, Thm.3.7(iii)/p.27, Thm.1.4 p.3, Thm.13.14 p.212 | OK |
| 28,37 | 04-bridge | halgreen1979self | Section 2 pp.14-16 | OK (note: pure-mixture proof is on p.15 alone) |
| 30-31,33,35 | 04-bridge | sato1999levy | Thm.8.1 pp.37-38; Def.15.1/Prop.15.5/Thm.15.10; Prop.15.5 p.93; Thm.24.11 p.153 and Rem.21.6 p.138 | SKIPPED (ledger dup) |
| 32 | 04-bridge | schilling2012bernstein | Prop.4.4 p.36 | SKIPPED (ledger dup; spot-checked, OK) |
| 36 | 04-bridge | steutel2004infinite | (2.7) p.345 | OK |
| 38 | 04-bridge | barndorffnielsen1977infinite | pp.309-311 | OK |
| 39 | 04-bridge | bondesson1992generalized | Thm.7.3.1 pp.115-116 | OK |
| 40 | 04-bridge | sato2001subordination | Thm.1.2, Lem.3.1 | OK |
| 41-42 | 05-corners | sato1999levy | Thm.25.3 p.159, Thm.26.1 p.168 | OK |
| 43 | 05-corners | fischer2025variance | (1.1), (2.12), Section 2.3 p.6 | OK |
| 44 | 05-corners | dlmf2026 | Section 10.25(ii), (10.25.3) | OK (held) |
| 45 | 05-corners | abramowitz1964handbook | Section 9.7, 9.7.2, p.378 | OK |
| 46-47 | 05-corners | schilling2012bernstein / feller2009introduction | Thm.1.4 p.3 / Section XIII.4 Thms.1,1a pp.439-440 | OK |
| 48 | 05-corners | bondesson1992generalized | Ch.7 p.105, (7.1.1)-(7.1.2) | OK |
| 49 | 05-corners | duits2004axioms; felsberg2001scale; felsberg2004monogenic | (general) | OK |
| 50 | 05-corners | halgreen1979self | Section 2 pp.14-15, (5) | OK |
| 51 | 05-corners | sato1999levy | Thm.14.14 p.86 | OK (note: boxed range 0<alpha<2, alpha=2 via proof cross-ref) |
| 52 | 05-corners | pedersen2005alpha | (general) | OK |
| 53 | 06-generator | sato1999levy | Thm.17.5 pp.108-109 | WEAKER/STRONGER (sign) |
| 54 | 06-generator | duits2004axioms | p.288, (66) | OK (note: endpoint alpha-prime=1) |
| 55-56 | 07-implementation | bondesson1992generalized / feller2009introduction | Thm.3.1.5 pp.34-35, (3.1.1)-(3.1.2) p.29 / Thm.2 p.431 | OK |
| 57,61 | 07-implementation | deriche1993recursively | eq.(38) p.12 | OK |
| 58 | 07-implementation | lindeberg1990scalespace | Thm. 2 (generating-function classification) | OK |
| 59 | 07-implementation | burt1983laplacian | (general) | OK |
| 60 | 07-implementation | young1995recursive | Table 1, p.141 | OK |
| 62 | 08-conclusions | fagerstrom2026hemigroup | (general) | OK |

Totals: 62 audited instances (some of the original 53 extracted context blocks cover more
than one instance of the same fact used twice). 1 source section not held (DLMF Section 6.2,
4 citing instances); 1 sign discrepancy worth the author attention (Sato Thm. 17.5,
Section 6); 2 minor range/endpoint notes (Sato Thm. 14.14 boxed range; Duits eq. (66)
endpoint); 1 minor page-span looseness, harmless (Halgreen pp. 14-16 for the pure-mixture
case, whose proof is on p. 15 alone); the remainder are plain OK, including several I
independently re-verified even though the ledger audit already covers them.
