<!-- Export note: 1 file path(s) on the author's machine were replaced by <local path> in this public copy; nothing else was changed. -->
# S8 - the six queued sources, acquired; read and transcribed (2026-09-20)

Dispatched from spatial-hemigroup-scale-space. All six items queued 2026-09-19
(notes/reviews/cone/SOURCES-round2-acquisitions-2026-09-19.md) are now held, pinned, filed
under Mathematics, and confirmed off the "To Acquire" queue (library acquire list no longer
shows their Zotero keys FB3JPSX6, XP8MZBGP, TI4JH74B, AS8ZM2MN, 4ET4S6V7, JQRJQ6CJ). No repository
file was touched; library bib export --dry-run reports the six entries already current (0
re-render needed). Files verified present and readable on <local path>

| # | Item | Citekey | Held as |
|---|------|---------|---------|
| 1 | Schoenberg 1951, J. d'Analyse Math. | schoenberg1951polya | PDF, text layer OK |
| 2 | Barndorff-Nielsen, Pedersen, Sato 2001, Adv. Appl. Probab. | barndorffnielsen2001multivariate | PDF, text layer OK |
| 3 | Maejima, Rosinski 2002, J. Theoret. Probab. | maejima2002type | PDF, text layer OK |
| 4 | Aoyama, Maejima 2007, Bernoulli | aoyama2007characterizations | PDF, text layer OK |
| 5 | Barndorff-Nielsen, Kent, Sorensen 1982, Int. Statist. Rev. | barndorffnielsen1982normal | PDF (JSTOR scan), text layer OK |
| 6 | Stein 1999, Interpolation of Spatial Data | stein1999interpolation | PDF, text layer OK |

No library write was needed this pass -- the acquisition, filing and pinning happened in
yesterday's dispatch; this pass is read-only verification plus the requested transcriptions.

---

## 1. State of each item

All six: library resolve <citekey> --json shows "pdf": {"status": "stored", "source": "mount"},
a clean single pinned citekey, no pin clash, and the same Zotero key that was queued yesterday
(the queue entry was enriched in place rather than a second item being created). None has an md
conversion made ("md": {"status": "on_demand", "cost": "high"} for all six -- normal for
not-yet-requested markdown, not a fault); none has a latex artifact (none is an arXiv source).
All six collection-classified under Mathematics, which fits the subject matter. Nothing further
needed on the filing side.

---

## 2a. The novelty question -- what BNPS2001 and MR2002 actually say

Read in full: barndorffnielsen2001multivariate (Barndorff-Nielsen, Pedersen, Sato 2001) and
maejima2002type (Maejima, Rosinski 2002).

### Barndorff-Nielsen-Pedersen-Sato 2001 -- every self-decomposability/subordination statement, verbatim

Definitions (p. 174, printed):
> "5.1. Operator self-decomposability. A random vector X on R^d is called self-decomposable if,
> for every b>1, there is a Y_b such that X =d= b^{-1}X + Y_b, where X and Y_b are independent...
> Let Q in M_(0,infinity)(d). A random vector X on R^d or its distribution mu is called
> Q-self-decomposable if, for every b>1, there is a Y_b such that X =d= b^{-Q}X + Y_b..."
> "The class of all Q-self-decomposable distributions on R^d is denoted L_0(Q). For
> m=1,2,..., the class L_m(Q) is defined to be the class of distributions on R^d such that,
> for every b>1, there exists mu_b in L_{m-1}(Q) satisfying (5.2). Then
> L_0(Q) is a superset of L_1(Q) is a superset of ... is a superset of L_infinity(Q)."

The classical d=1 prototype, cited (not reproved), p. 178:
> "In the simplest case where n=d=1 and {X(t)} is a Brownian motion, Ismail and Kelker (1979) and
> Halgreen (1979) showed that {Y(t)} is self-decomposable if {T(t)} is self-decomposable."
(Reference list, p. 186: "Halgreen, C. (1979). Self-decomposability of the generalized inverse
Gaussian and hyperbolic distributions. Z. Wahrscheinlichkeitsth. 47, 13-17." and "Ismail, M. E. H.
and Kelker, D. H. (1979). Special functions, Stieltjes transforms and infinite divisibility. SIAM
J. Math. Anal. 10, 884-901.")

The main inheritance theorem, fixed dimension, operator-stable subordinand (p. 179):
> "Theorem 6.1. Assume that each {X_j(t)} is strictly Q_j-stable for some Q_j in M_[1/2,infinity)(n_j).
> Let H = diag(h_1,...,h_d) with h_j>0 for all j. If {T(t)} is H-self-decomposable, then the
> subordinated n-dimensional Levy process {Y(t)} is D-self-decomposable, where
> D = diag(h_1 Q_1,...,h_d Q_d) in M_(0,infinity)(n). More generally, if {T(t)} is of class
> L_m(H;R^d) with m in {0,1,...,infinity}, then {Y(t)} is of class L_m(D;R^n)."

The scalar specialization used elsewhere in the article's literature (p. 185):
> "Proposition 6.7. If {T(t)} is a self-decomposable subordinator and {X(t)} is a strictly
> Q-stable subordinand on R^n with some Q in M_[1/2,infinity)(n), then the subordinated process
> {Y(t)} is Q-self-decomposable on R^n. If, further, {T(t)} is of class L_m with m in
> {1,2,...,infinity}, then {Y(t)} is of class L_m(Q;R^n). If {T(t)} is strictly stable with index
> beta, then {Y(t)} is strictly beta^{-1}Q-stable."
> "Remark 6.8. As a special case, assume that {X(t)} is strictly stable with index alpha. Let
> {T(t)} be self-decomposable. Then {Y(t)} is self-decomposable in the ordinary sense."

The "type G" connection, verbatim (abstract, p. 161, and section 6.2, p. 183):
> Abstract: "The prototype result is that subordination of the Brownian motion by
> self-decomposable subordinators gives self-decomposable processes. This is connected with
> distributions of type G, and we will formulate a special case of our result as a generalization
> of the concept of type G."
> Section 6.2 (p. 183): "A random vector Y on R^n is said to be of type G if there are a standard
> Gaussian random vector X on R^n and a nonnegative infinitely divisible random variable T
> independent of X such that Y =d= T^{1/2}X. In this subsection, we provide a generalization of
> type G random vectors." [type G(Q), Proposition 6.4, Proposition 6.5, Proposition 6.9 follow --
> all fixed-n statements, all in the sufficiency direction: type G(Q) with an H-self-decomposable
> mixing law T gives a self-decomposable Y.]

A negative/counterexample result showing self-decomposability does NOT always transfer (p. 182):
> "Let us give an example showing that a subordinated process is not always self-decomposable
> when the subordinator and subordinand are self-decomposable. Example 6.2. Let n=d=1, {X(t)} and
> {T(t)} be independent gamma processes with parameter 1, and define Y(t)=X(T(t)). Then {Y(t)} is
> not self-decomposable, although {X(t)} and {T(t)} are self-decomposable."
This is the paper's own demonstration that stability (not just self-decomposability) of the
subordinand is the load-bearing hypothesis in Theorem 6.1/Proposition 6.7 -- a gamma subordinand
(self-decomposable but not stable) breaks the inheritance.

Direct answers to the dispatch's questions about this paper:
- No statement is quantified "for every d." Every theorem fixes a dimension n (or d for the
  subordinator) and a specific operator/stability structure (Q_j-stable components, H = fixed
  diagonal). There is no statement of the form "self-decomposable in R^d for every d."
- The FORWARD direction (only Gaussian-variance-mixture-with-self-decomposable-mixing laws are
  self-decomposable in every dimension) does not appear in any form -- not for fixed d, not for
  all d, not as a counterexample. The paper's own counterexample (Example 6.2) goes the other way:
  it shows the SUFFICIENT-direction inheritance theorem needs a stability hypothesis, not that
  self-decomposability fails to characterize anything across dimensions.
- No further source is cited for a dimension-free radial characterization. The paper cites
  Halgreen (1979), Ismail-Kelker (1979), Sato (1999, Thm. 30.1) for the d=1 prototype, and its own
  Theorem 6.1/Propositions 6.4-6.9 for the multivariate generalization -- no Takano, no
  Rocha-Arteaga-Sato, no reference to a "for every d" theorem anywhere in the paper (checked: no
  hit for "Rocha", "Takano", or "for every d" in the full text).

### Maejima-Rosinski 2002 -- does not discuss self-decomposability at all

Finding, confirmed twice (searched "self", "decomposable", "self-decompos" -- all zero hits in
the full text; "Sato" also zero hits): the word "decomposable" does not occur anywhere in this
paper. This is a genuine, load-bearing negative result, not a search-tool artifact -- checked
against a positive control (library search maejima2002type "infinitely" returns 23 hits, so the
text layer is being read correctly).

What the paper is actually about (Abstract, p. 323):
> "This paper presents a systematic study of the class of multivariate distributions obtained by a
> Gaussian randomization of jumps of a Levy process. This class, called the class of type G
> distributions, constitutes a closed convolution semigroup of the family of symmetric infinitely
> divisible probability measures. Spectral form of Levy measures of type G distributions is
> obtained and it is shown that type G property can not be determined by one dimensional
> projections. Conditionally Gaussian structure of type G random vectors is exhibited via series
> representations."

Its own summary of contents (p. 325), the closest thing to a "dimension" result in the paper --
about projections, not about a radial law holding for every d:
> "Section 4 examines whether the following projection property is true: if all one dimensional
> projections of a symmetric infinitely divisible random vector are of type G, then the random
> vector is of type G. The answer is negative; we construct an example of a symmetric infinitely
> divisible probability measure on R^d, d>=2, which is not of type G on R^d but any lower
> dimensional projection is of type G on a lower dimensional space."
This is a fixed-d-vs-its-projections result (type G can hold on every lower-dimensional slice
without holding on the ambient space) -- the reverse kind of dimension statement from the article's
"radially self-decomposable in every ambient dimension" claim, and not a self-decomposability
statement at all (type G here means general infinitely-divisible mixing, not self-decomposable
mixing).

The mixing law is general infinitely divisible, not self-decomposable (Introduction, p. 323):
> "A real-valued random variable X is said to be of type G if X =d= V^{1/2}Z (1.1) where Z is the
> standard normal random variable and V is a nonnegative infinitely divisible random variable
> independent of Z."
No stronger hypothesis (self-decomposable, Thorin/GGC) is imposed anywhere as the paper's own
definition -- self-decomposability of the mixing law, which is exactly what the article's
prop:dimension-filtration needs, is simply outside this paper's scope.

Direct answers:
- The FORWARD direction does not appear, nor does the converse (sufficiency), because the
  paper never engages self-decomposability at all.
- No "for every d" statement appears. The one genuinely dimension-sensitive result (section 4) is
  about one-dimensional projections of a fixed ambient law, not about a single 1-d radial law
  extended into every ambient dimension.
- Further sources cited for related notions: Marcus (1978) ["xi-radial processes and random
  Fourier series," Mem. Amer. Math. Soc. 368 -- reference [4], introducing type G random vectors
  and processes]; Rosinski (1990, Ann. Probab. 18, "On series representations of infinitely
  divisible random vectors"; 1991, in Cambanis-Samorodnitsky-Taqqu (eds.), Stable Processes and
  Related Topics, "On a class of infinitely divisible processes represented as mixtures of
  Gaussian processes" -- references [5],[6], "further investigating" type G); Barndorff-Nielsen and
  Perez-Abreu (2000, 2001 preprints, references [2],[3], the broader marginal-infinitely-divisible
  class of which type G is a subclass). No Takano, no Rocha-Arteaga-Sato, no Sato citation of any
  kind (checked: zero hits for "Sato", "Takano", "Rocha").

### Attribution comparison across the three type-G sources now held

- Maejima-Rosinski 2002 (p. 325): "Type G random vectors and stochastic processes were
  introduced by Marcus [4] and further investigated by Rosinski.[5,6]" -- reference [4] is
  "Marcus, M. B. (1978). xi-radial processes and random Fourier series. Mem. Amer. Math. Soc. 368."
  (Note the year given here, 1978, versus the Crossref/AMS-catalogue year 1987 found for
  DOI 10.1090/memo/0368 in yesterday's Part 2 search -- the same memoir, two different years
  reported by two different sources; flagged, not resolved, since neither is held.)
- Aoyama-Maejima 2007, Definition 1.1 (p. 148), read again from the now-held file, confirming
  yesterday's proxy-read transcription verbatim: "Summarizing the discussions in Rosinski
  (1991) and Maejima and Rosinski (2001, 2002), we use the following definition of type G
  distributions on R^d." Marcus is not named here at all -- checked again in the held file
  (zero hits for "Marcus" in the full text and reference list of aoyama2007characterizations).
- So: Marcus (1978/1987) is the origin per Maejima-Rosinski's own attribution, but Aoyama-Maejima
  2007's Definition 1.1 (the definition this article's module B currently cites) attributes only to
  Rosinski (1991) and Maejima-Rosinski (2001, 2002), not to Marcus.
If the article's own
  attribution sentence for type G is meant to name the origin of the concept, Marcus belongs in
  it (per Maejima-Rosinski's own historical note); if it is meant to name the source of the
  precise Definition 1.1 as used, Rosinski (1991) + Maejima-Rosinski (2001/2002) is what
  Aoyama-Maejima itself cites, and this is not currently attributed to Steutel-van Harn as module
  B's text does (per the dispatch's own framing -- see section 2b below).

### 2a -- the paragraph the article can use

We have not found the equivalence stated -- neither the forward direction (radially
self-decomposable in every ambient dimension implies a self-decomposable-mixing Gaussian variance
mixture) nor a labeled biconditional of this shape -- in either Barndorff-Nielsen-Pedersen-Sato
(2001) or Maejima-Rosinski (2002), the two papers named as the most likely priors. What may be
said: BNPS 2001 proves, in a fixed dimension and for an operator-stable subordinand, that
self-decomposability (or class L_m) of the subordinator passes to the subordinated process
(Theorem 6.1, Propositions 6.7/6.9) -- this is the classical sufficiency half, generalized from
Ismail-Kelker/Halgreen's d=1 result, but stated for one d at a time, never "for every d," and with
no converse; its own Example 6.2 shows the hypothesis (stability, not just self-decomposability, of
the subordinand) is load-bearing. Maejima-Rosinski 2002 does not engage self-decomposability at
all -- its type G class uses a general infinitely-divisible (not self-decomposable) mixing law, and
its one dimension-sensitive theorem is about lower-dimensional projections of a fixed-d law, not
about extending a 1-d law into every ambient dimension.
A close relative found separately, worth
flagging to the author even though it is a different paper from the two named (from
barndorffnielsen1982normal, section 2c below): the general normal variance-mean mixture in
arbitrary dimension r (same mixing law F usable at every r, since F does not depend on r) is
self-decomposable whenever F is self-decomposable and the drift is zero -- this is closer in shape
to a genuine "for every dimension" sufficiency statement than anything in BNPS 2001, because the
r-dependence really is vacuous in the hypothesis. But it is still only the sufficiency half, no
converse is stated, and the paper does not itself phrase it as "for every r" (that reading is this
report's inference from the fact that r is a free parameter of Definition 2.1 with no
dimension-specific hypothesis on F). What may not be said: that the article's converse (only a
self-decomposable-mixing Gaussian variance mixture is radially self-decomposable in every
dimension) is a known theorem anywhere searched -- no held or newly-read source states or attempts
a converse of this kind; this remains, on the evidence now gathered from three independent
sufficiency statements (Ismail-Kelker/Halgreen d=1, BNPS2001's Theorem 6.1 fixed-d-operator-stable,
BNKS1982's fixed-drift=0 arbitrary-r), the article's own contribution to isolate.

---

## 2b. Type G -- the definition, verbatim, and the attribution question

Maejima-Rosinski 2002, the founding move (pp. 323-325):
> (1.1), p. 323: "A real-valued random variable X is said to be of type G if X =d= V^{1/2}Z where Z
> is the standard normal random variable and V is a nonnegative infinitely divisible random
> variable independent of Z."
> p. 325 (the multivariate case, via Gaussian randomization, (1.3)-(1.6)): "A multivariate Levy
> process is said to be of type G if it can be obtained by a Gaussian randomization of some
> R^d-valued Levy process {V_0(t)}... Consequently, a type G random vector X(1) has Levy measure
> given by (1.4) [nu(A) = E[nu_0(Z^{-1}A)]]... Then X(1) =d= V^{1/2}Z (1.6) where Z is the standard
> Gaussian random vector in R^d independent of V [V = the quadratic-covariation matrix of
> V_0]... Type G random vectors and stochastic processes were introduced by Marcus [4] and
> further investigated by Rosinski.[5,6]"

Aoyama-Maejima 2007, Definition 1.1 (p. 148), the "systematic" summary this article currently
cites, confirmed from the held file, verbatim, exactly matching yesterday's proxy-read
transcription:
> "Summarizing the discussions in Rosinski (1991) and Maejima and Rosinski (2001, 2002), we use the
> following definition of type G distributions on R^d. Definition 1.1. A probability measure mu_0
> in I_sym(R^d) is said to be of type G if its Levy measure nu_0 is given by nu_0(B) =
> E[nu(Z^{-1}B)], B in B_0(R^d), (1.1) where nu is another Levy measure on R^d and Z is the
> real-valued standard normal random variable."

Is there a "variance mixture of normals with infinitely divisible mixing law" biconditional
stated? Yes -- implicitly, via (1.1)/(1.2) in Maejima-Rosinski's introduction (V infinitely
divisible, X = V^{1/2}Z) -- the definitions given by both papers ARE this equivalence at the level
of the defining relation, not stated as a separately labeled "iff" theorem; the Levy-measure form
(1.1)/(1.4) is proved (Maejima-Rosinski, section 5, "we discuss a Gaussian randomization of Levy
processes using series representations and prove (1.5)-(1.6)") to be equivalent to the
variance-mixture form (1.2)/(1.6), which is the content module B would cite as "iff."

Attribution to correct, per the primary sources (compare to module B's current
Steutel-van Harn (2004) (2.7), p. 345 attribution): the primary attributions are Marcus (1978,
per Maejima-Rosinski's own reference list; the AMS Memoir catalogue elsewhere gives 1987 for the
same DOI/memoir number -- a genuine year discrepancy between two independent records, not resolved
here since Marcus's paper itself is not held) for the origin of type G random vectors/processes,
Rosinski (1990, 1991) for further development, and Maejima and Rosinski (2001, 2002) for the
systematic R^d treatment -- this is Aoyama-Maejima's own attribution sentence for "the following
definition of type G distributions on R^d," and is the citation module B should probably use in
place of (or in addition to) Steutel-van Harn.

---

## 2c. Barndorff-Nielsen, Kent, Sorensen 1982 -- normal variance-mean mixtures

Definition 2.1, verbatim (p. 146):
> "Definition 2.1. Suppose x is a random vector which, for a given u>=0, follows an r-dimensional
> normal distribution with covariance matrix uL and mean vector mu+u*beta, where L is a symmetric,
> positive-definite r x r-matrix with determinant one, and mu and beta are vectors of dimension r.
> Suppose moreover that u follows a probability distribution F on [0,infinity). Then we say that
> the distribution of x is a normal variance-mean mixture with position mu, drift beta, structure
> matrix L and mixing distribution F. If beta=0 we speak of a normal variance mixture."

The characteristic function (p. 146, eq. (2.2)):
> phi(theta) = e^{i*theta*mu'} phi_F(i*theta*beta' - theta*L*theta'),   (2.2)
where phi_F is the moment generating function of F, phi_F(s) = E{exp(su)}.

The inheritance theorem, verbatim (p. 147) -- this is item 2c's centerpiece:
> "Infinite divisibility of F implies that P is infinitely divisible, as follows immediately from
> (2.2). See also Kent (1981) and Kelker (1971). Self-decomposability of F is not, in general,
> sufficient to ensure self-decomposability of P, but it can be shown that if F is self-decomposable
> then P is self-decomposable provided theta=0. Moreover, one-dimensional variance-mean mixtures
> are self-decomposable if the mixing distribution F has the stronger property of belonging to the
> Thorin class of 'generalized gamma convolutions'; it can even be deduced that P belongs to the
> extended Thorin class. See Thorin (1978) and Halgreen (1979)."
(Here "P" is the mixture's own distribution and "theta" is the exponential-family canonical
parameter of a margin/conditional -- see the surrounding exponential-family apparatus on the same
page; "theta=0" corresponds to the drift beta=0 case of Definition 2.1.)

Why this bears directly on the article's dimension-free claim, flagged as a finding beyond what
was asked: Definition 2.1 fixes no relation between r and F -- the same mixing law F on [0,infinity)
can be used to build a normal variance-mean mixture in every dimension r (taking L=I, beta=0,
mu=0), and the quoted theorem's hypothesis and conclusion are stated with no dependence on r at
all. So this sentence, read across all r, says: for every dimension r, if the mixing law F is
self-decomposable then the r-dimensional isotropic Gaussian variance mixture (with zero drift)
built from it is self-decomposable. This is the sufficiency half of the article's
prop:dimension-filtration, stated in a form that is dimension-free in substance even though the
paper never writes "for every r" as such -- a paraphrase, not a direct quotation of that
quantifier, and flagged as this report's own reading rather than the paper's own words.

A confirming special case, verbatim (p. 149), which does use "any dimension" in print:
> "It was established by Bondesson (1979) and Halgreen (1979) that (2.4) belongs to the Thorin
> class. From the general results on variance-mean mixtures mentioned above it follows that for
> r=1 the distributions (2.5) are self-decomposable, and that they are self-decomposable in any
> dimension if beta=0. For r>1 and beta not 0 it was proved by Shanbhag & Sreehari (1979) that the
> generalized hyperbolic distributions are not in general self-decomposable according to the
> restricted, homothetical definition of self-decomposability of multivariate distributions."
This is the generalized hyperbolic family specifically (their eq. (2.4)/(2.5)), not the general
theorem, but it is the paper's own instance of the words "self-decomposable in any dimension" --
the closest verbatim match to the article's own vocabulary found in any of the six sources.

No converse is stated anywhere in this paper either (checked: the paper's own summary,
Theorem 3.1, applies the sufficiency direction to the z-distributions specifically: "The z
distributions are self-decomposable and are normal variance-mean mixtures, the mixing
distributions being the H(delta,gamma) distributions" -- again sufficiency, not a
characterization).

---

## 2d. Schoenberg 1951 -- the Polya frequency function theorem, at the primary source

The class definitions, verbatim (p. 331, the paper's own opening, eq. (1)-(3)):
> "We denote by T_1 the class of entire functions which are limits, uniform in every finite domain,
> of real polynomials with only real non-positive zeros... T_2 the wider class... only require that
> the approximating polynomials be real and have only real zeros... Psi(s) is in T_1 if and only
> if Psi(s) admits a representation of the form Psi(s) = C*e^{gamma*s}*s^p*Prod(1+a_v*s),
> (C real, gamma>=0, a_v>=0, Sum a_v<infinity)... elements Psi(s) of the class T_2 are
> characterized by the representation
> Psi(s) = C*e^{-gamma*s^2+delta*s}*s^p*Prod(1+a_v*s)*e^{-a_v*s},
> (C real, gamma>=0, delta,a_v real, Sum a_v^2<infinity)... Let now Psi(s) be in T_2, with
> Psi(0)>0, and such that Psi(s) does not reduce to the form C*e^{gamma*s}, hence
> Psi(s) = C*e^{-gamma*s^2+delta*s}*Prod(1+a_v*s)*e^{-a_v*s}, (3)
> (C>0, gamma>=0, delta,a_v real, 0<gamma+Sum a_v^2<infinity)"
(Printed text is OCR-degraded on the Greek letters -- gamma/delta render as garbled characters in
the raw scan, subscripts inconsistent between "a_v" and other renderings -- transcribed here with
the standard modern symbols matching Karlin's later reading of the same formula, which was checked
against this page image directly.)

The main theorem, verbatim (pp. 333-334) -- Theorem I is the two-sided (class T_2) case, the
direct primary source behind Karlin's Theorem 3.2(a):
> "A frequency function A(x), i.e. a non-negative measurable function satisfying the inequalities
> 0 < Integral A(x)dx < infinity, is said to be a Polya frequency function if and only if it
> satisfies the following condition: For every two sets of increasing numbers x_1<...<x_n,
> t_1<...<t_n (n=1,2,...), we have the inequality det||A(x_i-t_j)|| >= 0.
> I. If Psi(s) is defined by (3) then its reciprocal may be represented in the form
> 1/Psi(s) = Integral e^{-xs}*A(x)dx, (12) where A(x) is a Polya frequency function, a
> representation which is valid in the maximal vertical strip containing the origin in which the
> left-hand side of (12) is regular. Conversely, if A(x) is a Polya frequency function, then the
> integral (12) converges in a vertical strip containing the origin inside and represents there
> the reciprocal of a function Psi(s) of the form (3)."
> "II. If Phi(s) is defined by (6) [the one-sided T_1 form] then its reciprocal may be represented
> in the form 1/Phi(s) = Integral_0^infinity e^{-xs}*A(x)dx, (13)... where A(x) is a Polya
> frequency function such that A(x)=0 if x<0. Conversely, if A(x) is a Polya frequency function
> such that A(x)=0 if x<0, then the integral (13) converges in a half-plane Rs>alpha, (alpha<0),
> and represents there the reciprocal of a function Phi(s) of the form (6)."

Where the variation-diminishing property is proved: in this same paper (not a different one),
section 2, Lemma 6 (two-sided) and Lemma 8 (one-sided) -- verbatim:
> Lemma 6 (p. 344): "Let A(x) be a Polya frequency function and let f(x) be R-integrable in every
> finite interval and such that the integral g(x) = Integral A(x-t)f(t)dt converges for every real
> x. Then v(g) <= v(f), where v(g) and v(f) denote the numbers of variations in sign of the
> respective functions, for all real x." [Footnote 11 attributes the discrete/matrix precursor to
> Schoenberg's own 1930 paper, ref. [14]: "Ueber variationsvermindernde lineare Transformationen,"
> Math. Zeitschrift 32 (1930), 321-328, "See also [9], Chapter IV [Th. Motzkin, Beitraege zur
> Theorie der linearen Ungleichungen, Jerusalem 1936], and [18] for recent developments."]
> Lemma 8 (p. 347): "Let A(x) be a Polya frequency function such that A(x)=0 if x<0... Then
> v_(g) <= v_(f), where v_(g) and v_(f) denote the numbers of variations of sign of the respective
> functions in the range -infinity<x<=0."
So the variation-diminishing property is a within-paper consequence (Lemmas 6/8, section 2), not
imported from Schoenberg's 1950 companion paper ("On Polya frequency functions II," ref. [17] in
this paper's own bibliography, cited elsewhere for the convolution-operator perspective but not
needed for Theorem I/II's proof as given here).

Comparison with Karlin's Theorem 3.2(a), one line: same class, same normalization? Yes, the same
class (class T_2 here = class E_2 in Karlin, both requiring the exact form
C*e^{-gamma*s^2+delta*s}*Prod(1+a_v*s)*e^{-a_v*s} with gamma>=0, Sum a_v^2<infinity), with the
same non-degeneracy condition (0<gamma+Sum a_v^2<infinity here vs. Karlin's gamma+Sum a_i^2>0),
differing only in a normalization convention that Karlin makes explicit and Schoenberg leaves
implicit: Karlin's Theorem 3.2(a) restricts to the subclass E_2* with psi(0)=1 (a genuine,
normalized density's reciprocal-transform), whereas Schoenberg's Theorem I states the
representation for the un-normalized C>0 case directly. Karlin's own "Notes and References"
(already transcribed in yesterday's report, p. 391) states this outright: "Sections 3 and 4 [of
Chapter 7, containing Theorem 3.2] are elaborations of Schoenberg [1951]" -- so Karlin's
Theorem 3.2(a) is not an independent theorem but a restatement, at the normalized-density level,
of exactly Schoenberg's Theorem I read here at the primary source.

---

## 2e. Stein 1999 -- the Matern class, verbatim, with page

Printed p. 31 (pdf page 46), section "Matern class," read from the page image (the OCR text
layer omits the displayed equation (14), transcribed here from the image):
> "A class of autocovariance functions that I believe has considerable practical value is obtained
> from spectral densities of the form f(omega) = phi*(alpha^2+omega^2)^{-nu-1/2} for nu>0, phi>0
> and alpha>0. The corresponding autocovariance function is
>   K(t) = [pi^{1/2}*phi / (2^{nu-1}*Gamma(nu+1/2)*alpha^{2*nu})] * (alpha*|t|)^nu * K_nu(alpha*|t|),   (14)
> where K_nu is a modified Bessel function (Abramowitz and Stegun 1965, pp. 374-379). I call this
> class of autocovariance functions the Matern class after Bertil Matern (Matern 1960, 1986). The
> critical parameter here is nu: the larger nu is, the smoother Z is. In particular, Z will be m
> times mean square differentiable if and only if nu>m, since Integral omega^{2m}*f(omega)d(omega)
> < infinity if and only if nu>m. When nu is of the form m+1/2 with m a nonnegative integer, the
> spectral density is rational and the autocovariance function is of the form e^{-alpha*|t|} times
> a polynomial in |t| of degree m (Abramowitz and Stegun 1965, 10.2.15). For example, as we have
> already seen, when nu=1/2, K(t)=pi*phi*alpha^{-1}*e^{-alpha*|t|} and when nu=3/2,
> K(t)=(1/2)*pi*phi*alpha^{-3}*e^{-alpha*|t|}*(1+alpha*|t|)."

This is both the spectral-density/covariance definition and the naming sentence, on the same
printed page (31), section header "Matern class" -- the section is repeated with more detail later
(TOC lists a second "Matern class" entry at printed p. 48, in the chapter on smoothness properties;
not re-read this pass, as the naming and defining sentence requested is fully at p. 31).

---

## 2f. Aoyama-Maejima 2007 -- confirmed from the held file (was proxy-read yesterday)

Definition 1.1, verbatim, printed p. 148, read again directly from the now-stored PDF (not the
proxy) -- matches yesterday's transcription exactly, word for word and equation for equation:
> "Summarizing the discussions in Rosinski (1991) and Maejima and Rosinski (2001, 2002), we use the
> following definition of type G distributions on R^d. Definition 1.1. A probability measure mu_0
> in I_sym(R^d) is said to be of type G if its Levy measure nu_0 is given by nu_0(B) =
> E[nu(Z^{-1}B)], B in B_0(R^d), (1.1) where nu is another Levy measure on R^d and Z is the
> real-valued standard normal random variable."
No discrepancy found between yesterday's render-proxy transcription and today's direct read of the
stored file -- the acquisition round's proxy-read text was accurate.

---

## Files written to the scratchpad (none in the repository)

stein1999interpolation_printed31.png (the Matern-class page image, used because the text layer
skips the displayed equation (14)). No other new files; all other verbatim transcriptions above
were read directly from library search/library page text output, quoted in this report.
