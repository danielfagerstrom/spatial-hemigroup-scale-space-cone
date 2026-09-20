#!/usr/bin/env python3
"""The recursive Gaussians read in the paper's coordinates (ex:numerical-run,
fig:recursive-gaussians; the claims tested are those of rem:recursive-gaussians).

A symmetric rational transfer R with R(0) = 1 and neither zero nor pole on the real axis
factors as

    R(omega) = prod_j (1 + omega^2/zeta_j^2) / prod_i (1 + omega^2/theta_i^2),   Re > 0,

and the Frullani identity  log(1 + omega^2/theta^2) = int_0^oo (1 - cos omega x) 2 e^{-theta x} dx/x,
valid for Re theta > 0, gives  -log R = int_0^oo (1 - cos omega x) k(x) dx/x  with

    k(x) = 2 sum_i e^{-theta_i x} - 2 sum_j e^{-zeta_j x},

a real function, the complex roots coming in conjugate pairs. R is the transform of an
infinitely divisible law exactly when k >= 0, and the kernel of an admissible family at one
scale exactly when k is also nonincreasing. A transfer with a zero on the real axis is the
transform of no infinitely divisible law at all, such transforms being zero-free. The three
designs, at sigma = 1:

  * the real-pole cascade of gamma identical sections (the Matern member): all poles at
    sqrt(2 gamma), k = 2 gamma e^{-sqrt(2 gamma) x};
  * Young and van Vliet 1995: the poles of their Table 1, p. 141, 1.1668 and
    1.10783 +- 1.40586 i in units of 1/q (from the factorization (6a)-(6b) of the rational
    approximation (3a)-(3b), Abramowitz and Stegun 26.2.20), no zeros, forward and backward
    passes in cascade (9a)-(9b);
  * Deriche 1993, eq. (38), p. 12, the fourth-order fit
    (1.68 cos(0.6318 x) + 3.735 sin(0.6318 x)) e^{-1.783 x}
      - (0.6803 cos(1.997 x) + 0.2598 sin(1.997 x)) e^{-1.723 x}
    of e^{-x^2/2} on x >= 0, extended symmetrically (the causal and anticausal halves are
    summed, his (24)-(30)); its transform is rational with the poles 1.783 +- 0.6318 i and
    1.723 +- 1.997 i and a cubic numerator in omega^2.

Output: ../figures/fig-recursive-gaussians.png and the numbers of the example on stdout.
"""
import os
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from scipy.integrate import quad

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "..", "figures")
plt.rcParams.update({"font.size": 9.0, "axes.linewidth": 0.8})
TEAL, BLUE, RED, GREY = "#2a9d8f", "#1b6ca8", "#d1495b", "#555555"

L, N = 60.0, 2 ** 18
DX = 2 * L / N
OM = 2 * np.pi * np.fft.rfftfreq(N, d=DX)
X = (np.arange(N) - N // 2) * DX
GAUSS = np.exp(-0.5 * X ** 2) / np.sqrt(2 * np.pi)
SEED = 20260918

DERICHE = dict(a0=1.68, a1=3.735, b0=1.783, w0=0.6318, c0=-0.6803, c1=-0.2598, b1=1.723,
               w1=1.997)
DIGITS = dict(a0=2, a1=3, b0=3, w0=4, c0=4, c1=4, b1=3, w1=3)   # decimals as printed


class AllPole:
    """R = 1 / prod (1 + w^2/theta^2), Re theta > 0."""

    def __init__(self, name, poles):
        self.name, self.poles = name, np.array(poles, complex)

    def R(self, om, scale=1.0):
        om = np.asarray(om, float) * scale
        return np.real(1.0 / np.prod([1 + om ** 2 / p ** 2 for p in self.poles], axis=0))

    def k(self, x):
        x = np.asarray(x, float)
        return np.real(2 * sum(np.exp(-p * x) for p in self.poles))

    def variance(self):
        return float(np.real(2 * sum(1 / p ** 2 for p in self.poles)))


def deriche_terms(c):
    return [((c["a0"] - 1j * c["a1"]) / 2, c["b0"] - 1j * c["w0"]),
            ((c["a0"] + 1j * c["a1"]) / 2, c["b0"] + 1j * c["w0"]),
            ((c["c0"] - 1j * c["c1"]) / 2, c["b1"] - 1j * c["w1"]),
            ((c["c0"] + 1j * c["c1"]) / 2, c["b1"] + 1j * c["w1"])]


def deriche_numerator(c):
    """Transform of the symmetric extension: sum_j 2 C_j lam_j/(lam_j^2 + u), u = omega^2.
    Returns the numerator's roots in u and the mass (the value at u = 0)."""
    terms = deriche_terms(c)
    lam2 = [lam ** 2 for _, lam in terms]
    num = np.zeros(4, complex)
    for j, (C, lam) in enumerate(terms):
        num += 2 * C * lam * np.poly([-l for i, l in enumerate(lam2) if i != j])
    mass = float(np.real(sum(2 * C / lam for C, lam in terms)))
    return np.roots(np.real(num)), mass


def deriche_R(om, c=DERICHE):
    terms = deriche_terms(c)
    mass = float(np.real(sum(2 * C / lam for C, lam in terms)))
    om = np.asarray(om, float)
    return np.real(sum(2 * C * lam / (lam ** 2 + om ** 2) for C, lam in terms)) / mass


def check_profile(r, oms=(0.5, 1.0, 2.0, 4.0)):
    """max over a few omega of |int (1 - cos omega x) k(x)/x dx + log R(omega)|."""
    worst = 0.0
    for w in oms:
        val = quad(lambda x: (1 - np.cos(w * x)) * float(r.k(x)) / x, 0, 60, limit=800)[0]
        worst = max(worst, abs(val + np.log(r.R(w))))
    return worst


def density(Rvals):
    return np.fft.fftshift(np.fft.irfft(Rvals, N)) / DX


def main():
    gam = 4
    mat = AllPole(r"real-pole cascade, $\gamma = 4$", [np.sqrt(2 * gam)] * gam)
    yvv = AllPole("Young–van Vliet", [1.1668, 1.10783 + 1.40586j, 1.10783 - 1.40586j])

    xg = np.linspace(1e-6, 12, 120001)
    for r in (mat, yvv):
        k = r.k(xg)
        neg = xg[k < 0]
        inc = xg[1:][np.diff(k) > 1e-13]
        print("%-32s variance %.4f  k(0+) = %.1f  profile against -log R: %.1e"
              % (r.name, r.variance(), k[0], check_profile(r)))
        print("   min k = %+.4f at x = %.3f; k < 0 from x = %s; k increases from x = %s"
              % (k.min(), xg[np.argmin(k)],
                 ("%.3f" % neg[0]) if len(neg) else "nowhere",
                 ("%.3f" % inc[0]) if len(inc) else "nowhere"))
        ph = density(r.R(OM))
        r.err = np.max(np.abs(ph - GAUSS)) / GAUSS.max()
        print("   kernel: min %.2e; sup |kernel - Gaussian| / peak = %.4f" % (ph.min(), r.err))
        ratio = r.R(OM, 2.0) / r.R(OM)
        atom = 2.0 ** (-2 * len(r.poles))
        r.inc = density(ratio - atom)
        print("   increment 1 -> 2: atom %.5f; continuous part min %.3e, max %.3e;"
              " negative mass %.3e" % (atom, r.inc.min(), r.inc.max(),
                                        -np.sum(np.minimum(r.inc, 0)) * DX))

    roots_u, mass = deriche_numerator(DERICHE)
    real_pos = sorted(float(np.real(u)) for u in roots_u if abs(np.imag(u)) < 1e-9 and np.real(u) > 0)
    c = DERICHE
    slope0 = c["a1"] * c["w0"] - c["a0"] * c["b0"] + c["c1"] * c["w1"] - c["c0"] * c["b1"]
    print("Deriche: mass of the fit %.6f (sqrt(2 pi) = %.6f); one-sided slope at 0: %+.4f"
          % (mass, np.sqrt(2 * np.pi), slope0))
    print("   numerator roots in omega^2: %s; transfer vanishes at omega sigma = %s"
          % (np.round(roots_u, 3), np.round(np.sqrt(real_pos), 3)))
    ph = density(deriche_R(OM))
    der_err = np.max(np.abs(ph - GAUSS)) / GAUSS.max()
    print("   kernel: min %.2e; sup |kernel - Gaussian| / peak = %.5f" % (ph.min(), der_err))
    rng = np.random.default_rng(SEED)
    n_draw, n_zero = 2000, 0
    for _ in range(n_draw):
        cp = {key: v + (rng.random() - 0.5) * 10.0 ** (-DIGITS[key]) for key, v in DERICHE.items()}
        ru, _ = deriche_numerator(cp)
        n_zero += any(abs(np.imag(u)) < 1e-9 and np.real(u) > 0 for u in ru)
    print("   coefficients perturbed within half a unit of the last printed digit:"
          " a real zero in %d of %d draws" % (n_zero, n_draw))
    # the slope a1 w0 - a0 b0 + c1 w1 - c0 b1 over the whole rounding box: each product is
    # monotone in each factor on the box, so its range is attained at the corners
    def prod_range(u, du, v, dv):
        vals = [(u + i * du) * (v + j * dv) for i in (-1, 1) for j in (-1, 1)]
        return min(vals), max(vals)
    h = {key: 0.5 * 10.0 ** (-DIGITS[key]) for key in DERICHE}
    r1 = prod_range(c["a1"], h["a1"], c["w0"], h["w0"])
    r2 = prod_range(c["a0"], h["a0"], c["b0"], h["b0"])
    r3 = prod_range(c["c1"], h["c1"], c["w1"], h["w1"])
    r4 = prod_range(c["c0"], h["c0"], c["b1"], h["b1"])
    lo = r1[0] - r2[1] + r3[0] - r4[1]
    hi = r1[1] - r2[0] + r3[1] - r4[0]
    print("   one-sided slope over the rounding box: between %+.6f and %+.6f (positive throughout,"
          " so the transform is negative at high frequency and has a real zero for every"
          " coefficient vector in the box)" % (lo, hi))
    zs = np.sqrt(real_pos)
    print("   zeros of R(2w) are at %s; none coincides with a zero of R(w), so the ratio"
          " R(2w)/R(w) has real poles at %s" % (np.round(zs / 2, 3), np.round(zs, 3)))

    gams = np.arange(1, 65)
    errs = np.array([np.max(np.abs(density((1 + OM ** 2 / (2 * g)) ** (-float(g))) - GAUSS))
                     / GAUSS.max() for g in gams])
    print("real-pole cascade, sup error / peak: " + ", ".join(
        "gamma=%d: %.4f" % (g, e) for g, e in zip(gams, errs) if g in (1, 2, 4, 8, 16, 32, 64)))
    print("   gamma x error at 32, 64: %.4f, %.4f; first gamma below Young--van Vliet's %.4f: %s"
          % (32 * errs[31], 64 * errs[63], yvv.err,
             next((int(g) for g, e in zip(gams, errs) if e < yvv.err), "none up to 64")))

    # The gauge of the comparison (second review round, referee D, finding 5): a sup error
    # against the unit Gaussian depends on the dilation at which a kernel is read. Three
    # readings of each: at the design's own scale parameter, at matched variance, and at the
    # dilation that minimizes the error.
    from scipy.optimize import minimize_scalar

    def sup_err(Rfun, s):
        return np.max(np.abs(density(Rfun(OM * s)) - GAUSS)) / GAUSS.max()

    def readings(name, Rfun, var):
        best = minimize_scalar(lambda s: sup_err(Rfun, s), bounds=(0.7, 2.0), method="bounded",
                               options={"xatol": 1e-6})
        print("   %-28s variance %.4f | own parameter %.4f%% | matched variance %.4f%% |"
              " best dilation %.4f%% (kernel dilated by %.4f)"
              % (name, var, 100 * sup_err(Rfun, 1.0), 100 * sup_err(Rfun, 1 / np.sqrt(var)),
                 100 * best.fun, best.x))
        return best.fun

    print("the gauge of the sup error against the unit Gaussian:")
    ph_d = density(deriche_R(OM))
    var_d = float(np.sum(X ** 2 * ph_d) * DX / (np.sum(ph_d) * DX))
    readings("Deriche", deriche_R, var_d)
    readings("Young--van Vliet", yvv.R, yvv.variance())
    best_c = np.array([readings("cascade gamma=%d" % g,
                                lambda om, g=g: (1 + om ** 2 / (2 * g)) ** (-float(g)), 1.0)
                       if g in (1, 2, 4, 8, 16, 32, 64) else np.nan for g in gams])
    allbest = np.array([minimize_scalar(
        lambda s, g=g: sup_err(lambda om: (1 + om ** 2 / (2 * g)) ** (-float(g)), s),
        bounds=(0.7, 2.0), method="bounded", options={"xatol": 1e-5}).fun for g in gams])
    yvv_best = minimize_scalar(lambda s: sup_err(yvv.R, s), bounds=(0.7, 2.0), method="bounded",
                               options={"xatol": 1e-6}).fun
    print("   cascade at its best dilation: first gamma below Young--van Vliet's own-parameter"
          " %.4f%%: %s; below its best-dilation %.4f%%: %s; gamma x error at 32, 64: %.4f, %.4f"
          % (100 * yvv.err, next((int(g) for g, e in zip(gams, allbest) if e < yvv.err), "none"),
             100 * yvv_best, next((int(g) for g, e in zip(gams, allbest) if e < yvv_best), "none"),
             32 * allbest[31], 64 * allbest[63]))

    fig, axes = plt.subplots(2, 2, figsize=(9.2, 5.8))
    (a0, a1), (a2, a3) = axes
    om = np.linspace(0, 14, 5000)
    a0.semilogy(om, np.exp(-0.5 * om ** 2), color=GREY, lw=1.0, ls="--", label="Gaussian")
    a0.semilogy(om, mat.R(om), color=BLUE, lw=1.2, label=mat.name)
    a0.semilogy(om, yvv.R(om), color=RED, lw=1.2, label=yvv.name)
    a0.semilogy(om, np.abs(deriche_R(om)), color=TEAL, lw=1.2, label="Deriche (modulus)")
    a0.set_ylim(1e-9, 2); a0.set_xlim(0, 14); a0.set_xlabel(r"$\omega\sigma$")
    a0.set_title("(a) transfer functions", fontsize=9)
    a0.legend(fontsize=7.5, frameon=False, loc="lower left")
    for z in np.sqrt(real_pos):
        a0.axvline(z, color=TEAL, lw=0.5, ls=":")
    ins0 = a0.inset_axes([0.52, 0.55, 0.45, 0.41])
    ins0.plot(om, 1e4 * deriche_R(om), color=TEAL, lw=1.0)
    ins0.axhline(0, color="k", lw=0.5)
    for z in np.sqrt(real_pos):
        ins0.axvline(z, color=TEAL, lw=0.5, ls=":")
    ins0.set_xlim(3.5, 14); ins0.set_ylim(-1.2, 1.2)
    ins0.text(0.97, 0.86, r"Deriche, signed, $\times 10^4$", fontsize=7, ha="right", transform=ins0.transAxes)
    ins0.tick_params(labelsize=6.5, length=2)

    xs = np.linspace(1e-6, 8, 4000)
    for r, col in ((mat, BLUE), (yvv, RED)):
        a1.plot(xs, r.k(xs), color=col, lw=1.2, label=r.name)
    a1.axhline(0, color="k", lw=0.5)
    a1.set_ylim(-0.6, 8.2); a1.set_xlim(0, 8); a1.set_xlabel(r"$x/\sigma$")
    a1.set_title("(b) folded profile $k$", fontsize=9); a1.legend(fontsize=7.5, frameon=False)
    ins = a1.inset_axes([0.45, 0.28, 0.5, 0.40])
    for r, col in ((mat, BLUE), (yvv, RED)):
        ins.plot(xs, r.k(xs), color=col, lw=1.0)
    ins.axhline(0, color="k", lw=0.5); ins.set_xlim(1.2, 8); ins.set_ylim(-0.26, 0.26)
    ins.tick_params(labelsize=7, length=2)

    for r, col in ((mat, BLUE), (yvv, RED)):
        a2.plot(X, r.inc, color=col, lw=1.1, label=r.name)
    a2.axhline(0, color="k", lw=0.5)
    a2.set_xlim(-8, 8); a2.set_xlabel(r"$x/\sigma$")
    a2.set_title(r"(c) stage from $\sigma$ to $2\sigma$, continuous part", fontsize=9)
    ins2 = a2.inset_axes([0.62, 0.45, 0.35, 0.45])
    for r, col in ((mat, BLUE), (yvv, RED)):
        ins2.plot(X, r.inc, color=col, lw=1.0)
    ins2.axhline(0, color="k", lw=0.5); ins2.set_xlim(2.5, 8); ins2.set_ylim(-0.003, 0.003); ins2.set_yticks([-0.002, 0.002])
    ins2.tick_params(labelsize=7, length=2)

    a3.loglog(gams, errs, ":", color=BLUE, lw=1.2, label="real-pole cascade, matched variance")
    a3.loglog(gams, allbest, "-", color=BLUE, lw=1.2, label="real-pole cascade, best dilation")
    a3.axhline(yvv.err, color=RED, lw=1.0, ls="--", label=yvv.name + ", own parameter")
    a3.axhline(der_err, color=TEAL, lw=1.0, ls="--", label="Deriche, own parameter")
    a3.set_xlabel(r"sections $\gamma$")
    a3.set_title("(d) sup error of the kernel / peak, against the Gaussian", fontsize=9)
    a3.legend(fontsize=7.5, frameon=False)
    fig.tight_layout()
    fig.savefig(os.path.join(OUT, "fig-recursive-gaussians.png"), dpi=200, bbox_inches="tight")
    print("wrote fig-recursive-gaussians.png")


if __name__ == "__main__":
    main()
