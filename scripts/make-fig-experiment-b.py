#!/usr/bin/env python3
"""Numerical experiment for module B (ex:numerical-run, the implementation section).

Runs the machine of the implementation section -- forward--backward first-order lag sections
over a geometric knot ladder -- on one synthetic signal, for the Matern members gamma = 1
and gamma = 4 and for a multi-range member with 24 nodes, beside the Poisson scale space
(the stable member alpha = 1, which is also the Student-t member a = 1/2) computed by its
transform. Five checks, each tied to a numbered result of the paper:

  C1  exactness at the knots (prop:knot-exactness, prop:matern-cascade,
      prop:rational-increments(1)): refining the ladder does not move the old knots, the
      ladder agrees with a single increment, and a forward-Euler march of the generator form
      (prop:scale-evolution with prop:corner-generators) shows the O(dt) error that the
      cascade does not have.
  C2  positivity and unit mass at the realization level (prop:matern-cascade, the four-term
      mixture): min f <= v <= max f after every section, and the mean is conserved.
  C3  moments and tails (prop:matern-exponent(3), prop:moments-tails, prop:stable-family):
      the variance of the impulse response against 2 gamma t^2 and against the variance
      formula; exponential tails at rate 1/t for the Matern members and theta_1/t for the
      multi-range member; the power -2 for the Poisson kernel.
  C4  the boundedness threshold at the origin (cor:origin-boundedness): the partial
      inversion integrals (1/pi) int_0^W e^{-F} converge as W grows exactly when k(0+) > 1.
  C5  the Thorin subclass as a machine (prop:thorin-machine), on the Poisson member, whose
      Thorin measure is (2/pi) d theta: quadratures with real weights converge to it;
      nodes of weight 2 (the rounding that makes the stages rational) converge to another
      member, with transform 1/cosh(omega), and no placement of such nodes found here comes
      close to the Poisson kernel; the same search is run for the Student-t member a = 3/2.

The sampling. Position is continuous in the paper; here the signal is sampled (spacing 1)
and periodic. A lag section of range tau (in samples) is realized with the pole

    p(tau) = 2 tau^2 / (2 tau^2 + 1 + sqrt(4 tau^2 + 1)),   so that  p/(1-p)^2 = tau^2,

and the section between knots s < t is  g (1 - p_s z^-1)/(1 - p_t z^-1),  g = (1-p_t)/(1-p_s),
its zero at the pole of the previous knot. Its impulse response is
g delta_0 + g (p_t - p_s) p_t^(n-1), positive with unit mass, so it is a convex combination of
the identity and a one-sided average, as in the paper. Forward times backward gives
(1 + s^2 W^2)/(1 + t^2 W^2) with W^2 = 4 sin^2(omega/2): the continuum transfer with omega^2
replaced by the symbol of minus the second difference. The sampled cascade therefore
telescopes exactly, has the variance 2 gamma t^2 exactly, and satisfies the generator
equation exactly with the sampled Laplace kernel.

Matching. The members are compared at equal bandwidth: at display scale s a member runs at
canonical scale t = c s with F(c) = 1, so that every transfer equals 1/e at omega = 1/s.

Outputs (written to ../figures): fig-experiment-b.png, and the numbers of the five checks on
stdout. Deterministic (fixed seed).
"""
import os
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from scipy.signal import lfilter
from scipy.optimize import brentq, minimize
from scipy.integrate import quad
from scipy.special import sici

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "..", "figures")
plt.rcParams.update({"font.size": 9.0, "axes.linewidth": 0.8})
TEAL, BLUE, RED, GREY = "#2a9d8f", "#1b6ca8", "#d1495b", "#555555"

NX = 4096                        # samples, periodic; spacing 1
SMIN, SMAX, M = 1.0, 64.0, 48    # display scale s (samples): geometric knot ladder
MDISP = 160                      # display-only scale grid
SEED = 20260918
NODES = 24                       # nodes of the multi-range member in the run

x = np.arange(NX, dtype=float)
OMEGA = 2 * np.pi * np.fft.rfftfreq(NX)
W2 = 4 * np.sin(OMEGA / 2) ** 2  # symbol of minus the second difference


# ------------------------------------------------------------------ the members of the run
class Member:
    """A finite Thorin member sum_i n_i log(1 + omega^2/theta_i^2): n_i sections at node i."""

    def __init__(self, name, thetas, mult):
        self.name = name
        self.thetas = np.asarray(thetas, float)
        self.mult = np.asarray(mult, int)
        self.c = brentq(lambda c: self.F(c) - 1.0, 1e-6, 50.0)

    def F(self, om):
        om = np.asarray(om, float)
        return sum(n * np.log1p((om / th) ** 2) for th, n in zip(self.thetas, self.mult))

    def transfer(self, s):
        """Closed-form transfer of the sampled cascade at display scale s."""
        t = self.c * s
        out = np.ones_like(W2)
        for th, n in zip(self.thetas, self.mult):
            out /= (1 + (t / th) ** 2 * W2) ** n
        return out


def pole(tau):
    tau2 = tau * tau
    return 2 * tau2 / (2 * tau2 + 1 + np.sqrt(4 * tau2 + 1))


def rec_periodic(y, p):
    """w[n] = p w[n-1] + y[n] on the periodic signal, in steady state."""
    if p == 0.0:
        return y.copy()
    w = lfilter([1.0], [1.0, -p], y)
    wl = w[-1] / (1 - p ** NX)
    return w + wl * p ** np.arange(1, NX + 1)


def lag(y, ps, pt):
    g = (1 - pt) / (1 - ps)
    w = rec_periodic(y, pt)
    return g * (w - ps * np.roll(w, 1))


def section(y, ps, pt):
    """One forward--backward pair between the poles ps < pt."""
    v = lag(y, ps, pt)
    return lag(v[::-1], ps, pt)[::-1]


def ladder(f, member, ss, bounds=None):
    """The cascade over the ladder of display scales ss (ss[0] = 0); returns the taps."""
    u = f.copy()
    taps = []
    for k in range(len(ss) - 1):
        for th, n in zip(member.thetas, member.mult):
            ps, pt = pole(member.c * ss[k] / th), pole(member.c * ss[k + 1] / th)
            for _ in range(n):
                u = section(u, ps, pt)
                if bounds is not None:
                    bounds[0] = min(bounds[0], u.min())
                    bounds[1] = max(bounds[1], u.max())
        taps.append(u.copy())
    return np.array(taps)


def euler_march(f, member, ss):
    """Forward Euler for d_t u = (1/t) sum_i 2 n_i (Lap_{t/theta_i} - I) u, from the first
    knot, where the exact tap is the initial value."""
    u = ladder(f, member, ss[:2])[0]
    for k in range(1, len(ss) - 1):
        t, dt = member.c * ss[k], member.c * (ss[k + 1] - ss[k])
        du = np.zeros_like(u)
        for th, n in zip(member.thetas, member.mult):
            du += 2 * n * (section(u, 0.0, pole(t / th)) - u)
        u = u + dt * du / t
    return u


def knots(m):
    return np.concatenate([[0.0], np.geomspace(SMIN, SMAX, m)])


def refine(ss):
    """Insert the geometric midpoint of every interval above the first knot."""
    out = [ss[0], ss[1]]
    for a, b in zip(ss[1:], ss[2:]):
        out += [np.sqrt(a * b), b]
    return np.array(out)


def make_signal():
    rng = np.random.default_rng(SEED)
    f = np.zeros(NX)
    bump = lambda x0, sig, amp: amp * np.exp(-0.5 * ((x - x0) / sig) ** 2)
    f += bump(300, 1.5, 0.95)         # a fine event: shows the kernel of each member
    f += bump(900, 30, 0.70)          # a broad event
    f += bump(1500, 8, 0.90)          # a strong event ...
    f += bump(1700, 8, 0.12)          # ... and a weak one 200 samples away
    f += 0.25 * (np.tanh((x - 2500) / 3.0) - np.tanh((x - 3800) / 3.0))   # a plateau
    burst = (x >= 3000) & (x < 3300)
    f[burst] += 0.35 * (rng.random(burst.sum()) - 0.5)
    return np.clip(f, 0.0, 1.0)


# ------------------------------------------------------------------ continuum references
LC, NC = 400.0, 2 ** 20
DXC = 2 * LC / NC
OMC = 2 * np.pi * np.fft.rfftfreq(NC, d=DXC)
XC = (np.arange(NC) - NC // 2) * DXC
CAUCHY = (1 / np.pi) / (1 + XC ** 2)
SECH = 0.5 / np.cosh(np.pi * XC / 2)


def kernel_of(Fvals):
    """Density at canonical scale 1 of the law with exponent values Fvals on OMC."""
    return np.fft.fftshift(np.fft.irfft(np.exp(-Fvals), NC)) / DXC


def dist(ph, ref):
    return np.max(np.abs(ph - ref)), np.sum(np.abs(ph - ref)) * DXC


def F_cin(om):
    om = np.abs(np.asarray(om, float))
    out = np.zeros_like(om)
    nz = om > 0
    out[nz] = np.euler_gamma + np.log(om[nz]) - sici(om[nz])[1]
    return out


def main():
    f = make_signal()
    ss = knots(M)
    sm = ss[1:]
    mat1 = Member(r"Matérn $\gamma = 1$", [1.0], [1])
    mat4 = Member(r"Matérn $\gamma = 4$", [1.0], [4])
    multi = Member(r"%d nodes of weight $2$ at $\pi(i - \frac{1}{2})$" % NODES,
                   np.pi * (np.arange(1, NODES + 1) - 0.5), [1] * NODES)
    members = [mat1, mat4, multi]
    C_POISSON, C_GAUSS = 1.0, np.sqrt(2.0)
    print("bandwidth factors c (canonical scale t = c s): "
          + ", ".join("%s %.4f" % (m.name, m.c) for m in members)
          + ", Poisson %.4f, Gaussian %.4f" % (C_POISSON, C_GAUSS))

    # --- C1: exactness at the knots ------------------------------------------------------
    print("C1 exactness at the knots")
    for m in members:
        b = [np.inf, -np.inf]
        taps = ladder(f, m, ss, bounds=b)
        m.taps, m.bounds = taps, b
        taps2 = ladder(f, m, refine(ss))
        e_ref = np.max(np.abs(taps[1:] - taps2[2::2]))
        direct = ladder(f, m, np.array([0.0, SMAX]))[0]
        e_dir = np.max(np.abs(taps[-1] - direct))
        e_tr = np.max(np.abs(taps[-1] - np.fft.irfft(np.fft.rfft(f) * m.transfer(SMAX), NX)))
        e_eu = np.max(np.abs(euler_march(f, m, ss) - direct))
        e_eu2 = np.max(np.abs(euler_march(f, m, refine(ss)) - direct))
        print("   %-46s refine %.1e  single increment %.1e  closed-form transfer %.1e"
              "  Euler %.2e (2M: %.2e)" % (m.name, e_ref, e_dir, e_tr, e_eu, e_eu2))
    # the sampled cascade against the continuum member, at the first and the last knot
    Ff = np.fft.rfft(f)
    for m, gam in ((mat1, 1), (mat4, 4)):
        for s in (SMIN, SMAX):
            cont = np.fft.irfft(Ff / (1 + (m.c * s * OMEGA) ** 2) ** gam, NX)
            samp = np.fft.irfft(Ff * m.transfer(s), NX)
            print("   %-46s sampled against continuum transfer at s = %2.0f: %.1e"
                  % (m.name, s, np.max(np.abs(cont - samp))))

    print("   sampled transfer of Matern 1 at omega = 1/s, s = 1: %.5f (continuum: 1/e = %.5f)"
          % (1.0 / (1 + (mat1.c * 1.0) ** 2 * 4 * np.sin(0.5) ** 2), np.exp(-1.0)))

    # --- C2: positivity and unit mass at the realization level -----------------------------
    print("C2 positivity and mass: min f = %.3f, max f = %.3f" % (f.min(), f.max()))
    for m in members:
        drift = np.max(np.abs(m.taps.mean(axis=1) - f.mean()))
        nsec = 2 * M * int(m.mult.sum())
        print("   %-46s %5d section outputs, all in [%.6f, %.6f]; mean drift %.1e"
              % (m.name, nsec, m.bounds[0], m.bounds[1], drift))

    # --- C3: moments and tails ---------------------------------------------------------------
    print("C3 moments and tails (impulse responses of the machine)")
    delta = np.zeros(NX); delta[NX // 2] = 1.0
    xc = x - NX // 2
    for m, gam in ((mat1, 1), (mat4, 4)):
        h = ladder(delta, m, ss)
        m.h = h
        var = (h * xc ** 2).sum(axis=1)
        t = m.c * sm
        rel = np.max(np.abs(var / (2 * gam * t ** 2) - 1))
        k = M - 1
        win = (xc > 12 * t[k]) & (xc < 20 * t[k])
        slope = np.polyfit(xc[win], np.log(h[k][win]) - (gam - 1) * np.log(xc[win]), 1)[0]
        print("   %-46s max |var/(2 gamma t^2) - 1| = %.1e over %d knots;"
              " tail rate x t = %.4f" % (m.name, rel, M, -slope * t[k]))
    h = ladder(delta, multi, ss)
    multi.h = h
    t = multi.c * sm
    var = (h * xc ** 2).sum(axis=1)
    pred = np.sum(2.0 / multi.thetas ** 2)
    k = int(np.argmin(np.abs(sm - 16.0)))
    win = (xc > 8 * t[k]) & (xc < 14 * t[k])
    slope = np.polyfit(xc[win], np.log(h[k][win]), 1)[0]
    print("   %-46s max |var/(t^2 int x k) - 1| = %.1e (int x k = %.4f);"
          " tail rate x t = %.4f (theta_1 = %.4f)"
          % (multi.name, np.max(np.abs(var / (pred * t ** 2) - 1)), pred,
             -slope * t[k], multi.thetas[0]))
    ph = kernel_of(np.abs(OMC))
    win = (XC > 10) & (XC < 40)
    pw = np.polyfit(np.log(XC[win]), np.log(ph[win]), 1)[0]
    print("   Poisson kernel by inversion: tail power %.3f (predicted -2);"
          " sup |inversion - closed form| = %.1e" % (pw, dist(ph, CAUCHY)[0]))

    # --- C4: the boundedness threshold --------------------------------------------------------
    print("C4 boundedness threshold: (1/pi) int_0^W e^{-F}, W = 1e2, 1e4, 1e6")
    cases = [("Matern gamma=0.4 (c=0.8)", lambda w: 0.4 * np.log1p(w * w)),
             ("Matern gamma=0.5 (c=1)", lambda w: 0.5 * np.log1p(w * w)),
             ("Cin ray (c=1)", F_cin),
             ("Matern gamma=0.6 (c=1.2)", lambda w: 0.6 * np.log1p(w * w)),
             ("atoms 0.3 at 1, 0.5 at 3 (c=0.8)",
              lambda w: 0.15 * np.log1p(w * w) + 0.25 * np.log1p(w * w / 9)),
             ("atoms 0.6 at 1, 0.6 at 3 (c=1.2)",
              lambda w: 0.3 * np.log1p(w * w) + 0.3 * np.log1p(w * w / 9))]
    for name, F in cases:
        vals = []
        for Wtop in (1e2, 1e4, 1e6):
            grid = np.concatenate([[0.0], np.geomspace(1e-3, Wtop, 600)])
            tot = sum(quad(lambda w: float(np.exp(-F(np.array([w]))[0])), a, b)[0]
                      for a, b in zip(grid, grid[1:]))
            vals.append(tot / np.pi)
        print("   %-36s %9.4f %9.4f %9.4f   increments %.4f %.4f"
              % ((name,) + tuple(vals) + (vals[1] - vals[0], vals[2] - vals[1])))

    # --- C5: the Thorin subclass as a machine ---------------------------------------------------
    print("C5 the Poisson member (U = (2/pi) d theta) against its quadratures, canonical scale 1")
    print("   distance between the Poisson kernel and the 1/cosh member: sup %.3e  L1 %.3e"
          % dist(SECH, CAUCHY))
    # The window cuts the Poisson kernel's tail (second review round, referee D, finding 1):
    # every L1 distance to the Poisson kernel computed on |x| <= LC is low by at most the mass
    # of that kernel outside the window. The distance between the two limits on the whole line:
    gap = lambda x: abs(1.0 / (np.pi * (1.0 + x * x)) - 0.5 / np.cosh(0.5 * np.pi * x))
    cuts = [0.0, 1.129, 3.166, 20.0, LC]
    inside = 2 * sum(quad(gap, a, b, limit=400)[0] for a, b in zip(cuts, cuts[1:]))
    outside = 1.0 - (2.0 / np.pi) * np.arctan(LC)
    print("   the same L1 distance on the whole line: %.6f (on |x| <= %g: %.6f; the Poisson"
          " kernel's mass outside the window: %.3e)" % (inside + outside, LC, inside, outside))
    conv = []
    for n in (4, 8, 16, 32, 64, 128, 256):
        # real weights: geometric cells on [2/n, 2n], the node at the cell's median, the
        # uncovered top of U carried as a Gaussian coefficient a = 1/(pi top)
        edges = np.concatenate([[0.0], np.geomspace(2.0 / n, 2.0 * n, n)])
        Fr = np.zeros_like(OMC)
        for lo, hi in zip(edges, edges[1:]):
            Fr += 0.5 * (2 / np.pi) * (hi - lo) * np.log1p((OMC / (0.5 * (lo + hi))) ** 2)
        Fr += OMC ** 2 / (np.pi * edges[-1])
        # weight 2 at the medians pi (i - 1/2): (a) the lag-section member itself, the finite
        # product; (b) the same with the uncovered top of the measure 2 sum delta_{pi(i-1/2)}
        # carried as a Gaussian coefficient, sum_{i>N} 1/theta_i^2 ~ 1/(pi^2 N). Variant (b) is
        # not realized by lag sections alone. (The first version of the example reported (b)
        # under the description of (a); the external referee reproduced both and said so.)
        th = np.pi * (np.arange(1, n + 1) - 0.5)
        Fa = sum(np.log1p((OMC / q) ** 2) for q in th)
        Fb = Fa + OMC ** 2 / (np.pi * np.pi * n)
        kr, ka, kb = kernel_of(Fr), kernel_of(Fa), kernel_of(Fb)
        conv.append((n,) + dist(kr, CAUCHY) + dist(ka, CAUCHY) + dist(ka, SECH)
                    + dist(kb, CAUCHY) + dist(kb, SECH))
        print("   N = %3d  real weights: L1 %.2e | weight 2, lag sections only: to Poisson L1 %.3f,"
              " to 1/cosh L1 %.2e | with the Gaussian remainder: to Poisson L1 %.3f,"
              " to 1/cosh L1 %.2e" % (n, conv[-1][2], conv[-1][4], conv[-1][6], conv[-1][8],
                                      conv[-1][10]))
    conv = np.array(conv)

    def search(target, label, Ks):
        """Members with K free nodes of weight 2 and a free Gaussian coefficient: the least
        L1 distance to the target kernel found by a simplex search from the median nodes."""
        def obj(p):
            th = np.exp(p[:-1]); a = np.exp(p[-1])
            return dist(kernel_of(sum(np.log1p((OMC / q) ** 2) for q in th) + a * OMC ** 2),
                        target)[1]
        found = None
        for K in Ks:
            p0 = np.concatenate([np.log(np.pi * (np.arange(1, K + 1) - 0.5)), [np.log(0.05)]])
            r = minimize(obj, p0, method="Nelder-Mead",
                         options={"maxiter": 600, "xatol": 1e-3, "fatol": 1e-6})
            print("   weight 2, %d free nodes and a free Gaussian coefficient: L1 to %s %.3e"
                  " (nodes %s, a = %.4f)" % (K, label, r.fun,
                                             np.round(np.sort(np.exp(r.x[:-1])), 3),
                                             np.exp(r.x[-1])))
            found = r.fun if found is None else min(found, r.fun)
        return found

    best = search(CAUCHY, "Poisson", (1, 2, 3))
    # the same search for the Student-t member a = 3/2, transform (1 + |omega|) e^{-|omega|}
    student = (2 / np.pi) / (1 + XC ** 2) ** 2
    print("   Student-t a = 3/2 by inversion against its closed form: sup %.1e"
          % dist(kernel_of(np.abs(OMC) - np.log1p(np.abs(OMC))), student)[0])
    search(student, "Student-t a = 3/2", (1, 2, 3))

    # ----------------------------------------------------------------------------- figure
    sd = np.geomspace(SMIN, SMAX, MDISP)
    lx = np.log10
    ext = [0, NX, lx(SMIN), lx(SMAX)]
    ytv = [1, 4, 16, 64]
    fig = plt.figure(figsize=(9.2, 11.6))
    outer = fig.add_gridspec(2, 1, height_ratios=[10.2, 2.6], hspace=0.16)
    gs = outer[0].subgridspec(5, 1, height_ratios=[1, 3, 2.3, 2.3, 2.3], hspace=0.10)
    gb = outer[1].subgridspec(1, 2, wspace=0.25)
    ax0 = fig.add_subplot(gs[0])
    ax0.plot(x, f, color="k", lw=0.7)
    ax0.set_xlim(0, NX); ax0.set_ylim(-0.05, 1.1); ax0.set_yticks([0, 1])
    ax0.set_ylabel("$f$"); ax0.tick_params(labelbottom=False)
    gmap = np.array([np.fft.irfft(Ff * np.exp(-0.5 * (C_GAUSS * s * OMEGA) ** 2), NX)
                     for s in sd])
    rows = [(mat1.name, lambda s: mat1.transfer(s)),
            (mat4.name, lambda s: mat4.transfer(s)),
            (r"Poisson ($\alpha = 1$), by its transform",
             lambda s: np.exp(-C_POISSON * s * OMEGA))]
    maps = [np.array([np.fft.irfft(Ff * tr(s), NX) for s in sd]) for _, tr in rows]
    vd = max(np.max(np.abs(m - gmap)) for m in maps)
    print("difference maps: max |u - u_Gauss| = " +
          ", ".join("%.3f" % np.max(np.abs(m - gmap)) for m in maps))
    axes = [fig.add_subplot(gs[i]) for i in range(1, 5)]
    # shown through a square root, so that the low levels, which are most of the map, are not
    # printed black (second review round, referee E); the difference maps stay linear
    from matplotlib.colors import PowerNorm
    axes[0].imshow(maps[0], aspect="auto", origin="lower", cmap="gray", extent=ext,
                   norm=PowerNorm(0.5, vmin=0, vmax=1), interpolation="nearest")
    labels = ["$u$ (square-root gray scale), " + rows[0][0]] + [r"$u - u_{\mathrm{Gauss}}$, " + n for n, _ in rows]
    for ax, m in zip(axes[1:], maps):
        im = ax.imshow(m - gmap, aspect="auto", origin="lower", cmap="gray", extent=ext,
                       vmin=-0.5 * vd, vmax=0.5 * vd, interpolation="nearest")
    # one gray-scale key for the three difference maps
    cax = axes[2].inset_axes([1.012, -0.6, 0.012, 2.2])
    cb = fig.colorbar(im, cax=cax, ticks=[-0.5 * vd, 0.0, 0.5 * vd])
    cb.ax.set_yticklabels(["$-%.3f$" % (0.5 * vd), "$0$", "$+%.3f$" % (0.5 * vd)], fontsize=7)
    for i, (ax, lab) in enumerate(zip(axes, labels)):
        ax.text(0.006, 0.82, lab, transform=ax.transAxes, fontsize=9,
                bbox=dict(fc="white", ec="none", alpha=0.75, pad=1.2))
        ax.set_ylabel("$s$ (log)")
        ax.set_yticks([lx(v) for v in ytv]); ax.set_yticklabels(["$%d$" % v for v in ytv])
        if i < 3:
            ax.tick_params(labelbottom=False)
        else:
            ax.set_xlabel("$x$ (samples)")

    # bottom row: the kernels at s = 16, their tails, and the two quadratures
    k16 = int(np.argmin(np.abs(sm - 16.0)))
    s16 = sm[k16]
    gauss = np.fft.fftshift(np.fft.irfft(np.exp(-0.5 * (C_GAUSS * s16 * OMEGA) ** 2), NX))
    pois = np.fft.fftshift(np.fft.irfft(np.exp(-C_POISSON * s16 * OMEGA), NX))
    a1 = fig.add_subplot(gb[0]); a2 = fig.add_subplot(gb[1])
    for a in (a1, a2):
        a.plot(xc, gauss, color=GREY, lw=1.0, ls="--", label="Gaussian")
        a.plot(xc, mat1.h[k16], color=RED, lw=1.1, label=r"Matérn $1$")
        a.plot(xc, mat4.h[k16], color=BLUE, lw=1.1, label=r"Matérn $4$")
        a.plot(xc, multi.h[k16], color=TEAL, lw=1.1, label="%d nodes" % NODES)
        a.plot(xc, pois, color="k", lw=0.9, ls=":", label="Poisson")
    a1.set_xlim(-60, 60); a1.set_xlabel("$x$")
    a1.set_title("kernels at $s = %.0f$" % s16, fontsize=9)
    a1.legend(fontsize=7.5, frameon=False, loc="upper right")
    a2.set_yscale("log"); a2.set_xscale("log"); a2.set_xlim(4, 2000); a2.set_ylim(1e-13, 0.1)
    a2.set_xlabel("$x$ (log)"); a2.set_title("the same, tails", fontsize=9)
    fig.savefig(os.path.join(OUT, "fig-experiment-b.png"), dpi=200, bbox_inches="tight")
    print("wrote fig-experiment-b.png")

    # ------------------------------------------------------------ figure: the quadratures
    fq, aq = plt.subplots(1, 1, figsize=(5.6, 3.6))
    aq.loglog(conv[:, 0], conv[:, 2], "o-", color="k", ms=3.5, lw=1.1,
              label="real weights: distance to Poisson")
    aq.loglog(conv[:, 0], conv[:, 4], "s-", color=RED, ms=3.5, lw=1.1,
              label="weight $2$: distance to Poisson")
    aq.loglog(conv[:, 0], conv[:, 6], "s--", color=TEAL, ms=3.5, lw=1.1,
              label=r"weight $2$, lag sections only: distance to $1/\cosh$")
    aq.loglog(conv[:, 0], conv[:, 10], "^:", color=TEAL, ms=3.5, lw=1.1,
              label=r"weight $2$ with a Gaussian remainder: distance to $1/\cosh$")
    aq.axhline(best, color=RED, lw=0.8, ls=":")
    aq.text(conv[-1, 0], best * 1.12, "best distance to Poisson found by the search", fontsize=7,
            color=RED, ha="right", va="bottom")
    aq.set_xlabel("nodes $N$"); aq.set_ylabel("$L^1$ distance of the kernels")
    aq.legend(fontsize=7, frameon=False, loc="lower left")
    fq.tight_layout()
    fq.savefig(os.path.join(OUT, "fig-quadrature.png"), dpi=200, bbox_inches="tight")
    print("wrote fig-quadrature.png")


if __name__ == "__main__":
    main()
