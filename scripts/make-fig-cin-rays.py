#!/usr/bin/env python3
"""fig-cin-rays.png -- what a Cin ray is: its profile, its exponent, its kernel.

Three panels, module B section 3 (the admissible cone). Left: the unit-step profiles
k = 1_(0,tau) for three values of tau, and a smooth nonincreasing profile drawn as the positive
stack of unit steps it is (Lemma 3.1(2): k(x) = varpi((x, infinity)) with varpi = -dk). Middle:
the exponents Cin(tau omega) = int_0^{tau omega} (1 - cos v) dv/v of the same three rays, with
the quadratic start (1/4) z^2 and the logarithmic asymptote log z + gamma_E of Cin (Lemma 3.1(1))
drawn for tau = 1, and the stationary points at omega = 2 pi n / tau marked (they are why no Cin
ray is subordinated, section 4). Right: the kernel p_tau of the ray tau = 1, the symmetric law
with transform exp(-Cin(omega)), computed as the inverse cosine transform on a fine grid: it is
logarithmically singular at the origin (Proposition 3.6, the threshold regime k(0+) = 1) and
carries the echoes of the step at +-tau, +-2tau, ... (the delay equation, Lemma 3.4 and
Remark 3.7), marked by the dotted lines.

numpy and matplotlib only; Cin is a cumulative trapezoid of its integrand, the kernel a direct
cosine sum with a Gaussian taper at high frequency (the transform decays like 1/omega, so the
taper only rounds the singularity at scale 1/Omega).

Run:  python scripts/make-fig-cin-rays.py      Out:  figures/fig-cin-rays.png
"""
import os
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "..", "figures", "fig-cin-rays.png")
os.makedirs(os.path.dirname(OUT), exist_ok=True)
plt.rcParams.update({"font.size": 9.0, "axes.linewidth": 0.8})

EULER = 0.5772156649015329
TAUS = [0.5, 1.0, 2.0]
COLORS = ["#6a4c93", "#1b6ca8", "#2a9d8f"]


def cin_table(zmax, n):
    """Cin on a grid [0, zmax] by cumulative trapezoid of (1 - cos v)/v (value 0 at v = 0)."""
    z = np.linspace(0.0, zmax, n)
    g = np.empty_like(z)
    g[0] = 0.0
    g[1:] = (1.0 - np.cos(z[1:])) / z[1:]
    c = np.concatenate([[0.0], np.cumsum(0.5 * (g[1:] + g[:-1]) * np.diff(z))])
    return z, c


ZMAX, NZ = 6000.0, 6_000_001
zgrid, cgrid = cin_table(ZMAX, NZ)


def cin(z):
    return np.interp(np.abs(z), zgrid, cgrid)


fig, (axl, axm, axr) = plt.subplots(1, 3, figsize=(10.4, 3.1))

# --- left: the unit-step profiles, and a profile as a stack of steps ------------------------
x = np.linspace(0.0, 3.0, 601)
for tau, col in zip(TAUS, COLORS):
    axl.step(x, (x < tau).astype(float), where="post", color=col, lw=1.6,
             label=rf"$1_{{(0,\tau)}}$, $\tau={tau:g}$")
# a smooth profile as a stack of unit steps: k(x) = sum_j w_j 1_(0, s_j)(x) with the weights
# w_j = k(s_j) - k(s_{j+1}) the mass of the tail measure -dk between consecutive step sizes
ks = 2.0 * np.exp(-x)
steps = np.linspace(0.3, 3.0, 10)
kvals = 2.0 * np.exp(-steps)
stack = np.zeros_like(x)
for j, s0 in enumerate(steps):
    w_j = kvals[j] - (kvals[j + 1] if j + 1 < len(steps) else 0.0)
    stack += w_j * (x < s0)
axl.step(x, stack, where="post", color="#9a9a9a", lw=1.0)
axl.plot(x, ks, color="#444444", lw=1.0, ls="--", label=r"$k=2e^{-x}$ as a stack of steps")
axl.set_xlabel(r"displacement size $x$")
axl.set_ylabel(r"profile $k(x)$")
axl.set_ylim(-0.05, 2.1)
axl.legend(frameon=False, fontsize=8.5, loc="upper right")
axl.set_title("the unit-step profiles", fontsize=9.5)

# --- middle: the exponents Cin(tau omega) ----------------------------------------------------
w = np.linspace(0.0, 16.0, 1601)
for tau, col in zip(TAUS, COLORS):
    axm.plot(w, cin(tau * w), color=col, lw=1.6, label=rf"$\mathrm{{Cin}}(\tau\omega)$, $\tau={tau:g}$")
wq = np.linspace(0.0, 2.2, 100)
axm.plot(wq, 0.25 * wq**2, color="#1b6ca8", lw=0.9, ls=":")
wl = np.linspace(1.5, 16.0, 100)
axm.plot(wl, np.log(wl) + EULER, color="#1b6ca8", lw=0.9, ls=":")
axm.text(1.35, 1.35, r"$\omega^2/4$", fontsize=8, color="#1b6ca8")
axm.text(11.6, 2.55, r"$\log\omega+\gamma_E$", fontsize=8, color="#1b6ca8")
for n in (1, 2):
    axm.plot([2 * np.pi * n], [cin(2 * np.pi * n)], "o", color="#1b6ca8", ms=3.5)
axm.annotate(r"stationary at $\omega = 2\pi n/\tau$", xy=(2 * np.pi, cin(2 * np.pi)),
             xytext=(3.2, 3.25), fontsize=7.5, color="#1b6ca8",
             arrowprops=dict(arrowstyle="-", color="#1b6ca8", lw=0.6))
axm.set_xlabel(r"wavenumber $\omega$")
axm.set_ylabel(r"exponent $F(\omega)$")
axm.set_ylim(0, 3.9)
axm.legend(frameon=False, fontsize=8.5, loc="lower right")
axm.set_title("the exponents of the rays", fontsize=9.5)

# --- right: the kernel of the ray tau = 1 -----------------------------------------------------
tau = 1.0
OMEGA, DW = 3000.0, 0.005
om = np.arange(0.0, OMEGA, DW) + DW / 2
weight = np.exp(-cin(tau * om)) * np.exp(-(om / 1500.0) ** 2)
xs = np.linspace(0.0, 3.2, 1281)
p = np.empty_like(xs)
CH = 40
for i in range(0, len(xs), CH):
    xc = xs[i:i + CH]
    p[i:i + CH] = (np.cos(np.outer(xc, om)) @ weight) * DW / np.pi
xx = np.concatenate([-xs[::-1], xs[1:]])
pp = np.concatenate([p[::-1], p[1:]])
axr.plot(xx, pp, color="#1b6ca8", lw=1.6, label=r"$p_\tau$, $\tau=1$")
for m in (-2, -1, 1, 2):
    axr.axvline(m * tau, color="#9a9a9a", lw=0.8, ls=":")
axr.set_xlabel(r"displacement $x$")
axr.set_ylabel(r"kernel density $p_\tau(x)$")
axr.set_ylim(0, 1.15)
axr.set_xlim(-3.2, 3.2)
axr.text(-3.05, 0.78, r"$\sim\log(1/|x|)$ at $0$", fontsize=7.5, color="#1b6ca8")
axr.text(-3.05, 0.42, r"echoes at $\pm\tau,\pm2\tau$", fontsize=7.5, color="#666666")
axr.legend(frameon=False, fontsize=8.5, loc="upper left")
axr.set_title("the kernel of a ray", fontsize=9.5)
# inset (external presentation review, 2026-09-19): the echo made visible. By the delay
# equation x p'(x) = -(1/2)[p(x - tau) + p(x + tau)], so the derivative inherits the
# logarithmic singularity of p at the origin as a logarithmic spike at x = tau.
ins = axr.inset_axes([0.60, 0.50, 0.38, 0.40])
sel = (xs > 0.45) & (xs < 2.45)
ins.plot(xs[sel], np.gradient(p, xs)[sel], color="#1b6ca8", lw=1.1)
for m in (1, 2):
    ins.axvline(m * tau, color="#9a9a9a", lw=0.7, ls=":")
ins.set_title(r"$p_\tau'(x)$ near $\tau$ and $2\tau$", fontsize=7.5)
ins.tick_params(labelsize=7, length=2)
ins.set_xticks([1, 2])

for ax in (axl, axm, axr):
    ax.spines["top"].set_visible(False)
    ax.spines["right"].set_visible(False)

fig.tight_layout(w_pad=1.6)
fig.savefig(OUT, dpi=220)
print("wrote", os.path.relpath(OUT, os.path.join(HERE, "..")), " p(0.0125) =", p[5], " p(1) =",
      p[np.searchsorted(xs, 1.0)], " mass =", 2 * np.trapezoid(p, xs))
