#!/usr/bin/env python3
"""fig-corners.png -- the three corner families: kernels and exponents, by parameter.

Module B section 5. Top row: the kernel at canonical scale 1 for several values of the family's
parameter. Bottom row: the exponent F(omega) = -log of the kernel's transform, same parameters.

  Matern (left):   transform (1 + omega^2)^(-gamma); density
                   (|x|/2)^(gamma - 1/2) K_(gamma - 1/2)(|x|) / (sqrt(pi) Gamma(gamma));
                   gamma = 1/2 (the Bessel K_0, logarithmically singular), 1 (Laplace), 2, 4.
                   Exponent gamma log(1 + omega^2): logarithmic growth.
  Student-t (mid): density Gamma(a + 1/2) / (sqrt(pi) Gamma(a)) (1 + x^2)^(-a - 1/2), 2a degrees
                   of freedom; a = 1/2 (Cauchy), 1, 2, 5. Transform 2^(1-a)/Gamma(a) |w|^a K_a(|w|);
                   exponent grows linearly.
  stable (right):  transform exp(-|omega|^alpha); alpha = 1/2, 1 (Cauchy), 3/2, 2 (Gaussian);
                   densities by numerical cosine inversion, closed forms at alpha = 1 and 2 used as
                   a check. Exponent |omega|^alpha: a power.

numpy, scipy (the modified Bessel function kv) and matplotlib.

Run:  uv run --with numpy --with scipy --with matplotlib python scripts/make-fig-corners.py
Out:  figures/fig-corners.png
"""
import os
import numpy as np
from scipy.special import kv, gamma as Gamma
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "..", "figures", "fig-corners.png")
os.makedirs(os.path.dirname(OUT), exist_ok=True)
plt.rcParams.update({"font.size": 9.0, "axes.linewidth": 0.8})

COLORS = ["#6a4c93", "#1b6ca8", "#2a9d8f", "#e09f3e"]
x = np.linspace(-4.0, 4.0, 1601)
ax_ = np.abs(x)
ax_[ax_ == 0] = 1e-9
w = np.linspace(0.0, 10.0, 1001)

fig, axes = plt.subplots(2, 3, figsize=(10.4, 5.6))

# --- Matern ---------------------------------------------------------------------------------
for g, col in zip([0.5, 1.0, 2.0, 4.0], COLORS):
    dens = (ax_ / 2.0) ** (g - 0.5) * kv(g - 0.5, ax_) / (np.sqrt(np.pi) * Gamma(g))
    axes[0, 0].plot(x, dens, color=col, lw=1.5, label=rf"$\gamma={g:g}$")
    axes[1, 0].plot(w, g * np.log1p(w ** 2), color=col, lw=1.5)
axes[0, 0].set_title("Matérn: kernels", fontsize=9.5)
axes[1, 0].set_title(r"Matérn: $F(\omega)=\gamma\log(1+\omega^2)$", fontsize=9.5)
axes[0, 0].set_ylim(0, 0.9)

# --- Student-t ------------------------------------------------------------------------------
wpos = np.where(w == 0, 1e-9, w)
for a, col in zip([0.5, 1.0, 2.0, 5.0], COLORS):
    dens = Gamma(a + 0.5) / (np.sqrt(np.pi) * Gamma(a)) * (1.0 + x ** 2) ** (-a - 0.5)
    axes[0, 1].plot(x, dens, color=col, lw=1.5, label=rf"$2a={2*a:g}$")
    tr = 2.0 ** (1.0 - a) / Gamma(a) * wpos ** a * kv(a, wpos)
    axes[1, 1].plot(w, -np.log(tr), color=col, lw=1.5)
axes[0, 1].set_title("Student-t: kernels", fontsize=9.5)
axes[1, 1].set_title(r"Student-t: $F(\omega)=-\log\,[c_a|\omega|^aK_a(|\omega|)]$", fontsize=9.5)
axes[0, 1].set_ylim(0, 1.3)

# --- symmetric stable -------------------------------------------------------------------------
om = np.arange(0.0, 400.0, 0.002) + 0.001
xs = np.linspace(0.0, 4.0, 401)
for al, col in zip([0.5, 1.0, 1.5, 2.0], COLORS):
    weight = np.exp(-om ** al)
    p = np.array([np.sum(np.cos(xx * om) * weight) for xx in xs]) * 0.002 / np.pi
    xx_full = np.concatenate([-xs[::-1], xs[1:]])
    p_full = np.concatenate([p[::-1], p[1:]])
    axes[0, 2].plot(xx_full, p_full, color=col, lw=1.5, label=rf"$\alpha={al:g}$")
    axes[1, 2].plot(w, w ** al, color=col, lw=1.5)
    if al == 1.0:
        err = np.max(np.abs(p - 1.0 / (np.pi * (1.0 + xs ** 2))))
        print("stable alpha=1 vs Cauchy, max error:", err)
    if al == 2.0:
        err = np.max(np.abs(p - np.exp(-xs ** 2 / 4.0) / np.sqrt(4.0 * np.pi)))
        print("stable alpha=2 vs Gaussian, max error:", err)
axes[0, 2].set_title("symmetric stable: kernels", fontsize=9.5)
axes[1, 2].set_title(r"symmetric stable: $F(\omega)=|\omega|^{\alpha}$", fontsize=9.5)
axes[0, 2].set_ylim(0, 0.7)
axes[1, 2].set_ylim(0, 12)

# line styles as well as colours, so that the curves stay apart in grayscale (external
# presentation review, 2026-09-19)
STYLES = ["-", "--", "-.", ":"]
for ax in axes.flat:
    for i, line in enumerate(ax.get_lines()):
        line.set_linestyle(STYLES[i % len(STYLES)])

for j in range(3):
    axes[0, j].set_xlabel(r"displacement $x$")
    axes[0, j].set_ylabel(r"density $\phi_1(x)$")
    axes[0, j].legend(frameon=False, fontsize=8.5, loc="upper right")
    axes[1, j].set_xlabel(r"wavenumber $\omega$")
    axes[1, j].set_ylabel(r"exponent $F(\omega)$")
for ax in axes.flat:
    ax.spines["top"].set_visible(False)
    ax.spines["right"].set_visible(False)

fig.tight_layout(w_pad=1.6, h_pad=1.4)
fig.savefig(OUT, dpi=220)
print("wrote", os.path.relpath(OUT, os.path.join(HERE, "..")))
