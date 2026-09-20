#!/usr/bin/env python3
"""fig-bridge.png -- the subordination bridge on two corner families.

Two rows, two columns, module B section 4. Each row is one causal family and its image under
the bridge: on the left the law of the causal delay T_1 on the half-line (the causal kernel at
canonical scale 1), on the right the law of W_{T_1}, Brownian motion run for that delay (the
spatial kernel at canonical scale 1). Row 1: the causal Gamma family at gamma = 2, delay density
u e^{-u}, whose image is the Matern member gamma = 2 at range 1/sqrt 2, density
(1 + |x|/b) e^{-|x|/b} / (4b) with b = 1/sqrt 2 (Proposition 4.x(2)). Row 2: the causal Bessel
family at shape a = 3/2, the inverse-gamma law of the delay 1/V with V chi-square on 3 degrees
of freedom, density u^{-a-1} e^{-1/(2u)} / (2^a Gamma(a)), whose image is the Student-t law on 3
degrees of freedom in the scale of prop:student-t, (2/pi)(1 + x^2)^{-2} (second review round,
referee B, finding 6: the row was drawn at 2a/V and labelled a/V). The
exponents are written in the panels where they are elementary: F_I(sigma) = 2 log(1 + sigma)
on the left and F(omega) = F_I(omega^2/2) = 2 log(1 + omega^2/2) on the right.

numpy and matplotlib only, closed forms throughout.

Run:  python scripts/make-fig-bridge.py      Out:  figures/fig-bridge.png
"""
import os
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "..", "figures", "fig-bridge.png")
os.makedirs(os.path.dirname(OUT), exist_ok=True)
plt.rcParams.update({"font.size": 9.0, "axes.linewidth": 0.8})

CAUSAL, SPATIAL = "#6a4c93", "#1b6ca8"

fig, axes = plt.subplots(2, 2, figsize=(9.6, 5.4))

# --- row 1: Gamma (gamma = 2) -> Matern (gamma = 2, range 1/sqrt2) ------------------------
u = np.linspace(0.0, 8.0, 801)
gamma_density = u * np.exp(-u)                       # Gamma(2, 1)
ax = axes[0, 0]
ax.plot(u, gamma_density, color=CAUSAL, lw=1.7)
ax.fill_between(u, 0, gamma_density, color=CAUSAL, alpha=0.12, lw=0)
ax.set_title(r"the causal Gamma family, $\gamma = 2$: the delay law", fontsize=9.5)
ax.set_xlabel(r"delay $u$ (time)")
ax.set_ylabel("density")
ax.text(3.2, 0.30, r"$F_{\mathrm{I}}(\sigma) = 2\log(1+\sigma)$", fontsize=8.5, color=CAUSAL)
ax.text(3.2, 0.24, r"$k_{\mathrm{I}}(u) = 2e^{-u}$", fontsize=8.5, color=CAUSAL)
ax.set_xlim(0, 8)
ax.set_ylim(0, 0.42)

x = np.linspace(-5.0, 5.0, 1001)
b = 1.0 / np.sqrt(2.0)
matern = (1.0 + np.abs(x) / b) * np.exp(-np.abs(x) / b) / (4.0 * b)
ax = axes[0, 1]
ax.plot(x, matern, color=SPATIAL, lw=1.7)
ax.fill_between(x, 0, matern, color=SPATIAL, alpha=0.12, lw=0)
ax.set_title("its image $W_{T_1}$: the Matérn member, $\\gamma = 2$, $\\theta = 1/\\sqrt{2}$", fontsize=9.5)
ax.set_xlabel(r"displacement $x$ (space)")
ax.set_ylabel("density")
ax.text(1.4, 0.30, r"$F(\omega) = F_{\mathrm{I}}(\omega^2/2) = 2\log(1+\omega^2/2)$", fontsize=8.5, color=SPATIAL)
ax.text(1.4, 0.24, r"$k(x) = 2\gamma\,e^{-\sqrt{2}\,x} = 4e^{-\sqrt{2}\,x}$", fontsize=8.5, color=SPATIAL)
ax.set_xlim(-5, 5)
ax.set_ylim(0, 0.42)

# --- row 2: Bessel corner (a = 3/2, inverse gamma) -> Student-t on 3 degrees of freedom -----
a = 1.5
u2 = np.linspace(0.005, 3.0, 1200)
invgamma = u2 ** (-a - 1.0) * np.exp(-0.5 / u2) / (2.0 ** a * np.sqrt(np.pi) / 2.0)   # Gamma(3/2) = sqrt(pi)/2
ax = axes[1, 0]
ax.plot(u2, invgamma, color=CAUSAL, lw=1.7)
ax.fill_between(u2, 0, invgamma, color=CAUSAL, alpha=0.12, lw=0)
ax.set_title(r"the causal Bessel family, shape $a = 3/2$: the delay law", fontsize=9.5)
ax.set_xlabel(r"delay $u$ (time)")
ax.set_ylabel("density")
ax.text(1.2, 1.3, r"$T_1 = 1/V$, $V \sim \chi^2_{2a}$ (inverse gamma)", fontsize=8.5, color=CAUSAL)
ax.set_xlim(0, 3)
ax.set_ylim(0, 2.0)

student = (2.0 / np.pi) * (1.0 + x ** 2) ** (-2.0)   # t on 3 degrees of freedom, scale of prop:student-t
ax = axes[1, 1]
ax.plot(x, student, color=SPATIAL, lw=1.7)
ax.fill_between(x, 0, student, color=SPATIAL, alpha=0.12, lw=0)
ax.set_title(r"its image $W_{T_1}$: the Student-t member, $2a = 3$ degrees of freedom", fontsize=9.5)
ax.set_xlabel(r"displacement $x$ (space)")
ax.set_ylabel("density")
ax.text(1.4, 0.48, r"$W_{T_1}$: the Gaussian mixture, $\propto (1+x^2)^{-a-1/2}$", fontsize=8.5, color=SPATIAL)
ax.set_xlim(-5, 5)
ax.set_ylim(0, 0.7)

for ax in axes.flat:
    ax.spines["top"].set_visible(False)
    ax.spines["right"].set_visible(False)

fig.tight_layout(w_pad=2.4, h_pad=1.6)
fig.savefig(OUT, dpi=220)
print("wrote", os.path.relpath(OUT, os.path.join(HERE, "..")),
      " masses:", np.trapezoid(gamma_density, u), np.trapezoid(matern, x),
      np.trapezoid(invgamma, u2), np.trapezoid(student, x))
