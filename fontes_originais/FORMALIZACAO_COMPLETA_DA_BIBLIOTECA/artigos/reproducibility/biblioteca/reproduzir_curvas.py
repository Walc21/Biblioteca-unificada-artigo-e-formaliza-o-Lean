#!/usr/bin/env python3
"""Reproduce every numerical check, table, and figure used in the articles.

The program is deterministic: it uses neither pseudorandom generators nor
external data.  It writes localized figures to ``figures/pt`` and
``figures/en`` and the numerical record to ``resultados.json``.
"""

from __future__ import annotations

import argparse
import json
import math
import os
import platform
import tempfile
from collections import defaultdict
from dataclasses import dataclass
from fractions import Fraction
from functools import lru_cache
from pathlib import Path
from typing import Iterable

os.environ.setdefault(
    "MPLCONFIGDIR", str(Path(tempfile.gettempdir()) / "biblioteca_deterministica_mpl")
)

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np


ROOT = Path(__file__).resolve().parent

plt.rcParams.update(
    {
        "font.family": "serif",
        "mathtext.fontset": "cm",
        "pdf.fonttype": 42,
        "ps.fonttype": 42,
        "axes.spines.top": False,
        "axes.spines.right": False,
        "figure.dpi": 170,
        "savefig.bbox": "tight",
        "savefig.pad_inches": 0.04,
    }
)


TEXT = {
    "pt": {
        "dyadic_title": r"Células diádicas $J_{k,m}$ e centros $x_0=(m+\frac{1}{2})2^{-k}$",
        "dyadic_note": "centros em vermelho; a posse das fronteiras usa células semiabertas",
        "cw_title": r"Árvore de Calkin--Wilf: enumeração bijetiva de $\mathbb{Q}_{>0}$",
        "cw_note": r"$CW(2^{q-1})=1/q$: o índice é exponencial na altura $q$.",
        "assembly_title": "Montagens racionais de segmentos afins ancorados",
        "assembly_scale": "escala",
        "assembly_segments": "segmentos",
        "assembly_curve": r"função-alvo $f$",
        "assembly_atoms": "montagem racional",
        "relu_title": "Equivalência exata montagem--ReLU racional",
        "relu_assembly": "montagem racional",
        "relu_knots": "nós diádicos",
        "relu_input": "entrada",
        "relu_output": "saída",
        "relu_affine": "termo afim",
        "relu_hidden": "unidades hinge",
        "exp_title": r"$f=e^x$ em $[0,1]$: razão erro/cota $\longrightarrow 1$",
        "scale": "escala",
        "exact_error": "erro exato",
        "bound": "cota",
        "ratio": "erro / cota",
        "runge_title": "Runge: refinamento diádico com majorante local certificado",
        "uniform": "uniforme",
        "adaptive": "adaptativo certificado",
        "reference": r"referência $N^{-2}$",
        "segments_count": "número de segmentos $N$",
        "empirical_error": "erro empírico",
        "adaptive_panel": r"partição para $\varepsilon_I=6{,}25\times10^{-4}$",
        "runge_curve": "função de Runge",
        "interpolant": "interpolante",
        "coding_title": "Custo exato de três formatos prefix-free",
        "coding_atoms": "átomos estruturais",
        "coding_relu_structural": "ReLU estrutural",
        "coding_relu_naive": "ReLU racional ingênua",
        "coding_height": "altura atômica $H$",
        "coding_bits": "comprimento do fluxo (bits)",
    },
    "en": {
        "dyadic_title": r"Dyadic cells $J_{k,m}$ and centers $x_0=(m+\frac{1}{2})2^{-k}$",
        "dyadic_note": "centers in red; half-open cells assign boundary ownership",
        "cw_title": r"Calkin--Wilf tree: a bijective enumeration of $\mathbb{Q}_{>0}$",
        "cw_note": r"$CW(2^{q-1})=1/q$: the index is exponential in the height $q$.",
        "assembly_title": "Rational assemblies of anchored affine segments",
        "assembly_scale": "scale",
        "assembly_segments": "segments",
        "assembly_curve": r"target function $f$",
        "assembly_atoms": "rational assembly",
        "relu_title": "Exact rational assembly--ReLU equivalence",
        "relu_assembly": "rational assembly",
        "relu_knots": "dyadic knots",
        "relu_input": "input",
        "relu_output": "output",
        "relu_affine": "affine term",
        "relu_hidden": "hinge units",
        "exp_title": r"$f=e^x$ on $[0,1]$: error-to-bound ratio $\longrightarrow 1$",
        "scale": "scale",
        "exact_error": "exact error",
        "bound": "bound",
        "ratio": "error / bound",
        "runge_title": "Runge function: certified dyadic refinement with local majorants",
        "uniform": "uniform",
        "adaptive": "certified adaptive",
        "reference": r"reference $N^{-2}$",
        "segments_count": "number of segments $N$",
        "empirical_error": "empirical error",
        "adaptive_panel": r"partition for $\varepsilon_I=6.25\times10^{-4}$",
        "runge_curve": "Runge function",
        "interpolant": "interpolant",
        "coding_title": "Exact cost of three prefix-free formats",
        "coding_atoms": "structural atoms",
        "coding_relu_structural": "structural ReLU",
        "coding_relu_naive": "naive rational ReLU",
        "coding_height": "atomic height $H$",
        "coding_bits": "stream length (bits)",
    },
}


def save_figure(fig: plt.Figure, directory: Path, name: str, formats: Iterable[str]) -> None:
    directory.mkdir(parents=True, exist_ok=True)
    for extension in formats:
        kwargs = {"format": extension}
        if extension == "png":
            kwargs["dpi"] = 240
        fig.savefig(directory / f"{name}.{extension}", **kwargs)
    plt.close(fig)


def stern(n: int) -> int:
    """Return Stern's diatomic sequence S_n using the binary recursion."""
    if n == 0:
        return 0
    a, b = 1, 1
    for bit in bin(n)[3:]:
        if bit == "0":
            b = a + b
        else:
            a = a + b
    return a


def cw(n: int) -> tuple[int, int]:
    return stern(n), stern(n + 1)


def cantor_pair(u: int, v: int) -> int:
    return (u + v) * (u + v + 1) // 2 + v


def cantor_unpair(n: int) -> tuple[int, int]:
    w = (math.isqrt(8 * n + 1) - 1) // 2
    triangular = w * (w + 1) // 2
    v = n - triangular
    return w - v, v


def unpack4(n: int) -> tuple[int, int, int, int]:
    u, v = cantor_unpair(n)
    k, mu = cantor_unpair(u)
    r, t = cantor_unpair(v)
    return k, mu, r, t


def pack4(k: int, mu: int, r: int, t: int) -> int:
    return cantor_pair(cantor_pair(k, mu), cantor_pair(r, t))


def height(value: Fraction) -> int:
    return max(abs(value.numerator), value.denominator)


def height_ordered_rationals(count: int, exclude_zero: bool = False) -> list[Fraction]:
    values: list[Fraction] = []
    shell_height = 1
    while len(values) < count:
        shell: list[tuple[int, int]] = []
        for denominator in range(1, shell_height + 1):
            for numerator in range(-shell_height, shell_height + 1):
                if max(abs(numerator), denominator) != shell_height:
                    continue
                if math.gcd(abs(numerator), denominator) != 1:
                    continue
                if exclude_zero and numerator == 0:
                    continue
                shell.append((denominator, numerator))
        shell.sort()  # denominator first, then numerator
        values.extend(Fraction(p, q) for q, p in shell)
        shell_height += 1
    return values[:count]


def integer_value(mu: int) -> int:
    """Inverse of the integer enumeration Z used in the manuscript."""
    return mu // 2 if mu % 2 == 0 else -(mu + 1) // 2


def integer_index(value: int) -> int:
    """Index Z^{-1}(value)."""
    return 2 * value if value >= 0 else -2 * value - 1


def atom_height_from_indices(
    atom: tuple[int, int, int, int],
    rationals: list[Fraction],
    nonzero: list[Fraction],
) -> int:
    """Height of the atom represented by the arithmetic indices (k, mu, r, t)."""
    k, mu, r, t = atom
    return max(
        2,
        k + 1,
        abs(integer_value(mu)) + 1,
        height(rationals[r]),
        height(nonzero[t]),
    )


def sharp_catalog(count: int) -> list[tuple[int, int, int, int]]:
    """First ``count`` atoms in the height order Gamma^sharp.

    Shells are ordered by height.  Inside one shell, the key is exactly
    (k, Z^{-1}(m), rank_Q(y_0), rank_Qstar(s)), as in Definition ``def:sharp``.
    """
    atoms: list[tuple[int, int, int, int]] = []
    shell_height = 2
    while len(atoms) < count:
        value_count = rationals_up_to_height(shell_height)
        rationals = height_ordered_rationals(value_count)
        nonzero = height_ordered_rationals(value_count - 1, exclude_zero=True)
        integer_indices = sorted(
            integer_index(m) for m in range(-(shell_height - 1), shell_height)
        )
        for k in range(shell_height):
            for mu in integer_indices:
                for r in range(len(rationals)):
                    for t in range(len(nonzero)):
                        atom = (k, mu, r, t)
                        if atom_height_from_indices(atom, rationals, nonzero) != shell_height:
                            continue
                        atoms.append(atom)
                        if len(atoms) == count:
                            return atoms
        shell_height += 1
    return atoms


def gamma_and_sharp_agree_on_height(H: int) -> bool:
    """Compare the two enumerations after both are restricted to L_H."""
    sharp = set(sharp_catalog(atoms_up_to_height(H)))
    arithmetic = [unpack4(n) for n in range(gamma_worst_address(H) + 1)]
    max_r = max(atom[2] for atom in arithmetic)
    max_t = max(atom[3] for atom in arithmetic)
    rationals = height_ordered_rationals(max_r + 1)
    nonzero = height_ordered_rationals(max_t + 1, exclude_zero=True)
    restricted = {
        atom
        for atom in arithmetic
        if atom_height_from_indices(atom, rationals, nonzero) <= H
    }
    return restricted == sharp


def exact_indexing_checks() -> dict[str, object]:
    cantor_limit = 20_000
    tuple_limit = 20_000
    rational_count = 5_000

    cantor_ok = all(cantor_pair(*cantor_unpair(n)) == n for n in range(cantor_limit))
    tuple_ok = all(pack4(*unpack4(n)) == n for n in range(tuple_limit))

    rationals = height_ordered_rationals(rational_count)
    nonzero = height_ordered_rationals(rational_count, exclude_zero=True)

    rational_unique = len(set(rationals)) == rational_count
    nonzero_unique = len(set(nonzero)) == rational_count and all(q != 0 for q in nonzero)
    height_rank_q = all(index < 3 * height(value) ** 2 for index, value in enumerate(rationals))
    height_rank_qx = all(index < 3 * height(value) ** 2 for index, value in enumerate(nonzero))
    cw_identity = all(cw(2 ** (q - 1)) == (1, q) for q in range(1, 21))

    sharp_limit = 20_000
    sharp_atoms = sharp_catalog(sharp_limit)
    sharp_lookup = {atom: index for index, atom in enumerate(sharp_atoms)}
    sharp_roundtrip = len(sharp_lookup) == sharp_limit and all(
        sharp_atoms[sharp_lookup[atom]] == atom for atom in sharp_atoms
    )
    shell_heights = (2, 3)
    shell_sets_match = all(gamma_and_sharp_agree_on_height(H) for H in shell_heights)

    return {
        "cantor_roundtrip_limit": cantor_limit,
        "cantor_roundtrip_ok": cantor_ok,
        "tuple_roundtrip_limit": tuple_limit,
        "tuple_roundtrip_ok": tuple_ok,
        "height_rationals_count": rational_count,
        "height_rationals_unique": rational_unique,
        "height_nonzero_unique_and_nonzero": nonzero_unique,
        "height_rank_bound_q_ok": height_rank_q,
        "height_rank_bound_q_nonzero_ok": height_rank_qx,
        "cw_power_identity_q_max": 20,
        "cw_power_identity_ok": cw_identity,
        "sharp_roundtrip_limit": sharp_limit,
        "sharp_roundtrip_ok": sharp_roundtrip,
        "gamma_sharp_shell_set_heights": list(shell_heights),
        "gamma_sharp_shell_sets_match": shell_sets_match,
    }


def figure_dyadic(lang: str, formats: Iterable[str], output: Path) -> None:
    txt = TEXT[lang]
    fig, ax = plt.subplots(figsize=(8.0, 3.0))
    for k in range(5):
        y = 4 - k
        for m in range(2**k):
            left, right = m / 2**k, (m + 1) / 2**k
            ax.plot([left, right], [y, y], color="#174a73", lw=2.0)
            ax.plot([left, left], [y - 0.09, y + 0.09], color="#174a73", lw=0.8)
            ax.scatter([(left + right) / 2], [y], s=18, color="#b22222", zorder=3)
        ax.text(-0.035, y, rf"$k={k}$", ha="right", va="center")
    ax.set_xlim(-0.08, 1.02)
    ax.set_ylim(-0.45, 4.45)
    ax.set_xlabel(r"$x$")
    ax.set_yticks([])
    ax.set_title(txt["dyadic_title"])
    ax.text(0.5, -0.28, txt["dyadic_note"], ha="center", va="center", fontsize=9)
    save_figure(fig, output, "fig01_diadicos" if lang == "pt" else "fig01_dyadic", formats)


def figure_calkin_wilf(lang: str, formats: Iterable[str], output: Path) -> None:
    txt = TEXT[lang]
    fig, ax = plt.subplots(figsize=(8.0, 3.8))
    max_level = 3
    for level in range(max_level + 1):
        first, count = 2**level, 2**level
        xs = (np.arange(count) + 0.5) / count
        y = max_level - level
        for offset, x in enumerate(xs):
            p, q = cw(first + offset)
            ax.text(
                x,
                y,
                rf"$\frac{{{p}}}{{{q}}}$",
                ha="center",
                va="center",
                fontsize=10,
                bbox=dict(boxstyle="circle,pad=0.22", fc="white", ec="#174a73", lw=0.8),
            )
            if level < max_level:
                child_xs = (np.arange(2 ** (level + 1)) + 0.5) / 2 ** (level + 1)
                for child in (2 * offset, 2 * offset + 1):
                    ax.plot([x, child_xs[child]], [y - 0.13, y - 0.87], color="#777", lw=0.6)
    ax.set_xlim(0, 1)
    ax.set_ylim(-0.5, 3.55)
    ax.axis("off")
    ax.set_title(txt["cw_title"], pad=8)
    ax.text(0.5, -0.35, txt["cw_note"], ha="center", va="center", fontsize=9)
    save_figure(fig, output, "fig02_calkin_wilf", formats)


def rationalized_values(values: np.ndarray, denominator: int = 2**18) -> np.ndarray:
    """Round to one rational grid and enforce distinct adjacent values."""
    numerators = np.rint(values * denominator).astype(np.int64)
    for j in range(1, len(numerators)):
        if numerators[j] == numerators[j - 1]:
            numerators[j] += 1 if j % 2 else -1
    return numerators.astype(float) / denominator


# ---------------------------------------------------------------------------
# Validated rational interval arithmetic and second-order automatic derivatives
# ---------------------------------------------------------------------------


class IntervalEvaluationError(ValueError):
    """Raised when a requested interval certificate cannot be produced safely."""


@dataclass(frozen=True)
class RationalInterval:
    """Closed interval with exact rational endpoints."""

    lower: Fraction
    upper: Fraction

    def __post_init__(self) -> None:
        object.__setattr__(self, "lower", Fraction(self.lower))
        object.__setattr__(self, "upper", Fraction(self.upper))
        if self.lower > self.upper:
            raise ValueError("an interval needs lower <= upper")

    @classmethod
    def point(cls, value: Fraction | int) -> "RationalInterval":
        value = Fraction(value)
        return cls(value, value)

    @property
    def width(self) -> Fraction:
        return self.upper - self.lower

    @property
    def midpoint(self) -> Fraction:
        return (self.lower + self.upper) / 2

    @property
    def abs_upper(self) -> Fraction:
        return max(abs(self.lower), abs(self.upper))

    def __add__(self, other: "RationalInterval") -> "RationalInterval":
        return RationalInterval(self.lower + other.lower, self.upper + other.upper)

    def __neg__(self) -> "RationalInterval":
        return RationalInterval(-self.upper, -self.lower)

    def __sub__(self, other: "RationalInterval") -> "RationalInterval":
        return self + (-other)

    def __mul__(self, other: "RationalInterval") -> "RationalInterval":
        products = (
            self.lower * other.lower,
            self.lower * other.upper,
            self.upper * other.lower,
            self.upper * other.upper,
        )
        return RationalInterval(min(products), max(products))

    def reciprocal(self) -> "RationalInterval":
        if self.lower <= 0 <= self.upper:
            raise IntervalEvaluationError("a denominator enclosure contains zero")
        return RationalInterval(
            min(Fraction(1, 1) / self.lower, Fraction(1, 1) / self.upper),
            max(Fraction(1, 1) / self.lower, Fraction(1, 1) / self.upper),
        )

    def __truediv__(self, other: "RationalInterval") -> "RationalInterval":
        return self * other.reciprocal()

    def __pow__(self, exponent: int) -> "RationalInterval":
        if exponent < 0:
            return (self.reciprocal()) ** (-exponent)
        result = RationalInterval.point(1)
        base = self
        power = exponent
        while power:
            if power & 1:
                result = result * base
            base = base * base
            power >>= 1
        return result

    def inflate(self, radius: Fraction) -> "RationalInterval":
        radius = abs(Fraction(radius))
        return RationalInterval(self.lower - radius, self.upper + radius)

    def intersect(self, other: "RationalInterval") -> "RationalInterval":
        lower = max(self.lower, other.lower)
        upper = min(self.upper, other.upper)
        if lower > upper:
            raise AssertionError("two proven enclosures cannot be disjoint")
        return RationalInterval(lower, upper)


def interval_hull(intervals: Iterable[RationalInterval]) -> RationalInterval:
    values = tuple(intervals)
    if not values:
        raise ValueError("cannot take the hull of no intervals")
    return RationalInterval(
        min(interval.lower for interval in values),
        max(interval.upper for interval in values),
    )


def _exp_small_nonnegative(value: Fraction, terms: int) -> RationalInterval:
    """Enclose exp(value) for 0 <= value <= 1/2 by a geometric tail."""
    if not 0 <= value <= Fraction(1, 2):
        raise ValueError("range reduction failed")
    partial = Fraction(1)
    term = Fraction(1)
    for index in range(1, terms + 1):
        term *= value / index
        partial += term
    next_term = term * value / (terms + 1)
    ratio = value / (terms + 2)
    tail = next_term / (1 - ratio)
    return RationalInterval(partial, partial + tail)


def exp_point_interval(value: Fraction, precision_bits: int = 80) -> RationalInterval:
    """Rigorous rational enclosure of exp(value), with adjustable precision."""
    value = Fraction(value)
    if value == 0:
        return RationalInterval.point(1)
    if value < 0:
        return exp_point_interval(-value, precision_bits).reciprocal()

    reductions = 0
    reduced = value
    while reduced > Fraction(1, 2):
        reduced /= 2
        reductions += 1
    target = Fraction(1, 2**precision_bits)
    candidate = RationalInterval.point(1)
    for terms in range(2, 513):
        candidate = _exp_small_nonnegative(reduced, terms)
        for _ in range(reductions):
            candidate = candidate * candidate
        if candidate.width <= target:
            return candidate
    return candidate


def exp_interval(interval: RationalInterval, precision_bits: int = 80) -> RationalInterval:
    lower = exp_point_interval(interval.lower, precision_bits).lower
    upper = exp_point_interval(interval.upper, precision_bits).upper
    return RationalInterval(lower, upper)


def _trig_interval(
    interval: RationalInterval, kind: str, precision_bits: int = 80
) -> RationalInterval:
    """Taylor enclosure with a uniform rational Lagrange remainder."""
    if kind not in {"sin", "cos"}:
        raise ValueError("kind must be sin or cos")
    magnitude = interval.abs_upper
    target = Fraction(1, 2**precision_bits)
    terms = 0
    remainder = Fraction(0)
    for terms in range(513):
        degree = 2 * terms + (2 if kind == "sin" else 1)
        remainder = magnitude**degree / math.factorial(degree)
        if remainder <= target:
            break
    else:
        return RationalInterval(-1, 1)

    polynomial = RationalInterval.point(0)
    for index in range(terms + 1):
        degree = 2 * index + (1 if kind == "sin" else 0)
        term = (interval**degree) / RationalInterval.point(math.factorial(degree))
        polynomial = polynomial + (term if index % 2 == 0 else -term)
    return polynomial.inflate(remainder).intersect(RationalInterval(-1, 1))


def sin_interval(interval: RationalInterval, precision_bits: int = 80) -> RationalInterval:
    return _trig_interval(interval, "sin", precision_bits)


def cos_interval(interval: RationalInterval, precision_bits: int = 80) -> RationalInterval:
    return _trig_interval(interval, "cos", precision_bits)


@dataclass(frozen=True)
class Expression:
    """Small expression grammar used by the certified adaptive algorithm."""

    operation: str
    arguments: tuple["Expression", ...] = ()
    constant: Fraction | None = None

    def __add__(self, other: object) -> "Expression":
        return Expression("add", (self, as_expression(other)))

    def __radd__(self, other: object) -> "Expression":
        return as_expression(other) + self

    def __neg__(self) -> "Expression":
        return Expression("neg", (self,))

    def __sub__(self, other: object) -> "Expression":
        return self + (-as_expression(other))

    def __rsub__(self, other: object) -> "Expression":
        return as_expression(other) - self

    def __mul__(self, other: object) -> "Expression":
        return Expression("mul", (self, as_expression(other)))

    def __rmul__(self, other: object) -> "Expression":
        return as_expression(other) * self

    def reciprocal(self) -> "Expression":
        return Expression("inv", (self,))

    def __truediv__(self, other: object) -> "Expression":
        return self * as_expression(other).reciprocal()

    def __rtruediv__(self, other: object) -> "Expression":
        return as_expression(other) / self

    def __pow__(self, exponent: int) -> "Expression":
        if exponent < 0:
            return (self.reciprocal()) ** (-exponent)
        result = as_expression(1)
        for _ in range(exponent):
            result = result * self
        return result


def as_expression(value: object) -> Expression:
    if isinstance(value, Expression):
        return value
    if isinstance(value, (int, Fraction)):
        return Expression("const", constant=Fraction(value))
    raise TypeError(f"unsupported expression operand: {type(value)!r}")


X = Expression("var")


def Exp(argument: object) -> Expression:
    return Expression("exp", (as_expression(argument),))


def Sin(argument: object) -> Expression:
    return Expression("sin", (as_expression(argument),))


def Cos(argument: object) -> Expression:
    return Expression("cos", (as_expression(argument),))


@dataclass(frozen=True)
class IntervalJet2:
    value: RationalInterval
    first: RationalInterval
    second: RationalInterval


def evaluate_interval_jet2(
    expression: Expression, domain: RationalInterval, precision_bits: int = 80
) -> IntervalJet2:
    """Evaluate value, first derivative, and second derivative inclusions."""
    zero = RationalInterval.point(0)
    one = RationalInterval.point(1)
    operation = expression.operation
    if operation == "const":
        assert expression.constant is not None
        return IntervalJet2(RationalInterval.point(expression.constant), zero, zero)
    if operation == "var":
        return IntervalJet2(domain, one, zero)

    jets = tuple(
        evaluate_interval_jet2(argument, domain, precision_bits)
        for argument in expression.arguments
    )
    if operation == "neg":
        u = jets[0]
        return IntervalJet2(-u.value, -u.first, -u.second)
    if operation == "add":
        u, v = jets
        return IntervalJet2(u.value + v.value, u.first + v.first, u.second + v.second)
    if operation == "mul":
        u, v = jets
        return IntervalJet2(
            u.value * v.value,
            u.first * v.value + u.value * v.first,
            u.second * v.value
            + RationalInterval.point(2) * u.first * v.first
            + u.value * v.second,
        )
    if operation == "inv":
        u = jets[0]
        reciprocal = u.value.reciprocal()
        reciprocal2 = reciprocal * reciprocal
        return IntervalJet2(
            reciprocal,
            -u.first * reciprocal2,
            RationalInterval.point(2) * u.first * u.first * reciprocal2 * reciprocal
            - u.second * reciprocal2,
        )
    if operation == "exp":
        u = jets[0]
        value = exp_interval(u.value, precision_bits)
        return IntervalJet2(
            value,
            value * u.first,
            value * (u.first * u.first + u.second),
        )
    if operation == "sin":
        u = jets[0]
        sine = sin_interval(u.value, precision_bits)
        cosine = cos_interval(u.value, precision_bits)
        return IntervalJet2(
            sine,
            cosine * u.first,
            -sine * u.first * u.first + cosine * u.second,
        )
    if operation == "cos":
        u = jets[0]
        sine = sin_interval(u.value, precision_bits)
        cosine = cos_interval(u.value, precision_bits)
        return IntervalJet2(
            cosine,
            -sine * u.first,
            -cosine * u.first * u.first - sine * u.second,
        )
    raise ValueError(f"unknown expression operation: {operation}")


@dataclass(frozen=True)
class SecondDerivativeCertificate:
    lower: Fraction
    upper: Fraction
    majorant: Fraction
    boxes_evaluated: int
    subdivision_depth: int
    precision_bits: int


def BoundSecondDerivative(
    expression: Expression,
    interval: tuple[Fraction | int, Fraction | int],
    *,
    subdivision_depth: int = 0,
    max_depth: int | None = None,
    precision_bits: int = 80,
) -> SecondDerivativeCertificate:
    """Return a sound rational enclosure of f'' on an interval.

    The routine never falls back to sampling.  If a denominator cannot be
    separated from zero by the permitted subdivisions, it raises
    ``IntervalEvaluationError`` instead of returning an uncertified number.
    """
    lower, upper = map(Fraction, interval)
    if lower >= upper:
        raise ValueError("BoundSecondDerivative needs a nondegenerate interval")
    if subdivision_depth < 0 or precision_bits < 2:
        raise ValueError("invalid certification parameters")
    if max_depth is None:
        max_depth = subdivision_depth
    if max_depth < subdivision_depth:
        raise ValueError("max_depth must be at least subdivision_depth")

    enclosures: list[RationalInterval] = []
    deepest = 0

    def visit(box: RationalInterval, depth: int) -> None:
        nonlocal deepest
        deepest = max(deepest, depth)
        if depth < subdivision_depth:
            midpoint = box.midpoint
            visit(RationalInterval(box.lower, midpoint), depth + 1)
            visit(RationalInterval(midpoint, box.upper), depth + 1)
            return
        try:
            enclosures.append(
                evaluate_interval_jet2(expression, box, precision_bits).second
            )
        except IntervalEvaluationError:
            if depth >= max_depth:
                raise
            midpoint = box.midpoint
            visit(RationalInterval(box.lower, midpoint), depth + 1)
            visit(RationalInterval(midpoint, box.upper), depth + 1)

    visit(RationalInterval(lower, upper), 0)
    hull = interval_hull(enclosures)
    return SecondDerivativeCertificate(
        lower=hull.lower,
        upper=hull.upper,
        majorant=max(abs(hull.lower), abs(hull.upper)),
        boxes_evaluated=len(enclosures),
        subdivision_depth=deepest,
        precision_bits=precision_bits,
    )


# ---------------------------------------------------------------------------
# Exact rational assembly--ReLU conversion
# ---------------------------------------------------------------------------


def dyadic_exponent(value: Fraction) -> int:
    """Return k when the reduced denominator of ``value`` is 2**k."""
    denominator = value.denominator
    if denominator & (denominator - 1):
        raise ValueError(f"non-dyadic rational: {value}")
    return denominator.bit_length() - 1


@dataclass(frozen=True)
class RationalLeaf:
    """One exact library atom represented by its local rational parameters."""

    k: int
    m: int
    y0: Fraction
    slope: Fraction

    def __post_init__(self) -> None:
        if self.k < 0 or self.slope == 0:
            raise ValueError("a library leaf needs k >= 0 and nonzero slope")

    @property
    def left(self) -> Fraction:
        return Fraction(self.m, 2**self.k)

    @property
    def right(self) -> Fraction:
        return Fraction(self.m + 1, 2**self.k)

    @property
    def centre(self) -> Fraction:
        return Fraction(2 * self.m + 1, 2 ** (self.k + 1))

    @property
    def intercept(self) -> Fraction:
        return self.y0 - self.slope * self.centre

    @property
    def left_value(self) -> Fraction:
        return self.intercept + self.slope * self.left

    @property
    def right_value(self) -> Fraction:
        return self.intercept + self.slope * self.right


@dataclass(frozen=True)
class HingeNetwork:
    """Normalized shallow network c + q*x + sum a_j*ReLU(x-t_j)."""

    intercept: Fraction
    linear_weight: Fraction
    hinges: tuple[tuple[Fraction, Fraction], ...]  # (knot, output weight)

    def value(self, x: Fraction) -> Fraction:
        return self.intercept + self.linear_weight * x + sum(
            coefficient * max(Fraction(0), x - knot)
            for knot, coefficient in self.hinges
        )

    def slope_at(self, x: Fraction) -> Fraction:
        if any(x == knot for knot, _ in self.hinges):
            raise ValueError("the derivative is not queried at a hinge")
        return self.linear_weight + sum(
            coefficient for knot, coefficient in self.hinges if x > knot
        )


def _validate_continuous_leaves(leaves: tuple[RationalLeaf, ...]) -> None:
    if not leaves:
        raise ValueError("an assembly must contain at least one leaf")
    for left, right in zip(leaves, leaves[1:]):
        if left.right != right.left:
            raise ValueError("leaves must be spatially consecutive")
        if left.right_value != right.left_value:
            raise ValueError("adjacent atoms do not agree at their boundary")


def assembly_to_relu(leaves: Iterable[RationalLeaf]) -> HingeNetwork:
    """Convert an exact continuous rational assembly to normalized ReLU form."""
    ordered = tuple(sorted(leaves, key=lambda leaf: leaf.left))
    _validate_continuous_leaves(ordered)
    hinges = tuple(
        (ordered[j].left, ordered[j].slope - ordered[j - 1].slope)
        for j in range(1, len(ordered))
    )
    return HingeNetwork(ordered[0].intercept, ordered[0].slope, hinges)


def relu_to_assembly(
    network: HingeNetwork, domain_left: Fraction, domain_right: Fraction
) -> tuple[RationalLeaf, ...]:
    """Convert a normalized rational ReLU network on a dyadic domain to atoms.

    A uniform dyadic refinement containing every active hinge is used.  The
    conversion is rejected exactly when a local slope vanishes, because such a
    piece is outside the content-addressable library.
    """
    if domain_left >= domain_right:
        raise ValueError("the domain must be a nondegenerate interval")
    active_knots = tuple(
        knot for knot, _ in network.hinges if domain_left < knot < domain_right
    )
    exponents = [dyadic_exponent(domain_left), dyadic_exponent(domain_right)]
    exponents.extend(dyadic_exponent(knot) for knot in active_knots)
    k = max(exponents)
    scale = 2**k
    left_index = domain_left * scale
    right_index = domain_right * scale
    if left_index.denominator != 1 or right_index.denominator != 1:
        raise AssertionError("dyadic refinement failed to align the domain")

    leaves: list[RationalLeaf] = []
    for m in range(int(left_index), int(right_index)):
        centre = Fraction(2 * m + 1, 2 ** (k + 1))
        slope = network.slope_at(centre)
        if slope == 0:
            raise ValueError("a zero local slope is not a library atom")
        leaves.append(RationalLeaf(k, m, network.value(centre), slope))
    result = tuple(leaves)
    _validate_continuous_leaves(result)
    return result


def piecewise_signature(
    leaves: Iterable[RationalLeaf],
) -> tuple[tuple[Fraction, Fraction, Fraction, Fraction], ...]:
    """Canonical functional signature, merging redundant adjacent pieces."""
    ordered = tuple(sorted(leaves, key=lambda leaf: leaf.left))
    _validate_continuous_leaves(ordered)
    pieces: list[tuple[Fraction, Fraction, Fraction, Fraction]] = []
    for leaf in ordered:
        current = (leaf.left, leaf.right, leaf.intercept, leaf.slope)
        if (
            pieces
            and pieces[-1][1] == current[0]
            and pieces[-1][2:] == current[2:]
        ):
            previous = pieces[-1]
            pieces[-1] = (previous[0], current[1], previous[2], previous[3])
        else:
            pieces.append(current)
    return tuple(pieces)


def _deterministic_rational_assembly(case: int) -> tuple[RationalLeaf, ...]:
    """Generate one exact test assembly without pseudorandomness."""
    k = 3 + case % 3
    count = 2 + case % 6
    start = (case // 6) % 7 - 3
    left_value = Fraction(case % 23 - 11, 1 + case % 9)
    leaves: list[RationalLeaf] = []
    previous_slope: Fraction | None = None
    width = Fraction(1, 2**k)
    for j in range(count):
        numerator = ((case + 3) * (j + 2) + 5 * j) % 19 - 9
        if numerator == 0:
            numerator = 10
        slope = Fraction(numerator, 1 + (case + 2 * j) % 7)
        if slope == previous_slope:
            slope += Fraction(1, 11 + j)
        if slope == 0:
            slope = Fraction(1, 13 + j)
        y0 = left_value + slope * width / 2
        leaf = RationalLeaf(k, start + j, y0, slope)
        leaves.append(leaf)
        left_value = leaf.right_value
        previous_slope = slope
    result = tuple(leaves)
    _validate_continuous_leaves(result)
    return result


def relu_equivalence_checks(example_count: int = 4_096) -> dict[str, object]:
    """Thousands of exact two-way conversions using ``Fraction`` only."""
    forward_ok = True
    reverse_ok = True
    rational_ok = True
    nonzero_ok = True
    widths_ok = True
    largest_width = 0
    largest_reverse_leaf_count = 0
    for case in range(example_count):
        leaves = _deterministic_rational_assembly(case)
        network = assembly_to_relu(leaves)
        largest_width = max(largest_width, len(network.hinges))
        widths_ok &= len(network.hinges) == len(leaves) - 1
        rational_ok &= all(
            isinstance(value, Fraction)
            for value in (network.intercept, network.linear_weight)
        ) and all(
            isinstance(value, Fraction)
            for hinge in network.hinges
            for value in hinge
        )
        for leaf in leaves:
            forward_ok &= network.value(leaf.left) == leaf.left_value
            forward_ok &= network.value(leaf.right) == leaf.right_value
            forward_ok &= network.value(leaf.centre) == leaf.y0
            forward_ok &= network.slope_at(leaf.centre) == leaf.slope

        reconstructed = relu_to_assembly(network, leaves[0].left, leaves[-1].right)
        largest_reverse_leaf_count = max(largest_reverse_leaf_count, len(reconstructed))
        reverse_ok &= piecewise_signature(reconstructed) == piecewise_signature(leaves)
        nonzero_ok &= all(leaf.slope != 0 for leaf in reconstructed)

    return {
        "exact_examples": example_count,
        "arithmetic": "fractions.Fraction",
        "assembly_to_relu_exact": bool(forward_ok),
        "relu_to_assembly_exact": bool(reverse_ok),
        "all_network_parameters_rational": bool(rational_ok),
        "nonzero_local_slopes_preserved": bool(nonzero_ok),
        "width_equals_leaf_count_minus_one": bool(widths_ok),
        "largest_tested_hidden_width": largest_width,
        "largest_reconstructed_leaf_count": largest_reverse_leaf_count,
    }


def figure_relu_equivalence(lang: str, formats: Iterable[str], output: Path) -> None:
    """Exact rational example and its normalized shallow-network diagram."""
    txt = TEXT[lang]
    slopes = (Fraction(1), Fraction(-1, 2), Fraction(3, 2), Fraction(1, 3))
    left_value = Fraction(-1, 4)
    leaves: list[RationalLeaf] = []
    for m, slope in enumerate(slopes):
        leaf = RationalLeaf(2, m, left_value + slope / 8, slope)
        leaves.append(leaf)
        left_value = leaf.right_value
    network = assembly_to_relu(leaves)

    fig, axes = plt.subplots(1, 2, figsize=(9.0, 3.35), gridspec_kw={"width_ratios": [1.15, 1.0]})
    ax = axes[0]
    for j, leaf in enumerate(leaves):
        xs = np.array([float(leaf.left), float(leaf.right)])
        ys = np.array([float(leaf.left_value), float(leaf.right_value)])
        ax.plot(xs, ys, lw=2.0, color="#1f77b4", label=txt["relu_assembly"] if j == 0 else None)
    knots = [float(leaf.right) for leaf in leaves[:-1]]
    knot_values = [float(network.value(leaf.right)) for leaf in leaves[:-1]]
    ax.scatter(knots, knot_values, color="#b22222", s=25, zorder=3, label=txt["relu_knots"])
    ax.set_xlabel(r"$x$")
    ax.set_ylabel(r"$g(x)$")
    ax.set_xlim(-0.02, 1.02)
    ax.grid(alpha=0.18)
    ax.legend(fontsize=8, loc="best")
    ax.set_title(r"$g(x)=c+qx+\sum_{j=1}^{3}a_j\rho(x-t_j)$", fontsize=10)

    ax = axes[1]
    ax.set_xlim(0, 1)
    ax.set_ylim(-0.58, 0.88)
    ax.axis("off")
    input_xy = (0.08, 0.12)
    output_xy = (0.92, 0.12)
    hidden_y = (0.67, 0.24, -0.19)
    for y, (knot, coefficient) in zip(hidden_y, network.hinges):
        ax.plot([input_xy[0], 0.46], [input_xy[1], y], color="#777", lw=0.8)
        ax.plot([0.54, output_xy[0]], [y, output_xy[1]], color="#777", lw=0.8)
        ax.scatter([0.50], [y], s=640, facecolor="white", edgecolor="#174a73", linewidth=1.0, zorder=3)
        ax.text(0.50, y, rf"$\rho(x-{str(knot)})$", ha="center", va="center", fontsize=8)
        ax.text(0.70, (y + output_xy[1]) / 2 + 0.025, rf"$a={str(coefficient)}$", fontsize=7, color="#555")
    ax.plot([input_xy[0], output_xy[0]], [input_xy[1] - 0.08, output_xy[1] - 0.08], "--", color="#b22222", lw=1.0)
    ax.scatter([input_xy[0], output_xy[0]], [input_xy[1], output_xy[1]], s=500, facecolor="white", edgecolor="#174a73", linewidth=1.0, zorder=3)
    ax.text(*input_xy, "$x$", ha="center", va="center", fontsize=10)
    ax.text(*output_xy, "$g(x)$", ha="center", va="center", fontsize=9)
    ax.text(0.50, -0.48, txt["relu_affine"] + r" $c+qx$", ha="center", fontsize=8, color="#8b1a1a")
    ax.text(0.50, 0.83, txt["relu_hidden"], ha="center", fontsize=9)
    fig.suptitle(txt["relu_title"])
    fig.tight_layout()
    save_figure(fig, output, "fig07_relu" if lang == "pt" else "fig07_relu", formats)


def figure_approximation(lang: str, formats: Iterable[str], output: Path) -> None:
    txt = TEXT[lang]
    target = lambda x: np.exp(0.8 * x) * np.cos(3 * x)
    x = np.linspace(0.0, 1.0, 3_000)
    fig, axes = plt.subplots(1, 2, figsize=(8.0, 3.1), sharey=True)
    for ax, k in zip(axes, (2, 4)):
        nodes = np.linspace(0.0, 1.0, 2**k + 1)
        nodal = rationalized_values(target(nodes))
        ax.plot(x, target(x), color="black", lw=1.45, label=txt["assembly_curve"])
        ax.plot(x, np.interp(x, nodes, nodal), color="#1f77b4", lw=1.15, label=txt["assembly_atoms"])
        ax.scatter(nodes, nodal, s=9, color="#b22222", zorder=3)
        ax.set_title(
            f"{txt['assembly_scale']} $k={k}$ ({2**k} {txt['assembly_segments']})"
        )
        ax.set_xlabel(r"$x$")
        ax.grid(alpha=0.18)
    axes[0].set_ylabel(r"$y$")
    axes[0].legend(loc="best", fontsize=8)
    fig.suptitle(txt["assembly_title"])
    fig.tight_layout()
    save_figure(fig, output, "fig03_aproximacao" if lang == "pt" else "fig03_approximation", formats)


def exp_interpolation_error(k: int) -> float:
    h = 2.0 ** (-k)
    largest = 0.0
    for j in range(2**k):
        left, right = j * h, (j + 1) * h
        slope = (math.exp(right) - math.exp(left)) / h
        critical = math.log(slope)
        chord = math.exp(left) + slope * (critical - left)
        largest = max(largest, chord - math.exp(critical))
    return largest


def figure_exp_and_table(lang: str, formats: Iterable[str], output: Path) -> list[dict[str, float]]:
    txt = TEXT[lang]
    scales = np.arange(1, 11)
    errors = np.array([exp_interpolation_error(int(k)) for k in scales])
    bounds = np.exp(1.0) * 2.0 ** (-2.0 * scales) / 8.0
    ratios = errors / bounds

    fig, axes = plt.subplots(1, 2, figsize=(8.0, 3.1))
    axes[0].semilogy(scales, errors, "o-", color="#1f77b4", label=txt["exact_error"])
    axes[0].semilogy(scales, bounds, "--", color="#b22222", label=txt["bound"])
    axes[0].set_xlabel(txt["scale"] + r" $k$")
    axes[0].set_ylabel(r"$\|f-P_kf\|_\infty$")
    axes[0].legend(fontsize=8)
    axes[0].grid(alpha=0.2)
    axes[1].plot(scales, ratios, "o-", color="#1f77b4")
    axes[1].axhline(1.0, ls="--", color="#b22222", lw=1.0)
    axes[1].set_xlabel(txt["scale"] + r" $k$")
    axes[1].set_ylabel(txt["ratio"])
    axes[1].set_ylim(0.45, 1.02)
    axes[1].grid(alpha=0.2)
    fig.suptitle(txt["exp_title"])
    fig.tight_layout()
    save_figure(fig, output, "fig04_exp", formats)

    table: list[dict[str, float]] = []
    for k in (2, 4, 6, 8, 10):
        index = k - 1
        table.append(
            {
                "k": k,
                "error": float(errors[index]),
                "bound": float(bounds[index]),
                "ratio": float(ratios[index]),
            }
        )
    return table


def runge(x: np.ndarray | float) -> np.ndarray:
    values = np.asarray(x)
    return 1.0 / (1.0 + 25.0 * values**2)


def runge_second(x: float) -> float:
    return 50.0 * (75.0 * x * x - 1.0) / (1.0 + 25.0 * x * x) ** 3


def runge_local_majorant(left: float, right: float) -> float:
    candidates = [left, right]
    candidates.extend(point for point in (-0.2, 0.0, 0.2) if left <= point <= right)
    return max(abs(runge_second(point)) for point in candidates)


RUNGE_EXPRESSION = 1 / (1 + 25 * X * X)


@lru_cache(maxsize=None)
def runge_interval_certificate(
    left: Fraction, right: Fraction
) -> SecondDerivativeCertificate:
    """Validated curvature enclosure used by the adaptive algorithm."""
    return BoundSecondDerivative(
        RUNGE_EXPRESSION,
        (left, right),
        subdivision_depth=5,
        max_depth=10,
        precision_bits=96,
    )


@dataclass(frozen=True)
class Leaf:
    left: Fraction
    right: Fraction

    @property
    def width(self) -> Fraction:
        return self.right - self.left

    @property
    def certificate(self) -> float:
        curvature = runge_interval_certificate(self.left, self.right).majorant
        return float(self.width**2 * curvature / 8)

    @property
    def exact_curvature_certificate(self) -> float:
        return (
            float(self.width) ** 2
            * runge_local_majorant(float(self.left), float(self.right))
            / 8.0
        )


def adaptive_leaves(tolerance: float) -> list[Leaf]:
    leaves = [Leaf(Fraction(-1), Fraction(0)), Leaf(Fraction(0), Fraction(1))]
    while True:
        changed = False
        refined: list[Leaf] = []
        for leaf in leaves:
            if leaf.certificate > tolerance:
                midpoint = (leaf.left + leaf.right) / 2
                refined.extend([Leaf(leaf.left, midpoint), Leaf(midpoint, leaf.right)])
                changed = True
            else:
                refined.append(leaf)
        leaves = refined
        if not changed:
            return leaves


def piecewise_error(leaves: list[Leaf], points_per_leaf: int = 4_001) -> float:
    largest = 0.0
    for leaf in leaves:
        left, right = float(leaf.left), float(leaf.right)
        x = np.linspace(left, right, points_per_leaf)
        approx = np.interp(x, [left, right], [runge(left), runge(right)])
        largest = max(largest, float(np.max(np.abs(runge(x) - approx))))
    return largest


def uniform_runge_error(n: int) -> float:
    nodes = np.linspace(-1.0, 1.0, n + 1)
    x = np.linspace(-1.0, 1.0, max(40_001, 500 * n + 1))
    return float(np.max(np.abs(runge(x) - np.interp(x, nodes, runge(nodes)))))


def figure_adaptive_and_table(
    lang: str, formats: Iterable[str], output: Path
) -> list[dict[str, float]]:
    txt = TEXT[lang]
    tolerances = np.array([2e-2, 1e-2, 5e-3, 2.5e-3, 1.25e-3, 6.25e-4, 3.125e-4])
    adaptive: list[dict[str, float]] = []
    for tolerance in tolerances:
        leaves = adaptive_leaves(float(tolerance))
        interval_certificates = [
            runge_interval_certificate(leaf.left, leaf.right) for leaf in leaves
        ]
        certificate = max(leaf.certificate for leaf in leaves)
        exact_curvature_certificate = max(
            leaf.exact_curvature_certificate for leaf in leaves
        )
        adaptive.append(
            {
                "tolerance": float(tolerance),
                "n": len(leaves),
                "e_cert": certificate,
                "e_emp": piecewise_error(leaves),
                "e_exact": None,
                "exact_curvature_certificate": exact_curvature_certificate,
                "certificate_slack_over_exact_curvature": (
                    certificate / exact_curvature_certificate
                ),
                "interval_boxes_per_leaf": interval_certificates[0].boxes_evaluated,
                "interval_subdivision_depth": max(
                    item.subdivision_depth for item in interval_certificates
                ),
                "scaled_leaf_count_sqrt_tolerance": float(
                    len(leaves) * math.sqrt(float(tolerance))
                ),
                "uniform_certified_n": int(
                    2 ** math.ceil(math.log2(5.0 / math.sqrt(float(tolerance))))
                ),
            }
        )

    uniform_ns = np.array([8, 16, 32, 64, 128, 256])
    uniform_errors = np.array([uniform_runge_error(int(n)) for n in uniform_ns])
    adaptive_ns = np.array([row["n"] for row in adaptive])
    adaptive_errors = np.array([row["e_emp"] for row in adaptive])

    fig, axes = plt.subplots(1, 2, figsize=(8.0, 3.15))
    axes[0].loglog(uniform_ns, uniform_errors, "o-", color="#555", label=txt["uniform"])
    axes[0].loglog(adaptive_ns, adaptive_errors, "s-", color="#1f77b4", label=txt["adaptive"])
    reference_n = np.array([8.0, 256.0])
    axes[0].loglog(reference_n, 3.2 / reference_n**2, "--", color="#b22222", label=txt["reference"])
    axes[0].set_xlabel(txt["segments_count"])
    axes[0].set_ylabel(txt["empirical_error"])
    axes[0].grid(alpha=0.2, which="both")
    axes[0].legend(fontsize=8)

    representative = adaptive_leaves(6.25e-4)
    nodes = np.array(
        [float(representative[0].left)]
        + [float(leaf.right) for leaf in representative]
    )
    dense = np.linspace(-1.0, 1.0, 4_000)
    axes[1].plot(dense, runge(dense), color="black", lw=1.35, label=txt["runge_curve"])
    axes[1].plot(dense, np.interp(dense, nodes, runge(nodes)), color="#1f77b4", lw=1.0, label=txt["interpolant"])
    for node in nodes[1:-1]:
        axes[1].axvline(node, color="#b22222", lw=0.28, alpha=0.38)
    axes[1].set_xlim(-1.02, 1.02)
    axes[1].set_xlabel(r"$x$")
    axes[1].set_title(txt["adaptive_panel"] + f" ($N={len(representative)}$)")
    axes[1].legend(fontsize=7, loc="upper right")
    fig.suptitle(txt["runge_title"])
    fig.tight_layout()
    save_figure(fig, output, "fig05_adaptativo" if lang == "pt" else "fig05_adaptive", formats)
    return adaptive


def _linear_interpolation_empirical_error(
    function: object, left: float, right: float, samples: int = 200_001
) -> float:
    grid = np.linspace(left, right, samples)
    endpoint_values = np.asarray(function(np.array([left, right])), dtype=float)
    interpolant = np.interp(grid, [left, right], endpoint_values)
    return float(np.max(np.abs(np.asarray(function(grid), dtype=float) - interpolant)))


def interval_arithmetic_checks() -> dict[str, object]:
    """Check the certified grammar without using samples as proof."""
    quadratic = X * X
    exponential = Exp(X)
    sine = Sin(X)
    cosine_composition = Cos(X * X + Fraction(1, 7))
    rational = 1 / (2 + X * X)

    certificates = {
        "polynomial": BoundSecondDerivative(quadratic, (-1, 1)),
        "rational": BoundSecondDerivative(
            rational, (-1, 1), subdivision_depth=5, max_depth=8
        ),
        "exp": BoundSecondDerivative(
            exponential, (0, 1), subdivision_depth=4, precision_bits=96
        ),
        "sin": BoundSecondDerivative(
            sine, (0, Fraction(1, 2)), subdivision_depth=4, precision_bits=96
        ),
        "cos_composition": BoundSecondDerivative(
            cosine_composition,
            (0, Fraction(1, 2)),
            subdivision_depth=5,
            precision_bits=96,
        ),
        "runge": BoundSecondDerivative(
            RUNGE_EXPRESSION, (-1, 1), subdivision_depth=7, max_depth=10
        ),
    }

    numeric_second_derivatives = {
        "polynomial": lambda x: np.full_like(np.asarray(x, dtype=float), 2.0),
        "rational": lambda x: (6.0 * np.asarray(x, dtype=float) ** 2 - 4.0)
        / (2.0 + np.asarray(x, dtype=float) ** 2) ** 3,
        "exp": lambda x: np.exp(np.asarray(x, dtype=float)),
        "sin": lambda x: -np.sin(np.asarray(x, dtype=float)),
        "cos_composition": lambda x: -4.0
        * np.asarray(x, dtype=float) ** 2
        * np.cos(np.asarray(x, dtype=float) ** 2 + 1.0 / 7.0)
        - 2.0 * np.sin(np.asarray(x, dtype=float) ** 2 + 1.0 / 7.0),
        "runge": lambda x: 50.0
        * (75.0 * np.asarray(x, dtype=float) ** 2 - 1.0)
        / (1.0 + 25.0 * np.asarray(x, dtype=float) ** 2) ** 3,
    }
    domains = {
        "polynomial": (-1.0, 1.0),
        "rational": (-1.0, 1.0),
        "exp": (0.0, 1.0),
        "sin": (0.0, 0.5),
        "cos_composition": (0.0, 0.5),
        "runge": (-1.0, 1.0),
    }
    diagnostic_sampling_inside = True
    probe_rows = []
    for name, certificate in certificates.items():
        left, right = domains[name]
        grid = np.linspace(left, right, 20_001)
        values = np.asarray(numeric_second_derivatives[name](grid), dtype=float)
        diagnostic_sampling_inside &= bool(
            values.min() >= float(certificate.lower) - 2e-12
            and values.max() <= float(certificate.upper) + 2e-12
        )
        probe_rows.append(
            {
                "expression": name,
                "interval_lower": str(certificate.lower),
                "interval_upper": str(certificate.upper),
                "majorant": float(certificate.majorant),
                "boxes_evaluated": certificate.boxes_evaluated,
                "subdivision_depth": certificate.subdivision_depth,
                "sampled_values_inside_diagnostic": bool(
                    values.min() >= float(certificate.lower) - 2e-12
                    and values.max() <= float(certificate.upper) + 2e-12
                ),
            }
        )

    denominator_failure_safe = False
    try:
        BoundSecondDerivative(1 / X, (-1, 1), subdivision_depth=4, max_depth=8)
    except IntervalEvaluationError:
        denominator_failure_safe = True

    coarse_runge = BoundSecondDerivative(
        RUNGE_EXPRESSION, (-1, 1), subdivision_depth=3
    )
    fine_runge = certificates["runge"]

    quadratic_empirical = _linear_interpolation_empirical_error(
        lambda x: np.asarray(x, dtype=float) ** 2, 0.0, 1.0
    )
    exp_empirical = _linear_interpolation_empirical_error(np.exp, 0.0, 1.0)
    runge_empirical = _linear_interpolation_empirical_error(runge, -1.0, 1.0)
    error_rows = [
        {
            "function": "x^2 on [0,1]",
            "e_emp": quadratic_empirical,
            "e_cert": float(certificates["polynomial"].majorant) / 8.0,
            "e_exact": 0.25,
        },
        {
            "function": "exp(x) on [0,1]",
            "e_emp": exp_empirical,
            "e_cert": float(certificates["exp"].majorant) / 8.0,
            "e_exact": exp_interpolation_error(0),
        },
        {
            "function": "1/(1+25x^2) on [-1,1]",
            "e_emp": runge_empirical,
            "e_cert": float(fine_runge.majorant) / 2.0,
            "e_exact": 25.0 / 26.0,
        },
    ]

    return {
        "arithmetic": "fractions.Fraction endpoints; rational Taylor remainders",
        "grammar": ["polynomials", "rational functions", "exp", "sin", "cos", "compositions"],
        "precision_bits": 96,
        "probe_certificates": probe_rows,
        "error_reporting": error_rows,
        "polynomial_second_derivative_exact": bool(
            certificates["polynomial"].lower == certificates["polynomial"].upper == 2
        ),
        "all_certificate_endpoints_rational": all(
            isinstance(value, Fraction)
            for certificate in certificates.values()
            for value in (certificate.lower, certificate.upper, certificate.majorant)
        ),
        "denominator_zero_enclosure_fails_safely": denominator_failure_safe,
        "subdivision_tightens_runge_majorant": bool(
            fine_runge.majorant <= coarse_runge.majorant
        ),
        "runge_exact_curvature_50_is_enclosed": bool(fine_runge.majorant >= 50),
        "sampled_values_inside_certificates_diagnostic_only": bool(
            diagnostic_sampling_inside
        ),
        "guarantee_depends_on_sampling": False,
    }


# ---------------------------------------------------------------------------
# Address complexity: exact atom counts and worst-case address length
# ---------------------------------------------------------------------------


def rationals_up_to_height(H: int) -> int:
    """Number of reduced p/q with max(|p|, q) <= H (zero included)."""
    total = 1  # 0/1
    for q in range(1, H + 1):
        for p in range(1, H + 1):
            if math.gcd(p, q) == 1:
                total += 2
    return total


def atoms_up_to_height(H: int) -> int:
    """Exact cardinality of the shell L_H of atoms of height at most H."""
    scales = H                      # k in {0, ..., H-1}
    cells = 2 * H - 1               # m in {-(H-1), ..., H-1}
    values = rationals_up_to_height(H)
    slopes = values - 1             # nonzero slopes
    return scales * cells * values * slopes


def gamma_worst_address(H: int) -> int:
    """Largest arithmetic address pack4(k, mu, r, t) over the shell L_H."""
    k_max = H - 1
    mu_max = 2 * (H - 1)            # Z^{-1} is maximal at m = H-1
    values = rationals_up_to_height(H)
    r_max = values - 1
    t_max = values - 2
    return pack4(k_max, mu_max, r_max, t_max)


def address_complexity_table(heights: Iterable[int]) -> list[dict[str, float]]:
    rows: list[dict[str, float]] = []
    for H in heights:
        shell = atoms_up_to_height(H)
        gamma = gamma_worst_address(H)
        sharp = shell - 1
        rows.append(
            {
                "height": H,
                "atoms": shell,
                "gamma_worst": gamma,
                "sharp_worst": sharp,
                "lower_bound": sharp,
                "bits_gamma": math.log2(gamma + 1),
                "bits_sharp": math.log2(sharp + 1),
                "ratio_18H6": shell / (18.0 * H**6),
            }
        )
    return rows


def _fit_exponent(rows: list[dict[str, float]], key: str, tail: int = 4) -> float:
    subset = rows[-tail:]
    xs = np.log2(np.array([row["height"] for row in subset], dtype=float))
    ys = np.log2(np.array([row[key] + 1.0 for row in subset], dtype=float))
    slope, _ = np.polyfit(xs, ys, 1)
    return float(slope)


def address_checks(rows: list[dict[str, float]]) -> dict[str, object]:
    """Consistency checks tying the counting lemma to the two enumerations."""
    brute_ok = True
    for H in (2, 3, 4):
        values = [v for v in height_ordered_rationals(3 * H * H + 4) if height(v) <= H]
        slopes = [v for v in values if v != 0]
        brute = 0
        for k in range(H):
            for m in range(-(H - 1), H):
                brute += len(values) * len(slopes)
        brute_ok = brute_ok and brute == atoms_up_to_height(H)
    within_18 = all(row["ratio_18H6"] <= 1.0 for row in rows)
    sharp_below_gamma = all(row["sharp_worst"] <= row["gamma_worst"] for row in rows)
    return {
        "brute_force_shell_counts_match": brute_ok,
        "shell_count_below_18H6": within_18,
        "sharp_never_worse_than_gamma": sharp_below_gamma,
        "fitted_exponent_atoms": _fit_exponent(rows, "atoms"),
        "fitted_exponent_sharp": _fit_exponent(rows, "sharp_worst"),
        "fitted_exponent_gamma": _fit_exponent(rows, "gamma_worst"),
    }


# ---------------------------------------------------------------------------
# Finite truncated catalogs and exact minimization
# ---------------------------------------------------------------------------


LEAF_SHAPE = "leaf"


@dataclass(frozen=True)
class AssemblyRepresentation:
    shape: object
    leaves: tuple[RationalLeaf, ...]


@dataclass(frozen=True)
class CatalogEntry:
    stream: str
    representation: AssemblyRepresentation


def tree_shapes(max_depth: int) -> tuple[object, ...]:
    """All ordered full binary-tree shapes of depth at most ``max_depth``."""
    if max_depth < 0:
        return ()
    if max_depth == 0:
        return (LEAF_SHAPE,)
    children = tree_shapes(max_depth - 1)
    return (LEAF_SHAPE,) + tuple((left, right) for left in children for right in children)


def tree_skeleton(shape: object) -> str:
    """Prefix skeleton: 1 for a leaf and 0 for an internal node."""
    if shape == LEAF_SHAPE:
        return "1"
    left, right = shape
    return "0" + tree_skeleton(left) + tree_skeleton(right)


def atoms_for_cell(k: int, m: int, H: int, reverse: bool = False) -> tuple[RationalLeaf, ...]:
    """Exact atoms in L_H whose support is the prescribed dyadic cell."""
    if max(2, k + 1, abs(m) + 1) > H:
        return ()
    count = rationals_up_to_height(H)
    values = height_ordered_rationals(count)
    slopes = height_ordered_rationals(count - 1, exclude_zero=True)
    atoms = tuple(
        RationalLeaf(k, m, y0, slope)
        for y0 in values
        for slope in slopes
    )
    return tuple(reversed(atoms)) if reverse else atoms


def enumerate_shape_representations(
    shape: object, k: int, m: int, H: int, reverse: bool = False
) -> tuple[AssemblyRepresentation, ...]:
    """Enumerate labels exactly, pruning pairs that violate continuity."""
    if shape == LEAF_SHAPE:
        return tuple(
            AssemblyRepresentation(LEAF_SHAPE, (atom,))
            for atom in atoms_for_cell(k, m, H, reverse=reverse)
        )

    left_shape, right_shape = shape
    left_representations = enumerate_shape_representations(
        left_shape, k + 1, 2 * m, H, reverse=reverse
    )
    right_representations = enumerate_shape_representations(
        right_shape, k + 1, 2 * m + 1, H, reverse=reverse
    )
    right_by_boundary: dict[Fraction, list[AssemblyRepresentation]] = defaultdict(list)
    for representation in right_representations:
        right_by_boundary[representation.leaves[0].left_value].append(representation)

    combined: list[AssemblyRepresentation] = []
    for left in left_representations:
        for right in right_by_boundary[left.leaves[-1].right_value]:
            combined.append(
                AssemblyRepresentation(shape, left.leaves + right.leaves)
            )
    return tuple(combined)


def elias_gamma(value: int) -> str:
    if value <= 0:
        raise ValueError("Elias gamma codes positive integers only")
    payload = bin(value)[2:]
    return "0" * (len(payload) - 1) + payload


def decode_elias_gamma(stream: str, position: int = 0) -> tuple[int, int]:
    zeros = 0
    while position + zeros < len(stream) and stream[position + zeros] == "0":
        zeros += 1
    one_position = position + zeros
    if one_position >= len(stream):
        raise ValueError("truncated Elias gamma word")
    end = one_position + zeros + 1
    if end > len(stream):
        raise ValueError("truncated Elias gamma payload")
    return int(stream[one_position:end], 2), end


def encode_signed_integer(value: int) -> str:
    zigzag = 2 * value if value >= 0 else -2 * value - 1
    return elias_gamma(zigzag + 1)


def decode_signed_integer(stream: str, position: int = 0) -> tuple[int, int]:
    encoded, position = decode_elias_gamma(stream, position)
    zigzag = encoded - 1
    value = zigzag // 2 if zigzag % 2 == 0 else -(zigzag + 1) // 2
    return value, position


def encode_rational(value: Fraction) -> str:
    value = Fraction(value)
    return encode_signed_integer(value.numerator) + elias_gamma(value.denominator)


def decode_rational(stream: str, position: int = 0) -> tuple[Fraction, int]:
    numerator, position = decode_signed_integer(stream, position)
    denominator, position = decode_elias_gamma(stream, position)
    return Fraction(numerator, denominator), position


def encode_dyadic_structural(value: Fraction) -> str:
    """Encode the canonical pair (odd numerator, dyadic exponent)."""
    value = Fraction(value)
    exponent = dyadic_exponent(value)
    return encode_signed_integer(value.numerator) + elias_gamma(exponent + 1)


def decode_dyadic_structural(stream: str, position: int = 0) -> tuple[Fraction, int]:
    numerator, position = decode_signed_integer(stream, position)
    exponent_plus_one, position = decode_elias_gamma(stream, position)
    return Fraction(numerator, 2 ** (exponent_plus_one - 1)), position


def encode_atom_assembly(leaves: Iterable[RationalLeaf]) -> str:
    """Prefix-free structural leaf stream, conditioned only on its convention."""
    ordered = tuple(sorted(leaves, key=lambda leaf: leaf.left))
    _validate_continuous_leaves(ordered)
    stream = elias_gamma(len(ordered))
    for leaf in ordered:
        stream += elias_gamma(leaf.k + 1)
        stream += encode_signed_integer(leaf.m)
        stream += encode_rational(leaf.y0)
        stream += encode_rational(leaf.slope)
    return stream


def decode_atom_assembly(stream: str) -> tuple[RationalLeaf, ...]:
    count, position = decode_elias_gamma(stream)
    leaves = []
    for _ in range(count):
        k_plus_one, position = decode_elias_gamma(stream, position)
        m, position = decode_signed_integer(stream, position)
        y0, position = decode_rational(stream, position)
        slope, position = decode_rational(stream, position)
        leaves.append(RationalLeaf(k_plus_one - 1, m, y0, slope))
    if position != len(stream):
        raise ValueError("trailing bits in structural atom stream")
    result = tuple(leaves)
    _validate_continuous_leaves(result)
    return result


def encode_relu_structural(leaves: Iterable[RationalLeaf]) -> str:
    """ReLU stream that retains a dyadic anchor instead of expanding it."""
    ordered = tuple(sorted(leaves, key=lambda leaf: leaf.left))
    _validate_continuous_leaves(ordered)
    network = assembly_to_relu(ordered)
    first = ordered[0]
    stream = elias_gamma(len(ordered))
    stream += encode_dyadic_structural(first.centre)
    stream += encode_rational(first.y0)
    stream += encode_rational(first.slope)
    for knot, coefficient in network.hinges:
        stream += encode_dyadic_structural(knot)
        stream += encode_rational(coefficient)
    return stream


def decode_relu_structural(stream: str) -> HingeNetwork:
    leaf_count, position = decode_elias_gamma(stream)
    centre, position = decode_dyadic_structural(stream, position)
    y0, position = decode_rational(stream, position)
    slope, position = decode_rational(stream, position)
    hinges = []
    for _ in range(leaf_count - 1):
        knot, position = decode_dyadic_structural(stream, position)
        coefficient, position = decode_rational(stream, position)
        hinges.append((knot, coefficient))
    if position != len(stream):
        raise ValueError("trailing bits in structural ReLU stream")
    return HingeNetwork(y0 - slope * centre, slope, tuple(hinges))


def encode_relu_naive(network: HingeNetwork) -> str:
    """Expanded format: every knot and affine coefficient is a reduced rational."""
    stream = elias_gamma(len(network.hinges) + 1)
    stream += encode_rational(network.intercept)
    stream += encode_rational(network.linear_weight)
    for knot, coefficient in network.hinges:
        stream += encode_rational(knot)
        stream += encode_rational(coefficient)
    return stream


def decode_relu_naive(stream: str) -> HingeNetwork:
    hinge_count_plus_one, position = decode_elias_gamma(stream)
    intercept, position = decode_rational(stream, position)
    linear, position = decode_rational(stream, position)
    hinges = []
    for _ in range(hinge_count_plus_one - 1):
        knot, position = decode_rational(stream, position)
        coefficient, position = decode_rational(stream, position)
        hinges.append((knot, coefficient))
    if position != len(stream):
        raise ValueError("trailing bits in naive ReLU stream")
    return HingeNetwork(intercept, linear, tuple(hinges))


def assembly_atomic_height(leaves: Iterable[RationalLeaf]) -> int:
    return max(
        max(2, leaf.k + 1, abs(leaf.m) + 1, height(leaf.y0), height(leaf.slope))
        for leaf in leaves
    )


def _coding_gap_assembly(H: int, leaf_count: int = 2) -> tuple[RationalLeaf, ...]:
    """Alternating cells exposing the joint Theta(N H) naive cost."""
    if H < 2:
        raise ValueError("H must be at least two")
    if leaf_count < 2 or leaf_count % 2 or leaf_count > H:
        raise ValueError("leaf_count must be even and satisfy 2 <= leaf_count <= H")
    k = H - 1
    leaves = tuple(
        RationalLeaf(k, index, Fraction(0), Fraction(1 if index % 2 == 0 else -1))
        for index in range(leaf_count)
    )
    _validate_continuous_leaves(leaves)
    assert assembly_atomic_height(leaves) == H
    return leaves


def coding_format_checks(example_count: int = 4_096) -> dict[str, object]:
    """Exact roundtrips, height propagation, and bit-format comparison."""
    atom_roundtrip = True
    structural_roundtrip = True
    naive_roundtrip = True
    difference_height_bound = True
    product_height_bound = True
    intercept_height_bound = True
    dyadic_pair_bound = True

    for case in range(example_count):
        leaves = _deterministic_rational_assembly(case)
        network = assembly_to_relu(leaves)
        H = assembly_atomic_height(leaves)

        atom_stream = encode_atom_assembly(leaves)
        structural_stream = encode_relu_structural(leaves)
        naive_stream = encode_relu_naive(network)
        atom_roundtrip &= piecewise_signature(decode_atom_assembly(atom_stream)) == piecewise_signature(leaves)
        structural_roundtrip &= decode_relu_structural(structural_stream) == network
        naive_roundtrip &= decode_relu_naive(naive_stream) == network

        for knot, jump in network.hinges:
            difference_height_bound &= height(jump) <= 2 * H**2
            product_height_bound &= all(
                height(leaf.slope * knot) <= H * 2**H for leaf in leaves
            )
            dyadic_pair_bound &= (
                dyadic_exponent(knot) <= H and abs(knot.numerator) <= H
            )
        intercept_height_bound &= height(network.intercept) <= 2 ** (H + 1) * H**2

    family_rows = []
    for H in (4, 8, 16, 32, 64, 128):
        leaves = _coding_gap_assembly(H)
        network = assembly_to_relu(leaves)
        atom_bits = len(encode_atom_assembly(leaves))
        structural_bits = len(encode_relu_structural(leaves))
        naive_bits = len(encode_relu_naive(network))
        family_rows.append(
            {
                "height": H,
                "leaves": len(leaves),
                "atom_structural_bits": atom_bits,
                "relu_structural_bits": structural_bits,
                "relu_naive_rational_bits": naive_bits,
                "naive_to_structural_ratio": naive_bits / structural_bits,
            }
        )

    joint_family_rows = []
    for H, leaf_count in ((8, 4), (16, 8), (32, 16), (64, 32)):
        leaves = _coding_gap_assembly(H, leaf_count)
        network = assembly_to_relu(leaves)
        full_denominator_knots = sum(
            dyadic_exponent(knot) == H - 1 for knot, _ in network.hinges
        )
        joint_family_rows.append(
            {
                "height": H,
                "leaves": leaf_count,
                "atomic_height_exact": assembly_atomic_height(leaves) == H,
                "all_slope_jumps_nonzero": all(
                    coefficient != 0 for _, coefficient in network.hinges
                ),
                "full_denominator_knots": full_denominator_knots,
                "full_denominator_knots_at_least_half_leaves": (
                    full_denominator_knots >= leaf_count // 2
                ),
                "atom_structural_bits": len(encode_atom_assembly(leaves)),
                "relu_structural_bits": len(encode_relu_structural(leaves)),
                "relu_naive_rational_bits": len(encode_relu_naive(network)),
            }
        )

    return {
        "exact_examples": example_count,
        "integer_code": "Elias gamma after signed zigzag",
        "rational_code": "reduced numerator/denominator, each prefix-free",
        "dyadic_code": "canonical (odd numerator, exponent), each prefix-free",
        "atom_stream_roundtrip_exact": bool(atom_roundtrip),
        "relu_structural_stream_roundtrip_exact": bool(structural_roundtrip),
        "relu_naive_stream_roundtrip_exact": bool(naive_roundtrip),
        "height_r_minus_s_at_most_2H2": bool(difference_height_bound),
        "height_s_times_t_at_most_H2powH": bool(product_height_bound),
        "height_expanded_intercept_at_most_2powHplus1H2": bool(intercept_height_bound),
        "canonical_dyadic_pair_coordinates_at_most_H": bool(dyadic_pair_bound),
        "gap_family": family_rows,
        "joint_gap_family_checks": joint_family_rows,
        "joint_gap_family_valid": all(
            row["atomic_height_exact"]
            and row["all_slope_jumps_nonzero"]
            and row["full_denominator_knots_at_least_half_leaves"]
            for row in joint_family_rows
        ),
        "naive_overhead_ratio_strictly_grows": all(
            right["naive_to_structural_ratio"] > left["naive_to_structural_ratio"]
            for left, right in zip(family_rows, family_rows[1:])
        ),
    }


# ---------------------------------------------------------------------------
# Joint leaf/height budget for the constructive C^2 rate (item 7)
# ---------------------------------------------------------------------------


def _nearest_alternating_dyadic(
    value: Fraction, leaf_count: int, node_index: int
) -> Fraction:
    """Nearest point of the alternating grid with step ``leaf_count**-2``.

    The returned value has the common representation ``b/(2*n**2)`` with
    ``b`` even at even nodes and odd at odd nodes.  Ties are resolved toward
    the smaller numerator, making the construction fully deterministic.
    """
    n = leaf_count
    if n < 2 or n & (n - 1):
        raise ValueError("leaf_count must be a dyadic power at least two")
    scale = 2 * n * n
    target = Fraction(value) * scale
    floor_value = target.numerator // target.denominator
    candidates = tuple(
        candidate
        for candidate in range(floor_value - 2, floor_value + 3)
        if candidate % 2 == node_index % 2
    )
    numerator = min(
        candidates,
        key=lambda candidate: (abs(Fraction(candidate) - target), candidate),
    )
    return Fraction(numerator, scale)


def joint_budget_assembly(function, leaf_count: int) -> tuple[RationalLeaf, ...]:
    """Construct the exact alternating-grid assembly from Theorem item 7."""
    n = leaf_count
    if n < 2 or n & (n - 1):
        raise ValueError("leaf_count must be a dyadic power at least two")
    level = n.bit_length() - 1
    values = tuple(
        _nearest_alternating_dyadic(function(Fraction(index, n)), n, index)
        for index in range(n + 1)
    )
    leaves = tuple(
        RationalLeaf(
            level,
            index,
            (values[index] + values[index + 1]) / 2,
            n * (values[index + 1] - values[index]),
        )
        for index in range(n)
    )
    _validate_continuous_leaves(leaves)
    return leaves


def _quadratic_assembly_error(
    leaves: tuple[RationalLeaf, ...], coefficient: Fraction = Fraction(4)
) -> Fraction:
    """Exact uniform error for ``coefficient*x*(x-1)`` against an assembly."""
    worst = Fraction(0)
    for leaf in leaves:
        candidates = [leaf.left, leaf.right]
        # Derivative of a*x*(x-1) - (intercept+slope*x) vanishes here.
        critical = (coefficient + leaf.slope) / (2 * coefficient)
        if leaf.left <= critical <= leaf.right:
            candidates.append(critical)
        for x in candidates:
            exact = coefficient * x * (x - 1)
            affine = leaf.intercept + leaf.slope * x
            worst = max(worst, abs(exact - affine))
    return worst


def joint_budget_checks() -> dict[str, object]:
    """Exact checks for the simultaneous error, N, height, and bit bounds."""
    radius = Fraction(1)
    curvature = Fraction(8)
    derivative_bound = 4 * radius + curvature / 2
    height_constant = max(
        4 * (radius + 1),
        2 * (derivative_bound + 1),
    )
    probes = {
        "quadratic": lambda x: 4 * x * (x - 1),
        "constant": lambda x: Fraction(1, 3),
        "affine": lambda x: Fraction(2, 3) * x - Fraction(1, 3),
        "rational": lambda x: Fraction(1, 1) / (2 + x),
    }

    construction_ok = True
    nodal_error_ok = True
    height_ok = True
    parameter_height_ok = True
    roundtrip_ok = True
    tested_leaves = 0
    for n in (2, 4, 8, 16, 32, 64, 128, 256):
        for function in probes.values():
            leaves = joint_budget_assembly(function, n)
            tested_leaves += len(leaves)
            construction_ok &= len(leaves) == n and all(
                leaf.slope != 0 for leaf in leaves
            )
            values = (leaves[0].left_value,) + tuple(
                leaf.right_value for leaf in leaves
            )
            nodal_error_ok &= all(
                abs(values[index] - function(Fraction(index, n)))
                <= Fraction(1, 2 * n * n)
                for index in range(n + 1)
            )
            height_ok &= assembly_atomic_height(leaves) <= height_constant * n * n

            network = assembly_to_relu(leaves)
            parameter_height_ok &= height(network.intercept) <= 2 * (radius + 1) * n * n
            parameter_height_ok &= height(network.linear_weight) <= 2 * (derivative_bound + 1) * n
            parameter_height_ok &= all(
                height(knot) <= n
                and height(jump) <= 4 * (derivative_bound + 1) * n
                for knot, jump in network.hinges
            )
            roundtrip_ok &= (
                piecewise_signature(decode_atom_assembly(encode_atom_assembly(leaves)))
                == piecewise_signature(leaves)
            )
            roundtrip_ok &= decode_relu_structural(encode_relu_structural(leaves)) == network
            roundtrip_ok &= decode_relu_naive(encode_relu_naive(network)) == network

    rows = []
    for n in (2, 4, 8, 16, 32, 64):
        leaves = joint_budget_assembly(probes["quadratic"], n)
        network = assembly_to_relu(leaves)
        exact_error = _quadratic_assembly_error(leaves)
        certified_error = Fraction(curvature + 4, 8 * n * n)
        rows.append(
            {
                "leaves": n,
                "certified_error": str(certified_error),
                "exact_error": str(exact_error),
                "exact_error_times_N_squared": str(exact_error * n * n),
                "actual_atomic_height": assembly_atomic_height(leaves),
                "proved_height_bound": int(height_constant * n * n),
                "atom_bits": len(encode_atom_assembly(leaves)),
                "relu_structural_bits": len(encode_relu_structural(leaves)),
                "relu_naive_bits": len(encode_relu_naive(network)),
            }
        )

    exact_error_ok = all(
        Fraction(row["exact_error"]) <= Fraction(row["certified_error"])
        for row in rows
    )
    quadratic_scaled_error_constant = len(
        {row["exact_error_times_N_squared"] for row in rows}
    ) == 1
    table_height_ok = all(
        row["actual_atomic_height"] <= row["proved_height_bound"] for row in rows
    )
    bit_growth_diagnostic = {
        key: max(
            row[key]
            / (row["leaves"] * max(1, math.log2(row["leaves"])))
            for row in rows
        )
        for key in ("atom_bits", "relu_structural_bits", "relu_naive_bits")
    }

    return {
        "arithmetic": "fractions.Fraction",
        "ball": {"radius": int(radius), "curvature": int(curvature)},
        "derivative_bound_C0": int(derivative_bound),
        "height_constant_CH": int(height_constant),
        "quantization_step": "N^-2 on alternating dyadic grids",
        "probe_functions": list(probes),
        "dyadic_scales_tested": [2, 4, 8, 16, 32, 64, 128, 256],
        "exact_leaves_tested": tested_leaves,
        "all_assemblies_continuous_with_nonzero_slopes": bool(construction_ok),
        "all_nodal_errors_at_most_1_over_2N2": bool(nodal_error_ok),
        "all_atomic_heights_at_most_CH_N2": bool(height_ok),
        "all_relu_parameter_height_bounds_hold": bool(parameter_height_ok),
        "all_three_serializations_roundtrip_exactly": bool(roundtrip_ok),
        "quadratic_exact_errors_within_certificate": bool(exact_error_ok),
        "quadratic_exact_error_times_N2_is_constant": bool(
            quadratic_scaled_error_constant
        ),
        "all_table_heights_within_proved_bound": bool(table_height_ok),
        "bit_growth_over_N_log2N_diagnostic": bit_growth_diagnostic,
        "table": rows,
    }


def figure_coding_formats(
    checks: dict[str, object], lang: str, formats: Iterable[str], output: Path
) -> None:
    """Plot exact lengths for the family exposing explicit-denominator cost."""
    txt = TEXT[lang]
    rows = checks["gap_family"]
    heights = np.array([row["height"] for row in rows], dtype=float)
    atoms = np.array([row["atom_structural_bits"] for row in rows], dtype=float)
    structural = np.array([row["relu_structural_bits"] for row in rows], dtype=float)
    naive = np.array([row["relu_naive_rational_bits"] for row in rows], dtype=float)

    fig, ax = plt.subplots(figsize=(6.8, 3.55))
    ax.plot(heights, atoms, "o-", lw=1.25, ms=4, label=txt["coding_atoms"])
    ax.plot(
        heights,
        structural,
        "s-",
        lw=1.25,
        ms=4,
        label=txt["coding_relu_structural"],
    )
    ax.plot(
        heights,
        naive,
        "^-",
        lw=1.25,
        ms=4,
        label=txt["coding_relu_naive"],
    )
    ax.set_xscale("log", base=2)
    ax.set_xlabel(txt["coding_height"])
    ax.set_ylabel(txt["coding_bits"])
    ax.grid(alpha=0.2, which="both")
    ax.legend(fontsize=8, loc="upper left")
    ax.set_title(txt["coding_title"])
    fig.tight_layout()
    save_figure(
        fig,
        output,
        "fig08_codificacoes" if lang == "pt" else "fig08_encodings",
        formats,
    )


def shortlex_key(stream: str) -> tuple[int, str]:
    return len(stream), stream


def sharp_rank_and_rational_indices(
    H: int,
) -> tuple[dict[tuple[int, int, int, int], int], dict[Fraction, int], dict[Fraction, int]]:
    rationals = height_ordered_rationals(rationals_up_to_height(H))
    nonzero = height_ordered_rationals(rationals_up_to_height(H) - 1, exclude_zero=True)
    sharp_atoms = sharp_catalog(atoms_up_to_height(H))
    return (
        {atom: index for index, atom in enumerate(sharp_atoms)},
        {value: index for index, value in enumerate(rationals)},
        {value: index for index, value in enumerate(nonzero)},
    )


def serialize_representation(
    representation: AssemblyRepresentation,
    sharp_rank: dict[tuple[int, int, int, int], int],
    rational_index: dict[Fraction, int],
    nonzero_index: dict[Fraction, int],
) -> str:
    stream = tree_skeleton(representation.shape)
    for leaf in representation.leaves:
        atom = (
            leaf.k,
            integer_index(leaf.m),
            rational_index[leaf.y0],
            nonzero_index[leaf.slope],
        )
        stream += elias_gamma(sharp_rank[atom] + 1)
    return stream


def enumerate_finite_catalog(
    D: int, H: int, reverse: bool = False
) -> tuple[dict[tuple[tuple[Fraction, Fraction, Fraction, Fraction], ...], CatalogEntry], int]:
    """Enumerate Sigma^L_{D,H}([0,1]) and canonically deduplicate functions."""
    if D < 0 or H < 2:
        raise ValueError("the implemented root K=[0,1] needs D >= 0 and H >= 2")
    rank, q_index, qstar_index = sharp_rank_and_rational_indices(H)
    shapes = tree_shapes(D)
    if reverse:
        shapes = tuple(reversed(shapes))
    catalog: dict[
        tuple[tuple[Fraction, Fraction, Fraction, Fraction], ...], CatalogEntry
    ] = {}
    represented_count = 0
    for shape in shapes:
        representations = enumerate_shape_representations(
            shape, 0, 0, H, reverse=reverse
        )
        for representation in representations:
            represented_count += 1
            signature = piecewise_signature(representation.leaves)
            stream = serialize_representation(
                representation, rank, q_index, qstar_index
            )
            old = catalog.get(signature)
            if old is None or shortlex_key(stream) < shortlex_key(old.stream):
                catalog[signature] = CatalogEntry(stream, representation)
    return catalog, represented_count


CATALOG_SAMPLE_POINTS = tuple(Fraction(j, 4) for j in range(5))


def evaluate_assembly(leaves: tuple[RationalLeaf, ...], x: Fraction) -> Fraction:
    for index, leaf in enumerate(leaves):
        if leaf.left <= x < leaf.right or (index == len(leaves) - 1 and x == leaf.right):
            return leaf.intercept + leaf.slope * x
    raise ValueError(f"point {x} lies outside the assembly domain")


def exact_catalog_loss(leaves: tuple[RationalLeaf, ...]) -> Fraction:
    """Exact empirical squared loss against f(x)=2|x-1/2|."""
    return sum(
        (evaluate_assembly(leaves, x) - 2 * abs(x - Fraction(1, 2))) ** 2
        for x in CATALOG_SAMPLE_POINTS
    )


def exact_catalog_minimizer(
    catalog: dict[tuple[tuple[Fraction, Fraction, Fraction, Fraction], ...], CatalogEntry]
) -> tuple[Fraction, tuple[tuple[Fraction, Fraction, Fraction, Fraction], ...], CatalogEntry]:
    if not catalog:
        raise ValueError("cannot minimize over an empty catalog")
    signature, entry = min(
        catalog.items(),
        key=lambda item: (
            exact_catalog_loss(item[1].representation.leaves),
            shortlex_key(item[1].stream),
        ),
    )
    return exact_catalog_loss(entry.representation.leaves), signature, entry


def finite_catalog_checks() -> dict[str, object]:
    """Exact enumeration and order-independent canonical minimization."""
    cases = ((0, 2), (1, 2), (2, 2), (0, 3))
    catalogs = {}
    rows = []
    all_reproducible = True
    all_ties_unique = True
    for D, H in cases:
        catalog, represented = enumerate_finite_catalog(D, H)
        reversed_catalog, reversed_represented = enumerate_finite_catalog(D, H, reverse=True)
        loss, signature, entry = exact_catalog_minimizer(catalog)
        reverse_loss, reverse_signature, reverse_entry = exact_catalog_minimizer(reversed_catalog)
        same_catalog = {
            key: value.stream for key, value in catalog.items()
        } == {
            key: value.stream for key, value in reversed_catalog.items()
        }
        reproducible = (
            represented == reversed_represented
            and same_catalog
            and loss == reverse_loss
            and signature == reverse_signature
            and entry.stream == reverse_entry.stream
        )
        competing_streams = [
            candidate.stream
            for candidate in catalog.values()
            if exact_catalog_loss(candidate.representation.leaves) == loss
        ]
        unique_tie_break = sum(
            shortlex_key(stream) == min(map(shortlex_key, competing_streams))
            for stream in competing_streams
        ) == 1
        catalogs[(D, H)] = (catalog, loss)
        all_reproducible &= reproducible
        all_ties_unique &= unique_tie_break
        rows.append(
            {
                "max_depth": D,
                "max_height": H,
                "represented_assemblies": represented,
                "distinct_functions": len(catalog),
                "minimum_exact_squared_loss": str(loss),
                "minimizer_stream": entry.stream,
                "minimizer_stream_length": len(entry.stream),
                "minimizer_leaf_count": len(entry.representation.leaves),
                "enumeration_order_independent": reproducible,
                "canonical_tie_break_unique": unique_tie_break,
            }
        )

    nesting = {
        "D0H2_subset_D1H2": set(catalogs[(0, 2)][0]) <= set(catalogs[(1, 2)][0]),
        "D1H2_subset_D2H2": set(catalogs[(1, 2)][0]) <= set(catalogs[(2, 2)][0]),
        "D0H2_subset_D0H3": set(catalogs[(0, 2)][0]) <= set(catalogs[(0, 3)][0]),
    }
    monotone_minima = {
        "D0H2_to_D1H2": catalogs[(1, 2)][1] <= catalogs[(0, 2)][1],
        "D1H2_to_D2H2": catalogs[(2, 2)][1] <= catalogs[(1, 2)][1],
        "D0H2_to_D0H3": catalogs[(0, 3)][1] <= catalogs[(0, 2)][1],
    }
    return {
        "root": "J_{0,0}=[0,1]",
        "objective": "sum_{x in {0,1/4,1/2,3/4,1}} (g(x)-2|x-1/2|)^2",
        "arithmetic": "fractions.Fraction",
        "cases": rows,
        "all_catalogs_nonempty": all(row["distinct_functions"] > 0 for row in rows),
        "all_enumerations_order_independent": bool(all_reproducible),
        "all_canonical_tie_breaks_unique": bool(all_ties_unique),
        "nested_catalogs_verified": all(nesting.values()),
        "minimum_values_nonincreasing_under_truncation": all(monotone_minima.values()),
        "nesting_details": nesting,
        "minimum_monotonicity_details": monotone_minima,
    }


#: Deterministic probes of the ball ``F_{R,M}`` used by the codebook check.
#: With ``R = 1`` and ``M = 8`` the quadratic saturates both constraints at once
#: (``||f||_inf = M/8 = R`` and ``||f''||_inf = M``), and the sine saturates them
#: for every phase, so the second-difference budget is actually attained.
CODEBOOK_BALL = {"radius": 1.0, "curvature": 8.0}


def codebook_probe_functions(
    radius: float, curvature: float, samples: int = 200_001
) -> list[tuple[str, object, object]]:
    """Probes rescaled so that each one provably lies in ``F_{R,M}``.

    Every candidate is divided by whatever factor is needed to satisfy both
    ``||f||_inf <= R`` and ``||f''||_inf <= M``; the factor is computed from a
    fine deterministic sampling of the candidate and its exact second
    derivative.  Without this step a probe such as the Runge function, whose
    curvature reaches ``200`` after the affine change of variable, would sit
    outside the ball and the check would be meaningless.
    """
    omega = math.sqrt(curvature / radius)
    scale = 25.0
    grid = np.linspace(0.0, 1.0, samples)

    def runge(x):
        return 1.0 / (1.0 + scale * (2.0 * x - 1.0) ** 2)

    def runge_second(x):
        u = 2.0 * x - 1.0
        return 4.0 * (2.0 * scale * (3.0 * scale * u**2 - 1.0)) / (
            1.0 + scale * u**2
        ) ** 3

    candidates = [
        (
            "quadratic_saturating_both_constraints",
            lambda x: 0.5 * curvature * (np.asarray(x, dtype=float) ** 2 - np.asarray(x, dtype=float)),
            lambda x: np.full_like(np.asarray(x, dtype=float), curvature),
        ),
        (
            "sine_saturating_both_constraints",
            lambda x: radius * np.sin(omega * np.asarray(x, dtype=float)),
            lambda x: -radius * omega**2 * np.sin(omega * np.asarray(x, dtype=float)),
        ),
        (
            "shifted_cosine",
            lambda x: radius * np.cos(omega * np.asarray(x, dtype=float) + 0.7),
            lambda x: -radius * omega**2 * np.cos(omega * np.asarray(x, dtype=float) + 0.7),
        ),
        ("rescaled_runge", runge, runge_second),
    ]

    probes: list[tuple[str, object, object]] = []
    for name, function, second in candidates:
        sup_value = float(np.abs(np.asarray(function(grid), dtype=float)).max())
        sup_curvature = float(np.abs(np.asarray(second(grid), dtype=float)).max())
        factor = min(radius / sup_value, curvature / sup_curvature)
        probes.append(
            (
                name,
                (lambda f, s: lambda x: s * np.asarray(f(x), dtype=float))(function, factor),
                (lambda g, s: lambda x: s * np.asarray(g(x), dtype=float))(second, factor),
            )
        )
    return probes


def codebook_successor_check(
    tolerance: float,
    radius: float = CODEBOOK_BALL["radius"],
    curvature: float = CODEBOOK_BALL["curvature"],
    samples_per_cell: int = 129,
) -> dict[str, object]:
    """Verify the curvature restriction behind the log-free codebook length.

    The codebook of Theorem ``thm:entropy`` quantizes nodal values on the
    alternating dyadic grid ``G_j``.  Its cardinality is bounded not by counting
    every grid vector, but by observing that the second difference confines
    ``v_{j+1}`` to a window of length ``12*eps`` once ``v_{j-1}`` and ``v_j`` are
    fixed, so only a universal constant ``K = 25`` of grid points remain.  This
    routine checks that constant empirically, together with the hypotheses it
    rests on, and contrasts the resulting word length with the older bound that
    still paid a logarithmic factor.
    """
    level = 0
    while curvature / (8.0 * 4.0**level) > tolerance / 2.0:
        level += 1
    n = 2**level
    h = 1.0 / n
    delta = 2.0 ** (-math.ceil(math.log2(1.0 / tolerance)))
    derivative_bound = 4.0 * radius + curvature / 2.0

    def grid(index: int) -> np.ndarray:
        offset = 0.5 * delta if index % 2 else 0.0
        low = math.floor((-radius - delta - offset) / delta)
        high = math.ceil((radius + delta - offset) / delta)
        points = offset + delta * np.arange(low, high + 1)
        return points[(points >= -radius - delta) & (points <= radius + delta)]

    nodes = np.arange(n + 1) / n
    window = curvature * h * h + 2.0 * delta
    worst_successors = 0
    worst_second_difference = 0.0
    worst_distortion = 0.0
    worst_nodal_error = 0.0
    adjacent_values_distinct = True
    every_piece_is_an_atom = True

    for _, function, _second in codebook_probe_functions(radius, curvature):
        exact = np.asarray(function(nodes), dtype=float)
        quantized = np.empty(n + 1)
        for index in range(n + 1):
            candidates = grid(index)
            quantized[index] = candidates[np.argmin(np.abs(candidates - exact[index]))]
        worst_nodal_error = max(worst_nodal_error, float(np.abs(quantized - exact).max()))
        adjacent_values_distinct &= bool(np.all(np.diff(quantized) != 0.0))

        second = quantized[2:] - 2.0 * quantized[1:-1] + quantized[:-2]
        worst_second_difference = max(worst_second_difference, float(np.abs(second).max()))
        for index in range(1, n):
            centre = 2.0 * quantized[index] - quantized[index - 1]
            candidates = grid(index + 1)
            inside = np.count_nonzero(np.abs(candidates - centre) <= window)
            worst_successors = max(worst_successors, int(inside))

        for index in range(n):
            slope = Fraction(quantized[index + 1] - quantized[index]) * n
            midpoint = (
                Fraction(quantized[index]) + Fraction(quantized[index + 1])
            ) / 2
            every_piece_is_an_atom &= slope != 0 and midpoint.denominator > 0
            local = np.linspace(nodes[index], nodes[index + 1], samples_per_cell)
            interpolant = quantized[index] + (local - nodes[index]) * n * (
                quantized[index + 1] - quantized[index]
            )
            worst_distortion = max(
                worst_distortion,
                float(np.abs(np.asarray(function(local), dtype=float) - interpolant).max()),
            )

    first_node_choices = int(grid(0).size)
    second_node_choices = int(
        min(
            grid(1).size,
            2.0 * (derivative_bound * h + delta) / delta + 1.0,
        )
    )
    log_free_bits = (
        math.log2(first_node_choices)
        + math.log2(second_node_choices)
        + (n - 1) * math.log2(25.0)
    )
    logarithmic_bits = (n + 1) * math.log2(2.0 * (radius + 1.0) / tolerance)
    return {
        "tolerance": tolerance,
        "cells": n,
        "grid_step": delta,
        "grid_step_between_half_tolerance_and_tolerance": bool(
            tolerance / 2.0 < delta <= tolerance
        ),
        "curvature_times_h_squared_at_most_four_tolerances": bool(
            curvature * h * h <= 4.0 * tolerance + 1e-15
        ),
        "second_difference_window": window,
        "worst_second_difference": worst_second_difference,
        "second_difference_within_window": bool(
            worst_second_difference <= window + 1e-12
        ),
        "worst_admissible_successors": worst_successors,
        "successors_at_most_25": bool(worst_successors <= 25),
        "worst_nodal_error_at_most_half_step": bool(
            worst_nodal_error <= delta / 2.0 + 1e-12
        ),
        "adjacent_values_distinct": adjacent_values_distinct,
        "every_piece_is_an_atom": every_piece_is_an_atom,
        "worst_distortion": worst_distortion,
        "distortion_within_tolerance": bool(worst_distortion <= tolerance + 1e-12),
        "log_free_bits": log_free_bits,
        "logarithmic_bits": logarithmic_bits,
        "log_free_bits_times_sqrt_tolerance": log_free_bits * math.sqrt(tolerance),
        "logarithmic_bits_times_sqrt_tolerance": logarithmic_bits * math.sqrt(tolerance),
    }


def codebook_checks(
    tolerances: Iterable[float] = (2.0**-4, 2.0**-6, 2.0**-8, 2.0**-10, 2.0**-12),
) -> dict[str, object]:
    """Table and verdicts for the log-free codebook of Theorem ``thm:entropy``."""
    rows = [codebook_successor_check(tolerance) for tolerance in tolerances]
    scaled_free = [row["log_free_bits_times_sqrt_tolerance"] for row in rows]
    scaled_log = [row["logarithmic_bits_times_sqrt_tolerance"] for row in rows]

    radius = CODEBOOK_BALL["radius"]
    curvature = CODEBOOK_BALL["curvature"]
    grid = np.linspace(0.0, 1.0, 200_001)
    membership = []
    for name, function, second in codebook_probe_functions(radius, curvature):
        sup_value = float(np.abs(np.asarray(function(grid), dtype=float)).max())
        sup_curvature = float(np.abs(np.asarray(second(grid), dtype=float)).max())
        membership.append(
            {
                "name": name,
                "sup_value": sup_value,
                "sup_second_derivative": sup_curvature,
                "inside_ball": bool(
                    sup_value <= radius + 1e-9 and sup_curvature <= curvature + 1e-9
                ),
            }
        )

    return {
        "ball": CODEBOOK_BALL,
        "probe_functions": membership,
        "all_probes_inside_ball": all(item["inside_ball"] for item in membership),
        "rows": rows,
        "successors_at_most_25_everywhere": all(row["successors_at_most_25"] for row in rows),
        "second_difference_within_window_everywhere": all(
            row["second_difference_within_window"] for row in rows
        ),
        "distortion_within_tolerance_everywhere": all(
            row["distortion_within_tolerance"] for row in rows
        ),
        "adjacent_values_distinct_everywhere": all(
            row["adjacent_values_distinct"] for row in rows
        ),
        "nodal_error_within_half_step_everywhere": all(
            row["worst_nodal_error_at_most_half_step"] for row in rows
        ),
        "every_piece_is_an_atom_everywhere": all(
            row["every_piece_is_an_atom"] for row in rows
        ),
        # The point of the improvement: the log-free length stays proportional to
        # eps^{-1/2}, so this column is bounded, while the older bound grows like
        # log(1/eps) and its column is not.
        "log_free_scaled_bits_bounded": max(scaled_free) / min(scaled_free) < 1.5,
        "logarithmic_scaled_bits_grow": scaled_log[-1] > 1.8 * scaled_log[0],
        "log_free_scaled_bits": scaled_free,
        "logarithmic_scaled_bits": scaled_log,
    }


def figure_addresses(
    rows: list[dict[str, float]], lang: str, formats: Iterable[str], output: Path
) -> None:
    labels = {
        "pt": {
            "title": "Comprimento de endereço no pior caso sobre $\\mathcal{L}_H$",
            "x": "altura $H$",
            "y": "bits, $\\log_2(n+1)$",
            "gamma": "gerador aritmético $\\Gamma$  ($\\sim 8\\log_2 H$)",
            "sharp": "ordem por altura $\\Gamma^\\sharp$  (minimax exato)",
            "bound": "cota inferior universal  ($6\\log_2 H+O(1)$)",
            "counts": "cardinalidade $|\\mathcal{L}_H|$",
            "upper": "cota $18H^6$",
        },
        "en": {
            "title": "Worst-case address length over $\\mathcal{L}_H$",
            "x": "height $H$",
            "y": "bits, $\\log_2(n+1)$",
            "gamma": "arithmetic generator $\\Gamma$  ($\\sim 8\\log_2 H$)",
            "sharp": "height order $\\Gamma^\\sharp$  (exact minimax)",
            "bound": "universal lower bound  ($6\\log_2 H+O(1)$)",
            "counts": "cardinality $|\\mathcal{L}_H|$",
            "upper": "bound $18H^6$",
        },
    }[lang]
    heights = np.array([row["height"] for row in rows], dtype=float)
    bits_gamma = np.array([row["bits_gamma"] for row in rows])
    bits_sharp = np.array([row["bits_sharp"] for row in rows])
    atoms = np.array([row["atoms"] for row in rows], dtype=float)

    fig, axes = plt.subplots(1, 2, figsize=(9.0, 3.3))
    axes[0].plot(heights, bits_gamma, "o-", color="#b22222", lw=1.2, ms=3.4, label=labels["gamma"])
    axes[0].plot(heights, bits_sharp, "s-", color="#1f77b4", lw=1.2, ms=3.4, label=labels["sharp"])
    axes[0].plot(heights, 6.0 * np.log2(heights), "--", color="black", lw=1.0, label=labels["bound"])
    axes[0].set_xscale("log", base=2)
    axes[0].set_xlabel(labels["x"])
    axes[0].set_ylabel(labels["y"])
    axes[0].grid(alpha=0.2, which="both")
    axes[0].legend(fontsize=7, loc="upper left")

    axes[1].loglog(heights, atoms, "s-", color="#1f77b4", lw=1.2, ms=3.4, label=labels["counts"])
    axes[1].loglog(heights, 18.0 * heights**6, "--", color="black", lw=1.0, label=labels["upper"])
    axes[1].set_xlabel(labels["x"])
    axes[1].grid(alpha=0.2, which="both")
    axes[1].legend(fontsize=7, loc="upper left")
    fig.suptitle(labels["title"])
    fig.tight_layout()
    save_figure(fig, output, "fig06_enderecos" if lang == "pt" else "fig06_addresses", formats)


def write_address_table(rows: list[dict[str, float]], destination: Path) -> None:
    lines = [
        r"\begin{tabular}{rrrrr}",
        r"\toprule",
        r"$H$ & $|\Library_H|$ & $|\Library_H|/(18H^6)$ & $\max n$ ($\Gamma$) & $\max n^\sharp=$ cota inf.\\",
        r"\midrule",
    ]
    for row in rows:
        lines.append(
            "{H} & {atoms} & {ratio:.4f} & {gamma} & {sharp}\\\\".format(
                H=int(row["height"]),
                atoms=int(row["atoms"]),
                ratio=row["ratio_18H6"],
                gamma=int(row["gamma_worst"]),
                sharp=int(row["sharp_worst"]),
            )
        )
    lines += [r"\bottomrule", r"\end{tabular}", ""]
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text("\n".join(lines), encoding="utf-8")


def _latex_fraction(value: str) -> str:
    if "/" not in value:
        return value
    numerator, denominator = value.split("/", 1)
    return rf"\frac{{{numerator}}}{{{denominator}}}"


def write_catalog_table(checks: dict[str, object], destination: Path) -> None:
    lines = [
        r"\begin{tabular}{rrrrrr}",
        r"\toprule",
        r"$D$ & $H$ & representações & funções & $\min J$ & bits do desempate\\",
        r"\midrule",
    ]
    for row in checks["cases"]:
        lines.append(
            "{D} & {H} & {represented} & {functions} & ${loss}$ & {bits}\\\\".format(
                D=row["max_depth"],
                H=row["max_height"],
                represented=row["represented_assemblies"],
                functions=row["distinct_functions"],
                loss=_latex_fraction(row["minimum_exact_squared_loss"]),
                bits=row["minimizer_stream_length"],
            )
        )
    lines += [r"\bottomrule", r"\end{tabular}", ""]
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text("\n".join(lines), encoding="utf-8")


def _latex_scientific(value: float, digits: int = 3) -> str:
    mantissa, exponent = f"{value:.{digits}e}".split("e")
    return rf"{mantissa}\,10^{{{int(exponent)}}}"


def write_adaptive_table(rows: list[dict[str, object]], destination: Path) -> None:
    lines = [
        r"\begin{tabular}{rrrrrrr}",
        r"\toprule",
        r"$\varepsilon_I$ & folhas & $e_{\rm cert}$ & $e_{\rm emp}$ & cert. $M$ exato & folga & uniforme\\",
        r"\midrule",
    ]
    for row in rows:
        lines.append(
            "${eps}$ & {n} & ${cert}$ & ${emp}$ & ${reference}$ & ${slack:.3f}$ & {uniform}\\\\".format(
                eps=_latex_scientific(float(row["tolerance"])),
                n=row["n"],
                cert=_latex_scientific(float(row["e_cert"])),
                emp=_latex_scientific(float(row["e_emp"])),
                reference=_latex_scientific(float(row["exact_curvature_certificate"])),
                slack=float(row["certificate_slack_over_exact_curvature"]),
                uniform=row["uniform_certified_n"],
            )
        )
    lines += [r"\bottomrule", r"\end{tabular}", ""]
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text("\n".join(lines), encoding="utf-8")


def write_interval_error_table(checks: dict[str, object], destination: Path) -> None:
    labels = {
        "x^2 on [0,1]": r"$x^2$, $[0,1]$",
        "exp(x) on [0,1]": r"$e^x$, $[0,1]$",
        "1/(1+25x^2) on [-1,1]": r"Runge, $[-1,1]$",
    }
    lines = [
        r"\begin{tabular}{lrrrr}",
        r"\toprule",
        r"função e intervalo & $e_{\rm emp}$ & $e_{\rm cert}$ & $e_{\rm exato}$ & $e_{\rm cert}/e_{\rm exato}$\\",
        r"\midrule",
    ]
    for row in checks["error_reporting"]:
        exact = float(row["e_exact"])
        lines.append(
            "{label} & ${emp}$ & ${cert}$ & ${exact}$ & ${ratio:.3f}$\\\\".format(
                label=labels[row["function"]],
                emp=_latex_scientific(float(row["e_emp"])),
                cert=_latex_scientific(float(row["e_cert"])),
                exact=_latex_scientific(exact),
                ratio=float(row["e_cert"]) / exact,
            )
        )
    lines += [r"\bottomrule", r"\end{tabular}", ""]
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text("\n".join(lines), encoding="utf-8")


def write_coding_table(checks: dict[str, object], destination: Path) -> None:
    lines = [
        r"\begin{tabular}{rrrrr}",
        r"\toprule",
        r"$H$ & $L_{\rm atom}$ & $L_{\rm ReLU,str}$ & $L_{\rm ReLU,rat}$ & razão rat./str.\\",
        r"\midrule",
    ]
    for row in checks["gap_family"]:
        lines.append(
            "{H} & {atoms} & {structural} & {naive} & {ratio:.3f}\\\\".format(
                H=row["height"],
                atoms=row["atom_structural_bits"],
                structural=row["relu_structural_bits"],
                naive=row["relu_naive_rational_bits"],
                ratio=row["naive_to_structural_ratio"],
            )
        )
    lines += [r"\bottomrule", r"\end{tabular}", ""]
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text("\n".join(lines), encoding="utf-8")


def write_joint_budget_table(checks: dict[str, object], destination: Path) -> None:
    lines = [
        r"\begin{tabular}{rrrrrrrr}",
        r"\toprule",
        r"$N$ & $e_{\rm cert}$ & $e_{\rm exato}$ & $\height_{\max}$ & $H_N$ & $L_{\rm atom}$ & $L_{\rm str}$ & $L_{\rm rat}$\\",
        r"\midrule",
    ]
    for row in checks["table"]:
        lines.append(
            "{N} & ${cert}$ & ${exact}$ & {actual_height} & {height_bound} & {atoms} & {structural} & {naive}\\\\".format(
                N=row["leaves"],
                cert=_latex_fraction(row["certified_error"]),
                exact=_latex_fraction(row["exact_error"]),
                actual_height=row["actual_atomic_height"],
                height_bound=row["proved_height_bound"],
                atoms=row["atom_bits"],
                structural=row["relu_structural_bits"],
                naive=row["relu_naive_bits"],
            )
        )
    lines += [r"\bottomrule", r"\end{tabular}", ""]
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text("\n".join(lines), encoding="utf-8")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--language", choices=("pt", "en", "all"), default="all")
    parser.add_argument("--formats", default="pdf,png", help="comma-separated: pdf,png")
    parser.add_argument("--output-root", type=Path, default=ROOT)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    formats = tuple(item.strip() for item in args.formats.split(",") if item.strip())
    if not formats or any(item not in {"pdf", "png"} for item in formats):
        raise ValueError("--formats must contain pdf and/or png")

    languages = ("pt", "en") if args.language == "all" else (args.language,)
    exp_table: list[dict[str, float]] | None = None
    adaptive_table: list[dict[str, float]] | None = None
    address_rows = address_complexity_table([2, 3, 4, 6, 8, 12, 16, 24, 32, 48, 64])
    interval_verdicts = interval_arithmetic_checks()
    coding_verdicts = coding_format_checks()
    joint_budget_verdicts = joint_budget_checks()
    for lang in languages:
        figure_output = args.output_root / "figures" / lang
        figure_dyadic(lang, formats, figure_output)
        figure_calkin_wilf(lang, formats, figure_output)
        figure_approximation(lang, formats, figure_output)
        current_exp = figure_exp_and_table(lang, formats, figure_output)
        current_adaptive = figure_adaptive_and_table(lang, formats, figure_output)
        figure_addresses(address_rows, lang, formats, figure_output)
        figure_relu_equivalence(lang, formats, figure_output)
        figure_coding_formats(coding_verdicts, lang, formats, figure_output)
        exp_table = current_exp if exp_table is None else exp_table
        adaptive_table = current_adaptive if adaptive_table is None else adaptive_table
    sections_dir = args.output_root.parents[1] / "artigo" / "secoes"
    write_address_table(address_rows, sections_dir / "tab_enderecos.tex")
    assert adaptive_table is not None
    write_adaptive_table(
        adaptive_table,
        sections_dir / "tab_adaptativo.tex",
    )
    write_interval_error_table(
        interval_verdicts,
        sections_dir / "tab_intervalos.tex",
    )
    write_coding_table(
        coding_verdicts,
        sections_dir / "tab_codificacoes.tex",
    )
    write_joint_budget_table(
        joint_budget_verdicts,
        sections_dir / "tab_orcamento_conjunto.tex",
    )

    indexing_verdicts = exact_indexing_checks()
    assert indexing_verdicts["cantor_roundtrip_ok"]
    assert indexing_verdicts["tuple_roundtrip_ok"]
    assert indexing_verdicts["height_rationals_unique"]
    assert indexing_verdicts["height_nonzero_unique_and_nonzero"]
    assert indexing_verdicts["height_rank_bound_q_ok"]
    assert indexing_verdicts["height_rank_bound_q_nonzero_ok"]
    assert indexing_verdicts["cw_power_identity_ok"]
    assert indexing_verdicts["sharp_roundtrip_ok"]
    assert indexing_verdicts["gamma_sharp_shell_sets_match"]

    codebook_verdicts = codebook_checks()
    assert codebook_verdicts["all_probes_inside_ball"]
    assert codebook_verdicts["nodal_error_within_half_step_everywhere"]
    assert codebook_verdicts["successors_at_most_25_everywhere"]
    assert codebook_verdicts["second_difference_within_window_everywhere"]
    assert codebook_verdicts["distortion_within_tolerance_everywhere"]
    assert codebook_verdicts["adjacent_values_distinct_everywhere"]
    assert codebook_verdicts["every_piece_is_an_atom_everywhere"]
    assert codebook_verdicts["log_free_scaled_bits_bounded"]
    assert codebook_verdicts["logarithmic_scaled_bits_grow"]

    relu_verdicts = relu_equivalence_checks()
    assert relu_verdicts["assembly_to_relu_exact"]
    assert relu_verdicts["relu_to_assembly_exact"]
    assert relu_verdicts["all_network_parameters_rational"]
    assert relu_verdicts["nonzero_local_slopes_preserved"]
    assert relu_verdicts["width_equals_leaf_count_minus_one"]

    assert interval_verdicts["polynomial_second_derivative_exact"]
    assert interval_verdicts["all_certificate_endpoints_rational"]
    assert interval_verdicts["denominator_zero_enclosure_fails_safely"]
    assert interval_verdicts["subdivision_tightens_runge_majorant"]
    assert interval_verdicts["runge_exact_curvature_50_is_enclosed"]
    assert interval_verdicts["sampled_values_inside_certificates_diagnostic_only"]
    assert not interval_verdicts["guarantee_depends_on_sampling"]

    assert coding_verdicts["atom_stream_roundtrip_exact"]
    assert coding_verdicts["relu_structural_stream_roundtrip_exact"]
    assert coding_verdicts["relu_naive_stream_roundtrip_exact"]
    assert coding_verdicts["height_r_minus_s_at_most_2H2"]
    assert coding_verdicts["height_s_times_t_at_most_H2powH"]
    assert coding_verdicts["height_expanded_intercept_at_most_2powHplus1H2"]
    assert coding_verdicts["canonical_dyadic_pair_coordinates_at_most_H"]
    assert coding_verdicts["joint_gap_family_valid"]
    assert coding_verdicts["naive_overhead_ratio_strictly_grows"]

    assert joint_budget_verdicts["all_assemblies_continuous_with_nonzero_slopes"]
    assert joint_budget_verdicts["all_nodal_errors_at_most_1_over_2N2"]
    assert joint_budget_verdicts["all_atomic_heights_at_most_CH_N2"]
    assert joint_budget_verdicts["all_relu_parameter_height_bounds_hold"]
    assert joint_budget_verdicts["all_three_serializations_roundtrip_exactly"]
    assert joint_budget_verdicts["quadratic_exact_errors_within_certificate"]
    assert joint_budget_verdicts["quadratic_exact_error_times_N2_is_constant"]
    assert joint_budget_verdicts["all_table_heights_within_proved_bound"]

    catalog_verdicts = finite_catalog_checks()
    assert catalog_verdicts["all_catalogs_nonempty"]
    assert catalog_verdicts["all_enumerations_order_independent"]
    assert catalog_verdicts["all_canonical_tie_breaks_unique"]
    assert catalog_verdicts["nested_catalogs_verified"]
    assert catalog_verdicts["minimum_values_nonincreasing_under_truncation"]
    write_catalog_table(
        catalog_verdicts,
        sections_dir / "tab_catalogos.tex",
    )

    metadata = {
        "deterministic": True,
        "python": platform.python_version(),
        "numpy": np.__version__,
        "matplotlib": matplotlib.__version__,
        "indexing_checks": indexing_verdicts,
        "address_complexity": address_rows,
        "address_checks": address_checks(address_rows),
        "codebook_checks": codebook_verdicts,
        "relu_equivalence_checks": relu_verdicts,
        "interval_arithmetic_checks": interval_verdicts,
        "coding_format_checks": coding_verdicts,
        "joint_leaf_height_budget_checks": joint_budget_verdicts,
        "finite_catalog_checks": catalog_verdicts,
        "table_exp": exp_table,
        "table_adaptive": adaptive_table,
        "empirical_error_sampling": {
            "adaptive_points_per_leaf": 4_001,
            "uniform_minimum_points": 40_001,
        },
    }
    result_path = args.output_root / "resultados.json"
    result_path.parent.mkdir(parents=True, exist_ok=True)
    result_path.write_text(json.dumps(metadata, ensure_ascii=False, indent=2), encoding="utf-8")
    print(json.dumps(metadata, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
