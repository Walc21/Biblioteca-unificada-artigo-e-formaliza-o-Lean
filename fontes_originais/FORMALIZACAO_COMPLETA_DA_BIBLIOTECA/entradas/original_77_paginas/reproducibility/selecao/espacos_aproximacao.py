#!/usr/bin/env python3
"""Auditoria determinística das classes de aproximação por altura.

O programa separa três objetos que não devem ser confundidos:

1. a construção racional exata para uma quadrática;
2. as agendas de altura usadas no teorema direto;
3. diagnósticos de somabilidade e as obstruções aritmética/geométrica.

Toda decisão aritmética usa ``fractions.Fraction``. Ponto flutuante aparece
somente nos diagnósticos de séries e na renderização da figura.
"""

from __future__ import annotations

import argparse
import json
import math
from fractions import Fraction
from pathlib import Path
from typing import Dict, Iterable, List, Tuple


def rational_height(x: Fraction) -> int:
    return max(abs(x.numerator), x.denominator)


def ceil_fraction(x: Fraction) -> int:
    return -((-x.numerator) // x.denominator)


def nearest_integer_with_parity(x: Fraction, parity: int) -> int:
    """Nearest integer b to x with b == parity (mod 2), ties to the smaller b."""

    floor_x = x.numerator // x.denominator
    candidates = []
    for b in range(floor_x - 3, floor_x + 4):
        if b % 2 == parity:
            candidates.append(b)
    return min(candidates, key=lambda b: (abs(x - b), b))


def alternating_round(value: Fraction, q: int, parity: int) -> Tuple[int, Fraction]:
    b = nearest_integer_with_parity(2 * q * value, parity)
    return b, Fraction(b, 2 * q)


def quadratic_value(x: Fraction) -> Fraction:
    return 4 * x * (x - 1)


def quadratic_interval_error(
    left: Fraction, right: Fraction, value_left: Fraction, value_right: Fraction
) -> Fraction:
    """Exact sup error for f(x)=4x(x-1) against the endpoint line."""

    slope = (value_right - value_left) / (right - left)
    intercept = value_left - slope * left
    # f-line = 4*x^2 + (-4-slope)*x - intercept.
    coeff_b = -4 - slope
    coeff_c = -intercept

    def error_at(x: Fraction) -> Fraction:
        return abs(4 * x * x + coeff_b * x + coeff_c)

    candidates = [error_at(left), error_at(right)]
    critical = -coeff_b / 8
    if left <= critical <= right:
        candidates.append(error_at(critical))
    return max(candidates)


def quadratic_construction(n: int) -> Dict[str, object]:
    assert n >= 2 and n & (n - 1) == 0
    q = n * n
    b_values: List[int] = []
    values: List[Fraction] = []
    for j in range(n + 1):
        x = Fraction(j, n)
        b, value = alternating_round(quadratic_value(x), q, j % 2)
        b_values.append(b)
        values.append(value)

    max_y0 = 0
    max_slope = 0
    max_atom = 0
    max_error = Fraction(0)
    r = int(math.log2(n))
    for j in range(n):
        y0 = Fraction(b_values[j] + b_values[j + 1], 4 * n * n)
        slope = Fraction(b_values[j + 1] - b_values[j], 2 * n)
        h_y0 = rational_height(y0)
        h_slope = rational_height(slope)
        h_atom = max(2, r + 1, j + 1, h_y0, h_slope)
        max_y0 = max(max_y0, h_y0)
        max_slope = max(max_slope, h_slope)
        max_atom = max(max_atom, h_atom)
        err = quadratic_interval_error(
            Fraction(j, n), Fraction(j + 1, n), values[j], values[j + 1]
        )
        max_error = max(max_error, err)

    expected_error = Fraction(49, 64 * n * n)
    assert max_error == expected_error
    assert max_atom <= 4 * n * n
    return {
        "n": n,
        "max_y0_height": max_y0,
        "max_slope_height": max_slope,
        "max_atom_height": max_atom,
        "proved_height": 18 * n * n,
        "old_plan_height": n**3,
        "exact_error": str(max_error),
        "expected_error": str(expected_error),
    }


def largest_power_of_two_at_most(x: int) -> int:
    if x < 1:
        raise ValueError("upper bound must be positive")
    return 1 << (x.bit_length() - 1)


def scheduled_quadratic_construction(n: int, h_budget: int) -> Dict[str, object]:
    """Independent instance of the rational Jackson construction on [0,1]."""

    assert n >= 2 and n & (n - 1) == 0
    # Here ||4x(x-1)||_infty=1, hence 8(R+1)=16.
    q = largest_power_of_two_at_most(h_budget // 16)
    b_values: List[int] = []
    values: List[Fraction] = []
    for j in range(n + 1):
        x = Fraction(j, n)
        b, value = alternating_round(quadratic_value(x), q, j % 2)
        b_values.append(b)
        values.append(value)

    max_height = 0
    max_error = Fraction(0)
    r = int(math.log2(n))
    for j in range(n):
        y0 = Fraction(b_values[j] + b_values[j + 1], 4 * q)
        slope = Fraction(n * (b_values[j + 1] - b_values[j]), 2 * q)
        atom_height = max(
            2, r + 1, j + 1, rational_height(y0), rational_height(slope)
        )
        max_height = max(max_height, atom_height)
        max_error = max(
            max_error,
            quadratic_interval_error(
                Fraction(j, n), Fraction(j + 1, n), values[j], values[j + 1]
            ),
        )

    jackson_bound = Fraction(1, n * n) + Fraction(1, 2 * q)
    assert max_height <= h_budget
    assert max_error <= jackson_bound
    return {
        "N": n,
        "H_budget": h_budget,
        "Q": q,
        "max_atom_height": max_height,
        "exact_error": str(max_error),
        "quadratic_jackson_bound": str(jackson_bound),
    }


def rationals_of_height(h: int) -> Iterable[Fraction]:
    seen = set()
    for q in range(1, h + 1):
        for p in range(-h, h + 1):
            x = Fraction(p, q)
            if rational_height(x) <= h and x not in seen:
                seen.add(x)
                yield x


def verify_constant_obstruction(h: int) -> Dict[str, object]:
    target = Fraction(1, 2 * h)
    distance = min(abs(target - x) for x in rationals_of_height(h))
    expected = Fraction(1, 2 * h)
    assert distance == expected
    return {"H": h, "target": str(target), "distance": str(distance)}


def uniform_geometry_min_height(n: int, k0: int = 0, m0: int = 0) -> int:
    assert n >= 1 and n & (n - 1) == 0
    r = int(math.log2(n))
    scale = k0 + r + 1
    translations = [abs(n * m0 + j) + 1 for j in range(n)]
    return max(2, scale, max(translations))


def quantization_series(q: float, kappa: float, cutoff: int) -> float:
    return sum(
        1.0 / (n * (math.log(math.e * n) ** (kappa * q)))
        for n in range(2, cutoff + 1)
    )


def write_height_table(path: Path, rows: List[Dict[str, object]]) -> None:
    lines = [
        r"\begin{tabular}{rrrrrr}",
        r"\toprule",
        r"$N$ & $\height(y_0)$ & $\height(s)$ & $H_{\rm efetivo}$ & $4N^2$ & $N^3$\\",
        r"\midrule",
    ]
    for row in rows:
        n = int(row["n"])
        lines.append(
            f"{n} & {row['max_y0_height']} & {row['max_slope_height']} & "
            f"{row['max_atom_height']} & {4*n*n} & {n**3}\\\\"
        )
    lines.extend([r"\bottomrule", r"\end{tabular}"])
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def write_schedule_table(path: Path) -> None:
    lines = [
        r"\begin{tabularx}{\linewidth}{@{}cclX@{}}",
        r"\toprule",
        r"regularidade & $q$ & agenda suficiente & mecanismo dominante\\",
        r"\midrule",
        r"$0<s<1$ & $0<q\le\infty$ & $H(N)\asymp N$ & geometria; a quantização $H^{-1}$ é subcrítica\\",
        r"$1\le s<2$ & $q=\infty$ & $H(N)\asymp N^s$ & altura da ordenada racional\\",
        r"$1\le s<2$ & $q<\infty$ & $H(N)\asymp N^s\log^\kappa(eN)$, $\kappa>1/q$ & somabilidade do piso aritmético\\",
        r"$1\le s<2$ & $q<\infty$ & $H(N)\asymp N^{s+\eta}$, $\eta>0$ & alternativa puramente polinomial\\",
        r"$s=2$ & $q=\infty$ & $H(N)\asymp N^2$ & endpoint uniforme de $C^2$\\",
        r"\bottomrule",
        r"\end{tabularx}",
    ]
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def render_figure(path_pdf: Path, path_png: Path, rows: List[Dict[str, object]]) -> None:
    import matplotlib.pyplot as plt

    n_values = [int(row["n"]) for row in rows]
    actual = [int(row["max_atom_height"]) for row in rows]
    corrected = [4 * n * n for n in n_values]
    old = [n**3 for n in n_values]

    fig, ax = plt.subplots(figsize=(7.2, 4.3))
    ax.loglog(n_values, actual, "o-", color="#1f5a99", label="altura efetiva")
    ax.loglog(n_values, corrected, "--", color="#26855b", label=r"referência $4N^2$")
    ax.loglog(n_values, old, ":", color="#b34a3c", label=r"escala comparativa $N^3$")
    ax.set_xlabel("número de folhas $N$")
    ax.set_ylabel("altura")
    ax.grid(True, which="both", alpha=0.25)
    ax.legend(frameon=False)
    fig.tight_layout()
    fig.savefig(path_pdf)
    fig.savefig(path_png, dpi=180)
    plt.close(fig)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output-root", type=Path, required=True)
    args = parser.parse_args()
    root = args.output_root.resolve()
    repro = root / "reproducibility" / "selecao"
    sections = root / "artigo" / "secoes"
    figures = repro / "figures" / "pt"
    figures.mkdir(parents=True, exist_ok=True)

    n_values = [4, 8, 16, 32, 64, 128]
    rows = [quadratic_construction(n) for n in n_values]
    # Valores de regressão destacados no artigo.
    by_n = {int(row["n"]): row for row in rows}
    assert by_n[32]["max_y0_height"] == 4096
    assert by_n[32]["max_slope_height"] == 249
    assert by_n[128]["max_y0_height"] == 65536
    assert by_n[128]["max_slope_height"] == 1017

    obstruction = [verify_constant_obstruction(h) for h in [2, 3, 4, 8, 16, 32]]
    geometry = []
    for n in [1, 2, 4, 8, 16, 32]:
        minimum = uniform_geometry_min_height(n)
        assert minimum == max(2, n)
        geometry.append({"N": n, "minimum_H_for_uniform_mesh_on_0_1": minimum})

    # A soma crítica é do tipo sum 1/[N log(eN)^(kappa*q)].
    series = []
    for kappa in [0.0, 0.4, 0.6, 1.0]:
        q = 2.0
        values = {
            str(cutoff): quantization_series(q, kappa, cutoff)
            for cutoff in [100, 1000, 10000]
        }
        series.append(
            {
                "q": q,
                "kappa": kappa,
                "kappa_q": kappa * q,
                "converges_by_integral_test": kappa * q > 1,
                "partial_sums": values,
            }
        )

    direct_samples = []
    for n in [4, 16, 64]:
        schedules = {
            "s=0.5,q=inf,H=64N": 64 * n,
            "s=1,q=inf,H=64N": 64 * n,
            "s=1.5,q=inf,H=64N^1.5": 64 * n * math.isqrt(n),
            "s=1.5,q=2,kappa=0.6": math.ceil(
                64 * n * math.isqrt(n) * (math.log(math.e * n) ** 0.6)
            ),
        }
        for label, budget in schedules.items():
            row = scheduled_quadratic_construction(n, budget)
            row["schedule"] = label
            direct_samples.append(row)

    # Certificado simbólico da falha de homogeneidade do funcional bruto.
    nonhomogeneity = {
        "base_function": "f(x)=x",
        "base_exact_from_height": 2,
        "scalar": "sqrt(2)",
        "reason": (
            "every finite catalog function has rational slope on each nondegenerate leaf; "
            "sqrt(2)*x has irrational slope on every such leaf"
        ),
        "conclusion": "a_H(f)=0 while a_H(sqrt(2)f)>0",
    }

    results = {
        "metadata": {
            "deterministic": True,
            "exact_arithmetic": "fractions.Fraction except plotted/series diagnostics",
        },
        "quadratic_construction": rows,
        "constant_height_obstruction": obstruction,
        "uniform_geometry": geometry,
        "critical_log_series": series,
        "direct_schedule_samples": direct_samples,
        "nonhomogeneity_certificate": nonhomogeneity,
        "audits": {
            "quadratic_values_reproduced": True,
            "quadratic_error_formula_exact": True,
            "arithmetic_lower_bound_enumerated": True,
            "uniform_mesh_height_exact": True,
            "critical_log_integral_test_recorded": True,
            "direct_schedules_checked_exactly": True,
            "raw_functional_not_mislabeled_quasinorm": True,
        },
    }

    (repro / "resultados_espacos_aproximacao.json").write_text(
        json.dumps(results, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )
    write_height_table(sections / "tab_auditoria_altura.tex", rows)
    write_schedule_table(sections / "tab_agendas_altura.tex")
    render_figure(
        figures / "fig_altura_agendas.pdf",
        figures / "fig_altura_agendas.png",
        rows,
    )
    print(json.dumps(results["audits"], indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
