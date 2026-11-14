#!/usr/bin/env python3
"""Auditoria deterministica da constante assintotica estritamente diadica.

O nucleo combinatorio e todos os testes de funcoes quadráticas por partes
usam ``fractions.Fraction``. Ponto flutuante aparece apenas nos dois
diagnosticos C^2 e na renderizacao das figuras.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass
from fractions import Fraction
from functools import lru_cache
from pathlib import Path
from typing import Callable, Iterable

import matplotlib.pyplot as plt
import numpy as np


F = Fraction


@dataclass(frozen=True, order=True)
class Cell:
    """Celula diadica [index/2^depth,(index+1)/2^depth] em [0,1]."""

    depth: int
    index: int

    @property
    def left(self) -> F:
        return F(self.index, 2**self.depth)

    @property
    def right(self) -> F:
        return F(self.index + 1, 2**self.depth)

    @property
    def length(self) -> F:
        return F(1, 2**self.depth)

    def children(self) -> tuple["Cell", "Cell"]:
        return Cell(self.depth + 1, 2 * self.index), Cell(
            self.depth + 1, 2 * self.index + 1
        )


class PiecewiseQuadratic:
    """Funcao C^1 obtida integrando uma curvatura racional por partes.

    ``curvatures[i]`` e o valor de f'' na i-esima celula da malha uniforme
    de profundidade ``base_depth``. Fixamos f(0)=f'(0)=0.
    """

    def __init__(self, base_depth: int, curvatures: Iterable[F | int]):
        self.base_depth = base_depth
        self.curvatures = tuple(F(value) for value in curvatures)
        if len(self.curvatures) != 2**base_depth:
            raise ValueError("numero de curvaturas incompatível com a malha base")
        self.h = F(1, 2**base_depth)
        values = [F(0)]
        slopes = [F(0)]
        for kappa in self.curvatures:
            values.append(values[-1] + slopes[-1] * self.h + kappa * self.h**2 / 2)
            slopes.append(slopes[-1] + kappa * self.h)
        self.values = tuple(values)
        self.slopes = tuple(slopes)

    def _piece_index(self, x: F) -> int:
        if x == 1:
            return len(self.curvatures) - 1
        return min(int(x / self.h), len(self.curvatures) - 1)

    def value(self, x: F) -> F:
        i = self._piece_index(x)
        x0 = i * self.h
        dx = x - x0
        return self.values[i] + self.slopes[i] * dx + self.curvatures[i] * dx**2 / 2

    def derivative(self, x: F, piece: int | None = None) -> F:
        i = self._piece_index(x) if piece is None else piece
        x0 = i * self.h
        return self.slopes[i] + self.curvatures[i] * (x - x0)

    @lru_cache(maxsize=None)
    def local_error(self, cell: Cell) -> F:
        """Erro uniforme exato do interpolante nas extremidades da celula."""

        a, b = cell.left, cell.right
        fa, fb = self.value(a), self.value(b)
        secant = (fb - fa) / (b - a)
        candidates = {a, b}
        first = self._piece_index(a)
        last = self._piece_index(b)
        for i in range(first, last + 1):
            lo = max(a, i * self.h)
            hi = min(b, (i + 1) * self.h)
            if lo > hi:
                continue
            candidates.add(lo)
            candidates.add(hi)
            kappa = self.curvatures[i]
            if kappa:
                critical = i * self.h + (secant - self.slopes[i]) / kappa
                if lo <= critical <= hi:
                    candidates.add(critical)

        def residual(x: F) -> F:
            line = fa + secant * (x - a)
            return abs(self.value(x) - line)

        return max(residual(x) for x in candidates)

    def curvature_integral_float(self) -> float:
        return float(self.h) * sum(math.sqrt(abs(float(k))) for k in self.curvatures)


def ceil_log4_ratio(numerator: F, denominator: F) -> int:
    """Menor r>=0 tal que numerator*4^{-r} <= denominator."""

    if denominator <= 0:
        raise ValueError("a tolerancia deve ser positiva")
    r = 0
    current = numerator
    while current > denominator:
        current /= 4
        r += 1
    return r


def quadratic_formula(kappa: F, n_leaves: int) -> F:
    if n_leaves < 1:
        raise ValueError("o orçamento deve ser positivo")
    r = n_leaves.bit_length() - 1
    return abs(kappa) / (8 * 4**r)


def threshold_tree_exact(
    local_error: Callable[[Cell], F], epsilon: F, max_depth: int = 80
) -> tuple[Cell, ...]:
    """Arvore menos refinada exata: subdivide os nos com e(J)>eps."""

    leaves: list[Cell] = []
    stack = [Cell(0, 0)]
    while stack:
        cell = stack.pop()
        if local_error(cell) <= epsilon:
            leaves.append(cell)
            continue
        if cell.depth >= max_depth:
            raise RuntimeError("profundidade de seguranca excedida")
        left, right = cell.children()
        stack.append(right)
        stack.append(left)
    return tuple(sorted(leaves))


def optimal_error_dp_exact(local_error: Callable[[Cell], F], budget: int) -> F:
    """DP independente para o menor gargalo com no maximo ``budget`` folhas."""

    @lru_cache(maxsize=None)
    def exact(cell: Cell, leaves: int) -> F:
        if leaves == 1:
            return local_error(cell)
        left, right = cell.children()
        return min(
            max(exact(left, left_count), exact(right, leaves - left_count))
            for left_count in range(1, leaves)
        )

    return min(exact(Cell(0, 0), leaves) for leaves in range(1, budget + 1))


def piecewise_count_formula(model: PiecewiseQuadratic, epsilon: F) -> int:
    count = 0
    for kappa in model.curvatures:
        if not kappa:
            count += 1
            continue
        base_error = abs(kappa) * model.h**2 / 8
        count += 2 ** ceil_log4_ratio(base_error, epsilon)
    return count


def activation_threshold(model: PiecewiseQuadratic) -> F:
    """Limiar abaixo do qual toda a malha base e forçada."""

    if model.base_depth == 0:
        return model.local_error(Cell(0, 0))
    ancestor_errors = [
        model.local_error(Cell(depth, index))
        for depth in range(model.base_depth)
        for index in range(2**depth)
    ]
    positive = [value for value in ancestor_errors if value > 0]
    if len(positive) != len(ancestor_errors):
        raise ValueError("um ancestral afim impede a formula de ativacao simples")
    return min(positive)


def smooth_threshold_count(
    local_error: Callable[[float, float], float], epsilon: float, max_depth: int = 60
) -> int:
    count = 0
    stack = [(0, 0)]
    while stack:
        depth, index = stack.pop()
        scale = 2.0**depth
        a, b = index / scale, (index + 1) / scale
        if local_error(a, b) <= epsilon:
            count += 1
        else:
            if depth >= max_depth:
                raise RuntimeError("profundidade numerica de seguranca excedida")
            stack.append((depth + 1, 2 * index + 1))
            stack.append((depth + 1, 2 * index))
    return count


def exp_error(a: float, b: float) -> float:
    fa, fb = math.exp(a), math.exp(b)
    slope = (fb - fa) / (b - a)
    critical = math.log(slope)
    line = lambda x: fa + slope * (x - a)
    candidates = [a, b]
    if a <= critical <= b:
        candidates.append(critical)
    return max(abs(math.exp(x) - line(x)) for x in candidates)


def cubic_value(x: float) -> float:
    return (x - 0.5) ** 3


def cubic_error(a: float, b: float) -> float:
    fa, fb = cubic_value(a), cubic_value(b)
    slope = (fb - fa) / (b - a)
    candidates = [a, b]
    if slope >= 0:
        root = math.sqrt(slope / 3.0)
        for critical in (0.5 - root, 0.5 + root):
            if a <= critical <= b:
                candidates.append(critical)
    line = lambda x: fa + slope * (x - a)
    return max(abs(cubic_value(x) - line(x)) for x in candidates)


def fmt_fraction(value: F) -> str:
    return str(value.numerator) if value.denominator == 1 else f"{value.numerator}/{value.denominator}"


def save_figure(fig: plt.Figure, pt_pdf: Path, en_pdf: Path) -> None:
    pt_pdf.parent.mkdir(parents=True, exist_ok=True)
    en_pdf.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(pt_pdf, bbox_inches="tight")
    fig.savefig(pt_pdf.with_suffix(".png"), dpi=220, bbox_inches="tight")
    fig.savefig(en_pdf, bbox_inches="tight")
    fig.savefig(en_pdf.with_suffix(".png"), dpi=220, bbox_inches="tight")
    plt.close(fig)


def write_tex_tables(root: Path, results: dict) -> None:
    sections = root / "artigo" / "secoes"
    quadratic = results["quadratic"]
    rows = []
    for row in quadratic["samples"]:
        rows.append(
            f"{row['N']} & {row['r']} & ${row['error_tex']}$ & "
            f"{row['normalized']:.6f} \\\\"
        )
    table = "\n".join(
        [
            r"\begin{tabular}{rrrr}",
            r"\toprule",
            r"$N$ & $\lfloor\log_2N\rfloor$ & $E_N^{\rm dia}(q)_\infty$ & $N^2E_N/A$ \\",
            r"\midrule",
            *rows,
            r"\bottomrule",
            r"\end{tabular}",
            "",
        ]
    )
    (sections / "tab_constante_quadratica.tex").write_text(table, encoding="utf-8")

    audit = results["tests"]
    audit_rows = [
        ("Fórmula quadrática $=$ DP independente", audit["quadratic_dp"]),
        ("Limiar quadrático $=$ contagem fechada", audit["quadratic_threshold"]),
        ("Contagem por partes $=$ árvore de limiar", audit["piecewise_count"]),
        ("DP por partes $=$ inversão do limiar", audit["piecewise_dp"]),
        ("Fases sincronizadas atingem os dois extremos", audit["synchronized_extremes"]),
        ("Diagnóstico $C^2$ positivo dentro do envelope", audit["smooth_positive_envelope"]),
        ("Mudança de sinal dentro do envelope", audit["sign_change_envelope"]),
        ("Varreduras suaves estritamente interiores (400 pontos)", audit["smooth_strict_interior_scan"]),
        ("Execução sem números pseudoaleatórios", True),
    ]
    lines = [r"\begin{tabularx}{\linewidth}{@{}Xr@{}}", r"\toprule", "Verificação & resultado \\\\", r"\midrule"]
    lines.extend(f"{label} & {str(value).lower()} \\\\" for label, value in audit_rows)
    lines.extend([r"\bottomrule", r"\end{tabularx}", ""])
    (sections / "tab_auditoria_constante.tex").write_text("\n".join(lines), encoding="utf-8")

    diagnostics = results["smooth_diagnostics"]
    lines = [
        r"\begin{tabular}{lrrr}",
        r"\toprule",
        r"função & $I(f)^2/8$ & faixa observada de $\varepsilon n_f(\varepsilon)^2$ & $I(f)^2/2$ \\",
        r"\midrule",
    ]
    for name in ("exp", "cubic"):
        row = diagnostics[name]
        lines.append(
            f"{row['label']} & {row['lower']:.6f} & "
            f"[{row['observed_min']:.6f}, {row['observed_max']:.6f}] & "
            f"{row['upper']:.6f} \\\\"
        )
    lines.extend([r"\bottomrule", r"\end{tabular}", ""])
    (sections / "tab_diagnosticos_assintoticos.tex").write_text("\n".join(lines), encoding="utf-8")


def run(root: Path) -> dict:
    figures_pt = root / "reproducibility" / "selecao" / "figures" / "pt"
    figures_en = root / "reproducibility" / "selecao" / "figures" / "en"

    # 1. Curvatura constante: formula fechada, limiar e DP independente.
    quadratic = PiecewiseQuadratic(0, [2])  # q(x)=x^2; A=1/4.
    A = F(1, 4)
    quadratic_dp_ok = all(
        optimal_error_dp_exact(quadratic.local_error, n) == quadratic_formula(F(2), n)
        for n in range(1, 15)
    )
    quadratic_threshold_ok = True
    for r in range(0, 13):
        eps = A / 4**r
        leaves = threshold_tree_exact(quadratic.local_error, eps)
        quadratic_threshold_ok &= len(leaves) == 2**r

    sample_N = [1, 2, 3, 4, 7, 8, 15, 16, 31]
    samples = []
    for n in sample_N:
        r = n.bit_length() - 1
        error = quadratic_formula(F(2), n)
        samples.append(
            {
                "N": n,
                "r": r,
                "error": fmt_fraction(error),
                "error_tex": rf"\frac{{{error.numerator}}}{{{error.denominator}}}",
                "normalized": float(n * n * error / A),
            }
        )

    n_values = np.arange(1, 513)
    normalized = np.array(
        [float(n * n * quadratic_formula(F(2), int(n)) / A) for n in n_values]
    )
    fig, ax = plt.subplots(figsize=(7.25, 3.65))
    ax.plot(n_values, normalized, color="#1f5a94", linewidth=1.15)
    ax.axhline(1.0, color="#1b7f4b", linestyle="--", linewidth=1.0, label="liminf = 1")
    ax.axhline(4.0, color="#a13b2a", linestyle="--", linewidth=1.0, label="limsup = 4")
    ax.set_xscale("log", base=2)
    ax.set_xlabel("orçamento de folhas N")
    ax.set_ylabel(r"$N^2E_N^{\mathrm{dia}}/A$")
    ax.set_title("Curvatura constante: patamares e oscilação diádica")
    ax.set_ylim(0.82, 4.15)
    ax.grid(alpha=0.22)
    ax.legend(frameon=False, ncol=2, loc="lower right")
    fig.tight_layout()
    save_figure(
        fig,
        figures_pt / "fig03_constante_quadratica.pdf",
        figures_en / "fig03_quadratic_constant.pdf",
    )

    # 2. Quadraticas por partes: uma familia sincronizada e outra defasada.
    synchronized = PiecewiseQuadratic(2, [1, -4, 16, -4])
    desynchronized = PiecewiseQuadratic(2, [1, -2, 9, -5])
    activation = min(activation_threshold(synchronized), activation_threshold(desynchronized))
    piecewise_count_ok = True
    for model in (synchronized, desynchronized):
        threshold = min(activation_threshold(model), *(abs(k) * model.h**2 / 8 for k in model.curvatures))
        for r in range(3, 10):
            eps = threshold / 4**r
            direct = len(threshold_tree_exact(model.local_error, eps))
            formula = piecewise_count_formula(model, eps)
            piecewise_count_ok &= direct == formula

    piecewise_dp_ok = True
    for budget in range(1, 13):
        dp_value = optimal_error_dp_exact(desynchronized.local_error, budget)
        # Inversao exata: basta testar os erros locais gerados ate profundidade budget-1.
        spectrum = {
            desynchronized.local_error(Cell(depth, index))
            for depth in range(budget)
            for index in range(2**depth)
        }
        inverse = min(
            eps
            for eps in spectrum
            if len(threshold_tree_exact(desynchronized.local_error, eps)) <= budget
        )
        piecewise_dp_ok &= dp_value == inverse

    A_values = [abs(k) * synchronized.h**2 / 8 for k in synchronized.curvatures]
    I_sync = synchronized.curvature_integral_float()
    lower_sync = I_sync**2 / 8.0
    upper_sync = I_sync**2 / 2.0
    synchronized_extremes = True
    synced_rows = []
    for r in range(3, 13):
        eps = max(A_values) / 4**r
        count = piecewise_count_formula(synchronized, eps)
        low_value = float(eps) * count**2
        # Um orçamento abaixo da duplicacao completa preserva o mesmo erro.
        high_value = float(eps) * (2 * count - 1) ** 2
        synced_rows.append((r, count, low_value, high_value))
        synchronized_extremes &= abs(low_value - lower_sync) < 1e-12
    synchronized_extremes &= abs(synced_rows[-1][3] - upper_sync) < 4e-4

    phases = np.linspace(0.0, 1.0, 600, endpoint=False)
    fig, ax = plt.subplots(figsize=(7.25, 3.75))
    for model, label, color in (
        (synchronized, "fases sincronizadas", "#1f5a94"),
        (desynchronized, "fases defasadas", "#b05a2b"),
    ):
        base_errors = [abs(k) * model.h**2 / 8 for k in model.curvatures]
        # A formula e 1-periodica em s=-log_4(epsilon).
        values = []
        for s in phases:
            eps = 4.0 ** (-(12.0 + s))
            count = sum(
                2 ** max(0, math.ceil(math.log(float(a) / eps, 4) - 1e-13))
                for a in base_errors
            )
            values.append(math.sqrt(eps) * count)
        ax.plot(phases, values, color=color, linewidth=1.35, label=label)
    ax.axhline(I_sync / math.sqrt(8), color="#1b7f4b", linestyle="--", linewidth=0.9)
    ax.axhline(I_sync / math.sqrt(2), color="#1b7f4b", linestyle=":", linewidth=0.9)
    ax.set_xlabel(r"fase $\{-\log_4\varepsilon\}$")
    ax.set_ylabel(r"$\sqrt{\varepsilon}\,n_f(\varepsilon)$")
    ax.set_title("Quadráticas por partes: lei periódica das fases diádicas")
    ax.grid(alpha=0.22)
    ax.legend(frameon=False)
    fig.tight_layout()
    save_figure(
        fig,
        figures_pt / "fig04_fases_piecewise.pdf",
        figures_en / "fig04_piecewise_phases.pdf",
    )

    # 3. Diagnosticos deterministas em C^2: curvatura positiva e mudanca de sinal.
    diagnostics: dict[str, dict] = {}
    smooth_tests = []
    strict_interior_tests = []
    smooth_specs = [
        (
            "exp",
            r"$e^x$",
            exp_error,
            2.0 * (math.sqrt(math.e) - 1.0),
        ),
        (
            "cubic",
            r"$(x-\frac{1}{2})^3$",
            cubic_error,
            2.0 * math.sqrt(3.0) / 3.0,
        ),
    ]
    fig, ax = plt.subplots(figsize=(7.25, 3.8))
    colors = {"exp": "#1f5a94", "cubic": "#a13b2a"}
    for name, label, error_function, integral in smooth_specs:
        eps_values = np.logspace(-3.0, -10.0, 400)
        counts = np.array(
            [smooth_threshold_count(error_function, float(eps)) for eps in eps_values],
            dtype=float,
        )
        scaled = eps_values * counts**2
        lower = integral**2 / 8.0
        upper = integral**2 / 2.0
        scan = scaled
        strict_interior = bool(np.min(scan) > lower and np.max(scan) < upper)
        diagnostics[name] = {
            "label": label,
            "integral": integral,
            "lower": lower,
            "upper": upper,
            "samples": int(len(eps_values)),
            "epsilon_min": float(np.min(eps_values)),
            "epsilon_max": float(np.max(eps_values)),
            "observed_min": float(np.min(scan)),
            "observed_max": float(np.max(scan)),
            "strictly_inside_scan": strict_interior,
        }
        # Verificacao finita: nao e usada como prova de afastamento assintotico.
        smooth_tests.append(np.min(scan) >= lower * 0.965 and np.max(scan) <= upper * 1.035)
        strict_interior_tests.append(strict_interior)
        ax.plot(-np.log10(eps_values), scaled, color=colors[name], linewidth=1.2, label=label)
        ax.axhline(lower, color=colors[name], linestyle="--", linewidth=0.8, alpha=0.75)
        ax.axhline(upper, color=colors[name], linestyle=":", linewidth=0.8, alpha=0.75)
    ax.set_xlabel(r"$-\log_{10}\varepsilon$")
    ax.set_ylabel(r"$\varepsilon\,n_f(\varepsilon)^2$")
    ax.set_title(r"Diagnósticos $C^2$: envelope universal e mudança de sinal")
    ax.grid(alpha=0.22)
    ax.legend(frameon=False)
    fig.tight_layout()
    save_figure(
        fig,
        figures_pt / "fig05_envelope_c2.pdf",
        figures_en / "fig05_c2_envelope.pdf",
    )

    results = {
        "schema": "biblioteca-constante-diadica-v1",
        "deterministic": True,
        "quadratic": {
            "function": "q(x)=x^2",
            "kappa": "2",
            "A": fmt_fraction(A),
            "closed_formula": "E_N=A*4^(-floor(log2(N)))",
            "liminf_N2E": fmt_fraction(A),
            "limsup_N2E": fmt_fraction(4 * A),
            "samples": samples,
        },
        "piecewise": {
            "base_depth": 2,
            "synchronized_curvatures": [fmt_fraction(k) for k in synchronized.curvatures],
            "desynchronized_curvatures": [fmt_fraction(k) for k in desynchronized.curvatures],
            "activation_threshold": fmt_fraction(activation),
            "synchronized_I": I_sync,
            "synchronized_lower": lower_sync,
            "synchronized_upper": upper_sync,
            "synchronized_rows": [
                {"scale": r, "leaves": n, "lower_value": lo, "prejump_value": hi}
                for r, n, lo, hi in synced_rows
            ],
        },
        "smooth_diagnostics": diagnostics,
        "tests": {
            "quadratic_dp": bool(quadratic_dp_ok),
            "quadratic_threshold": bool(quadratic_threshold_ok),
            "piecewise_count": bool(piecewise_count_ok),
            "piecewise_dp": bool(piecewise_dp_ok),
            "synchronized_extremes": bool(synchronized_extremes),
            "smooth_positive_envelope": bool(smooth_tests[0]),
            "sign_change_envelope": bool(smooth_tests[1]),
            "smooth_strict_interior_scan": bool(all(strict_interior_tests)),
        },
    }
    if not all(results["tests"].values()):
        failed = [name for name, value in results["tests"].items() if not value]
        raise AssertionError(f"auditorias falharam: {failed}")

    output = root / "reproducibility" / "selecao" / "resultados_constante_diadica.json"
    output.write_text(json.dumps(results, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    write_tex_tables(root, results)
    return results


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output-root", type=Path, required=True)
    args = parser.parse_args()
    results = run(args.output_root.resolve())
    print(json.dumps({"tests": results["tests"]}, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
