#!/usr/bin/env python3
"""Auditoria deterministica das restricoes da ponte com redes ReLU.

O programa executa independentemente das demais auditorias. Toda identidade
algébrica usa ``fractions.Fraction``; ponto flutuante aparece apenas na figura.
"""

from __future__ import annotations

import argparse
import itertools
import json
import math
import platform
from fractions import Fraction
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np


Q = Fraction


def rho(x: Q) -> Q:
    return max(Q(0), x)


def height(x: Q) -> int:
    return max(abs(x.numerator), x.denominator)


def is_dyadic(x: Q) -> bool:
    d = x.denominator
    return d > 0 and d & (d - 1) == 0


def dyadic_depth(x: Q) -> int:
    assert is_dyadic(x)
    return x.denominator.bit_length() - 1


def eval_relu(x: Q, c: Q, q: Q, hinges: tuple[tuple[Q, Q], ...]) -> Q:
    return c + q * x + sum(a * rho(x - tau) for tau, a in hinges)


def local_slopes(q: Q, hinges: tuple[tuple[Q, Q], ...]) -> tuple[Q, ...]:
    slopes = [q]
    current = q
    for _, a in hinges:
        current += a
        slopes.append(current)
    return tuple(slopes)


def canonical_library_conditions(
    c: Q, q: Q, hinges: tuple[tuple[Q, Q], ...]
) -> bool:
    del c  # Fraction ja certifica racionalidade.
    knots = [tau for tau, _ in hinges]
    jumps = [a for _, a in hinges]
    return (
        knots == sorted(knots)
        and len(knots) == len(set(knots))
        and all(Q(0) < tau < Q(1) and is_dyadic(tau) for tau in knots)
        and all(a != 0 for a in jumps)
        and all(s != 0 for s in local_slopes(q, hinges))
    )


def relu_to_uniform_atoms(
    c: Q, q: Q, hinges: tuple[tuple[Q, Q], ...]
) -> tuple[tuple[int, int, Q, Q], ...]:
    assert canonical_library_conditions(c, q, hinges)
    depth = max((dyadic_depth(tau) for tau, _ in hinges), default=0)
    atoms = []
    for m in range(2**depth):
        left = Q(m, 2**depth)
        right = Q(m + 1, 2**depth)
        center = (left + right) / 2
        slope = q + sum(a for tau, a in hinges if tau < center)
        value = eval_relu(center, c, q, hinges)
        assert slope != 0
        atoms.append((depth, m, value, slope))
    return tuple(atoms)


def atoms_to_canonical_relu(
    atoms: tuple[tuple[int, int, Q, Q], ...]
) -> tuple[Q, Q, tuple[tuple[Q, Q], ...]]:
    assert atoms
    depth = atoms[0][0]
    assert all(k == depth and m == j for j, (k, m, _, _) in enumerate(atoms))
    first_center = Q(1, 2 ** (depth + 1))
    q = atoms[0][3]
    c = atoms[0][2] - q * first_center
    hinges = []
    previous = q
    for j in range(1, len(atoms)):
        slope = atoms[j][3]
        jump = slope - previous
        if jump:
            hinges.append((Q(j, 2**depth), jump))
        previous = slope
    return c, q, tuple(hinges)


def norm_infty(c: Q, q: Q, hinges: tuple[tuple[Q, Q], ...]) -> Q:
    points = (Q(0),) + tuple(tau for tau, _ in hinges) + (Q(1),)
    return max(abs(eval_relu(x, c, q, hinges)) for x in points)


def second_difference_max(
    c: Q, q: Q, hinges: tuple[tuple[Q, Q], ...], h: Q
) -> Q:
    assert Q(0) < h <= Q(1, 2)
    candidates = {Q(0), Q(1) - 2 * h}
    for tau, _ in hinges:
        candidates.update((tau, tau - h, tau - 2 * h))
    candidates = {x for x in candidates if Q(0) <= x <= Q(1) - 2 * h}
    return max(
        abs(
            eval_relu(x + 2 * h, c, q, hinges)
            - 2 * eval_relu(x + h, c, q, hinges)
            + eval_relu(x, c, q, hinges)
        )
        for x in candidates
    )


def tent(x: Q) -> Q:
    assert Q(0) <= x <= Q(1)
    return 2 * rho(x) - 4 * rho(x - Q(1, 2))


def tent_iterate(x: Q, depth: int) -> Q:
    value = x
    for _ in range(depth):
        value = tent(value)
    return value


def atom_height(k: int, m: int, y0: Q, slope: Q) -> int:
    return max(2, k + 1, abs(m) + 1, height(y0), height(slope))


def audit_roundtrips() -> dict[str, int | bool]:
    knots = (Q(1, 4), Q(1, 2), Q(3, 4))
    coefficients = (Q(-2), Q(-1), Q(1), Q(2))
    intercepts = (Q(0), Q(1, 2))
    checked = 0
    rejected_zero_slope = 0
    for count in range(4):
        for selected in itertools.combinations(knots, count):
            for c in intercepts:
                for q in coefficients:
                    for jumps in itertools.product(coefficients, repeat=count):
                        hinges = tuple(zip(selected, jumps))
                        if not all(s != 0 for s in local_slopes(q, hinges)):
                            rejected_zero_slope += 1
                            continue
                        assert canonical_library_conditions(c, q, hinges)
                        atoms = relu_to_uniform_atoms(c, q, hinges)
                        recovered = atoms_to_canonical_relu(atoms)
                        assert recovered == (c, q, hinges)
                        for j in range(17):
                            x = Q(j, 16)
                            assert eval_relu(x, c, q, hinges) == eval_relu(
                                x, recovered[0], recovered[1], recovered[2]
                            )
                        checked += 1
    return {
        "canonical_roundtrips": checked,
        "zero_slope_networks_rejected": rejected_zero_slope,
        "all_exact": True,
    }


def audit_obstructions() -> dict[str, object]:
    non_dyadic = (Q(0), Q(1), ((Q(1, 3), Q(1)),))
    plateau = (Q(0), Q(1), ((Q(1, 2), Q(-1)),))
    assert not canonical_library_conditions(*non_dyadic)
    assert not canonical_library_conditions(*plateau)
    assert local_slopes(plateau[1], plateau[2]) == (Q(1), Q(0))
    assert math.isqrt(2) ** 2 != 2
    return {
        "non_dyadic_kink": {
            "function": "x + rho(x-1/3)",
            "dyadic_knot": False,
            "local_slopes": ["1", "2"],
            "in_library": False,
        },
        "flat_region": {
            "function": "x - rho(x-1/2)",
            "dyadic_knot": True,
            "local_slopes": ["1", "0"],
            "in_library": False,
        },
        "irrational_slope": {
            "function": "sqrt(2) x",
            "certificate": "2 is not a perfect square; sqrt(2) is irrational",
            "in_library": False,
        },
    }


def audit_tent(max_depth: int = 10) -> list[dict[str, int | bool]]:
    rows = []
    for depth in range(1, max_depth + 1):
        regions = 2**depth
        values = [tent_iterate(Q(j, regions), depth) for j in range(regions + 1)]
        assert values == [Q(j % 2) for j in range(regions + 1)]
        heights = []
        slopes = []
        for m in range(regions):
            left = Q(m, regions)
            right = Q(m + 1, regions)
            slope = (values[m + 1] - values[m]) / (right - left)
            y0 = tent_iterate((left + right) / 2, depth)
            assert y0 == Q(1, 2)
            assert slope == (regions if m % 2 == 0 else -regions)
            slopes.append(slope)
            heights.append(atom_height(depth, m, y0, slope))
        assert max(heights) == regions
        # Duas amostras internas adicionais por célula confrontam a composição
        # com a reta determinada por seus extremos.
        for m in range(regions):
            left = Q(m, regions)
            for offset in (Q(1, 3), Q(2, 3)):
                x = left + offset / regions
                expected = values[m] + slopes[m] * (x - left)
                assert tent_iterate(x, depth) == expected
        rows.append(
            {
                "depth": depth,
                "network_blocks": depth,
                "affine_regions": regions,
                "minimum_library_leaves": regions,
                "minimum_atomic_height": regions,
                "verified": True,
            }
        )
    return rows


def audit_kink() -> dict[str, object]:
    # |x-1/2| = 1/2-x + 2 rho(x-1/2).
    c, q, hinges = Q(1, 2), Q(-1), ((Q(1, 2), Q(2)),)
    atoms = relu_to_uniform_atoms(c, q, hinges)
    heights = [atom_height(*atom) for atom in atoms]
    assert heights == [4, 4]
    modulus = []
    for r in range(1, 13):
        h = Q(1, 2**r)
        exact = second_difference_max(c, q, hinges, h)
        assert exact == 2 * h
        modulus.append({"r": r, "h": str(h), "omega2": str(exact)})
    return {
        "function": "abs(x-1/2)",
        "leaves": 2,
        "atomic_height": 4,
        "omega2_formula": "2h for 0<h<=1/2",
        "dyadic_checks": modulus,
        "besov_threshold": {
            "s<1": "all 0<r<=infinity",
            "s=1": "only r=infinity",
            "s>1": "none",
        },
    }


def audit_bernstein() -> dict[str, int | bool]:
    knots = (Q(1, 4), Q(1, 2), Q(3, 4))
    coefficients = (Q(-2), Q(-1), Q(1), Q(2))
    checked_networks = 0
    checked_inequalities = 0
    for count in range(4):
        for selected in itertools.combinations(knots, count):
            for q in coefficients:
                for jumps in itertools.product(coefficients, repeat=count):
                    hinges = tuple(zip(selected, jumps))
                    slopes = local_slopes(q, hinges)
                    if not all(s != 0 for s in slopes):
                        continue
                    c = Q(1, 3)
                    bound = max(abs(s) for s in slopes)
                    size = norm_infty(c, q, hinges)
                    for r in range(1, 7):
                        h = Q(1, 2**r)
                        omega = second_difference_max(c, q, hinges, h)
                        assert omega <= 4 * size
                        assert omega <= 2 * bound * h
                        checked_inequalities += 1
                    checked_networks += 1
    return {
        "networks": checked_networks,
        "exact_inequalities": checked_inequalities,
        "bound": "omega2(g,h) <= min(4||g||_infty, 2||g'||_infty h)",
        "all_true": True,
    }


def write_table(path: Path, rows: list[dict[str, int | bool]]) -> None:
    lines = [
        r"\begin{tabular}{rrrr}",
        r"\toprule",
        r"profundidade $L$ & blocos & regiões/folhas mín. & altura mín.\\",
        r"\midrule",
    ]
    for row in rows[:8]:
        lines.append(
            f"{row['depth']} & {row['network_blocks']} & "
            f"{row['affine_regions']} & {row['minimum_atomic_height']}\\\\"
        )
    lines.extend((r"\bottomrule", r"\end{tabular}"))
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def write_figure(pdf_path: Path, png_path: Path) -> None:
    xs = np.linspace(0.0, 1.0, 2049)

    def tent_float(values: np.ndarray) -> np.ndarray:
        return 2 * np.maximum(values, 0) - 4 * np.maximum(values - 0.5, 0)

    fig, axes = plt.subplots(1, 2, figsize=(10.2, 3.6))
    for depth, color in zip((1, 2, 3, 4), ("#1f77b4", "#2ca02c", "#ff7f0e", "#d62728")):
        ys = xs.copy()
        for _ in range(depth):
            ys = tent_float(ys)
        axes[0].plot(xs, ys, lw=1.5, color=color, label=f"L={depth}")
    axes[0].set_xlabel("x")
    axes[0].set_ylabel(r"$T^{\circ L}(x)$")
    axes[0].set_title("Composição da tenda")
    axes[0].legend(ncol=2, frameon=False)
    axes[0].grid(alpha=0.2)

    depths = np.arange(1, 11)
    exponential = 2.0**depths
    axes[1].semilogy(depths, exponential, "o-", color="#7f3c8d", label="regiões = folhas = altura")
    axes[1].plot(depths, depths, "s--", color="#11a579", label="blocos de rede")
    axes[1].set_xticks(depths)
    axes[1].set_xlabel("profundidade L")
    axes[1].set_ylabel("complexidade (escala log)")
    axes[1].set_title("Separação por profundidade")
    axes[1].legend(frameon=False)
    axes[1].grid(alpha=0.2, which="both")

    fig.tight_layout()
    fig.savefig(pdf_path, bbox_inches="tight")
    fig.savefig(png_path, dpi=220, bbox_inches="tight")
    plt.close(fig)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output-root", type=Path, required=True)
    args = parser.parse_args()
    root = args.output_root.resolve()
    figures = root / "reproducibility" / "selecao" / "figures" / "pt"
    figures.mkdir(parents=True, exist_ok=True)

    roundtrips = audit_roundtrips()
    obstructions = audit_obstructions()
    tent_rows = audit_tent()
    kink = audit_kink()
    bernstein = audit_bernstein()

    results = {
        "metadata": {
            "python": platform.python_version(),
            "numpy": np.__version__,
            "matplotlib": matplotlib.__version__,
            "deterministic": True,
            "floating_point_scope": "figure only",
        },
        "canonical_network_image": roundtrips,
        "independent_obstructions": obstructions,
        "deep_tent_separation": tent_rows,
        "inverse_besov_counterexample": kink,
        "bernstein_height_audit": bernstein,
        "verdicts": {
            "generic_relu_reverse_map": False,
            "shallow_restricted_reverse_map": True,
            "deep_complexity_equivalence": False,
            "naive_besov_inverse_above_order_one": False,
            "all_assertions_passed": True,
        },
    }
    (root / "reproducibility" / "selecao" / "resultados_restricoes_rede.json").write_text(
        json.dumps(results, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )
    write_table(root / "artigo" / "secoes" / "tab_tenda_rede.tex", tent_rows)
    write_figure(
        figures / "fig_restricoes_rede.pdf",
        figures / "fig_restricoes_rede.png",
    )

    print("Restrições ReLU: todas as auditorias passaram.")
    print(json.dumps(results["verdicts"], indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
