#!/usr/bin/env python3
"""Auditoria independente da reversibilidade regularizada.

O programa verifica cinco mecanismos em aritmetica racional exata:

1. arvore diadica canonica de uma forma ReLU rasa;
2. ida e volta exata para a biblioteca marcada que admite inclinacao zero;
3. reversao aproximada de redes rasas com nos nao diadicos;
4. desigualdade universal do certificado de autorregularidade;
5. testemunhas criticas (quina, tenda profunda e pente de tendas), incluindo
   a transferencia do pente para a biblioteca original por perturbacoes
   diadicas de inclinacao nao nula.

Ponto flutuante e usado apenas para desenhar a figura de diagnostico.
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


def ceil_fraction(x: Q) -> int:
    return -((-x.numerator) // x.denominator)


def is_dyadic(x: Q) -> bool:
    d = x.denominator
    return d > 0 and d & (d - 1) == 0


def dyadic_depth(x: Q) -> int:
    assert is_dyadic(x)
    return x.denominator.bit_length() - 1


def eval_relu(x: Q, c: Q, q: Q, hinges: tuple[tuple[Q, Q], ...]) -> Q:
    return c + q * x + sum(a * rho(x - tau) for tau, a in hinges)


def local_slopes(q: Q, hinges: tuple[tuple[Q, Q], ...]) -> tuple[Q, ...]:
    values = [q]
    current = q
    for _, jump in hinges:
        current += jump
        values.append(current)
    return tuple(values)


def reduced_hinges(hinges: tuple[tuple[Q, Q], ...]) -> tuple[tuple[Q, Q], ...]:
    combined: dict[Q, Q] = {}
    for tau, jump in hinges:
        combined[tau] = combined.get(tau, Q(0)) + jump
    return tuple((tau, jump) for tau, jump in sorted(combined.items()) if jump)


def sup_difference(
    first: tuple[Q, Q, tuple[tuple[Q, Q], ...]],
    second: tuple[Q, Q, tuple[tuple[Q, Q], ...]],
) -> Q:
    points = {Q(0), Q(1)}
    points.update(tau for tau, _ in first[2] if Q(0) < tau < Q(1))
    points.update(tau for tau, _ in second[2] if Q(0) < tau < Q(1))
    return max(
        abs(eval_relu(x, *first) - eval_relu(x, *second)) for x in points
    )


def second_modulus(
    network: tuple[Q, Q, tuple[tuple[Q, Q], ...]], h: Q
) -> Q:
    assert Q(0) < h <= Q(1, 2)
    c, q, hinges = network
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


def canonical_tree_leaves(
    knots: tuple[Q, ...], k: int = 0, m: int = 0
) -> tuple[tuple[int, int], ...]:
    """Folhas da unica arvore diadica menos refinada compativel com knots."""
    left = Q(m, 2**k)
    right = Q(m + 1, 2**k)
    interior = tuple(tau for tau in knots if left < tau < right)
    if not interior:
        return ((k, m),)
    middle = (left + right) / 2
    left_knots = tuple(tau for tau in interior if tau < middle)
    right_knots = tuple(tau for tau in interior if tau > middle)
    return canonical_tree_leaves(left_knots, k + 1, 2 * m) + canonical_tree_leaves(
        right_knots, k + 1, 2 * m + 1
    )


def atom_height(k: int, m: int, y0: Q, slope: Q) -> int:
    return max(2, k + 1, abs(m) + 1, height(y0), height(slope))


def network_to_marked_atoms(
    network: tuple[Q, Q, tuple[tuple[Q, Q], ...]]
) -> tuple[tuple[int, int, Q, Q], ...]:
    c, q, hinges = network
    hinges = reduced_hinges(hinges)
    assert all(is_dyadic(tau) and Q(0) < tau < Q(1) for tau, _ in hinges)
    leaves = canonical_tree_leaves(tuple(tau for tau, _ in hinges))
    atoms = []
    for k, m in leaves:
        center = Q(2 * m + 1, 2 ** (k + 1))
        slope = q + sum(jump for tau, jump in hinges if tau < center)
        atoms.append((k, m, eval_relu(center, c, q, hinges), slope))
    return tuple(atoms)


def atoms_to_relu(
    atoms: tuple[tuple[int, int, Q, Q], ...]
) -> tuple[Q, Q, tuple[tuple[Q, Q], ...]]:
    assert atoms
    ordered = sorted(atoms, key=lambda atom: Q(atom[1], 2 ** atom[0]))
    first = ordered[0]
    first_center = Q(2 * first[1] + 1, 2 ** (first[0] + 1))
    q = first[3]
    c = first[2] - q * first_center
    hinges: list[tuple[Q, Q]] = []
    previous_slope = q
    previous_right = Q(first[1] + 1, 2 ** first[0])
    for atom in ordered[1:]:
        left = Q(atom[1], 2 ** atom[0])
        assert left == previous_right
        slope = atom[3]
        if slope != previous_slope:
            hinges.append((left, slope - previous_slope))
        previous_slope = slope
        previous_right = Q(atom[1] + 1, 2 ** atom[0])
    assert previous_right == 1
    return c, q, tuple(hinges)


def round_to_grid(x: Q, denominator: int) -> Q:
    scaled = x * denominator
    lower = scaled.numerator // scaled.denominator
    upper = lower + 1
    chosen = lower if scaled - lower <= upper - scaled else upper
    return Q(chosen, denominator)


def round_to_dyadic(x: Q, depth: int) -> Q:
    return min(Q(1), max(Q(0), round_to_grid(x, 2**depth)))


def approximate_reverse(
    network: tuple[Q, Q, tuple[tuple[Q, Q], ...]], eps: Q
) -> tuple[tuple[Q, Q, tuple[tuple[Q, Q], ...]], dict[str, int | Q]]:
    """Quantiza coeficientes e nos; uma inclinacao global evita platôs."""
    c, q, hinges = network
    m = len(hinges)
    w = max(
        [Q(1), abs(c), abs(q)] + [abs(jump) for _, jump in hinges]
    )
    eta = eps / (16 * (m + 1) * (w + 1))
    denominator = ceil_fraction(1 / eta)
    depth = max(1, math.ceil(math.log2(float(1 / eta))))

    c_new = round_to_grid(c, denominator)
    q_new = round_to_grid(q, denominator)
    rounded = []
    for tau, jump in hinges:
        tau_new = round_to_dyadic(tau, depth)
        jump_new = round_to_grid(jump, denominator)
        if tau_new == 0:
            q_new += jump_new
        elif tau_new < 1 and jump_new:
            rounded.append((tau_new, jump_new))
    hinges_new = reduced_hinges(tuple(rounded))

    # Ha no maximo M+1 valores proibidos para t. Entre M+2 inteiros,
    # escolhe-se um que torne todas as inclinacoes locais nao nulas.
    for t in range(1, len(hinges_new) + 3):
        candidate_q = q_new + Q(t, denominator)
        if all(slope != 0 for slope in local_slopes(candidate_q, hinges_new)):
            q_new = candidate_q
            break
    else:  # pragma: no cover - principio da casa dos pombos impede este ramo.
        raise AssertionError("nao foi encontrada perturbacao de inclinacao")

    quantized = (c_new, q_new, hinges_new)
    error = sup_difference(network, quantized)
    assert error <= eps
    atoms = network_to_marked_atoms(quantized)
    assert all(slope != 0 for _, _, _, slope in atoms)
    actual_height = max(atom_height(*atom) for atom in atoms)
    depth_sum = sum(dyadic_depth(tau) for tau, _ in hinges_new)
    assert len(atoms) <= 1 + depth_sum
    theorem_height_bound = ceil_fraction(
        Q(4096) * (m + 1) ** 3 * (ceil_fraction(w) + 1) ** 3 / (eps**2)
    )
    assert actual_height <= theorem_height_bound
    return quantized, {
        "M": m,
        "W": ceil_fraction(w),
        "epsilon": eps,
        "depth": depth,
        "leaves": len(atoms),
        "leaf_bound": 1 + m * depth,
        "height": actual_height,
        "height_bound": theorem_height_bound,
        "error": error,
    }


def tent_hinges(left: Q, width: Q, amplitude: Q) -> tuple[tuple[Q, Q], ...]:
    middle = left + width / 2
    right = left + width
    slope = 2 * amplitude / width
    return ((left, slope), (middle, -2 * slope), (right, slope))


def audit_exact_reversibility() -> dict[str, object]:
    knots_pool = (Q(1, 8), Q(1, 4), Q(1, 2), Q(3, 4))
    coeffs = (Q(-2), Q(-1), Q(1), Q(2))
    checked = 0
    flat_cases = 0
    leaf_ratios = []
    for count in range(4):
        for knots in itertools.combinations(knots_pool, count):
            for c in (Q(0), Q(1, 3)):
                for q in coeffs:
                    for jumps in itertools.product(coeffs, repeat=count):
                        network = (c, q, tuple(zip(knots, jumps)))
                        atoms = network_to_marked_atoms(network)
                        recovered = atoms_to_relu(atoms)
                        assert recovered == network
                        depths = sum(dyadic_depth(tau) for tau in knots)
                        assert count + 1 <= len(atoms) <= 1 + depths
                        for j in range(33):
                            x = Q(j, 32)
                            assert eval_relu(x, *network) == eval_relu(x, *recovered)
                        checked += 1
                        flat_cases += int(any(s == 0 for s in local_slopes(q, network[2])))
                        leaf_ratios.append((len(atoms), 1 + depths))
    return {
        "exact_roundtrips": checked,
        "roundtrips_with_flat_regions": flat_cases,
        "max_canonical_leaves": max(a for a, _ in leaf_ratios),
        "all_leaf_bounds_hold": all(a <= b for a, b in leaf_ratios),
    }


def audit_approximate_reverse() -> tuple[dict[str, object], list[dict[str, object]]]:
    knots = (Q(1, 3), Q(2, 5), Q(5, 7))
    coeffs = (Q(-7, 3), Q(-1, 2), Q(2, 3), Q(5, 4))
    rows: list[dict[str, object]] = []
    checked = 0
    ratios = []
    for count in (1, 2, 3):
        for chosen_knots in itertools.combinations(knots, count):
            for q in coeffs:
                jumps = tuple(coeffs[(i + count) % len(coeffs)] for i in range(count))
                network = (Q(1, 5), q, tuple(zip(chosen_knots, jumps)))
                for eps in (Q(1, 32), Q(1, 64), Q(1, 128)):
                    _, data = approximate_reverse(network, eps)
                    checked += 1
                    ratio = data["error"] / eps
                    ratios.append(ratio)
                    if len(rows) < 6:
                        rows.append(
                            {
                                key: (str(value) if isinstance(value, Q) else value)
                                for key, value in data.items()
                            }
                        )
    return (
        {
            "networks_quantized": checked,
            "maximum_error_over_epsilon": float(max(ratios)),
            "all_error_bounds_hold": max(ratios) <= 1,
        },
        rows,
    )


def audit_regularized_triangle() -> dict[str, object]:
    networks = []
    knots = (Q(1, 4), Q(1, 2), Q(3, 4))
    for q in (Q(-2), Q(-1), Q(1), Q(2)):
        for jumps in itertools.product((Q(-1), Q(1)), repeat=3):
            networks.append((Q(1, 5), q, tuple(zip(knots, jumps))))
    checked = 0
    maximum_ratio = Q(0)
    for first, second in itertools.islice(itertools.product(networks, repeat=2), 420):
        error = sup_difference(first, second)
        for h in (Q(1, 32), Q(1, 16), Q(1, 8)):
            lhs = second_modulus(first, h)
            rhs = 4 * error + second_modulus(second, h)
            assert lhs <= rhs
            if rhs:
                maximum_ratio = max(maximum_ratio, lhs / rhs)
            checked += 1
    return {
        "triangle_certificates": checked,
        "maximum_lhs_over_rhs": float(maximum_ratio),
        "all_certificates_hold": True,
    }


def audit_kink_and_tent() -> tuple[list[dict[str, object]], list[dict[str, object]]]:
    kink = (Q(1, 2), Q(-1), ((Q(1, 2), Q(2)),))
    kink_rows = []
    for r in range(1, 11):
        n = 2**r
        h = Q(1, n)
        modulus = second_modulus(kink, h) if h <= Q(1, 2) else Q(0)
        assert modulus == 2 * h
        kink_rows.append(
            {
                "r": r,
                "N": n,
                "raw_error": "0",
                "roughness": str(modulus),
                "scaled_s_half": float((Q(n) ** Q(1, 2)) * modulus),
                "scaled_s_one": float(n * modulus),
                "scaled_s_three_halves": float((Q(n) ** Q(3, 2)) * modulus),
            }
        )

    tent_rows = []
    for depth in range(1, 11):
        regions = 2**depth
        hinges = []
        q = Q(regions)
        for j in range(1, regions):
            hinges.append((Q(j, regions), Q(-2 * regions if j % 2 else 2 * regions)))
        network = (Q(0), q, tuple(hinges))
        modulus = second_modulus(network, Q(1, regions))
        assert modulus == 2
        tent_rows.append(
            {
                "depth": depth,
                "regions": regions,
                "lipschitz": regions,
                "roughness_at_region_scale": str(modulus),
            }
        )
    return kink_rows, tent_rows


def audit_critical_comb(
    alpha: int = 1, gamma: int = 1, block: int = 4, count: int = 6
) -> list[dict[str, object]]:
    assert 0 < alpha <= gamma
    all_hinges: list[tuple[Q, Q]] = []
    rows = []
    previous_r = -10
    sigma = Q(alpha, alpha + gamma)
    for j in range(1, count + 1):
        a = block * alpha * j
        b = block * gamma * j
        r = a + b - 1
        assert r >= previous_r + 2
        previous_r = r
        amplitude = Q(1, 2**a)
        width = Q(1, 2**r)
        left = Q(1, 2**r)
        all_hinges.extend(tent_hinges(left, width, amplitude))
        network = (Q(0), Q(0), reduced_hinges(tuple(all_hinges)))
        marked_atoms = network_to_marked_atoms(network)
        n_budget = 2 ** (block * j)
        delta = Q(1, 2 ** (block * alpha * (j + 1) + 2))
        original_atoms: list[tuple[int, int, Q, Q]] = []
        for k, m, y0, slope in marked_atoms:
            if slope:
                original_atoms.append((k, m, y0, slope))
                continue
            assert y0 == 0
            tent_slope = delta * (2 ** (k + 1))
            original_atoms.extend(
                (
                    (k + 1, 2 * m, delta / 2, tent_slope),
                    (k + 1, 2 * m + 1, delta / 2, -tent_slope),
                )
            )
        atoms = tuple(original_atoms)
        perturbed_network = atoms_to_relu(atoms)
        perturbation_error = sup_difference(network, perturbed_network)
        actual_height = max(atom_height(*atom) for atom in atoms)
        assert all(atom[3] != 0 for atom in atoms)
        assert perturbation_error == delta
        assert len(atoms) <= n_budget
        height_constant = 2 ** (block * alpha + 3)
        assert actual_height <= height_constant * (n_budget**gamma)
        next_amplitude = Q(1, 2 ** (block * alpha * (j + 1)))
        total_error_bound = next_amplitude + perturbation_error
        assert total_error_bound <= Q(2, n_budget**alpha)
        h = width / 2
        modulus = second_modulus(network, h)
        assert modulus >= 2 * amplitude
        normalized = Q(modulus.numerator, modulus.denominator) / (h**sigma)
        rows.append(
            {
                "j": j,
                "N": n_budget,
                "leaves": len(atoms),
                "height": actual_height,
                "original_library": True,
                "all_local_slopes_nonzero": True,
                "flat_leaf_perturbation": str(delta),
                "perturbation_error": str(perturbation_error),
                "tail_plus_perturbation_bound": str(total_error_bound),
                "height_constant": height_constant,
                "amplitude": str(amplitude),
                "half_width": str(h),
                "critical_ratio": float(normalized),
            }
        )
    return rows


def write_tables(output_root: Path, approx_rows: list[dict[str, object]], kink_rows: list[dict[str, object]]) -> None:
    sections = output_root / "artigo" / "secoes"
    sections.mkdir(parents=True, exist_ok=True)
    resource_lines = [
        r"\begin{tabular}{rrrrrr}",
        r"\toprule",
        r"$M$ & $\varepsilon$ & $D$ & folhas & cota de folhas & erro/$\varepsilon$\\",
        r"\midrule",
    ]
    for row in approx_rows:
        ratio = float(Q(row["error"]) / Q(row["epsilon"]))
        resource_lines.append(
            f"{row['M']} & ${row['epsilon']}$ & {row['depth']} & {row['leaves']} & "
            f"{row['leaf_bound']} & {ratio:.4f}\\\\"
        )
    resource_lines.extend([r"\bottomrule", r"\end{tabular}"])
    (sections / "tab_reversao_aproximada.tex").write_text(
        "\n".join(resource_lines) + "\n", encoding="utf-8"
    )

    kink_lines = [
        r"\begin{tabular}{rrrrr}",
        r"\toprule",
        r"$N$ & $e_N(\psi)$ & $\omega_2(\psi,N^{-1})$ & $N\omega_2$ & $N^{3/2}\omega_2$\\",
        r"\midrule",
    ]
    for row in kink_rows[1:7]:
        kink_lines.append(
            f"{row['N']} & 0 & ${row['roughness']}$ & "
            f"{row['scaled_s_one']:.3f} & {row['scaled_s_three_halves']:.3f}\\\\"
        )
    kink_lines.extend([r"\bottomrule", r"\end{tabular}"])
    (sections / "tab_certificado_quina.tex").write_text(
        "\n".join(kink_lines) + "\n", encoding="utf-8"
    )


def make_figure(
    output_root: Path,
    kink_rows: list[dict[str, object]],
    comb_rows: list[dict[str, object]],
    approx_rows: list[dict[str, object]],
) -> None:
    figure_dir = output_root / "reproducibility" / "selecao" / "figures" / "pt"
    figure_dir.mkdir(parents=True, exist_ok=True)
    fig, axes = plt.subplots(1, 3, figsize=(11.8, 3.4))

    widths = np.array([float(Q(row["half_width"])) for row in comb_rows])
    amplitudes = np.array([float(Q(row["amplitude"])) for row in comb_rows])
    axes[0].loglog(widths, amplitudes, "o-", color="#355C7D", label="pente crítico")
    reference = amplitudes[0] * (widths / widths[0]) ** 0.5
    axes[0].loglog(widths, reference, "--", color="#C06C84", label=r"inclinação $1/2$")
    axes[0].set_xlabel("meia-largura $h$")
    axes[0].set_ylabel("amplitude")
    axes[0].set_title("Agudeza do expoente inverso")
    axes[0].legend(fontsize=8)
    axes[0].grid(alpha=0.25)

    n = np.array([row["N"] for row in kink_rows], dtype=float)
    axes[1].loglog(n, [row["scaled_s_half"] for row in kink_rows], "o-", label=r"$s=1/2$")
    axes[1].loglog(n, [row["scaled_s_one"] for row in kink_rows], "s-", label=r"$s=1$")
    axes[1].loglog(n, [row["scaled_s_three_halves"] for row in kink_rows], "^-", label=r"$s=3/2$")
    axes[1].set_xlabel("orçamento $N$")
    axes[1].set_ylabel(r"$N^s\omega_2(\psi,N^{-1})$")
    axes[1].set_title("A quina deixa de ter taxa infinita")
    axes[1].legend(fontsize=8)
    axes[1].grid(alpha=0.25)

    eps = np.array([float(Q(row["epsilon"])) for row in approx_rows])
    errors = np.array([float(Q(row["error"])) for row in approx_rows])
    axes[2].loglog(eps, errors, "o", color="#6C5B7B", label="erro exato")
    grid = np.geomspace(eps.min(), eps.max(), 50)
    axes[2].loglog(grid, grid, "--", color="#F67280", label=r"erro $=\varepsilon$")
    axes[2].set_xlabel(r"tolerância $\varepsilon$")
    axes[2].set_ylabel("erro uniforme")
    axes[2].set_title("Reversão aproximada quantizada")
    axes[2].legend(fontsize=8)
    axes[2].grid(alpha=0.25)

    fig.tight_layout()
    fig.savefig(figure_dir / "fig_reversibilidade_regularizada.pdf", bbox_inches="tight")
    fig.savefig(figure_dir / "fig_reversibilidade_regularizada.png", dpi=220, bbox_inches="tight")
    plt.close(fig)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output-root", type=Path, required=True)
    args = parser.parse_args()
    output_root = args.output_root.resolve()

    exact = audit_exact_reversibility()
    approximate, approx_rows = audit_approximate_reverse()
    triangle = audit_regularized_triangle()
    kink_rows, tent_rows = audit_kink_and_tent()
    comb_rows = audit_critical_comb()

    result = {
        "metadata": {
            "python": platform.python_version(),
            "numpy": np.__version__,
            "arithmetic": "fractions.Fraction except plotting",
        },
        "exact_reversibility": exact,
        "approximate_reverse": approximate,
        "regularized_triangle": triangle,
        "kink": kink_rows,
        "deep_tent": tent_rows,
        "critical_comb": comb_rows,
        "all_assertions_passed": True,
    }

    reproducibility = output_root / "reproducibility" / "selecao"
    reproducibility.mkdir(parents=True, exist_ok=True)
    (reproducibility / "resultados_reversibilidade.json").write_text(
        json.dumps(result, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )
    write_tables(output_root, approx_rows, kink_rows)
    make_figure(output_root, kink_rows, comb_rows, approx_rows)

    print(json.dumps({
        "exact_roundtrips": exact["exact_roundtrips"],
        "approximate_networks": approximate["networks_quantized"],
        "triangle_certificates": triangle["triangle_certificates"],
        "critical_comb_rows": len(comb_rows),
        "all_assertions_passed": True,
    }, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
