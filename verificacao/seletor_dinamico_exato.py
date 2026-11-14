#!/usr/bin/env python3
"""Selecao exata em catalogos afins racionalmente truncados.

O programa implementa, com fractions.Fraction, as recorrencias do artigo:

* programacao dinamica para uma arvore diadica fixa;
* programacao dinamica que escolhe simultaneamente a arvore e os atomos;
* auditorias por enumeracao direta e por derivacao independente das definicoes;
* recorrencias com numero exato de folhas e gargalo uniforme;
* comparacao deterministica com malha uniforme, arvore certificada por
  curvatura e uma heuristica gulosa de particoes.

Nao ha numeros pseudoaleatorios e nenhuma decisao de otimalidade depende de
ponto flutuante. numpy e matplotlib sao usados apenas nas figuras.
"""

from __future__ import annotations

import argparse
import json
import math
import platform
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Callable, Iterator

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np


ROOT_CELL = (0, 0)


def rational_height(value: Fraction) -> int:
    return max(abs(value.numerator), value.denominator)


def integer_index(value: int) -> int:
    return 2 * value if value >= 0 else -2 * value - 1


def rationals_up_to_height(H: int, *, exclude_zero: bool = False) -> tuple[Fraction, ...]:
    values: list[Fraction] = []
    for shell in range(1, H + 1):
        shell_values: list[tuple[int, int]] = []
        for denominator in range(1, shell + 1):
            for numerator in range(-shell, shell + 1):
                if max(abs(numerator), denominator) != shell:
                    continue
                if math.gcd(abs(numerator), denominator) != 1:
                    continue
                if exclude_zero and numerator == 0:
                    continue
                shell_values.append((denominator, numerator))
        shell_values.sort()
        values.extend(Fraction(p, q) for q, p in shell_values)
    return tuple(values)


def atom_height(atom: "Atom") -> int:
    return max(
        2,
        atom.k + 1,
        abs(atom.m) + 1,
        rational_height(atom.y0),
        rational_height(atom.slope),
    )


def sharp_rank_map(H: int) -> dict[tuple[int, int, Fraction, Fraction], int]:
    """Ranks de Gamma^sharp em todas as cascas ate H."""
    rank: dict[tuple[int, int, Fraction, Fraction], int] = {}
    next_rank = 0
    for shell in range(2, H + 1):
        rationals = rationals_up_to_height(shell)
        nonzero = rationals_up_to_height(shell, exclude_zero=True)
        ordered_m = sorted(range(-(shell - 1), shell), key=integer_index)
        for k in range(shell):
            for m in ordered_m:
                for y0 in rationals:
                    for slope in nonzero:
                        key = (k, m, y0, slope)
                        candidate = Atom(k, m, y0, slope, -1)
                        if atom_height(candidate) != shell:
                            continue
                        rank[key] = next_rank
                        next_rank += 1
    return rank


def elias_gamma(value: int) -> str:
    if value < 1:
        raise ValueError("Elias gamma codifica apenas inteiros positivos")
    payload = f"{value:b}"
    return "0" * (len(payload) - 1) + payload


@dataclass(frozen=True, order=True)
class Cell:
    k: int
    m: int

    @property
    def left(self) -> Fraction:
        return Fraction(self.m, 2**self.k)

    @property
    def right(self) -> Fraction:
        return Fraction(self.m + 1, 2**self.k)

    @property
    def width(self) -> Fraction:
        return Fraction(1, 2**self.k)

    def children(self) -> tuple["Cell", "Cell"]:
        return Cell(self.k + 1, 2 * self.m), Cell(self.k + 1, 2 * self.m + 1)


@dataclass(frozen=True)
class Atom:
    k: int
    m: int
    y0: Fraction
    slope: Fraction
    sharp_rank: int

    @property
    def cell(self) -> Cell:
        return Cell(self.k, self.m)

    @property
    def left_value(self) -> Fraction:
        return self.y0 - self.slope * self.cell.width / 2

    @property
    def right_value(self) -> Fraction:
        return self.y0 + self.slope * self.cell.width / 2

    @property
    def intercept(self) -> Fraction:
        center = (self.cell.left + self.cell.right) / 2
        return self.y0 - self.slope * center

    def evaluate(self, x: Fraction) -> Fraction:
        return self.intercept + self.slope * x

    @property
    def leaf_stream(self) -> str:
        return "1" + elias_gamma(self.sharp_rank + 1)


@dataclass(frozen=True)
class Observation:
    x: Fraction
    y: Fraction
    weight: Fraction = Fraction(1)


@dataclass(frozen=True)
class Tree:
    cell: Cell
    atom: Atom | None = None
    left: "Tree | None" = None
    right: "Tree | None" = None

    @property
    def is_leaf(self) -> bool:
        return self.atom is not None

    def leaves(self) -> tuple[Atom, ...]:
        if self.is_leaf:
            assert self.atom is not None
            return (self.atom,)
        assert self.left is not None and self.right is not None
        return self.left.leaves() + self.right.leaves()

    def shape(self):
        if self.is_leaf:
            return "L"
        assert self.left is not None and self.right is not None
        return (self.left.shape(), self.right.shape())


@dataclass(frozen=True)
class Candidate:
    loss: Fraction
    bits: int
    splits: int
    stream: str
    tree: Tree
    lambda_bits: Fraction
    lambda_split: Fraction

    @property
    def cost(self) -> Fraction:
        return self.loss + self.lambda_bits * self.bits + self.lambda_split * self.splits

    @property
    def leaves(self) -> int:
        return self.splits + 1

    @property
    def key(self) -> tuple[Fraction, int, str]:
        return self.cost, len(self.stream), self.stream


def better(candidate: Candidate, incumbent: Candidate | None) -> bool:
    return incumbent is None or candidate.key < incumbent.key


def owned(cell: Cell, x: Fraction, root: Cell) -> bool:
    if cell.left <= x < cell.right:
        return True
    return x == root.right and cell.right == root.right


def atom_loss(atom: Atom, observations: tuple[Observation, ...], root: Cell) -> Fraction:
    return sum(
        (
            obs.weight * (obs.y - atom.evaluate(obs.x)) ** 2
            for obs in observations
            if owned(atom.cell, obs.x, root)
        ),
        Fraction(0),
    )


class ExactSelector:
    def __init__(
        self,
        H: int,
        observations: tuple[Observation, ...],
        *,
        root: Cell = Cell(*ROOT_CELL),
        lambda_bits: Fraction = Fraction(1, 500),
        lambda_split: Fraction = Fraction(1, 100),
    ) -> None:
        if H < max(2, root.k + 1, abs(root.m) + 1):
            raise ValueError("H nao admite sequer a raiz")
        self.H = H
        self.observations = observations
        self.root = root
        self.lambda_bits = lambda_bits
        self.lambda_split = lambda_split
        self.rationals = rationals_up_to_height(H)
        self.nonzero = rationals_up_to_height(H, exclude_zero=True)
        self.sharp_ranks = sharp_rank_map(H)
        self._leaf_cache: dict[Cell, dict[tuple[Fraction, Fraction], Candidate]] = {}
        self._variable_cache: dict[tuple[Cell, int], dict[tuple[Fraction, Fraction], Candidate]] = {}
        self._fixed_cache: dict[
            tuple[object, Cell], dict[tuple[Fraction, Fraction], Candidate]
        ] = {}
        self._budget_cache: dict[
            tuple[Cell, int],
            dict[int, dict[tuple[Fraction, Fraction], Candidate]],
        ] = {}

    def atoms(self, cell: Cell) -> tuple[Atom, ...]:
        if cell.k + 1 > self.H or abs(cell.m) + 1 > self.H:
            return ()
        rows: list[Atom] = []
        for y0 in self.rationals:
            for slope in self.nonzero:
                key = (cell.k, cell.m, y0, slope)
                rank = self.sharp_ranks.get(key)
                if rank is None:
                    raise AssertionError(f"atomo admissivel ausente de Gamma^sharp: {key}")
                rows.append(Atom(cell.k, cell.m, y0, slope, rank))
        return tuple(rows)

    def leaf_states(self, cell: Cell) -> dict[tuple[Fraction, Fraction], Candidate]:
        cached = self._leaf_cache.get(cell)
        if cached is not None:
            return cached
        states: dict[tuple[Fraction, Fraction], Candidate] = {}
        for atom in self.atoms(cell):
            stream = atom.leaf_stream
            candidate = Candidate(
                loss=atom_loss(atom, self.observations, self.root),
                bits=len(stream),
                splits=0,
                stream=stream,
                tree=Tree(cell=cell, atom=atom),
                lambda_bits=self.lambda_bits,
                lambda_split=self.lambda_split,
            )
            state = (atom.left_value, atom.right_value)
            if state in states:
                raise AssertionError("os extremos deveriam determinar um unico atomo")
            states[state] = candidate
        self._leaf_cache[cell] = states
        return states

    def combine(
        self,
        cell: Cell,
        left_states: dict[tuple[Fraction, Fraction], Candidate],
        right_states: dict[tuple[Fraction, Fraction], Candidate],
    ) -> dict[tuple[Fraction, Fraction], Candidate]:
        right_by_boundary: dict[Fraction, list[tuple[Fraction, Candidate]]] = {}
        for (middle, right_value), candidate in right_states.items():
            right_by_boundary.setdefault(middle, []).append((right_value, candidate))

        combined: dict[tuple[Fraction, Fraction], Candidate] = {}
        for (left_value, middle), left_candidate in left_states.items():
            for right_value, right_candidate in right_by_boundary.get(middle, ()):
                stream = "0" + left_candidate.stream + right_candidate.stream
                candidate = Candidate(
                    loss=left_candidate.loss + right_candidate.loss,
                    bits=1 + left_candidate.bits + right_candidate.bits,
                    splits=1 + left_candidate.splits + right_candidate.splits,
                    stream=stream,
                    tree=Tree(
                        cell=cell,
                        left=left_candidate.tree,
                        right=right_candidate.tree,
                    ),
                    lambda_bits=self.lambda_bits,
                    lambda_split=self.lambda_split,
                )
                state = (left_value, right_value)
                if better(candidate, combined.get(state)):
                    combined[state] = candidate
        return combined

    def variable_states(self, cell: Cell, remaining_depth: int) -> dict[tuple[Fraction, Fraction], Candidate]:
        cache_key = (cell, remaining_depth)
        cached = self._variable_cache.get(cache_key)
        if cached is not None:
            return cached
        states = dict(self.leaf_states(cell))
        if remaining_depth > 0:
            left_cell, right_cell = cell.children()
            split_states = self.combine(
                cell,
                self.variable_states(left_cell, remaining_depth - 1),
                self.variable_states(right_cell, remaining_depth - 1),
            )
            for state, candidate in split_states.items():
                if better(candidate, states.get(state)):
                    states[state] = candidate
        self._variable_cache[cache_key] = states
        return states

    def variable_optimum(self, D: int) -> Candidate:
        states = self.variable_states(self.root, D)
        if not states:
            raise RuntimeError("catalogo vazio")
        return min(states.values(), key=lambda candidate: candidate.key)

    def fixed_states(self, shape, cell: Cell | None = None) -> dict[tuple[Fraction, Fraction], Candidate]:
        if cell is None:
            cell = self.root
        cache_key = (shape, cell)
        cached = self._fixed_cache.get(cache_key)
        if cached is not None:
            return cached
        if shape == "L":
            states = self.leaf_states(cell)
        else:
            left_shape, right_shape = shape
            left_cell, right_cell = cell.children()
            states = self.combine(
                cell,
                self.fixed_states(left_shape, left_cell),
                self.fixed_states(right_shape, right_cell),
            )
        self._fixed_cache[cache_key] = states
        return states

    def fixed_optimum(self, shape) -> Candidate | None:
        states = self.fixed_states(shape)
        return min(states.values(), key=lambda candidate: candidate.key) if states else None

    def budget_states(
        self, cell: Cell, remaining_depth: int
    ) -> dict[int, dict[tuple[Fraction, Fraction], Candidate]]:
        """Melhor candidato por (numero de folhas, valores externos)."""
        cache_key = (cell, remaining_depth)
        cached = self._budget_cache.get(cache_key)
        if cached is not None:
            return cached

        by_leaves = {1: dict(self.leaf_states(cell))}
        if remaining_depth > 0:
            left_cell, right_cell = cell.children()
            left_levels = self.budget_states(left_cell, remaining_depth - 1)
            right_levels = self.budget_states(right_cell, remaining_depth - 1)
            for left_count, left_states in left_levels.items():
                for right_count, right_states in right_levels.items():
                    leaf_count = left_count + right_count
                    combined = self.combine(cell, left_states, right_states)
                    if not combined:
                        continue
                    target = by_leaves.setdefault(leaf_count, {})
                    for state, candidate in combined.items():
                        if better(candidate, target.get(state)):
                            target[state] = candidate

        self._budget_cache[cache_key] = by_leaves
        return by_leaves

    def budget_optimum(self, D: int, N: int) -> Candidate:
        candidates = [
            candidate
            for leaf_count, states in self.budget_states(self.root, D).items()
            if leaf_count <= N
            for candidate in states.values()
        ]
        if not candidates:
            raise RuntimeError("catalogo vazio sob o orcamento de folhas")
        return min(candidates, key=lambda candidate: candidate.key)


def full_shape(depth: int):
    if depth == 0:
        return "L"
    child = full_shape(depth - 1)
    return child, child


def tree_shapes(depth: int) -> tuple:
    if depth == 0:
        return ("L",)
    previous = tree_shapes(depth - 1)
    return ("L",) + tuple((left, right) for left in previous for right in previous)


def shape_leaves(shape) -> int:
    if shape == "L":
        return 1
    return shape_leaves(shape[0]) + shape_leaves(shape[1])


def iter_leaf_paths(shape, prefix: tuple[int, ...] = ()) -> Iterator[tuple[int, ...]]:
    if shape == "L":
        yield prefix
        return
    yield from iter_leaf_paths(shape[0], prefix + (0,))
    yield from iter_leaf_paths(shape[1], prefix + (1,))


def split_at_path(shape, path: tuple[int, ...]):
    if not path:
        if shape != "L":
            raise ValueError("o caminho nao aponta para uma folha")
        return ("L", "L")
    if shape == "L":
        raise ValueError("caminho atravessa uma folha")
    head, *tail = path
    if head == 0:
        return split_at_path(shape[0], tuple(tail)), shape[1]
    return shape[0], split_at_path(shape[1], tuple(tail))


def greedy_tree(selector: ExactSelector, D: int) -> Candidate:
    shape = "L"
    incumbent = selector.fixed_optimum(shape)
    assert incumbent is not None
    while True:
        best_shape = None
        best_candidate = incumbent
        for path in iter_leaf_paths(shape):
            if len(path) >= D:
                continue
            candidate_shape = split_at_path(shape, path)
            candidate = selector.fixed_optimum(candidate_shape)
            if candidate is not None and better(candidate, best_candidate):
                best_candidate = candidate
                best_shape = candidate_shape
        if best_shape is None:
            return incumbent
        shape = best_shape
        incumbent = best_candidate


def runge_value(x: Fraction) -> Fraction:
    t = x - Fraction(1, 4)
    return Fraction(1, 1) / (1 + 16 * t * t)


def runge_second_bound(cell: Cell) -> Fraction:
    """Maximo exato de |f''| para f=1/(1+16(x-1/4)^2) em uma celula."""
    a = cell.left - Fraction(1, 4)
    b = cell.right - Fraction(1, 4)
    square_min = Fraction(0) if a <= 0 <= b else min(a * a, b * b)
    square_max = max(a * a, b * b)
    candidates = [square_min, square_max]
    for critical in (Fraction(1, 48), Fraction(1, 16)):
        if square_min <= critical <= square_max:
            candidates.append(critical)

    def magnitude(square: Fraction) -> Fraction:
        return 32 * abs(48 * square - 1) / (1 + 16 * square) ** 3

    return max(magnitude(square) for square in candidates)


def certified_shape(cell: Cell, D: int, epsilon: Fraction):
    if D == 0 or runge_second_bound(cell) * cell.width * cell.width <= 8 * epsilon:
        return "L"
    left, right = cell.children()
    return certified_shape(left, D - 1, epsilon), certified_shape(right, D - 1, epsilon)


def observations_on_grid(power: int) -> tuple[Observation, ...]:
    denominator = 2**power
    return tuple(
        Observation(Fraction(i, denominator), runge_value(Fraction(i, denominator)))
        for i in range(denominator + 1)
    )


def evaluate_tree(tree: Tree, x: Fraction) -> Fraction:
    if tree.is_leaf:
        assert tree.atom is not None
        return tree.atom.evaluate(x)
    assert tree.left is not None and tree.right is not None
    if x < tree.left.cell.right:
        return evaluate_tree(tree.left, x)
    return evaluate_tree(tree.right, x)


def fraction_text(value: Fraction) -> str:
    return str(value.numerator) if value.denominator == 1 else f"{value.numerator}/{value.denominator}"


def decimal_text(value: Fraction, digits: int = 8) -> str:
    return f"{float(value):.{digits}f}"


def candidate_record(name: str, candidate: Candidate) -> dict[str, object]:
    leaf_rows = []
    for atom in candidate.tree.leaves():
        leaf_rows.append(
            {
                "cell": [atom.k, atom.m],
                "left": fraction_text(atom.cell.left),
                "right": fraction_text(atom.cell.right),
                "left_value": fraction_text(atom.left_value),
                "right_value": fraction_text(atom.right_value),
                "y0": fraction_text(atom.y0),
                "slope": fraction_text(atom.slope),
                "height": atom_height(atom),
                "sharp_rank": atom.sharp_rank,
            }
        )
    return {
        "name": name,
        "cost_exact": fraction_text(candidate.cost),
        "cost_decimal": float(candidate.cost),
        "loss_exact": fraction_text(candidate.loss),
        "loss_decimal": float(candidate.loss),
        "bits": candidate.bits,
        "splits": candidate.splits,
        "leaves": candidate.leaves,
        "stream": candidate.stream,
        "leaf_atoms": leaf_rows,
    }


def definition_level_audit() -> dict[str, object]:
    """Reconstroi pares e perdas diretamente das definicoes, sem os auxiliares da PD."""
    H = 2
    observations = tuple(
        Observation(x, 2 * abs(x - Fraction(1, 2)))
        for x in (
            Fraction(0),
            Fraction(1, 4),
            Fraction(1, 2),
            Fraction(3, 4),
            Fraction(1),
        )
    )
    selector = ExactSelector(
        H,
        observations,
        lambda_bits=Fraction(1, 200),
        lambda_split=Fraction(1, 50),
    )

    # Enumeracao separada de Q_H a partir de max{|p|,q} <= H e mdc(|p|,q)=1.
    direct_rationals = {
        Fraction(numerator, denominator)
        for denominator in range(1, H + 1)
        for numerator in range(-H, H + 1)
        if max(abs(numerator), denominator) <= H
        and math.gcd(abs(numerator), denominator) == 1
    }
    assert direct_rationals == set(selector.rationals)

    cells = (selector.root,) + selector.root.children()
    atoms_checked = 0
    losses_checked = 0
    for cell in cells:
        expected_states = {
            (
                y0 - slope * cell.width / 2,
                y0 + slope * cell.width / 2,
            )
            for y0 in direct_rationals
            for slope in direct_rationals
            if slope != 0
        }
        actual_states = set(selector.leaf_states(cell))
        assert actual_states == expected_states

        for atom in selector.atoms(cell):
            atoms_checked += 1
            u = atom.y0 - atom.slope * cell.width / 2
            v = atom.y0 + atom.slope * cell.width / 2
            direct_loss = Fraction(0)
            for observation in observations:
                belongs = cell.left <= observation.x < cell.right or (
                    observation.x == selector.root.right
                    and cell.right == selector.root.right
                )
                if not belongs:
                    continue
                value = u + (v - u) * (observation.x - cell.left) / cell.width
                direct_loss += observation.weight * (observation.y - value) ** 2
            assert direct_loss == atom_loss(atom, observations, selector.root)
            losses_checked += 1

    return {
        "H": H,
        "rational_values_from_definition": len(direct_rationals),
        "cells_checked": len(cells),
        "atoms_checked": atoms_checked,
        "losses_checked": losses_checked,
        "endpoint_dictionary_matches_definition": True,
        "local_losses_match_direct_formula": True,
    }


def direct_bruteforce_check() -> dict[str, object]:
    """Enumeracao direta de todas as representacoes para D=1,H=2."""
    observations = tuple(
        Observation(x, 2 * abs(x - Fraction(1, 2)))
        for x in (Fraction(0), Fraction(1, 4), Fraction(1, 2), Fraction(3, 4), Fraction(1))
    )
    selector = ExactSelector(
        2,
        observations,
        lambda_bits=Fraction(1, 200),
        lambda_split=Fraction(1, 50),
    )
    dp = selector.variable_optimum(1)
    candidates = list(selector.leaf_states(selector.root).values())
    left_cell, right_cell = selector.root.children()
    left_atoms = selector.atoms(left_cell)
    right_atoms = selector.atoms(right_cell)
    tested_split_pairs = 0
    for left_atom in left_atoms:
        for right_atom in right_atoms:
            tested_split_pairs += 1
            if left_atom.right_value != right_atom.left_value:
                continue
            left_stream = left_atom.leaf_stream
            right_stream = right_atom.leaf_stream
            stream = "0" + left_stream + right_stream
            candidate = Candidate(
                loss=atom_loss(left_atom, observations, selector.root)
                + atom_loss(right_atom, observations, selector.root),
                bits=len(stream),
                splits=1,
                stream=stream,
                tree=Tree(
                    selector.root,
                    left=Tree(left_cell, atom=left_atom),
                    right=Tree(right_cell, atom=right_atom),
                ),
                lambda_bits=selector.lambda_bits,
                lambda_split=selector.lambda_split,
            )
            candidates.append(candidate)
    brute = min(candidates, key=lambda candidate: candidate.key)
    assert brute.key == dp.key
    assert brute.stream == dp.stream
    return {
        "H": 2,
        "D": 1,
        "root_leaf_candidates": len(selector.leaf_states(selector.root)),
        "split_pairs_tested": tested_split_pairs,
        "continuous_representations_tested": len(candidates),
        "dp_equals_direct_enumeration": True,
        "winner_cost": fraction_text(dp.cost),
        "winner_stream": dp.stream,
    }


def exhaustive_representations(
    selector: "ExactSelector", cell: Cell, depth: int
) -> list[Candidate]:
    """Todas as representacoes continuas, SEM poda por estado.

    Serve para checar a canonicidade do desempate: a programacao dinamica
    guarda um unico candidato por estado, e este enumerador nao guarda
    nenhum, de modo que a coincidencia das duas chaves e uma verificacao
    genuina da compatibilidade de (custo, comprimento, ordem lexicografica)
    com a concatenacao de fluxos.
    """
    rows = list(selector.leaf_states(cell).values())
    if depth > 0:
        left_cell, right_cell = cell.children()
        left = exhaustive_representations(selector, left_cell, depth - 1)
        right = exhaustive_representations(selector, right_cell, depth - 1)
        by_boundary: dict[Fraction, list[Candidate]] = {}
        for candidate in right:
            by_boundary.setdefault(candidate.tree.leaves()[0].left_value, []).append(candidate)
        for left_candidate in left:
            middle = left_candidate.tree.leaves()[-1].right_value
            for right_candidate in by_boundary.get(middle, ()):
                stream = "0" + left_candidate.stream + right_candidate.stream
                rows.append(
                    Candidate(
                        loss=left_candidate.loss + right_candidate.loss,
                        bits=1 + left_candidate.bits + right_candidate.bits,
                        splits=1 + left_candidate.splits + right_candidate.splits,
                        stream=stream,
                        tree=Tree(cell=cell, left=left_candidate.tree, right=right_candidate.tree),
                        lambda_bits=selector.lambda_bits,
                        lambda_split=selector.lambda_split,
                    )
                )
    return rows


def candidate_boundary(candidate: Candidate) -> tuple[Fraction, Fraction]:
    leaves = candidate.tree.leaves()
    return leaves[0].left_value, leaves[-1].right_value


def bottleneck_states(
    selector: ExactSelector,
    cell: Cell,
    remaining_depth: int,
    local_error: Callable[[Atom], Fraction],
) -> dict[int, dict[tuple[Fraction, Fraction], Fraction]]:
    """Recorrencia min-max por numero exato de folhas."""
    leaf_states = {
        (atom.left_value, atom.right_value): local_error(atom)
        for atom in selector.atoms(cell)
    }
    by_leaves: dict[int, dict[tuple[Fraction, Fraction], Fraction]] = {
        1: leaf_states
    }
    if remaining_depth == 0:
        return by_leaves

    left_cell, right_cell = cell.children()
    left_levels = bottleneck_states(
        selector, left_cell, remaining_depth - 1, local_error
    )
    right_levels = bottleneck_states(
        selector, right_cell, remaining_depth - 1, local_error
    )
    for left_count, left_rows in left_levels.items():
        for right_count, right_rows in right_levels.items():
            leaf_count = left_count + right_count
            target = by_leaves.get(leaf_count)
            right_by_middle: dict[Fraction, list[tuple[Fraction, Fraction]]] = {}
            for (middle, right_value), error in right_rows.items():
                right_by_middle.setdefault(middle, []).append((right_value, error))
            for (left_value, middle), left_error in left_rows.items():
                for right_value, right_error in right_by_middle.get(middle, ()):
                    if target is None:
                        target = {}
                        by_leaves[leaf_count] = target
                    state = (left_value, right_value)
                    error = max(left_error, right_error)
                    incumbent = target.get(state)
                    if incumbent is None or error < incumbent:
                        target[state] = error
    return by_leaves


def budget_and_bottleneck_audit() -> dict[str, object]:
    """Compara as duas recorrencias da Secao 6 com enumeracao sem poda."""
    H, D = 3, 2
    observations = tuple(
        Observation(Fraction(i, 4), Fraction(i % 2, 2)) for i in range(5)
    )
    selector = ExactSelector(
        H,
        observations,
        lambda_bits=Fraction(1, 200),
        lambda_split=Fraction(1, 50),
    )
    every = exhaustive_representations(selector, selector.root, D)

    exhaustive_additive: dict[
        int, dict[tuple[Fraction, Fraction], Candidate]
    ] = {}
    for candidate in every:
        state = candidate_boundary(candidate)
        target = exhaustive_additive.setdefault(candidate.leaves, {})
        if better(candidate, target.get(state)):
            target[state] = candidate

    dynamic_additive = selector.budget_states(selector.root, D)
    assert set(dynamic_additive) == set(exhaustive_additive)
    additive_entries = 0
    for leaf_count, exhaustive_rows in exhaustive_additive.items():
        dynamic_rows = dynamic_additive[leaf_count]
        assert set(dynamic_rows) == set(exhaustive_rows)
        for state, exhaustive_candidate in exhaustive_rows.items():
            dynamic_candidate = dynamic_rows[state]
            assert dynamic_candidate.key == exhaustive_candidate.key
            assert dynamic_candidate.stream == exhaustive_candidate.stream
            additive_entries += 1

    # Para f=0, o supremo de uma funcao afim em cada folha e atingido em um
    # extremo, logo e_f(J;u,v)=max(|u|,|v|) exatamente em Fraction.
    def zero_target_error(atom: Atom) -> Fraction:
        return max(abs(atom.left_value), abs(atom.right_value))

    exhaustive_bottleneck: dict[
        int, dict[tuple[Fraction, Fraction], Fraction]
    ] = {}
    for candidate in every:
        error = max(zero_target_error(atom) for atom in candidate.tree.leaves())
        state = candidate_boundary(candidate)
        target = exhaustive_bottleneck.setdefault(candidate.leaves, {})
        incumbent = target.get(state)
        if incumbent is None or error < incumbent:
            target[state] = error

    dynamic_bottleneck = bottleneck_states(
        selector, selector.root, D, zero_target_error
    )
    assert dynamic_bottleneck == exhaustive_bottleneck

    at_most_budget_checks = 0
    for N in range(1, 2**D + 1):
        dynamic = selector.budget_optimum(D, N)
        exhaustive = min(
            (candidate for candidate in every if candidate.leaves <= N),
            key=lambda candidate: candidate.key,
        )
        assert dynamic.key == exhaustive.key and dynamic.stream == exhaustive.stream
        at_most_budget_checks += 1

    return {
        "H": H,
        "D": D,
        "continuous_representations": len(every),
        "feasible_leaf_counts": sorted(exhaustive_additive),
        "additive_state_entries_checked": additive_entries,
        "at_most_leaf_budgets_checked": at_most_budget_checks,
        "leaf_budget_dp_equals_exhaustive": True,
        "bottleneck_target": "f(x)=0",
        "bottleneck_dp_equals_exhaustive": True,
    }


def tie_break_stress() -> list[dict[str, object]]:
    """Instancias em que o minimo de custo NAO e unico.

    Sem esses casos o desempate canonico jamais e exercitado: nas instancias
    principais o minimizador de custo ja e unico.
    """
    scenarios = [
        # (a) empate total num nivel de recursao: todo custo vale zero.
        ("sem dados, lambdas nulas, um nivel", 2, 1, (), Fraction(0), Fraction(0)),
        # (b) empate total em dois niveis de recursao.
        ("sem dados, lambdas nulas, dois niveis", 3, 2, (), Fraction(0), Fraction(0)),
        # (c) empate que sobrevive ao criterio de comprimento e so e resolvido
        #     pela ordem lexicografica do fluxo.
        (
            "dados nulos, lambdas nulas",
            3,
            2,
            tuple(Observation(Fraction(i, 8), Fraction(0)) for i in range(9)),
            Fraction(0),
            Fraction(0),
        ),
    ]
    report: list[dict[str, object]] = []
    for name, H, D, observations, lam_bits, lam_split in scenarios:
        selector = ExactSelector(
            H, observations, lambda_bits=lam_bits, lambda_split=lam_split
        )
        every = exhaustive_representations(selector, selector.root, D)
        best = min(every, key=lambda candidate: candidate.key)
        dp = selector.variable_optimum(D)
        cheapest = min(candidate.cost for candidate in every)
        tied_cost = [c for c in every if c.cost == cheapest]
        shortest = min(len(c.stream) for c in tied_cost)
        tied_length = [c for c in tied_cost if len(c.stream) == shortest]
        assert dp.key == best.key and dp.stream == best.stream
        report.append(
            {
                "scenario": name,
                "H": H,
                "D": D,
                "continuous_representations": len(every),
                "tied_on_cost": len(tied_cost),
                "still_tied_on_length": len(tied_length),
                "dp_equals_exhaustive_key": True,
                "winner_stream": dp.stream,
            }
        )
    return report


def untruncated_robustness_audit(truncated_exact: Candidate) -> dict[str, object]:
    """Repete a comparacao num orcamento em que nenhuma celula e eliminada.

    Na instancia principal (D,H)=(3,4) a condicao de translacao elimina quatro
    celulas, e cabe perguntar se a comparacao entre seletores e um artefato
    dessa truncagem. Aqui (D,H)=(2,4) satisfaz as duas condicoes da
    Proposicao 2.5 --- k0+D+1 <= H e 2^D(m0+1) <= H ---, de modo que a arvore
    completa e integralmente admissivel. O mesmo alvo e as mesmas penalidades
    sao usados.
    """
    H, D = 4, 2
    observations = observations_on_grid(4)
    selector = ExactSelector(
        H,
        observations,
        lambda_bits=Fraction(1, 500),
        lambda_split=Fraction(1, 100),
    )
    geometry = catalog_geometry(H, D, Cell(*ROOT_CELL))
    assert geometry["cells_empty"] == 0
    assert geometry["tree_shapes_feasible"] == geometry["tree_shapes_total"]

    exact = selector.variable_optimum(D)
    uniform = min(
        (
            candidate
            for candidate in (selector.fixed_optimum(full_shape(d)) for d in range(D + 1))
            if candidate is not None
        ),
        key=lambda candidate: candidate.key,
    )
    adaptive_rows = []
    for power in range(1, 11):
        epsilon = Fraction(1, 2**power)
        candidate = selector.fixed_optimum(certified_shape(selector.root, D, epsilon))
        if candidate is not None:
            adaptive_rows.append((candidate, epsilon))
    adaptive, adaptive_epsilon = min(adaptive_rows, key=lambda row: row[0].key)
    greedy = greedy_tree(selector, D)

    return {
        "H": H,
        "D": D,
        "scale_condition_holds": ROOT_CELL[0] + D + 1 <= H,
        "translation_condition_holds": 2**D * (abs(ROOT_CELL[1]) + 1) <= H,
        "cells_empty": geometry["cells_empty"],
        "tree_shapes_feasible": geometry["tree_shapes_feasible"],
        "tree_shapes_total": geometry["tree_shapes_total"],
        "adaptive_epsilon": fraction_text(adaptive_epsilon),
        "objectives": {
            "exact": float(exact.cost),
            "uniform": float(uniform.cost),
            "adaptive": float(adaptive.cost),
            "greedy": float(greedy.cost),
        },
        "leaves": {
            "exact": exact.leaves,
            "uniform": uniform.leaves,
            "adaptive": adaptive.leaves,
            "greedy": greedy.leaves,
        },
        "exact_cost_exact": fraction_text(exact.cost),
        "exact_matches_truncated_instance": (
            exact.cost == truncated_exact.cost and exact.stream == truncated_exact.stream
        ),
    }


def geometry_formula_audit() -> dict[str, object]:
    """Testa a Proposicao 2.5, incluindo casos em que a escala falha."""
    cases = 0
    for k0 in range(5):
        for m0 in range(5):
            for H in range(2, 11):
                for r in range(6):
                    actual = sum(
                        1
                        for j in range(2**r)
                        if k0 + r + 1 <= H
                        and abs(2**r * m0 + j) + 1 <= H
                    )
                    predicted = (
                        min(2**r, max(0, H - 2**r * m0))
                        if k0 + r + 1 <= H
                        else 0
                    )
                    all_predicted = (
                        k0 + r + 1 <= H and 2**r * (m0 + 1) <= H
                    )
                    assert actual == predicted
                    assert (actual == 2**r) is all_predicted
                    cases += 1
    return {
        "parameter_cases_checked": cases,
        "includes_scale_failure_cases": True,
        "nonempty_cell_count_formula_verified": True,
        "full_uniform_refinement_conditions_verified": True,
    }


def catalog_geometry(H: int, D: int, root: Cell) -> dict[str, object]:
    """Diagnostico da obstrucao de translacao |m|+1 <= H.

    Esta funcao mede separadamente a geometria das celulas e a viabilidade
    das formas de arvore no catalogo concreto.
    """
    selector = ExactSelector(H, (), root=root)
    cells: list[Cell] = [root]
    frontier = [root]
    for _ in range(D):
        nxt: list[Cell] = []
        for cell in frontier:
            nxt.extend(cell.children())
        cells.extend(nxt)
        frontier = nxt
    empty = [cell for cell in cells if not selector.atoms(cell)]
    feasible_shapes = 0
    for shape in tree_shapes(D):
        if selector.fixed_states(shape):
            feasible_shapes += 1
    uniform = {}
    for depth in range(D + 1):
        uniform[depth] = bool(selector.fixed_states(full_shape(depth)))
    return {
        "H": H,
        "D": D,
        "cells_total": len(cells),
        "cells_empty": len(empty),
        "empty_cells": [[c.k, c.m] for c in empty],
        "tree_shapes_total": len(tree_shapes(D)),
        "tree_shapes_feasible": feasible_shapes,
        "uniform_mesh_feasible_by_depth": uniform,
        "max_uniform_refinement_depth": max(
            (r for r, feasible in uniform.items() if feasible), default=-1
        ),
    }


def compare_methods(H: int, D: int) -> tuple[dict[str, Candidate], dict[str, object]]:
    observations = observations_on_grid(4)
    selector = ExactSelector(
        H,
        observations,
        lambda_bits=Fraction(1, 500),
        lambda_split=Fraction(1, 100),
    )
    exact = selector.variable_optimum(D)

    shape_candidates = []
    for shape in tree_shapes(D):
        candidate = selector.fixed_optimum(shape)
        if candidate is not None:
            shape_candidates.append(candidate)
    shape_exact = min(shape_candidates, key=lambda candidate: candidate.key)
    assert exact.key == shape_exact.key
    assert exact.stream == shape_exact.stream

    uniform_candidates = []
    for depth in range(D + 1):
        candidate = selector.fixed_optimum(full_shape(depth))
        if candidate is not None:
            uniform_candidates.append(candidate)
    uniform = min(uniform_candidates, key=lambda candidate: candidate.key)

    # A referencia certificada varre uma grade de tolerancias e retem a melhor
    # sob o MESMO objetivo da comparacao. Isso favorece a referencia; o
    # varrimento e registrado em adaptive_sweep para que a leitura seja honesta.
    adaptive_candidates = []
    adaptive_sweep = []
    adaptive_epsilons = tuple(Fraction(1, 2**power) for power in range(1, 11))
    for epsilon in adaptive_epsilons:
        shape = certified_shape(selector.root, D, epsilon)
        candidate = selector.fixed_optimum(shape)
        adaptive_sweep.append(
            {
                "epsilon": fraction_text(epsilon),
                "requested_leaves": shape_leaves(shape),
                "feasible": candidate is not None,
                "objective": None if candidate is None else float(candidate.cost),
            }
        )
        if candidate is not None:
            adaptive_candidates.append((candidate, epsilon, shape))
    adaptive, chosen_epsilon, adaptive_shape = min(
        adaptive_candidates, key=lambda row: row[0].key
    )

    greedy = greedy_tree(selector, D)

    methods = {
        "Ótimo exato": exact,
        "Malha uniforme": uniform,
        "Adaptativo certificado": adaptive,
        "Heurística gulosa": greedy,
    }
    audit = {
        "H": H,
        "D": D,
        "observations": len(observations),
        "lambda_bits": fraction_text(selector.lambda_bits),
        "lambda_split": fraction_text(selector.lambda_split),
        "rational_values": len(selector.rationals),
        "nonzero_slopes": len(selector.nonzero),
        "atoms_per_admissible_cell": len(selector.rationals) * len(selector.nonzero),
        "tree_shapes_enumerated": len(tree_shapes(D)),
        "tree_shapes_feasible": len(shape_candidates),
        "finite_shape_dp_equals_variable_dp": True,
        "uniform_mesh_by_depth": [
            {
                "depth": depth,
                "feasible": selector.fixed_optimum(full_shape(depth)) is not None,
                "objective": (
                    None
                    if selector.fixed_optimum(full_shape(depth)) is None
                    else float(selector.fixed_optimum(full_shape(depth)).cost)
                ),
            }
            for depth in range(D + 1)
        ],
        "adaptive_epsilon": fraction_text(chosen_epsilon),
        "adaptive_shape_leaves": shape_leaves(adaptive_shape),
        "adaptive_sweep": adaptive_sweep,
        "root_states": len(selector.variable_states(selector.root, D)),
        "cached_cells": len(selector._leaf_cache),
        "exact_objective_no_worse_than_all_baselines": all(
            exact.cost <= candidate.cost for candidate in methods.values()
        ),
    }
    return methods, audit


def write_comparison_table(path: Path, methods: dict[str, Candidate]) -> None:
    lines = [
        r"\begin{tabular}{lrrrr}",
        r"\toprule",
        r"Método & folhas & erro quadrático & bits & objetivo \\",
        r"\midrule",
    ]
    for name, candidate in methods.items():
        lines.append(
            f"{name} & {candidate.leaves} & {decimal_text(candidate.loss, 6)} "
            f"& {candidate.bits} & {decimal_text(candidate.cost, 6)} \\\\"
        )
    lines.extend([r"\bottomrule", r"\end{tabular}"])
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def write_audit_table(
    path: Path,
    definitions: dict[str, object],
    direct: dict[str, object],
    audit: dict[str, object],
    ties: list[dict[str, object]],
    geometry: dict[str, object],
    geometry_formula: dict[str, object],
    budgets: dict[str, object],
) -> None:
    worst_tie = max(int(row["tied_on_cost"]) for row in ties)
    definitions_ok = bool(definitions["endpoint_dictionary_matches_definition"]) and bool(
        definitions["local_losses_match_direct_formula"]
    )
    lines = [
        r"\begin{tabularx}{\linewidth}{@{}Xr@{}}",
        r"\toprule",
        r"Verificação & resultado \\",
        r"\midrule",
        f"Dicionário/perdas derivados das definições & {str(definitions_ok).lower()} \\\\",
        f"Enumeração direta $(D,H)=(1,2)$ & {str(direct['dp_equals_direct_enumeration']).lower()} \\\\",
        f"Pares de subárvores examinados diretamente & {direct['split_pairs_tested']} \\\\",
        f"Formas de árvore enumeradas na instância principal & {audit['tree_shapes_enumerated']} \\\\",
        f"Formas de árvore com catálogo não vazio & {audit['tree_shapes_feasible']} \\\\",
        f"Células da árvore completa sem átomo admissível & {geometry['cells_empty']} \\\\",
        f"DP variável $=$ mínimo sobre formas fixas & {str(audit['finite_shape_dp_equals_variable_dp']).lower()} \\\\",
        f"Empates de custo máximos resolvidos pela chave & {worst_tie} \\\\",
        r"DP $=$ mínimo exaustivo sob empate & "
        + f"{str(all(bool(row['dp_equals_exhaustive_key']) for row in ties)).lower()} \\\\",
        f"Fórmula geométrica ({geometry_formula['parameter_cases_checked']} casos) & true \\\\",
        "Orçamento de folhas $=$ enumeração exaustiva & "
        + f"{str(budgets['leaf_budget_dp_equals_exhaustive']).lower()} \\\\",
        "Gargalo uniforme $=$ enumeração exaustiva & "
        + f"{str(budgets['bottleneck_dp_equals_exhaustive']).lower()} \\\\",
        f"Ótimo exato não pior que as três referências & {str(audit['exact_objective_no_worse_than_all_baselines']).lower()} \\\\",
        r"\bottomrule",
        r"\end{tabularx}",
    ]
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def draw_method_figure(path_pdf: Path, path_png: Path, methods: dict[str, Candidate]) -> None:
    candidates = list(methods.values())
    short_names = ["exato", "uniforme", "adaptativo", "guloso"]
    costs = np.array([float(candidate.cost) for candidate in candidates])
    losses = np.array([float(candidate.loss) for candidate in candidates])

    fig, axes = plt.subplots(1, 2, figsize=(9.2, 3.55))
    x = np.linspace(0.0, 1.0, 1201)
    axes[0].plot(x, 1.0 / (1.0 + 16.0 * (x - 0.25) ** 2), color="black", lw=1.8, label="alvo")
    styles = ["-", "--", "-.", ":"]
    colors = ["#0072B2", "#D55E00", "#009E73", "#CC79A7"]
    for candidate, label, style, color in zip(candidates, short_names, styles, colors):
        values = np.array([float(evaluate_tree(candidate.tree, Fraction(i, 1200))) for i in range(1201)])
        axes[0].plot(x, values, style, color=color, lw=1.25, label=f"{label} ({candidate.leaves} f.)")
    axes[0].set_xlabel("$x$")
    axes[0].set_ylabel("valor")
    axes[0].set_title("Montagens selecionadas")
    axes[0].grid(alpha=0.2)
    axes[0].legend(fontsize=7, ncol=2)

    width = 0.38
    positions = np.arange(len(short_names))
    axes[1].bar(positions - width / 2, losses, width, label="erro quadrático", color="#56B4E9")
    axes[1].bar(positions + width / 2, costs, width, label="objetivo completo", color="#E69F00")
    axes[1].set_xticks(positions, short_names, rotation=18)
    axes[1].set_ylabel("custo")
    axes[1].set_title("Mesmo funcional, quatro seletores")
    axes[1].grid(axis="y", alpha=0.2)
    axes[1].legend(fontsize=7)
    fig.tight_layout()
    fig.savefig(path_pdf)
    fig.savefig(path_png, dpi=180)
    plt.close(fig)


def draw_state_figure(path_pdf: Path, path_png: Path) -> None:
    fig, ax = plt.subplots(figsize=(8.6, 3.0))
    ax.axis("off")
    ax.set_xlim(0.0, 1.0)
    ax.set_ylim(0.0, 1.0)
    positions = {
        "root": (0.50, 0.82),
        "left": (0.25, 0.38),
        "right": (0.75, 0.38),
    }
    ax.plot([0.48, 0.29], [0.74, 0.48], color="#444444", lw=1.4)
    ax.plot([0.52, 0.71], [0.74, 0.48], color="#444444", lw=1.4)
    boxes = {
        "root": r"$C_d(J;u,v)$",
        "left": r"$C_{d-1}(J_L;u,w)$",
        "right": r"$C_{d-1}(J_R;w,v)$",
    }
    for key, (px, py) in positions.items():
        ax.text(
            px,
            py,
            boxes[key],
            ha="center",
            va="center",
            fontsize=12,
            bbox=dict(boxstyle="round,pad=0.45", fc="#EAF2F8", ec="#2C3E50"),
        )
    ax.text(0.50, 0.57, r"continuidade: o mesmo $w$", ha="center", fontsize=10, color="#7D3C98")
    ax.text(
        0.50,
        0.08,
        r"$\min\{\,C_{\rm folha}(J;u,v),\;\lambda_{\rm bits}+\lambda_{\rm split}+\min_w(C_L+C_R)\,\}$",
        ha="center",
        fontsize=11,
    )
    fig.tight_layout()
    fig.savefig(path_pdf)
    fig.savefig(path_png, dpi=180)
    plt.close(fig)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output-root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--H", type=int, default=4)
    parser.add_argument("--D", type=int, default=3)
    args = parser.parse_args()

    output_root = args.output_root.resolve()
    figures_pt = output_root / "reproducibility" / "selecao" / "figures" / "pt"
    figures_en = output_root / "reproducibility" / "selecao" / "figures" / "en"
    sections = output_root / "artigo" / "secoes"
    figures_pt.mkdir(parents=True, exist_ok=True)
    figures_en.mkdir(parents=True, exist_ok=True)
    sections.mkdir(parents=True, exist_ok=True)

    definitions = definition_level_audit()
    direct = direct_bruteforce_check()
    methods, audit = compare_methods(args.H, args.D)
    ties = tie_break_stress()
    geometry = catalog_geometry(args.H, args.D, Cell(*ROOT_CELL))
    geometry_formula = geometry_formula_audit()
    budgets = budget_and_bottleneck_audit()
    robustness = untruncated_robustness_audit(methods["Ótimo exato"])

    write_comparison_table(sections / "tab_comparacao_seletores.tex", methods)
    write_audit_table(
        sections / "tab_auditoria_selecao.tex",
        definitions,
        direct,
        audit,
        ties,
        geometry,
        geometry_formula,
        budgets,
    )
    draw_method_figure(
        figures_pt / "fig02_comparacao_seletores.pdf",
        figures_pt / "fig02_comparacao_seletores.png",
        methods,
    )
    draw_state_figure(
        figures_pt / "fig01_estado_fronteira.pdf",
        figures_pt / "fig01_estado_fronteira.png",
    )
    draw_method_figure(
        figures_en / "fig02_selector_comparison.pdf",
        figures_en / "fig02_selector_comparison.png",
        methods,
    )
    draw_state_figure(
        figures_en / "fig01_boundary_state.pdf",
        figures_en / "fig01_boundary_state.png",
    )

    results = {
        "metadata": {
            "python": platform.python_version(),
            "numpy": np.__version__,
            "matplotlib": matplotlib.__version__,
            "deterministic": True,
            "random_numbers_used": False,
            "optimization_arithmetic": "fractions.Fraction",
            "plots_only_use_floating_point": True,
        },
        "definition_level_audit": definitions,
        "direct_enumeration_audit": direct,
        "main_instance_audit": audit,
        "tie_break_stress": ties,
        "catalog_geometry": geometry,
        "geometry_formula_audit": geometry_formula,
        "untruncated_robustness_audit": robustness,
        "budget_and_bottleneck_audit": budgets,
        "methods": {
            name: candidate_record(name, candidate) for name, candidate in methods.items()
        },
    }
    result_path = output_root / "reproducibility" / "selecao" / "resultados.json"
    result_path.write_text(json.dumps(results, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")

    assert definitions["endpoint_dictionary_matches_definition"] is True
    assert definitions["local_losses_match_direct_formula"] is True
    assert direct["dp_equals_direct_enumeration"] is True
    assert audit["finite_shape_dp_equals_variable_dp"] is True
    assert audit["exact_objective_no_worse_than_all_baselines"] is True
    assert robustness["cells_empty"] == 0
    assert robustness["exact_matches_truncated_instance"] is True
    assert all(row["dp_equals_exhaustive_key"] is True for row in ties)
    assert any(int(row["tied_on_cost"]) > 1 for row in ties), (
        "o desempate canonico precisa ser exercitado por ao menos um empate real"
    )
    assert any(int(row["still_tied_on_length"]) > 1 for row in ties), (
        "a componente lexicografica da chave precisa ser exercitada"
    )
    assert geometry_formula["nonempty_cell_count_formula_verified"] is True
    assert geometry_formula["full_uniform_refinement_conditions_verified"] is True
    assert budgets["leaf_budget_dp_equals_exhaustive"] is True
    assert budgets["bottleneck_dp_equals_exhaustive"] is True
    exact = methods["Ótimo exato"]
    leaves = exact.tree.leaves()
    for left, right in zip(leaves, leaves[1:]):
        assert left.cell.right == right.cell.left
        assert left.right_value == right.left_value
        assert atom_height(left) <= args.H and atom_height(right) <= args.H

    print(json.dumps({"status": "ok", "resultados": str(result_path)}, ensure_ascii=False))


if __name__ == "__main__":
    main()
