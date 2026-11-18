#!/usr/bin/env python3
"""Reproduz a contagem exata e a razão numérica da proposição III.3.2."""

import argparse
import math


def q_H(height: int) -> int:
    """Conta racionais reduzidos de altura até H usando a soma de totientes."""
    if height < 1:
        return 0
    phi = list(range(height + 1))
    for prime in range(2, height + 1):
        if phi[prime] == prime:
            for multiple in range(prime, height + 1, prime):
                phi[multiple] -= phi[multiple] // prime
    # A diagonal contém apenas (1, 1); cada par positivo dá dois sinais, mais zero.
    return 4 * sum(phi[1:]) - 1


def library_H(height: int) -> int:
    if height < 2:
        return 0
    rationals = q_H(height)
    return height * (2 * height - 1) * rationals * (rationals - 1)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument("heights", nargs="*", type=int, help="alturas inteiras positivas")
    modes.add_argument("--published", action="store_true", help="alturas impressas em III.3.2")
    args = parser.parse_args()
    if any(height < 1 for height in args.heights):
        parser.error("as alturas devem ser inteiras positivas")
    heights = (50, 800, 12800) if args.published else (args.heights or [2**i for i in range(1, 10)])

    constant = 288 / math.pi**4
    print(f"288/pi^4 = {constant:.10f}")
    for height in heights:
        count = library_H(height)
        quotient = count / height**6
        print(f"H={height:5d}  |L_H|={count}  |L_H|/H^6={quotient:.6f}  razao={quotient / constant:.6f}")


if __name__ == "__main__":
    main()
