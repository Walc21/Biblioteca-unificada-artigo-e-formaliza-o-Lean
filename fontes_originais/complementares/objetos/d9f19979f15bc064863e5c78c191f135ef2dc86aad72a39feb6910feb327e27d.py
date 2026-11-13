#!/usr/bin/env python3
"""Reproduz, em aritmética racional, os três comprimentos da tabela 2."""
from fractions import Fraction as F
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parents[1]


def gamma(n):
    if n < 1:
        raise ValueError("O código gama exige inteiro positivo.")
    b = bin(n)[2:]
    return "0" * (len(b) - 1) + b


def inteiro(z):
    return gamma((2*z if z >= 0 else -2*z-1) + 1)


def racional(q):
    q = F(q)
    return inteiro(q.numerator) + gamma(q.denominator)


def diadico(q):
    q = F(q)
    d = q.denominator
    if d & (d-1):
        raise ValueError("Fração não diádica.")
    return inteiro(q.numerator) + gamma(d.bit_length())


def montar(n):
    r = n.bit_length()-1
    if 2**r != n:
        raise ValueError("Número de folhas deve ser potência de dois.")
    t = [F(j, n) for j in range(n+1)]
    # 2 n² f(j/n) é par; a grade ímpar escolhe o menor no empate.
    b = [8*j*(j-n) - (j % 2) for j in range(n+1)]
    v = [F(z, 2*n*n) for z in b]
    y = [(v[j]+v[j+1])/2 for j in range(n)]
    s = [n*(v[j+1]-v[j]) for j in range(n)]
    atom = gamma(n) + "".join(
        gamma(r+1)+inteiro(j)+racional(y[j])+racional(s[j])
        for j in range(n))
    estrutural = gamma(n)+diadico(F(1, 2*n))+racional(y[0])+racional(s[0])
    expandido = gamma(n)+racional(v[0])+racional(s[0])
    for j in range(1, n):
        estrutural += diadico(t[j])+racional(s[j]-s[j-1])
        expandido += racional(t[j])+racional(s[j]-s[j-1])
    altura = max(
        [2, r+1, n] +
        [max(abs(q.numerator), q.denominator) for q in y+s])
    erro = F(0)
    for j in range(n):
        a, z = t[j], t[j+1]
        c = v[j]-s[j]*a
        crit = (4+s[j])/8
        candidatos = [a, z] + ([crit] if a <= crit <= z else [])
        for x in candidatos:
            erro = max(erro, abs(4*x*(x-1)-(s[j]*x+c)))
    return {
        "N": n, "erro_certificado": str(F(3, 2*n*n)),
        "erro_exato": str(erro), "altura": altura, "H_N": 18*n*n,
        "L_atom": len(atom), "L_str": len(estrutural), "L_rat": len(expandido)
    }


def main():
    ns = [2, 4, 8, 16, 32, 64]
    comprimentos = [(77,59,37), (195,115,89), (513,235,211),
                    (1243,495,497), (2921,1067,1159), (6731,2329,2669)]
    dados = [montar(n) for n in ns]
    for row, esperado in zip(dados, comprimentos):
        n = row["N"]
        assert row["erro_exato"] == str(F(49, 64*n*n))
        assert row["altura"] == 4*n*n
        assert tuple(row[k] for k in ("L_atom", "L_str", "L_rat")) == esperado
    out = ROOT/"dados"
    out.mkdir(exist_ok=True)
    (out/"tabela_2.json").write_text(
        json.dumps(dados, ensure_ascii=False, indent=2)+"\n", encoding="utf-8")
    print("Tabela 2: erros, alturas e três comprimentos reproduzidos exatamente.")


if __name__ == "__main__":
    main()
