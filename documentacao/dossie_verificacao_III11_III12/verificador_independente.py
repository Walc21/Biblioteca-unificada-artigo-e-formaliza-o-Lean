# Verificacao independente (apenas mpmath), sem usar codigo do repositorio.
# Calcula n_f(eps) pela recursao do limiar (celula e folha se erro <= eps)
# e compara sqrt(eps)*n_f(eps) com Psi_f(t), t = -log4(eps), para f = e^x em [0,1].
from mpmath import mp, mpf, exp, log, floor
mp.dps = 40


def err(a, b):
    """Erro local exato de e^x em [a,b] (f' monotona: um unico ponto critico)."""
    s = (exp(b) - exp(a)) / (b - a)      # inclinacao da corda
    x = log(s)                           # e^x = s
    return abs(exp(x) - (exp(a) + s * (x - a)))


def n_leaves(eps, a=mpf(0), b=mpf(1)):
    """Numero de folhas da arvore de limiar T_eps."""
    if err(a, b) <= eps:
        return 1
    m = (a + b) / 2
    return n_leaves(eps, a, m) + n_leaves(eps, m, b)


def Psi(t):
    """Psi_f(t) = ln4 * 2^{-t} * integral de u0 a u1 de 2^{ceil(u)} du,
    com u0 = t - 3/2 e u1 = u0 + 1/ln4 (forma fechada de III.12.9)."""
    u0 = t - mpf(3) / 2
    u1 = u0 + 1 / log(4)
    tot, lo, n = mpf(0), u0, int(floor(u0)) + 1
    while lo < u1:
        hi = min(mpf(n), u1)
        tot += mpf(2) ** n * (hi - lo)
        lo, n = hi, n + 1
    return log(4) * mpf(2) ** (-t) * tot


for t in [mpf(k) / 8 for k in range(80, 96)]:    # t em [10, 12)
    eps = mpf(4) ** (-t)
    n = n_leaves(eps)
    s = float(mpf(n) * mpf(2) ** (-t))
    print(f"t={float(t):6.3f}  n_f={n:6d}  sqrt(eps)*n_f={s:.6f}  "
          f"Psi={float(Psi(t)):.6f}")
print("m^2 = e/8 =", mp.nstr(exp(1) / 8, 15),
      "  Psi(1/2)^2 =", mp.nstr(Psi(mpf(1) / 2) ** 2, 15))
