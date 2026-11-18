#!/usr/bin/env python3
"""Lei de fase da Parte III (III.12.7--III.12.8): testes em alta precisão e com aritmética exata.

Requer mpmath >= 1.3 (pip install mpmath); a conversão Fraction -> mpf é feita por numerador e denominador. NÃO faz parte de reproduzir_tudo.py e não sustenta nenhuma prova.
  python3 lei_fase_exata.py precisao [Nmax]   e^x, ln(1+x), x^3+x^2 com 40 dígitos e Psi em forma fechada
  python3 lei_fase_exata.py atomo [Nmax]      C^2 com patamar f''=2 (átomo de mu_f), 40 dígitos
  python3 lei_fase_exata.py racional [Nmax]   quadráticas por partes com Fraction, sem tolerância
  python3 lei_fase_exata.py                   os três, com Nmax padrão
Notas: o erro local usa o ponto crítico em forma fechada (f' monótona em cada célula); os extremos
m_f, M_f de Psi são calculados por varredura + seção áurea, e em e^x conferidos nas fases de quebra.
"""
import heapq, sys, time
from fractions import Fraction
from mpmath import mp, mpf, exp, log, sqrt, floor, ceil
import heapq
from fractions import Fraction as F
mp.dps = 40
LN2 = log(2); LN4 = log(4)

# ---------- erro local exato por fórmula fechada (f' monótona em [0,1]) ----------
class Fn:
    def __init__(s, f, xstar):  # xstar(a,b,sl): ponto onde f'=inclinação
        s.f, s.xstar, s.cache = f, xstar, {}
    def val(s, num, k):          # f(num/2^k), nó diádico exato
        key = (num, k)
        v = s.cache.get(key)
        if v is None:
            v = s.f(mpf(num) / mpf(2) ** k); s.cache[key] = v
        return v
    def err(s, num, k, K=1):     # célula [num/2^k, (num+1)/2^k]
        a = mpf(num) / mpf(2) ** k; h = mpf(1) / mpf(2) ** k
        fa, fb = s.val(num, k), s.val(num + 1, k)
        sl = (fb - fa) / h
        x = s.xstar(a, a + h, sl)
        return abs(s.f(x) - (fa + sl * (x - a)))

EXP = Fn(exp, lambda a, b, s: log(s))
LOG1P = Fn(lambda x: log(1 + x), lambda a, b, s: 1 / s - 1)
CUB = Fn(lambda x: x**3 + x**2, lambda a, b, s: (-1 + sqrt(1 + 3 * s)) / 3)

def breakpoints(fn, Nmax, tol=mpf(10) ** -30):
    h = [(-fn.err(0, 0), 0, 0)]; n = 1; out = []
    while n < Nmax:
        th = -h[0][0]; nb = n
        while h and -h[0][0] >= th * (1 - tol):
            e, num, k = heapq.heappop(h)
            for c in (2 * num, 2 * num + 1):
                heapq.heappush(h, (-fn.err(c, k + 1), c, k + 1))
            n += 1
        out.append((th, nb, n))
    return out

def n_at_factory(bp):
    import bisect
    ths = [-b[0] for b in bp]          # crescente
    ths = [b[0] for b in bp][::-1]
    nas = [b[2] for b in bp][::-1]
    def n_at(eps):                     # n(eps)= n_after do último th>eps
        i = bisect.bisect_right(ths, eps)   # ths[:i] <= eps ; ths[i:] > eps
        # th decrescente em bp; invertido: crescente. maior índice com th>eps -> menor th>eps
        return 1 if i == len(ths) else nas[i]
    return n_at

# ---------- função de fase em forma fechada ----------
def Psi_exp(t):            # f=e^x em [0,1]: Psi = ln4 2^{-t} ∫_{u0}^{u1} 2^{ceil(u)} du
    u0 = t - mpf(3) / 2; u1 = u0 + 1 / LN4
    tot = mpf(0); n = int(floor(u0)) + 1
    lo = u0
    while lo < u1:
        hi = min(mpf(n), u1); tot += mpf(2) ** n * (hi - lo); lo = hi; n += 1
    return LN4 * mpf(2) ** (-t) * tot

def Psi_cub(t):            # f=x^3+x^2: c=6x+2, a in [-1,0]; Psi=(4 ln4/3) 2^{-t} ∑ 2^n ∫ 4^a da
    tot = mpf(0); n = int(floor(t - 1)) + 1; lo = mpf(-1)
    while lo < 0:
        hi = min(mpf(n) - t, mpf(0))
        if hi > lo: tot += mpf(2) ** n * (mpf(4) ** hi - mpf(4) ** lo) / LN4
        lo = max(lo, hi) if hi > lo else lo
        n += 1
        if hi <= lo and n > t + 5: break
    return 4 * LN4 / 3 * mpf(2) ** (-t) * tot

def Psi_log1p(t): return 1 / sqrt(8)

def _golden(f, a, b, sign, it=120):
    gr = (sqrt(5) - 1) / 2; c = b - gr * (b - a); d = a + gr * (b - a)
    for _ in range(it):
        if sign * f(c) < sign * f(d): b = d
        else: a = c
        c = b - gr * (b - a); d = a + gr * (b - a)
    return f((a + b) / 2)

def extremes(Psi, P=2000):
    h = mpf(1) / P
    v = [Psi(i * h) for i in range(P)]
    i0 = min(range(P), key=lambda i: v[i]); i1 = max(range(P), key=lambda i: v[i])
    m = _golden(Psi, (i0 - 1) * h, (i0 + 1) * h, +1)
    M = _golden(Psi, (i1 - 1) * h, (i1 + 1) * h, -1)
    return min(m, v[i0]), max(M, v[i1])

def report(name, fn, Psi, Nmax, I2):
    t0 = time.time(); bp = breakpoints(fn, Nmax); n_at = n_at_factory(bp)
    m, M = extremes(Psi)
    print(f"\n== {name}: N<= {bp[-1][2]} ({time.time()-t0:.0f}s)  I^2/8={float(I2/8):.6f} m^2={float(m*m):.8f} M^2={float(M*M):.8f} I^2/2={float(I2/2):.6f}")
    # janelas de N: [2^j,2^{j+1})
    lo = {}; hi = {}
    for th, nb, na in bp:
        # os N em [nb, na-1] têm E_N = th, logo x_N = N^2 th cresce com N: em cada janela
        # [2^j, 2^{j+1}) que o salto cruza, os extremos estão nos N das pontas recortadas.
        for j in range(nb.bit_length() - 1, (na - 1).bit_length()):
            N0 = max(nb, 2 ** j); N1 = min(na - 1, 2 ** (j + 1) - 1)
            if N0 > N1: continue
            for N in (N0, N1):
                x = N * N * th
                lo[j] = min(lo.get(j, x), x); hi[j] = max(hi.get(j, x), x)
    print("   janelas completas [2^j, 2^{j+1}) (as parciais, no fim, são omitidas)")
    print("   j   min x_N        max x_N       |min-m^2|     |max-M^2|")
    for j in sorted(lo):
        if j >= 8 and 2 ** (j + 1) <= bp[-1][2]:
            print(f"  {j:2d}  {float(lo[j]):.9f}  {float(hi[j]):.9f}  {float(abs(lo[j]-m*m)):.3e}  {float(abs(hi[j]-M*M)):.3e}")
    # sqrt(eps) n vs Psi em t = k+phase
    print("   max_t |sqrt(eps)n - Psi(t)| por janela t in [k,k+1):")
    nmax = bp[-1][1]
    for k in range(6, 40):
        w = 0
        for i in range(200):
            t = mpf(k) + mpf(i) / 200; eps = mpf(4) ** (-t)
            n = n_at(eps)
            if n > nmax: w = None; break
            w = max(w, abs(sqrt(eps) * n - Psi(t)))
        if w is None: break
        print(f"     k={k:2d}  {float(w):.3e}")
    return bp

# f = x^2 em [0,1/2];  x^2 + 2 (x-1/2)^3 em [1/2,1]:  f'' = 2 (patamar, átomo em a=-1) depois rampa 2->8 (C^2)
def f(x): return x*x + (2*(x-mpf(1)/2)**3 if x > mpf(1)/2 else 0)
def fp(x): return 2*x + (6*(x-mpf(1)/2)**2 if x > mpf(1)/2 else 0)
def xstar(a,b,s):
    if b <= mpf(1)/2: return s/2                       # f'=2x
    # f'(x)=2x+6(x-1/2)^2 = s  -> 6y^2+2y+1-s=0, y=x-1/2 (y>=0)
    return mpf(1)/2 + (-2 + sqrt(4 - 24*(1 - s)))/12
ATM = Fn(f, xstar)
def g(u,plus=False): return mpf(2)**((floor(u)+1 if plus else ceil(u))-u)
def Psi_atom(t, plus=False): return g(t,plus)/4 + Psi_cub(t)/2
def Psip(t): return Psi_atom(t, True)

def gaps(bp, lo, hi, Nlo, Nhi):
    xs=[]
    for th,nb,na in bp:
        for N in range(max(nb,Nlo), min(na,Nhi)):
            x=N*N*th
            if lo-1e-3<=x<=hi+1e-3: xs.append(x)
    xs.sort(); return max(b-a for a,b in zip(xs,xs[1:])), len(xs)

def run_racional(kappas, Nmax=2**19):
    q0=len(kappas).bit_length()-1; L=F(1,len(kappas))
    A=[F(abs(k))*L*L/8 for k in kappas]
    # heap de células-folha: (-erro, índice da base i, profundidade j); erro = A_i/4^j  (exato)
    h=[(-a,i,0) for i,a in enumerate(A)]; heapq.heapify(h)
    n=len(A); bpts=[]; 
    while n<Nmax:
        th=-h[0][0]; nb=n
        while h and -h[0][0]==th:                       # empate exato
            e,i,j=heapq.heappop(h)
            for _ in (0,1): heapq.heappush(h,(-A[i]/4**(j+1),i,j+1))
            n+=1
        bpts.append((th,nb,n))
    # contagem fechada (Thm III.12.2) em cada ponto de quebra, ε=th e ε=th^- 
    def closed(eps_num, strict_below=False):
        s=0
        for a in A:
            r=a/eps_num                                  # A/eps
            # ceil(log4 r): menor k com 4^k>=r (k=0 se r<=1)
            k=0
            while F(4)**k<r: k+=1
            if strict_below and F(4)**k==r: k+=1         # ε -> th^- : precisa 4^k>r
            s+=2**k
        return s
    # limiares testados: os 200 primeiros e os 50 últimos, sem repetição
    testados = {th: (nb, na) for th, nb, na in bpts[:200] + bpts[-50:]}
    for th, (nb, na) in testados.items():
        assert closed(th)==nb and closed(th,True)==na,(th,nb,na,closed(th),closed(th,True))
    # extremos exatos de x_N, para 2^10 <= N < (último N coberto pelas quebras)
    first = min(2**10, bpts[-1][2] - 1)
    xs_lo = min(max(nb, first)**2 * th for th, nb, na in bpts if na > first)
    xs_hi = max((na - 1)**2 * th for th, _, na in bpts if na > first)
    # Os extremos de fase ocorrem nos limiares A_i/4^j. Escolha um representante
    # de cada fase abaixo de min(A) para que o teto já esteja na faixa periódica.
    thresholds = set()
    for threshold in A:
        while threshold >= min(A):
            threshold /= 4
        thresholds.add(threshold)
    m2 = min(threshold * closed(threshold)**2 for threshold in thresholds)
    M2 = max(threshold * closed(threshold, True)**2 for threshold in thresholds)
    if Nmax >= 2**18:
        assert xs_lo == m2 and xs_hi <= M2
    I2_over_8 = sum(sqrt(mpf(x.numerator) / x.denominator) for x in A)**2
    print(f"κ={kappas}  q0={q0}  folhas até {bpts[-1][2]}; {len(bpts)} limiares distintos gerados;")
    print(f"   contagem fechada == floresta simulada abaixo da malha base (identidade quadrática): OK em {len(testados)} limiares distintos, cada um em ε=θ e ε→θ⁻")
    print(f"   x_N: min={float(xs_lo):.9f} max={float(xs_hi):.9f} | "
          f"m^2={float(m2):.9f} M^2={float(M2):.9f} | I^2/8={float(I2_over_8):.6f}")
    print(f"   |min x_N - m^2|={abs(xs_lo - m2)}   |max x_N - M^2|={abs(xs_hi - M2)}")

def run_atomo(NMAX):
    bp=breakpoints(ATM,NMAX)
    # extremos: m=min Psi ; M=max Psi+  (Psi esc. à esq., Psi+ à dir.)
    m,M=extremes(Psi_atom); M2=extremes(Psip)[1]; M=max(M,M2)
    print("m^2=",mp.nstr(m*m,12)," M^2=",mp.nstr(M*M,12))
    print("fase do átomo t=0: Psi(0)=",mp.nstr(Psi_atom(mpf(0)),10)," Psi+(0)=",mp.nstr(Psip(mpf(0)),10),"  salto^2:",mp.nstr(Psi_atom(mpf(0))**2,8),"->",mp.nstr(Psip(mpf(0))**2,8))
    n_at=n_at_factory(bp)
    print("\n sqrt(eps)n em t=k+fase (Psi, Psi+ entre colchetes):")
    for k in (14,16):
        for ph in (mpf(0),mpf('0.0005'),mpf('-0.0005')+1,mpf('0.3'),mpf('0.7')):
            t=mpf(k)+ph if ph>=0 else k+ph
            eps=mpf(4)**(-t); n=n_at(eps); s=sqrt(eps)*n
            print(f"  t=k+{float(ph):7.4f} k={k}: {mp.nstr(s,9)}   [{mp.nstr(Psi_atom(t),9)}, {mp.nstr(Psip(t),9)}]")
    print()
    top=(NMAX-1).bit_length()-1; j=[(top-3,top-2),(top-2,top-1),(top-1,top)]  # janelas completas de N
    for a,b in j:
        mx,c=gaps(bp,m*m,M*M,2**a,2**b)
        lo=min(N*N*th for th,nb,na in bp for N in range(max(nb,2**a),min(na,2**b)))
        hi=max(N*N*th for th,nb,na in bp for N in range(max(nb,2**a),min(na,2**b)))
        print(f"N in [2^{a},2^{b}): min x={float(lo):.9f} (m^2 {float(m*m):.9f})  max x={float(hi):.9f} (M^2 {float(M*M):.9f})  maior lacuna na lista ordenada de valores x_N={float(mx):.2e}  (nº valores {c})")


if __name__ == "__main__":
    which = sys.argv[1] if len(sys.argv) > 1 else "todos"
    N = int(sys.argv[2]) if len(sys.argv) > 2 else None
    if which in ("precisao", "todos"):
        n = N or 65536
        report("ln(1+x)", LOG1P, Psi_log1p, n, log(2) ** 2)
        I = 2 * (exp(mpf(1) / 2) - 1); report("e^x", EXP, Psi_exp, n, I * I)
        I = (mpf(8) ** 1.5 - mpf(2) ** 1.5) / 9; report("x^3+x^2", CUB, Psi_cub, n, I * I)
    if which in ("atomo", "todos"):
        run_atomo(N or 131072)
    if which in ("racional", "todos"):
        for k in ([2, 2, 8, 5], [1, 4, 16, 64], [1, 2, 3, 5, 7, 11, 13, 17]):
            run_racional(k, N or 2**18)
