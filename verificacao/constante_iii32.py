"""Verificacao numerica da constante de III.3.2: |Library_H| ~ (288/pi^4) H^6.

|Library_H| = H (2H-1) q_H (q_H - 1), onde q_H = #{r in Q : ht(r) <= H} (forma reduzida,
ht = max(|p|, q), 0 incluido). A contagem de q_H e a do Lean (RequestProject/Indexing.lean,
QH), conferida para H = 2..5: 252, 3150, 14168, 66690 atomos.
"""
import math

def q_H(H):
    return sum(1 for q in range(1, H + 1) for p in range(-H, H + 1) if math.gcd(abs(p), q) == 1)

def library_H(H):
    q = q_H(H)
    return H * (2 * H - 1) * q * (q - 1)

if __name__ == "__main__":
    K = 288 / math.pi ** 4
    print(f"288/pi^4 = {K:.10f}")
    for H in [2, 4, 8, 16, 32, 64, 128, 256, 512]:
        L = library_H(H)
        print(f"H={H:4d}  |L_H|={L}  |L_H|/H^6={L / H**6:.6f}  razao={(L / H**6) / K:.6f}")
