#!/usr/bin/env python3
"""Experimento numérico (ponto flutuante) para a lei de fase da Parte III, III.12.7--III.12.8.

NÃO faz parte de reproduzir_tudo.py nem sustenta nenhuma prova: compara, para
algumas funções C^2, (i) sqrt(eps)*n_f(eps) com a função de fase Psi_f e
(ii) o intervalo de valores de N^2 E_N^dia com [min Psi^2, max Psi+^2].
Uso: python3 lei_fase_experimento.py [Nmax]
"""
import sys
import math, heapq
LN4=math.log(4)
def make_err(f,fp,K=24):
    def err(a,b):
        s=(f(b)-f(a))/(b-a)
        # candidate extrema of r(x)=f(x)-chord: roots of fp(x)=s; scan K subintervals
        xs=[a+(b-a)*i/K for i in range(K+1)]
        g=[fp(x)-s for x in xs]
        best=0.0
        for i in range(K):
            if g[i]==0: cand=[xs[i]]
            elif g[i]*g[i+1]<0:
                lo,hi=xs[i],xs[i+1]; sl=g[i]<0
                for _ in range(60):
                    m=(lo+hi)/2
                    if (fp(m)-s<0)==sl: lo=m
                    else: hi=m
                cand=[(lo+hi)/2]
            else: cand=[]
            for x in cand:
                best=max(best,abs(f(x)-(f(a)+s*(x-a))))
        return best
    return err
def breakpoints(err,Nmax,a=0.0,b=1.0,tol=1e-11):
    """returns list of (eps*, n_before(=n(eps*)), n_after(=n(eps*-))) following threshold trees"""
    h=[(-err(a,b),a,b)]; n=1; out=[]
    while n<Nmax:
        th=-h[0][0]
        if th<=0: break
        nb=n
        while h and -h[0][0]>=th*(1-tol):
            e,x,y=heapq.heappop(h); m=(x+y)/2
            heapq.heappush(h,(-err(x,m),x,m)); heapq.heappush(h,(-err(m,y),m,y)); n+=1
        out.append((th,nb,n))
    return out
def n_at(bp,eps):
    # n(eps)= n_before of the first breakpoint with th<=eps?  n(eps)=n_after of last bp with th>eps
    n=1
    for th,nb,na in bp:
        if th>eps: n=na
        else: break
    return n
def Psi(fpp,t,M=40000,plus=False):
    tot=0.0
    for i in range(M):
        x=(i+.5)/M; c=abs(fpp(x))
        if c==0: continue
        u=t+math.log(c/8,4)
        cu=(math.floor(u)+1) if plus else math.ceil(u)
        tot+=math.sqrt(c/8)*2**(cu-u)
    return tot/M
def Ivalue(fpp,M=200000):
    return sum(math.sqrt(abs(fpp((i+.5)/M))) for i in range(M))/M


def psi_range(fpp, M=6000, P=400):
    vals=[Psi(fpp,i/P,M) for i in range(P)]
    valsp=[Psi(fpp,i/P,M,plus=True) for i in range(P)]
    return min(vals), max(vals+valsp)

def run(name,f,fp,fpp,Nmax,Nmin):
    err=make_err(f,fp); bp=breakpoints(err,Nmax)
    lo,hi=psi_range(fpp)
    xs=[N*N*th for th,nb,na in bp for N in range(nb,na) if Nmin<=N<=Nmax]
    sn=[]; 
    for s in [8+i/8 for i in range(16)]:
        eps=4.0**(-s)
        if n_at(bp,eps)>0.9*Nmax: break
        sn.append(abs(math.sqrt(eps)*n_at(bp,eps)-Psi(fpp,s,8000)))
    print(f"{name:26s} I={Ivalue(fpp):.4f} max|sqrt(eps)n-Psi|={max(sn) if sn else float('nan'):.4f} "
          f"N^2E_N in [{min(xs):.5f},{max(xs):.5f}]  Psi^2 range [{lo*lo:.5f},{hi*hi:.5f}]")

if __name__=='__main__':
    Nmax=int(sys.argv[1]) if len(sys.argv)>1 else 8000; Nmin=Nmax//8
    pi=math.pi
    run('ln(1+x)',lambda x:math.log(1+x),lambda x:1/(1+x),lambda x:-1/(1+x)**2,Nmax,Nmin)
    run('e^x',math.exp,math.exp,math.exp,Nmax,Nmin)
    run('x^3+x^2',lambda x:x**3+x*x,lambda x:3*x*x+2*x,lambda x:6*x+2,Nmax,Nmin)
    run('x^2',lambda x:x*x,lambda x:2*x,lambda x:2.0,Nmax,Nmin)
    run('x^4',lambda x:x**4,lambda x:4*x**3,lambda x:12*x*x,Nmax,Nmin)
    run('sin(2 pi x)',lambda x:math.sin(2*pi*x),lambda x:2*pi*math.cos(2*pi*x),lambda x:-4*pi*pi*math.sin(2*pi*x),Nmax,Nmin)
    run('(x-1/3)^4/12',lambda x:(x-1/3)**4/12,lambda x:(x-1/3)**3/3,lambda x:(x-1/3)**2,Nmax,Nmin)
    run('(x-1/2)_+^3 (afim em [0,1/2])',lambda x:max(x-.5,0)**3,lambda x:3*max(x-.5,0)**2,lambda x:6*max(x-.5,0),Nmax,Nmin)
    f3=lambda x:x*x+(2*(x-.5)**3 if x>.5 else 0.0)
    run('patamar f\'\'=2 em [0,1/2]',f3,lambda x:2*x+(6*(x-.5)**2 if x>.5 else 0.0),lambda x:2+(12*(x-.5) if x>.5 else 0.0),Nmax,Nmin)
