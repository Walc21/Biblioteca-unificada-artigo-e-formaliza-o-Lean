#!/usr/bin/env python3
"""Figuras vetoriais do artigo; certificação do exemplo em frações exatas."""
from fractions import Fraction as F
from pathlib import Path
import json
import numpy as np
from decimal import Decimal, localcontext
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import FancyBboxPatch, FancyArrowPatch

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT/"figuras"
OUT.mkdir(exist_ok=True)
DATA = ROOT/"dados"
DATA.mkdir(exist_ok=True)
INK, TEAL, AMBER = "#172c3c", "#166f80", "#c37732"
COLORS = [TEAL, AMBER, "#65518b", "#557f47"]
plt.rcParams.update({
    "font.family": "DejaVu Serif", "font.size": 10,
    "mathtext.fontset": "stix", "axes.spines.top": False,
    "axes.spines.right": False, "axes.labelcolor": INK,
    "text.color": INK, "xtick.color": INK, "ytick.color": INK,
    "axes.edgecolor": "#7e8b94", "axes.linewidth": .6,
    "pdf.fonttype": 42, "savefig.facecolor": "white",
})


def save(fig, name):
    temp=OUT/(name+".tmp.pdf")
    fig.savefig(temp, bbox_inches="tight", pad_inches=.07,
                metadata={"Creator":"scripts/figuras.py","Author":"Victor Gabriel de Oliveira"})
    plt.close(fig)
    if not temp.read_bytes().rstrip().endswith(b"%%EOF"):
        raise RuntimeError(f"Figura PDF incompleta: {name}")
    temp.replace(OUT/(name+".pdf"))


def cw():
    fig, ax = plt.subplots(figsize=(6.35, 2.65))
    levels = [[(1,1)]]
    for _ in range(3):
        levels.append([z for p,q in levels[-1] for z in ((p,p+q),(p+q,q))])
    for depth, level in enumerate(levels):
        xs = (np.arange(len(level))+.5)/len(level)
        for j, ((p,q), x) in enumerate(zip(level,xs)):
            color = TEAL if j == 0 else INK
            if depth:
                parent_x = (j//2+.5)/(len(level)//2)
                ax.plot([parent_x,x],[-depth+1-.19,-depth+.2],
                        color=TEAL if j == 0 else "#b5c0c8",lw=.9)
            ax.text(x,-depth,rf"$\frac{{{p}}}{{{q}}}$",ha="center",va="center",
                    fontsize=16,color=color)
    ax.text(.56,-3.65,r"$CW(2^{q-1})=1/q$",ha="center",fontsize=12,color=TEAL)
    ax.set(xlim=(-.02,1.02),ylim=(-3.9,.4))
    ax.axis("off")
    save(fig,"01_calkin_wilf")


def celulas():
    fig, ax = plt.subplots(figsize=(6.3, 2.0))
    for k in range(5):
        for m in range(2**k):
            a,b=m/2**k,(m+1)/2**k
            ax.plot([a,b],[-k,-k],color=INK,lw=1)
            ax.plot([a,a],[-k-.12,-k+.12],color=INK,lw=.65)
            ax.plot([b,b],[-k-.12,-k+.12],color=INK,lw=.65)
            ax.plot((a+b)/2,-k,"o",ms=3,color=AMBER)
        ax.text(-.065,-k,rf"$k={k}$",ha="right",va="center")
    ax.set(yticks=[],xticks=[0,.25,.5,.75,1],
           xticklabels=["0",r"$1/4$",r"$1/2$",r"$3/4$","1"],
           xlim=(-.11,1.02),ylim=(-4.6,.55))
    ax.spines[["left","bottom"]].set_visible(False)
    ax.tick_params(axis="x",length=0)
    save(fig,"02_celulas")


def alvo(x):
    return 8*x**3-12*x**2+3*x+.25


def montagem():
    fig, axs = plt.subplots(1,2,figsize=(6.5,2.75),sharey=True)
    xx=np.linspace(0,1,800)
    for ax,k in zip(axs,[2,4]):
        n=2**k
        ax.plot(xx,alvo(xx),color=INK,lw=1.2,label=r"função-alvo $f$")
        t=np.linspace(0,1,n+1)
        vals=alvo(t)
        assert np.all(np.diff(vals)!=0)
        for j in range(n):
            color=COLORS[j%4]
            ax.axvspan(t[j],t[j+1],color=color,alpha=.055)
            ax.plot(t[j:j+2],vals[j:j+2],color=color,lw=2)
            if n==4:
                ax.text((t[j]+t[j+1])/2,-1.15,rf"$J_{{2,{j}}}$",
                        color=color,ha="center",fontsize=9)
        ax.scatter(t,vals,s=16 if n==4 else 9,c="white",edgecolors=TEAL,zorder=4,lw=.8)
        ax.set(xlim=(-.02,1.02),ylim=(-1.3,.7),xlabel="$x$",
               xticks=[0,.25,.5,.75,1])
        ax.set_title(f"$k={k}$: {n} peças",fontsize=11,pad=9)
        ax.grid(axis="y",color="#dce2e6",lw=.5)
    axs[0].set_ylabel("$y$")
    axs[0].annotate("nó compartilhado",xy=(.5,alvo(.5)),xytext=(.37,.47),
                    fontsize=9,ha="left",arrowprops={"arrowstyle":"->","color":INK,"lw":.7})
    axs[1].legend(loc="upper right",frameon=False,fontsize=9)
    fig.tight_layout(w_pad=1)
    save(fig,"03_montagem_continua")


def box(ax, xy, text, width=.38, height=.17):
    x,y=xy
    rect=FancyBboxPatch((x-width/2,y-height/2),width,height,
                       boxstyle="round,pad=.018,rounding_size=.014",
                       ec="#82949e",fc="#f2f6f7",lw=.7)
    ax.add_patch(rect)
    ax.text(x,y,text,ha="center",va="center",fontsize=10)


def arrow(ax,a,b):
    ax.add_patch(FancyArrowPatch(a,b,arrowstyle="-|>",mutation_scale=8,
                                lw=.7,color="#82949e"))


def relu():
    fig,(ax,net)=plt.subplots(1,2,figsize=(6.5,2.5),gridspec_kw={"width_ratios":[1,1.15]})
    t=[F(j,4) for j in range(5)]
    s=[F(1,2),F(-1),F(1),F(-1,6)]
    v=[F(-1,8)]
    for j in range(4):
        v.append(v[-1]+s[j]*(t[j+1]-t[j]))
        ax.plot([float(t[j]),float(t[j+1])],[float(v[j]),float(v[j+1])],
                color=COLORS[j],lw=2)
    ax.scatter([float(z) for z in t],[float(z) for z in v],s=14,c="white",
               edgecolors=TEAL,zorder=3,lw=.8)
    ax.set(xlabel="$x$",ylabel="$g(x)$",xticks=[0,.25,.5,.75,1])
    ax.grid(axis="y",color="#dce2e6",lw=.5)
    net.axis("off")
    net.set(xlim=(-.02,1.02),ylim=(-.04,1.04))
    for y,expr,weight in [(0.86,r"$\rho(x-1/4)$",r"$-3/2$"),
                          (0.61,r"$\rho(x-1/2)$",r"$2$"),
                          (0.36,r"$\rho(x-3/4)$",r"$-7/6$")]:
        arrow(net,(.065,.51),(.26,y))
        box(net,(.47,y),expr)
        arrow(net,(.685,y),(.94,.51))
        net.text(.78,y+.075,weight,ha="center",fontsize=10)
    box(net,(.47,.10),r"$-1/8+x/2$",width=.40,height=.13)
    arrow(net,(.065,.51),(.25,.10))
    arrow(net,(.69,.10),(.94,.49))
    net.text(.03,.51,"$x$",ha="center",va="center")
    net.text(.97,.51,"$g(x)$",ha="left",va="center")
    fig.subplots_adjust(wspace=.25,left=.10,right=.96,bottom=.22,top=.96)
    save(fig,"04_relu")


def exponencial():
    ks=list(range(1,11))
    erros=[]; cotas=[]
    with localcontext() as ctx:
        ctx.prec=80
        for k in ks:
            h=Decimal(2)**(-k)
            a=1-h
            e=Decimal(1).exp()
            slope=(e-a.exp())/h
            z=slope.ln()
            err=a.exp()+(z-a)*slope-z.exp()
            erros.append(float(err))
            cotas.append(float(h*h*e/8))
    fig,(ax,bx)=plt.subplots(1,2,figsize=(6.35,2.2))
    ax.semilogy(ks,erros,"o-",color=TEAL,ms=3,lw=1.1,label="erro exato")
    ax.semilogy(ks,cotas,"--",color=AMBER,lw=1.1,label=r"$2^{-2k}e/8$")
    ax.set(xlabel="escala $k$",ylabel=r"$\|e^x-P_ke^x\|_\infty$",xticks=[2,4,6,8,10])
    ax.legend(frameon=False,fontsize=9)
    bx.plot(ks,np.array(erros)/cotas,"o-",color=TEAL,ms=3,lw=1.1)
    bx.axhline(1,color=AMBER,lw=.8,ls="--")
    bx.set(xlabel="escala $k$",ylabel="erro / cota",xticks=[2,4,6,8,10],ylim=(.72,1.025))
    for z in [ax,bx]:
        z.grid(color="#dce2e6",lw=.5)
    fig.tight_layout(w_pad=1.5)
    save(fig,"05_taxa_exponencial")


def f_racional(x):
    return 1/(1+64*(x-F(5,8))**2)


def majorante(a,b):
    # f''(x) = (24576 z² - 128) / (1 + 64 z²)³, z = x - 5/8.
    za,zb=a-F(5,8),b-F(5,8)
    lo=F(0) if za<=0<=zb else min(za*za,zb*zb)
    hi=max(za*za,zb*zb)
    nlo,nhi=24576*lo-128,24576*hi-128
    return max(abs(nlo),abs(nhi))/(1+64*lo)**3


def arredondar_grade(y,j,delta):
    shift=F(j%2,2)
    z=y/delta-shift
    low=z.numerator//z.denominator
    candidates=[delta*(low+shift),delta*(low+1+shift)]
    return min(candidates,key=lambda q:(abs(q-y),q))


def refinamento():
    epsI,epsR=F(1,100),F(1,5000)
    initial=[(F(j,4),F(j+1,4)) for j in range(4)]
    folhas=[]
    def visit(a,b):
        M=majorante(a,b)
        eta=(b-a)**2*M/8
        if eta>epsI:
            c=(a+b)/2
            visit(a,c); visit(c,b)
        else:
            folhas.append((a,b,M,eta))
    for a,b in initial:
        visit(a,b)
    t=[row[0] for row in folhas]+[folhas[-1][1]]
    v=[arredondar_grade(f_racional(x),j,epsR) for j,x in enumerate(t)]
    assert all(abs(y-f_racional(x))<epsR for x,y in zip(t,v))
    assert all(v[j+1]!=v[j] for j in range(len(v)-1))
    assert all(row[3]<=epsI for row in folhas)
    dados={
        "funcao":"1/(1+64*(x-5/8)^2)", "epsilon_I":str(epsI),
        "epsilon_R":str(epsR),"erro_total_certificado":str(epsI+epsR),
        "N":len(folhas),"folhas":[
            {"a":str(a),"b":str(b),"M":str(M),"eta":str(eta),
             "valor_esquerdo":str(v[j]),"valor_direito":str(v[j+1])}
            for j,(a,b,M,eta) in enumerate(folhas)]
    }
    (DATA/"refinamento.json").write_text(
        json.dumps(dados,ensure_ascii=False,indent=2)+"\n",encoding="utf-8")
    fig,(ax,mx,bx)=plt.subplots(3,1,figsize=(6.5,4.6),sharex=True,
                              gridspec_kw={"height_ratios":[2.5,1,1.7]})
    xx=np.linspace(0,1,2000)
    tf=np.array([float(z) for z in t])
    vf=np.array([float(z) for z in v])
    gg=np.interp(xx,tf,vf)
    ff=1/(1+64*(xx-5/8)**2)
    ax.fill_between(xx,gg-float(epsI+epsR),gg+float(epsI+epsR),
                    color=TEAL,alpha=.15,label=r"faixa $\varepsilon_I+\varepsilon_R$")
    ax.plot(xx,ff,color=INK,lw=1.2,label=r"função-alvo $f$")
    ax.plot(tf,vf,color=TEAL,lw=.9,label="montagem $g$")
    ax.scatter(tf,vf,s=6,c=TEAL,zorder=3)
    ax.set(ylabel="$y$",ylim=(-.04,1.1),xlim=(0,1))
    ax.legend(frameon=False,fontsize=8.2,loc="upper left")
    mx.set(ylim=(-.5,1.6),yticks=[1,0],yticklabels=["inicial","final"])
    mx.spines[["left","bottom"]].set_visible(False)
    mx.tick_params(length=0)
    for a,b in initial:
        color=AMBER if (b-a)**2*majorante(a,b)/8>epsI else TEAL
        mx.barh(1,float(b-a),left=float(a),height=.43,color=color,
                edgecolor="white",lw=.7)
    for a,b,M,eta in folhas:
        mx.barh(0,float(b-a),left=float(a),height=.43,color=TEAL,
                edgecolor="white",lw=.6)
        bx.bar(float((a+b)/2),float(eta),width=float(b-a)*.92,
               color=TEAL,alpha=.8,align="center")
    bx.axhline(float(epsI),color=AMBER,lw=1,ls="--")
    bx.text(.01,float(epsI)*1.11,r"$\varepsilon_I=10^{-2}$",color=AMBER,fontsize=9)
    bx.set(yscale="log",ylim=(2e-4,.02),xlabel="$x$",
           ylabel=r"$\eta_{\rm cert}(J)$",xticks=[0,.25,.5,.625,.75,1],
           xticklabels=["0","1/4","1/2","5/8","3/4","1"])
    bx.grid(axis="y",color="#dce2e6",lw=.4)
    ax.text(.99,1.02,f"{len(folhas)} folhas",transform=ax.transAxes,
            ha="right",va="bottom",fontsize=9,color=TEAL)
    fig.align_ylabels([ax,bx])
    fig.subplots_adjust(hspace=.24,left=.12,right=.99,bottom=.10,top=.95)
    save(fig,"06_refinamento_certificado")


def main():
    cw(); celulas(); montagem(); relu(); exponencial(); refinamento()
    print("Seis figuras vetoriais geradas; exemplo adaptativo certificado em frações exatas.")


if __name__=="__main__":
    main()
