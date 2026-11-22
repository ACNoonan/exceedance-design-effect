"""Section 4.4 / Appendix B.11: Proposition 3 with random, informative cluster sizes.

    python analysis/theory/random_sizes_check.py > analysis/theory/random_sizes_check_RESULTS.txt

MODEL. A cluster has size 1, 3, 8 or 20 with probability .4, .3, .2, .1. Its rows are
shift + tau * A + E with A, E standard normal, where the shift and tau depend on the size.
Sizes are informative, the indicator correlation differs between size classes, and rows in
different size classes have different marginals. The target is the row-weighted CDF.

REPORTED, at p = 0.5 and 0.9 and b = 60 and 240 clusters, 6,000 repetitions each:
  b*mu*Var(C)    simulated coverage variance, scaled by the expected sample size
  prop3 v        Var(X - pM) / mu, from 400,000 clusters
  prop2 plug-in  p(1-p)[1 + (m_tilde - 1) rho] with a pooled pair correlation
  mean vhat      mean of Section 6.1's unequal-size estimator

WHAT COULD HAVE FAILED. If Proposition 3's variance were wrong under informative sizes, the
first two columns would disagree as they do for the Proposition 2 plug-in, which is off by a
factor of four at p = 0.5 and negative at p = 0.9.
"""
import numpy as np
from scipy.stats import norm
rng=np.random.default_rng(7)
SZ=np.array([1,3,8,20]); PR=np.array([.4,.3,.2,.1]); SHIFT=np.array([-0.6,0.0,0.5,1.0]); TAU=np.array([0.3,0.6,0.9,1.2])
mu=(SZ*PR).sum()
def Frow(t):  # row-weighted CDF: sum_m P(m) m Phi((t-shift)/sqrt(1+tau^2)) / mu
    t=np.asarray(t)[...,None]
    return (PR*SZ*norm.cdf((t-SHIFT)/np.sqrt(1+TAU**2))).sum(-1)/mu
def draw(b):
    idx=rng.choice(4,size=b,p=PR); out=[]
    for i in range(4):
        c=(idx==i).sum(); m=SZ[i]
        out.append(SHIFT[i]+TAU[i]*rng.standard_normal((c,1))+rng.standard_normal((c,m)))
    return idx,out
# population quantities by a big sample
from scipy.optimize import brentq
for p in (0.5,0.9):
    q=brentq(lambda t:Frow(t)-p,-10,10)
    idx,out=draw(400000)
    X=np.concatenate([(o<=q).sum(1) for o in out]); M=np.concatenate([np.full(len(o),o.shape[1]) for o in out])
    sig2=np.mean((X-p*M)**2); v=sig2/mu
    # Prop 2 style plug-in: pooled ANOVA-free pair correlation + size-biased mean
    pairs=(X*(X-1)).sum()/ (M*(M-1)).sum(); rho=(pairs-p*p)/(p*(1-p)); mt=(M**2).mean()/M.mean()
    v2=p*(1-p)*(1+(mt-1)*rho)
    for b in (60,240):
        C=[];vh=[]
        for _ in range(6000):
            idx,out=draw(b); s=np.concatenate([o.ravel() for o in out]); n=s.size; k=int(np.ceil((n+1)*p))
            qh=np.sort(s)[k-1]; C.append(Frow(qh))
            Xh=np.concatenate([(o<=qh).sum(1) for o in out]); Mh=np.concatenate([np.full(len(o),o.shape[1]) for o in out])
            vh.append(b/(b-1)*((Xh-Mh*Xh.sum()/n)**2).sum()/n)
        C=np.array(C)
        print(f"p={p} b={b}: b*mu*Var(C)={b*mu*C.var():.4f}  prop3 v={v:.4f}  prop2 plug-in={v2:.4f}  iid={p*(1-p):.4f}  mean vhat={np.mean(vh):.4f}  mean C-p={C.mean()-p:+.4f}")
