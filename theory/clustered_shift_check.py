"""Fixed-copula comparison of training-conditional calibration shifts.

python clustered_shift_check.py --sizes cluster_sizes.json --out shift-results.json
The input is a JSON list of positive integer cluster sizes. No model or data download occurs.
The result concerns a Gaussian model with these sizes, not the observed scores.
"""
from pathlib import Path
import argparse
import hashlib
import json
import numpy as np
from scipy.integrate import quad
from scipy.optimize import brentq
from scipy.special import ndtr, ndtri
from scipy.stats import beta, binom, norm

P, DELTA, REPS, SEED = .90, .10, 200000, 20260918

def gaussian_r(rho):
    zcut=ndtri(P)
    def indicator_corr(r):
        joint=quad(lambda z: ndtr((zcut-np.sqrt(r)*z)/np.sqrt(1-r))**2*norm.pdf(z),
                   -10,10,epsabs=1e-11,epsrel=1e-11)[0]
        return (joint-P*P)/(P*(1-P))
    return brentq(lambda r:indicator_corr(r)-rho,1e-8,1-1e-8,xtol=1e-11)

def interval(successes,total):
    return [0. if successes==0 else float(beta.ppf(.025,successes,total-successes+1)),
            1. if successes==total else float(beta.ppf(.975,successes+1,total-successes))]

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--sizes',type=Path,required=True)
    ap.add_argument('--out',type=Path,required=True)
    args=ap.parse_args()
    raw=json.loads(args.sizes.read_text());sizes=np.asarray(raw,dtype=int)
    assert len(sizes)>0 and np.all(sizes>0) and np.array_equal(sizes,np.asarray(raw))
    n=int(sizes.sum());mt=float(np.dot(sizes.astype(float),sizes)/n)
    rng=np.random.default_rng(SEED)
    # Independent check of the count event against actual sorted raw observations.
    for _ in range(1000):
        x=np.sqrt(.6)*rng.standard_normal((5,1))+np.sqrt(.4)*rng.standard_normal((5,4))
        flat=x.ravel();k=int(np.ceil((len(flat)+1)*.9))
        assert (ndtr(np.partition(flat,k-1)[k-1])>=P)==(np.sum(flat<ndtri(P))<k)
    si=float(np.sqrt(np.log(1/DELTA)/(2*n)))
    sh=float(np.sqrt(np.log(1/DELTA)*mt/(2*n)))
    k_iid=int(np.ceil((n+1)*(P+si)))
    iid=rng.binomial(n,P,REPS);iid_est=float(np.mean(iid<k_iid))
    iid_exact=float(binom.cdf(k_iid-1,n,P))
    iid_se=float(np.sqrt(iid_exact*(1-iid_exact)/REPS))
    checks={'rank_event':True,'iid_binomial_control':abs(iid_est-iid_exact)<4*iid_se}
    rows=[]
    for rho in [.4946,.20]:
        r=gaussian_r(rho);counts=np.empty(REPS,dtype=int)
        for lo in range(0,REPS,1000):
            stop=min(lo+1000,REPS)
            z=rng.standard_normal((stop-lo,len(sizes)))
            probs=ndtr((ndtri(P)-np.sqrt(r)*z)/np.sqrt(1-r))
            counts[lo:stop]=rng.binomial(sizes,probs).sum(axis=1)
        seff=float(si*np.sqrt(1+(mt-1)*rho))
        routes=[]
        for name,shift in [('iid',si),('cluster_hoeffding',sh),('neff_heuristic',seff)]:
            k=int(np.ceil((n+1)*(P+shift)))
            successes=int(np.sum(counts<k))
            ci=interval(successes,REPS)
            routes.append(dict(route=name,shift=shift,rank=k,success_probability=successes/REPS,ci95=ci))
            if name=='cluster_hoeffding':checks[f'bound_not_refuted_rho_{rho}']=ci[1]>=1-DELTA
        # DKW yields a simultaneous 95% band for the simulated count CDF.
        eta=float(np.sqrt(np.log(2/.05)/(2*REPS)))
        ranks=[int(np.quantile(counts,q,method='inverted_cdf'))+1
               for q in [1-DELTA-eta,1-DELTA,1-DELTA+eta]]
        row=dict(rho_indicator_at_target=rho,gaussian_score_correlation=r,routes=routes,
                 estimated_minimum_rank=ranks[1],minimum_rank_dkw95=[ranks[0],ranks[2]],
                 sufficient_level_shift=[rank/(n+1)-P for rank in ranks])
        rows.append(row);print(json.dumps(row),flush=True)
    result=dict(parameters=dict(target=P,delta=DELTA,repetitions=REPS,seed=SEED,n=n,
                b=len(sizes),m_tilde=mt,sizes_sha256=hashlib.sha256(args.sizes.read_bytes()).hexdigest()),
                iid_control=dict(estimated=iid_est,exact=iid_exact,mc_se=iid_se),rows=rows,checks=checks)
    args.out.write_text(json.dumps(result,indent=2)+'\n')
    print(checks)
    return 0 if all(checks.values()) else 1

if __name__=='__main__':
    raise SystemExit(main())
