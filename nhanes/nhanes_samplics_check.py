"""Independent comparison against the published samplics 0.4.33 Taylor estimator.
Keep all survey design records. Estimate the age/observed-value domain, not a subset design.
Operating thresholds are read from the prior calculation and treated as fixed.
"""
from pathlib import Path
import importlib.metadata as md
import json
import argparse
import numpy as np
import pandas as pd
from samplics.estimation import TaylorEstimator
from samplics.utils import PopParam
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--data-dir',type=Path,required=True)
parser.add_argument('--results',type=Path,required=True,help='Output of nhanes_fixed_threshold.py.')
parser.add_argument('--out',type=Path,required=True)
args=parser.parse_args()
B=args.data_dir
frames=[]
for cycle in ['H','I','J']:
 d=pd.read_sas(B/f'DEMO_{cycle}.XPT')
 b=pd.read_sas(B/f'BIOPRO_{cycle}.XPT')
 f=d.merge(b,on='SEQN',how='left',suffixes=('','_bio'))
 f['stratum']=cycle+'_'+f.SDMVSTRA.astype(int).astype(str)
 frames.append(f)
f=pd.concat(frames,ignore_index=True).query('WTMEC2YR > 0')
cols=dict(sodium='LBXSNASI',potassium='LBXSKSI',calcium='LBXSCA',albumin='LBXSAL',creatinine='LBXSCR',glucose='LBXSGL',ALT='LBXSATSI',AST='LBXSASSI',bilirubin='LBXSTB',cholesterol='LBXSCH')
rows=[]
for old in json.loads(args.results.read_text()):
 x=f[cols[old['analyte']]]
 domain=(f.RIDAGEYR.between(18,70)&x.notna()).astype(int)
 est=TaylorEstimator(PopParam.mean)
 est.estimate(y=(x<=old['threshold']).astype(float),samp_weight=f.WTMEC2YR/3,
              stratum=f.stratum,psu=f.SDMVPSU,domain=domain)
 mean=float(est.point_est[1]);var=float(est.variance[1])
 row=dict(analyte=old['analyte'],p=old['p'],mean=mean,variance=var,
          relative_variance_difference=abs(var/old['variance']-1),
          absolute_mean_difference=abs(mean-old['weighted_cdf']))
 assert np.isclose(mean,old['weighted_cdf'],atol=1e-12,rtol=0),row
 assert np.isclose(var,old['variance'],atol=1e-14,rtol=1e-10),row
 rows.append(row)
result=dict(packages={p:md.version(p) for p in ['samplics','numpy','pandas','scipy']},
            cells=len(rows),max_relative_variance_difference=max(r['relative_variance_difference'] for r in rows),
            max_absolute_mean_difference=max(r['absolute_mean_difference'] for r in rows),rows=rows)
args.out.write_text(json.dumps(result,indent=2)+'\n')
print('PASS',result['cells'],'cells; max relative variance difference',result['max_relative_variance_difference'])
