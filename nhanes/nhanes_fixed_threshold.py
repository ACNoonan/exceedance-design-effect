"""Exploratory survey-design sensitivity at weighted empirical thresholds.
2013-2018 pooled MEC weights / 3. Adult 18-70 domain; observed analyte only.
Taylor variance for the weighted CDF at a fixed threshold, not a clinical interval.
Includes all positive-weight survey PSUs when computing domain variance.
"""
from pathlib import Path
import json
import argparse
import numpy as np
import pandas as pd
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--data-dir',type=Path,required=True,help='Directory containing DEMO and BIOPRO XPT files for H, I, J.')
parser.add_argument('--out',type=Path,required=True)
args=parser.parse_args()
B=args.data_dir
parts=[]
for c in ['H','I','J']:
 d=pd.read_sas(B/f'DEMO_{c}.XPT');x=pd.read_sas(B/f'BIOPRO_{c}.XPT')
 f=d[['SEQN','RIDAGEYR','WTMEC2YR','SDMVSTRA','SDMVPSU']].merge(x,on='SEQN',how='left')
 f['cycle']=c;parts.append(f)
f=pd.concat(parts,ignore_index=True);f=f[f.WTMEC2YR>0].copy();f['weight']=f.WTMEC2YR/3
f['stratum']=f.cycle+'_'+f.SDMVSTRA.astype(int).astype(str)
cols={'LBXSNASI':'sodium','LBXSKSI':'potassium','LBXSCA':'calcium','LBXSAL':'albumin','LBXSCR':'creatinine','LBXSGL':'glucose','LBXSATSI':'ALT','LBXSASSI':'AST','LBXSTB':'bilirubin','LBXSCH':'cholesterol'}
rows=[]
for col,name in cols.items():
 domain=f.RIDAGEYR.between(18,70)&f[col].notna()
 w=f.loc[domain,'weight'].to_numpy();x=f.loc[domain,col].to_numpy();order=np.argsort(x);W=w.sum()
 for p in [.9,.95,.975,.99]:
  q=x[order][np.searchsorted(np.cumsum(w[order]),p*W)]
  y=(x<=q).astype(float);ph=np.dot(w,y)/W
  score=np.zeros(len(f));score[domain.to_numpy()]=w*(y-ph)/W
  f['score']=score
  totals=f.groupby(['stratum','SDMVPSU']).score.sum()
  v=0.
  for _,g in totals.groupby(level=0):
   assert len(g)==2
   v+=len(g)/(len(g)-1)*np.sum((g-g.mean())**2)
  # For two PSUs per stratum, direct difference gives an independent arithmetic check.
  direct=sum((g.iloc[0]-g.iloc[1])**2 for _,g in totals.groupby(level=0))
  assert np.isclose(v,direct,rtol=1e-12)
  srs=ph*(1-ph)/len(x)
  rows.append(dict(analyte=name,p=p,threshold=float(q),weighted_cdf=float(ph),n=len(x),strata=totals.index.get_level_values(0).nunique(),variance=float(v),srs_variance=float(srs),design_ratio=float(v/srs),max_atom_weight=float(max(pd.Series(w).groupby(x).sum())/W)))
args.out.write_text(json.dumps(rows,indent=2)+'\n')
for a in rows: print(a['analyte'],a['p'],round(a['design_ratio'],3),round(a['weighted_cdf'],5))
