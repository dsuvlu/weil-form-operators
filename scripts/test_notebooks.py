#!/usr/bin/env python3
"""Run editable notebooks and compare their defaults with the original CLI scripts."""
import argparse,contextlib,importlib.util,io,json,math,os,runpy,shutil,sys,tempfile,time
from pathlib import Path
import numpy as np
from matplotlib.figure import Figure

KEYS={
1:['t','f','S2','S6_direct','S2_then_3','error'],
2:['Z_direct','Z_product','Z_inverse','identity','current_from_log_derivative'],
3:['R','residual'],4:['K','absolute_integral','theoretical_bound','r','K_r'],
5:['input_norms','raw_norms','completed_norms','limit_errors'],
6:['critical_retained','critical_escaped','critical_product','retained_derivative','weil_direct'],
7:['H_float','H_formula','H_direct','difference'],
8:['coefficients','eigenvalues_for_plot','endpoint_after','xi'],
9:['theta_real','log_modulus','roots','errors'],
10:['projection_matrix','singular_values','ground','chi'],
11:['rows','curves'],12:['anchor_value','energy','gap','endpoint','anchor_text']}

def equal(a,b,label):
    if isinstance(a,dict):
        assert a.keys()==b.keys(),label
        for k in a:equal(a[k],b[k],f'{label}.{k}')
    elif isinstance(a,(list,tuple)):
        assert len(a)==len(b),label
        for i,(x,y) in enumerate(zip(a,b)):equal(x,y,f'{label}[{i}]')
    elif isinstance(a,str):assert a==b,(label,a,b)
    else:np.testing.assert_allclose(a,b,rtol=1e-11,atol=1e-12,err_msg=label)

def load(path):
    name='notebook_test_'+path.stem
    spec=importlib.util.spec_from_file_location(name,path)
    module=importlib.util.module_from_spec(spec);sys.modules[name]=module
    spec.loader.exec_module(module)
    return module.app

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root',type=Path,default=Path(__file__).resolve().parents[1]/'experiments')
    parser.add_argument('--quick',action='store_true')
    parser.add_argument('--report',type=Path)
    args=parser.parse_args();root=args.root.resolve()
    meta=json.loads((root/'notebooks/NOTEBOOK_MAP.json').read_text())['notebooks']
    selected=[m for i,m in enumerate(meta,1) if not args.quick or i in [1,3,4,8]]
    report=[]
    with tempfile.TemporaryDirectory(prefix='weil-notebook-reference-') as directory:
        reference=Path(directory)
        for p in root.glob('*.py'):shutil.copy2(p,reference/p.name)
        old_path=sys.path[:];old_argv=sys.argv[:];sys.path.insert(0,str(reference))
        try:
            for item in selected:
                started=time.monotonic();n=int(item['file'].split('_')[1]);app=load(root/'notebooks'/item['file'])
                captured=io.StringIO()
                try:
                    with contextlib.redirect_stdout(captured):
                        outputs,actual=app.run()
                        sys.argv=[str(reference/item['script'])]
                        expected=runpy.run_path(str(reference/item['script']),run_name='__main__')
                    for key in KEYS[n]:equal(actual[key],expected[key],f'{n:02}.{key}')
                    figures=[o for o in outputs if isinstance(o,Figure)]
                    expected_plots=(reference/item['script']).read_text().count('plt.figure(')
                    assert len(figures)==expected_plots,(n,len(figures),expected_plots)
                    if n==11:
                        assert len(figures[0].axes[0].get_legend().get_texts())==len(actual['curves'])
                except Exception:
                    print(captured.getvalue());raise
                row={'notebook':item['file'],'default_comparison':'PASS','compared_outputs':KEYS[n],'seconds':round(time.monotonic()-started,2)}
                report.append(row);print(f'{n:02}: default outputs match reference ({row["seconds"]}s)',flush=True)
            # A changed finite-window resolvent parameter must change the output.
            app3=load(root/'notebooks'/meta[2]['file'])
            with contextlib.redirect_stdout(io.StringIO()):
                _,negative=app3.run(defs={'settings':{'L':2.0,'b':-0.5,'points':800}})
            assert negative['R'].shape==(800,)
            assert negative['R'][-1]==0
            assert np.max(np.abs(negative['residual'][5:-5]))<1e-3
            print('03: changed L, negative b, changed grid: PASS',flush=True)
            # Exercise an arbitrary-precision branch independently of the default.
            app8=load(root/'notebooks'/meta[7]['file'])
            with contextlib.redirect_stdout(io.StringIO()):
                _,high=app8.run(defs={'settings':{'x':2.0,'N':3,'precision':'mp50'}})
            assert len(high['coefficients'])==7
            assert abs(high['endpoint_after']-1)<1e-12
            assert high['data']['eigenpair_residual']<1e-40
            print('08: mp50 branch and changed N: PASS',flush=True)
            for index, overrides in [
                (4, {'settings':dict(meta[3]['defaults'], y_max=3.0, precision='mp50')}),
                (7, {'settings':dict(meta[6]['defaults'], x=2.0, N=2, y_steps=1000, precision='mp50')}),
                (9, {'settings':dict(meta[8]['defaults'], N=3, precision='mp50')}),
                (11, {'settings':{'precision':'mp50'}, 'pairs':[(1.5,3),(2.0,3)]})]:
                with contextlib.redirect_stdout(io.StringIO()):
                    _, high_other=load(root/'notebooks'/meta[index-1]['file']).run(defs=overrides)
                if index==4: assert 0<float(high_other['absolute_integral'])<8*math.pi/3
                if index==7: assert high_other['H_formula'].shape==(5,5)
                if index==9: assert max(high_other['errors'])<1e-40
                if index==11: assert len(high_other['rows'])==2
                print(f'{index:02}: changed-parameter mp50 branch: PASS',flush=True)
        finally:sys.path[:]=old_path;sys.argv[:]=old_argv
    if args.report:
        args.report.write_text(json.dumps({'status':'PASS','defaults':report,'variants':['03: negative b, L=2, 800 samples','08: mp50, N=3','04: mp50, y_max=3','07: mp50, x=2, N=2','09: mp50, N=3','11: mp50, two-carrier family']},indent=2)+'\n')
if __name__=='__main__':main()
