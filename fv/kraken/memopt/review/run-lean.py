from pathlib import Path
import subprocess, json, os
E=Path(__file__).resolve().parent
L=Path.cwd()
log=[]
def run(label,args,env=None):
    with (E/(label+'.txt')).open('w') as out:
        p=subprocess.run(args,stdout=out,stderr=subprocess.STDOUT,env=env)
    log.append({'label':label,'cwd':str(L),'command':args,'exit':p.returncode})
    (E/'lean-commands.json').write_text(json.dumps(log,indent=2)+'\n')
    print(label,'exit',p.returncode,flush=True)
    if p.returncode: raise SystemExit(p.returncode)
for stage in ['orig','new']:
    for mod in ['WitLcM0','WitLcM1','WitLcM4','WitLcM1x1','WitLcM4x16','WitLcMMix']:
        src=E/stage/'Fk'/(mod+'.lean')
        run(stage+'-'+mod,['lake','env','lean','-R',str(E/stage),'-o',str(src.with_suffix('.olean')),str(src)])
run('recheck',['lake','env','lean',str(E/'Recheck.lean')])
run('axioms',['lake','env','lean','tools/Axioms.lean'])
run('axioms-all',['lake','env','lean','tools/AxiomsAll.lean'])
