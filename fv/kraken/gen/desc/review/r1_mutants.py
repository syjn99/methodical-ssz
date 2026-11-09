import json,os,sys,copy
work=sys.argv[1]; orig=work+'/orig'; out=work+'/rmut'; os.makedirs(out,exist_ok=True)
def L(name): return json.load(open('%s/%s.desc.json'%(orig,name)))
M=[]  # id, base, what, mutate, reviewer expectation of a sound checker
def add(i,base,what,fn,want):
    d=L(base); fn(d); p='%s/%s.desc.json'%(out,i); json.dump(d,open(p,'w'),indent=1); M.append({'id':i,'base':base,'what':what,'file':p,'sound_checker_should':want})
# R1 wrong limit vs hand spec, reference removed by the mutant
def r1(d): d['ssz']['fields'][0]['limit']=17; d['fields'][0]['limit']=17; d['reference']=None
add('r1-ref-dropped','ListU64','limit 16->17 in term and claim, reference set to null',r1,'FAIL')
# R2 wrong kind vs hand spec with reference retargeted to another known Desc of the mutated shape? (bitList->byteList has no twin) -> reference key removed
def r2(d): d['ssz']['fields'][0]['k']='byteList'; d['fields'][0]['kind']='byteList'; del d['reference']
add('r2-ref-key-removed','BitL','bitList->byteList in term and claim, reference key deleted',r2,'FAIL')
# R3 Prysm bool -> uint8 (same width), claims follow
def r3(d): d['ssz']['fields'][3]={'k':'uint','w':1}; d['fields'][3]['kind']='uint'
add('r3-prysm-bool-uint8','prysm_v1alpha1.Validator','Slashed bool -> uint8, claim follows',r3,'FAIL')
# R4 Prysm bitvector bit length inside the same byte count
def r4(d): d['ssz']['fields'][0]['n']=505; d['fields'][0]['length']=505
add('r4-prysm-bitvec-505','prysm_v1alpha1.SyncAggregate','Bitvector 512 -> 505 bits (still 64 bytes), claim follows',r4,'FAIL')
# R5 Prysm list limit in term and claim
def r5(d): d['ssz']['fields'][0]['limit']=4096; d['fields'][0]['limit']=4096
add('r5-prysm-limit','prysm_v1alpha1.IndexedAttestation','list[uint64] limit 2048 -> 4096 in term and claim',r5,'FAIL')
# R6 Prysm field order: swap two fixed fields consistently (term, names, claims, offsets)
def r6(d):
    s=d['ssz']; s['names'][0],s['names'][1]=s['names'][1],s['names'][0]; s['fields'][0],s['fields'][1]=s['fields'][1],s['fields'][0]
    f=d['fields']; f[0],f[1]=f[1],f[0]; f[0]['offset']=0; f[0]['index']=0; f[1]['offset']=f[0]['width']; f[1]['index']=1
add('r6-prysm-field-swap','prysm_v1alpha1.StatusV2','fields 0 and 1 swapped consistently',r6,'FAIL')
# R7 claim field name differs from the term name
def r7(d): d['fields'][0]['name']='Zzz'
add('r7-claim-name','Scalars','claim name of field 0 changed (term names unchanged)',r7,'FAIL')
# R8 names swapped in the term of a hand type (reference compares up to names)
def r8(d): d['ssz']['names']=list(reversed(d['ssz']['names'])); 
add('r8-term-names-swapped','Scalars','term field names reversed, shapes unchanged',r8,'FAIL')
# R9 elem_variable claim flipped
def r9(d): d['fields'][0]['elem_variable']=False
add('r9-elem-variable','ListC','elem_variable true -> false (elem_size stays null)',r9,'FAIL')
# R10 callee claim changed
def r10(d): d['fields'][3]['callee']='github.com/x/y.Other'
add('r10-callee','AttestationData','callee of field 3 changed',r10,'FAIL')
# R11 index claim changed
def r11(d): d['fields'][1]['index']=7
add('r11-index','Checkpoint','index claim of field 1 -> 7',r11,'FAIL')
# R12 type name changed
def r12(d): d['type']='Checkpoint'
add('r12-type','Scalars','type name Scalars -> Checkpoint (reference stays Fv1.scDesc)',r12,'FAIL')
# R13 reference retargeted to a wrong hand Desc: expected FAIL by ref
def r13(d): d['reference']='Fv1.cpDesc'
add('r13-ref-wrong','Scalars','reference Fv1.scDesc -> Fv1.cpDesc',r13,'FAIL')
# R14 extra claim field
def r14(d): d['fields'].append(dict(d['fields'][-1],index=2,offset=40))
add('r14-extra-claim','Checkpoint','one extra field claim',r14,'FAIL')
# R15 term-only change (uint64 -> uint32) with claims left
def r15(d): d['ssz']['fields'][0]['w']=4
add('r15-term-only','Checkpoint','term uint 8 -> 4, claims unchanged',r15,'FAIL')
# R16 variable offset claim wrong
def r16(d): d['fields'][2]['offset']=20
add('r16-var-offset','Nested','variable field 2 offset 24 -> 20',r16,'FAIL')
# R17 nested (delegated) container inner change on a Prysm type: Attestation.Data.Slot uint64->bytes8
def r17(d): d['ssz']['fields'][1]['fields'][0]={'k':'byteVector','n':8}
add('r17-prysm-inner-kind','prysm_v1alpha1.Attestation','inner AttestationData.Slot uint64 -> byteVector 8',r17,'FAIL')
# R18 vector length 0 hidden in a Prysm type is caught by wf? vector of 0 bytes
def r18(d): d['ssz']['fields'][1]['n']=0; d['fields'][1]['length']=0; d['fields'][1]['width']=0
add('r18-prysm-bytes0','prysm_v1alpha1.SyncAggregate','byteVector 96 -> 0 with claims (offsets consistent)',r18,'FAIL')
# R19 variable_order with a duplicate
def r19(d): d['variable_order']=[0,0]
add('r19-order-dup','ListU64','variable_order [0] -> [0,0]',r19,'FAIL')
# R20 fixed_size claimed for a variable type
def r20(d): d['fixed_size']=4
add('r20-fixed-for-variable','ListU64','fixed_size null -> 4',r20,'FAIL')
json.dump(M,open(work+'/rmut.json','w'),indent=1)
lst=open(work+'/list.txt').read().split('\n'); lst=[x for x in lst if x]
open(work+'/list-all.txt','w').write('\n'.join(lst+[m['file'] for m in M])+'\n')
print(len(M), len(lst)+len(M))
