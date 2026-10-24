"""Emit exact data-only stages and kernel identities in one reusable leaf module.

No numerical result is trusted here. Raw data, scalar weights, polynomial
pieces, joins, Bernstein rows, signs and logarithms all have kernel checks.
"""
import math
from fractions import Fraction as Q
def rational(value):
    value=Q(value)
    return str(value.numerator) if value.denominator==1 else f'({value.numerator}/{value.denominator})'

def body(tag,index,cell,shared_weights=False,outer_table=None,outer_chunk=12):
    assert tag in ['10','30','00']
    stem=f'leaf{index:05d}';prefix=stem+'_w_'
    s,L,R=map(Q,(cell['young'],cell['square_lower'],cell['payment']))
    alpha,beta=L*(1+s),L*(1+1/s);K=math.lcm(alpha.denominator,beta.denominator)
    A,B=int(K*alpha),int(K*beta)
    l,w=list(map(Q,cell['box_left'])),list(map(Q,cell['box_width']))
    D=[math.lcm(a.denominator,b.denominator) for a,b in zip(l,w)]
    lN,wN=[int(a*b) for a,b in zip(l,D)],[int(a*b) for a,b in zip(w,D)]
    degrees=cell['degrees'];assert len(degrees)==3 and all(x>=0 for x in degrees)
    assert outer_chunk in [3,6,12]
    count=degrees[0]+1;chunk=outer_chunk;parts=(count+chunk-1)//chunk
    def vec(values):return '!['+','.join(map(str,values))+']'
    deg=vec(degrees);left,width=vec(map(rational,l)),vec(map(rational,w))
    ln,wn,den=vec(lN),vec(wN),vec(D);inv=str(cell['reciprocal']).lower()
    sq,lower,pay=map(rational,(s,L,R));k,n=cell['logarithm_k'],cell['logarithm_n']
    raw,inner,affine=(prefix+x for x in ['raw','inner','affine'])
    norm='DegreeOneIntegerNorm'+tag+'.pack';pack='DegreeOneNormPack'+tag+'.pack'
    text=f'''open NestedInteger NestedHorner
def {raw} : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 {deg} (IntegerNormProgramPack.polynomial {norm} {inv} {K} {A} {B}))
theorem {stem}_raw : IntegerNormProgramPack.rawCheck {norm} {inv} {K} {A} {B} {raw}=true := by decide +kernel
theorem {stem}_rectangular : NestedInteger.rectangular 3 {deg} {raw}=true := by decide +kernel
#print axioms {stem}_raw
#print axioms {stem}_rectangular
def {inner} : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerAffineStages.inner {raw} {ln} {wn} {den})
theorem {stem}_inner : {inner}=IntegerAffineStages.inner {raw} {ln} {wn} {den} := by decide +kernel
#print axioms {stem}_inner
'''
    for i in range(parts):
        source,seg,weights,piece=(prefix+f'{x}{i:02d}' for x in ['source','segment','weights','piece'])
        previous=inner if i==0 else prefix+f'source{i-1:02d}.drop {chunk}'
        text+=f'''def {source} : NestedInteger.Poly 3 := {previous}
def {seg} : NestedInteger.Poly 3 := {source}.take {chunk}
'''
        if outer_table:
            table=f'{outer_table[1]}.part{i:02d}'
            size=min(chunk,count-chunk*i)
            text+=f'''def {weights} : List (List ℤ) := {table}
theorem {weights}_identity : {weights}=IntegerWeightedOuter.weights {lN[0]} {wN[0]} {D[0]} {chunk*i} {seg} :=
  IntegerOuterTable.checked (n := 2) {lN[0]} {wN[0]} {D[0]} {chunk*i} {size} {seg} {table}
    (by decide +kernel) {table}_identity
'''
        else:
            text+=f'''def {weights} : List (List ℤ) := rg_integer_row%
  (IntegerWeightedOuter.weights {lN[0]} {wN[0]} {D[0]} {chunk*i} {seg})
theorem {weights}_identity : {weights}=IntegerWeightedOuter.weights {lN[0]} {wN[0]} {D[0]} {chunk*i} {seg} := by decide +kernel
'''
        text+=f'''def {piece} : NestedInteger.Poly 3 := rg_integer_data% (IntegerWeightedOuter.applyWeights {weights} {seg})
theorem {piece}_weighted : {piece}=IntegerWeightedOuter.applyWeights {weights} {seg} := by decide +kernel
theorem {piece}_identity : {piece}=IntegerOuterTerms.transform {lN[0]} {wN[0]} {D[0]} {chunk*i} {seg} :=
  IntegerWeightedOuter.checked {lN[0]} {wN[0]} {D[0]} {chunk*i} {seg} {piece} {weights} {weights}_identity {piece}_weighted
#print axioms {weights}_identity
#print axioms {piece}_weighted
#print axioms {piece}_identity
'''
    following=None
    for i in reversed(range(parts)):
        source,seg,piece=(prefix+f'{x}{i:02d}' for x in ['source','segment','piece'])
        name=affine if i==0 else prefix+f'suffix{i:02d}'
        offset=chunk*i
        if i==parts-1:
            text+=f'''def {name} : NestedInteger.Poly 3 := {piece}
theorem {name}_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 {name}) x=eval (castPoly 3 (IntegerOuterTerms.transform {lN[0]} {wN[0]} {D[0]} {offset} {source})) x := by
  have h : {seg}={source} := by decide +kernel
  rw [{name},{piece}_identity,h]
#print axioms {name}_eval
'''
        else:
            tail=prefix+f'source{i+1:02d}'
            text+=f'''def {name} : NestedInteger.Poly 3 := rg_integer_data%
  (NestedInteger.add (NestedInteger.scale ({D[0]}^{tail}.length) {piece}) {following})
theorem {name}_join : {name}=NestedInteger.add (NestedInteger.scale ({D[0]}^{tail}.length) {piece}) {following} := by decide +kernel
theorem {name}_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 {name}) x=eval (castPoly 3 (IntegerOuterTerms.transform {lN[0]} {wN[0]} {D[0]} {offset} {source})) x := by
  have hlen : {seg}.length={chunk} := by decide +kernel
  calc
    _ = ({D[0]} : ℝ)^{tail}.length *
        eval (castPoly 3 (IntegerOuterTerms.transform {lN[0]} {wN[0]} {D[0]} {offset} {seg})) x+
        eval (castPoly 3 (IntegerOuterTerms.transform {lN[0]} {wN[0]} {D[0]} ({offset}+{seg}.length) {tail})) x := by
      rw [{name}_join,cast_add,eval_add,cast_scale,eval_scale,{piece}_identity,{following}_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform {lN[0]} {wN[0]} {D[0]} {offset} ({seg}++{tail}))) x :=
      (IntegerOuterPieces.eval_append {lN[0]} {wN[0]} {D[0]} {offset} {seg} {tail} x).symm
    _ = _ := by rw [show {seg}++{tail}={source} from List.take_append_drop {chunk} {source}]
#print axioms {name}_join
#print axioms {name}_eval
'''
        following=name
    rownames=[]
    if shared_weights:
        text+=f'theorem {affine}_length : {affine}.length={count} := by decide +kernel\n#print axioms {affine}_length\n'
    for j in range(count):
        row,weights=prefix+f'row{j:03d}',prefix+f'bernsteinWeights{j:03d}';rownames.append(row)
        if shared_weights:
            table=f'IntegerBernsteinWeights{degrees[0]}.row{j:03d}'
            weight_proof=f'(IntegerBernsteinTable.checked (n := 2) {degrees[0]} {j} 0 {count} {affine} {table} {affine}_length {table}_identity)'
            text+=f'''def {row} : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights {table} {affine})
theorem {row}_weighted : {row}=IntegerWeightedBernstein.applyWeights {table} {affine} := by decide +kernel
theorem {row}_identity : {row}=NestedInteger.coefficientFrom {degrees[0]} {j} 0 {affine} :=
  IntegerWeightedBernstein.checked {degrees[0]} {j} 0 {affine} {row} {table} {weight_proof} {row}_weighted
theorem {row}_positive : NestedInteger.bernsteinCheck 2 {vec(degrees[1:])} {row}=true := by decide +kernel
#print axioms {row}_weighted
#print axioms {row}_identity
#print axioms {row}_positive
'''
            continue
        scalars=['some '+str(math.comb(degrees[0]-v,j-v)) if v<=j else 'none' for v in range(count)]
        text+=f'''def {weights} : List (Option ℤ) := [{','.join(scalars)}]
theorem {weights}_identity : {weights}=IntegerWeightedBernstein.weights {degrees[0]} {j} 0 {affine} := by decide +kernel
def {row} : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights {weights} {affine})
theorem {row}_weighted : {row}=IntegerWeightedBernstein.applyWeights {weights} {affine} := by decide +kernel
theorem {row}_identity : {row}=NestedInteger.coefficientFrom {degrees[0]} {j} 0 {affine} :=
  IntegerWeightedBernstein.checked {degrees[0]} {j} 0 {affine} {row} {weights} {weights}_identity {row}_weighted
theorem {row}_positive : NestedInteger.bernsteinCheck 2 {vec(degrees[1:])} {row}=true := by decide +kernel
#print axioms {weights}_identity
#print axioms {row}_weighted
#print axioms {row}_identity
#print axioms {row}_positive
'''
    rows=prefix+'rows'
    text+=f'def {rows} : Fin {count} → NestedInteger.Poly 2 := !['+','.join(rownames)+']\n'
    text+=f'''theorem {stem}_sign : NestedInteger.bernsteinCheck 3 {deg} {affine}=true := by
  apply IntegerBernsteinRows.checked {deg} {affine} {rows} (by decide +kernel)
  · intro j
    fin_cases j
'''+''.join(f'    · exact {row}_identity\n' for row in rownames)
    text+='  · intro j\n    fin_cases j\n'+''.join(f'    · exact {row}_positive\n' for row in rownames)
    c1=4 if tag=='00' else int(tag[0])-1
    text+=f'''#print axioms {stem}_sign
theorem {stem}_log : RationalLog.accepts {lower} {pay} {k} {n}=true := by decide +kernel
#print axioms {stem}_log
def {stem} : FastNestedCellData.Cell := IntegerScaledCell.make {pack} {inv} {sq} {lower} {pay} {k} {n} {deg} {left} {width} {K} {den} {affine}
theorem {stem}_checked : FastNestedCellData.accepts 1 {c1} 4 {stem}=true :=
  IntegerPiecewiseCell.accepts_make {norm} {inv} {sq} {lower} {pay} {k} {n} {deg} {left} {width}
    {K} {A} {B} {ln} {wn} {den} {raw} {inner} {affine}
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    {stem}_raw {stem}_rectangular {stem}_inner {affine}_eval {stem}_sign {stem}_log
#print axioms {stem}_checked
'''
    imports=['Proofs.RadenkovicGutmanIntegerPiecewiseCell','Proofs.RadenkovicGutmanIntegerWeightedOuter',
      'Proofs.RadenkovicGutmanIntegerWeightedBernstein','Proofs.RadenkovicGutmanD1IntegerNorm'+tag]
    if shared_weights:imports.append('Proofs.RadenkovicGutmanIntegerBernsteinWeights'+str(degrees[0]))
    if outer_table:imports.append(outer_table[0])
    return imports,text
