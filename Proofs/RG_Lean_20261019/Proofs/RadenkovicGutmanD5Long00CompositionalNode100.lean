/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode043
import Proofs.RadenkovicGutmanD5Long00CompositionalNode057
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e100 : NestedArithmetic.Expr 3 := .times e043 e057
noncomputable def p100 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,-225],[0,-450,90],[-225,90]],[[0,0,0],[0,0,0],[0,0]],[[0,-9315,-1140],[-9315,-930,390],[-1140,390]],[[0,0,0],[0,0,0],[0,0]],[[-89100,-88155,-955],[-88155,7090,480],[-955,480]],[[0,0,0],[0,0,0],[0,0]],[[-1155600,-349515,4210],[-349515,31790,210],[4210,210]],[[0,0,0],[0,0,0],[0,0]],[[-6712470,-751980,11610],[-751980,54900,30],[11610,30]],[[0,0,0],[0,0],[0]],[[-23153550,-922495,12830],[-922495,50500],[12830]],[[0,0,0],[0,0],[0]],[[-52939430,-549415,7545],[-549415,26730],[7545]],[[0,0,0],[0,0],[0]],[[-84683720,92800,2470],[92800,8150],[2470]],[[0,0,0],[0,0],[0]],[[-97252590,455955,425],[455955,1330],[425]],[[0,0,0],[0,0],[0]],[[-80583820,402985,30],[402985,90],[30]],[[0,0],[0]],[[-47175880,198690],[198690]],[[0,0],[0]],[[-17990650,61075],[61075]],[[0,0],[0]],[[-2991770,11645],[11645]],[[0,0],[0]],[[1080330,1265],[1265]],[[0,0],[0]],[[953250,60],[60]],[[0]],[[345300]],[[0]],[[75950]],[[0]],[[10480]],[[0]],[[840]],[[0]],[[30]]]
theorem step100 : p100=NestedArithmetic.mul p043 p057 := by decide +kernel
#print axioms step100
theorem h100 : NestedArithmetic.compile e100=p100 := StagedExprCompile.compile_times e100 e043 e057 p043 p057 p100 rfl h043 h057 step100
#print axioms h100
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
