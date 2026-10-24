/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode173
import Proofs.RadenkovicGutmanD5Long00CompositionalNode218
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e270 : NestedArithmetic.Expr 3 := .times e173 e218
noncomputable def p270 : NestedHorner.Poly 3 := [[[30],[0],[0]],[[0,0],[0,0],[0]],[[840,0,0],[0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[10480,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[75950,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[345300,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[953250,60,0],[60,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[1080330,1265,0],[1265,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-2991770,11645,0],[11645,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-17990650,61075,0],[61075,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-47175880,198690,0],[198690,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-80583820,402985,30],[402985,90,0],[30,0]],[[0,0,0],[0,0,0],[0,0]],[[-97252590,455955,425],[455955,1330,0],[425,0]],[[0,0,0],[0,0,0],[0,0]],[[-84683720,92800,2470],[92800,8150,0],[2470,0]],[[0,0,0],[0,0,0],[0,0]],[[-52939430,-549415,7545],[-549415,26730,0],[7545,0]],[[0,0,0],[0,0,0],[0,0]],[[-23153550,-922495,12830],[-922495,50500,0],[12830,0]],[[0,0,0],[0,0,0],[0,0]],[[-6712470,-751980,11610],[-751980,54900,30],[11610,30]],[[0,0,0],[0,0,0],[0,0]],[[-1155600,-349515,4210],[-349515,31790,210],[4210,210]],[[0,0,0],[0,0,0],[0,0]],[[-89100,-88155,-955],[-88155,7090,480],[-955,480]],[[0,0,0],[0,0,0],[0,0]],[[0,-9315,-1140],[-9315,-930,390],[-1140,390]],[[0,0,0],[0,0,0],[0,0]],[[0,0,-225],[0,-450,90],[-225,90]]]
theorem step270 : p270=NestedArithmetic.mul p173 p218 := by decide +kernel
#print axioms step270
theorem h270 : NestedArithmetic.compile e270=p270 := StagedExprCompile.compile_times e270 e173 e218 p173 p218 p270 rfl h173 h218 step270
#print axioms h270
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
