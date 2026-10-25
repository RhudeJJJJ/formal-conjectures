/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD11Long00CompositionalNode043
import Proofs.RadenkovicGutmanD11Long00CompositionalNode066
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e071 : NestedArithmetic.Expr 3 := .times e043 e066
noncomputable def p071 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-363],[0,-363,198]],[[0,0,0],[0,0,0],[0,0,0]],[[0,-3267,-5445],[-3267,-18216,3113],[-5445,3113,36]],[[0,0,0],[0,0,0],[0,0]],[[-81972,-225720,-15609],[-225720,-35256,13078],[-15609,13078]],[[0,0,0],[0,0,0],[0,0]],[[-2750868,-1654002,31846],[-1654002,200188,15577],[31846,15577]],[[0,0,0],[0,0,0],[0,0]],[[-26160678,-5081908,200803],[-5081908,875400,7249],[200803,7249]],[[0,0,0],[0,0,0],[0,0]],[[-127641036,-7298158,371306],[-7298158,1472352,1346],[371306,1346]],[[0,0,0],[0,0,0],[0,0]],[[-384038920,-1622130,357393],[-1622130,1345644,72],[357393,72]],[[0,0,0],[0,0],[0]],[[-772133396,12139372,199426],[12139372,726780],[199426]],[[0,0,0],[0,0],[0]],[[-1071809988,23426671,65737],[23426671,235120],[65737]],[[0,0,0],[0,0],[0]],[[-1020103762,23318083,12303],[23318083,43840],[12303]],[[0,0,0],[0,0],[0]],[[-612548406,14830139,1148],[14830139,4180],[1148]],[[0,0,0],[0,0],[0]],[[-135179314,6359148,36],[6359148,144],[36]],[[0,0],[0]],[[139146344,1851201],[1851201]],[[0,0],[0]],[[177991892,357366],[357366]],[[0,0],[0]],[[109908964,43051],[43051]],[[0,0],[0]],[[44790872,2834],[2834]],[[0,0],[0]],[[12822556,72],[72]],[[0]],[[2594054]],[[0]],[[361566]],[[0]],[[32674]],[[0]],[[1686]],[[0]],[[36]]]
theorem step071 : p071=NestedArithmetic.mul p043 p066 := by decide +kernel
#print axioms step071
theorem h071 : NestedArithmetic.compile e071=p071 := StagedExprCompile.compile_times e071 e043 e066 p043 p066 p071 rfl h043 h066 step071
#print axioms h071
end Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
