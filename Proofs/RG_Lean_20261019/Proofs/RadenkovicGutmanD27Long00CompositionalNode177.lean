/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD27Long00CompositionalNode174
import Proofs.RadenkovicGutmanD27Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e177 : NestedArithmetic.Expr 3 := .times e174 e176
noncomputable def p177 : NestedHorner.Poly 3 := [[[-50],[0]],[[0,0],[0]],[[-850,0],[0,0]],[[0,0],[0,0]],[[-6100,0],[0,0]],[[0,0],[0,0]],[[-24050,0],[0,0]],[[0,0],[0,0]],[[-56800,0],[0,0]],[[0,0],[0,0]],[[-82200,-50],[-50,0]],[[0,0],[0,0]],[[-71500,-400],[-400,0]],[[0,0],[0,0]],[[-34850,-1100],[-1100,0]],[[0,0],[0,0]],[[-7950,-1200],[-1200,0]],[[0,0],[0,0]],[[-450,-450],[-450,0]],[[0],[0,0]],[[0],[0,-50]]]
theorem step177 : p177=NestedArithmetic.mul p174 p176 := by decide +kernel
#print axioms step177
theorem h177 : NestedArithmetic.compile e177=p177 := StagedExprCompile.compile_times e177 e174 e176 p174 p176 p177 rfl h174 h176 step177
#print axioms h177
end Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
