/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD8Long00CompositionalNode174
import Proofs.RadenkovicGutmanD8Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e177 : NestedArithmetic.Expr 3 := .times e174 e176
noncomputable def p177 : NestedHorner.Poly 3 := [[[-12],[0]],[[0,0],[0]],[[-204,0],[0,0]],[[0,0],[0,0]],[[-1464,0],[0,0]],[[0,0],[0,0]],[[-5772,0],[0,0]],[[0,0],[0,0]],[[-13632,0],[0,0]],[[0,0],[0,0]],[[-19728,-12],[-12,0]],[[0,0],[0,0]],[[-17160,-96],[-96,0]],[[0,0],[0,0]],[[-8364,-264],[-264,0]],[[0,0],[0,0]],[[-1908,-288],[-288,0]],[[0,0],[0,0]],[[-108,-108],[-108,0]],[[0],[0,0]],[[0],[0,-12]]]
theorem step177 : p177=NestedArithmetic.mul p174 p176 := by decide +kernel
#print axioms step177
theorem h177 : NestedArithmetic.compile e177=p177 := StagedExprCompile.compile_times e177 e174 e176 p174 p176 p177 rfl h174 h176 step177
#print axioms h177
end Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
