/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD8Long00CompositionalNode177
import Proofs.RadenkovicGutmanD8Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e178 : NestedArithmetic.Expr 3 := .times e177 e122
noncomputable def p178 : NestedHorner.Poly 3 := [[[-12],[0]],[[0,0],[0]],[[-204,0],[0,0]],[[0,0],[0,0]],[[-1464,0],[0,0]],[[0,0],[0,0]],[[-5772,0],[0,0]],[[0,0],[0,0]],[[-13632,0],[0,0]],[[0,0],[0,0]],[[-19728,-12],[-12,0]],[[0,0],[0,0]],[[-17160,-96],[-96,0]],[[0,0],[0,0]],[[-8364,-264],[-264,0]],[[0,0],[0,0]],[[-1908,-288],[-288,0]],[[0,0],[0,0]],[[-108,-108],[-108,0]],[[0],[0,0]],[[0],[0,-12]]]
theorem step178 : p178=NestedArithmetic.mul p177 p122 := by decide +kernel
#print axioms step178
theorem h178 : NestedArithmetic.compile e178=p178 := StagedExprCompile.compile_times e178 e177 e122 p177 p122 p178 rfl h177 h122 step178
#print axioms h178
end Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
