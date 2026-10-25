/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD8Long00CompositionalNode119
import Proofs.RadenkovicGutmanD8Long00CompositionalNode163
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e164 : NestedArithmetic.Expr 3 := .times e119 e163
noncomputable def p164 : NestedHorner.Poly 3 := [[[-12],[0]],[[0,0],[0]],[[-172,0],[0,0]],[[0,0],[0,0]],[[-1016,0],[0,0]],[[0,0],[0,0]],[[-3180,0],[0,0]],[[0,0],[0,0]],[[-5632,0],[0,0]],[[0,0],[0,0]],[[-5520,-12],[-12,0]],[[0,0],[0,0]],[[-2504,-96],[-96,0]],[[0,0],[0,0]],[[116,-264],[-264,0]],[[0,0],[0,0]],[[588,-288],[-288,0]],[[0,0],[0,0]],[[180,-108],[-108,0]],[[0],[0,0]],[[0],[0,-12]]]
theorem step164 : p164=NestedArithmetic.mul p119 p163 := by decide +kernel
#print axioms step164
theorem h164 : NestedArithmetic.compile e164=p164 := StagedExprCompile.compile_times e164 e119 e163 p119 p163 p164 rfl h119 h163 step164
#print axioms h164
end Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
