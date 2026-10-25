/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD45Long00CompositionalNode119
import Proofs.RadenkovicGutmanD45Long00CompositionalNode163
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e164 : NestedArithmetic.Expr 3 := .times e119 e163
noncomputable def p164 : NestedHorner.Poly 3 := [[[-86],[0]],[[0,0],[0]],[[-1282,0],[0,0]],[[0,0],[0,0]],[[-7972,0],[0,0]],[[0,0],[0,0]],[[-26786,0],[0,0]],[[0,0],[0,0]],[[-52696,0],[0,0]],[[0,0],[0,0]],[[-61464,-86],[-86,0]],[[0,0],[0,0]],[[-40540,-688],[-688,0]],[[0,0],[0,0]],[[-12242,-1892],[-1892,0]],[[0,0],[0,0]],[[366,-2064],[-2064,0]],[[0,0],[0,0]],[[846,-774],[-774,0]],[[0],[0,0]],[[0],[0,-86]]]
theorem step164 : p164=NestedArithmetic.mul p119 p163 := by decide +kernel
#print axioms step164
theorem h164 : NestedArithmetic.compile e164=p164 := StagedExprCompile.compile_times e164 e119 e163 p119 p163 p164 rfl h119 h163 step164
#print axioms h164
end Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
