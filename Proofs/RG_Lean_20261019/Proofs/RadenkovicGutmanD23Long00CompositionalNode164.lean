/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD23Long00CompositionalNode119
import Proofs.RadenkovicGutmanD23Long00CompositionalNode163
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e164 : NestedArithmetic.Expr 3 := .times e119 e163
noncomputable def p164 : NestedHorner.Poly 3 := [[[-42],[0]],[[0,0],[0]],[[-622,0],[0,0]],[[0,0],[0,0]],[[-3836,0],[0,0]],[[0,0],[0,0]],[[-12750,0],[0,0]],[[0,0],[0,0]],[[-24712,0],[0,0]],[[0,0],[0,0]],[[-28200,-42],[-42,0]],[[0,0],[0,0]],[[-17924,-336],[-336,0]],[[0,0],[0,0]],[[-4894,-924],[-924,0]],[[0,0],[0,0]],[[498,-1008],[-1008,0]],[[0,0],[0,0]],[[450,-378],[-378,0]],[[0],[0,0]],[[0],[0,-42]]]
theorem step164 : p164=NestedArithmetic.mul p119 p163 := by decide +kernel
#print axioms step164
theorem h164 : NestedArithmetic.compile e164=p164 := StagedExprCompile.compile_times e164 e119 e163 p119 p163 p164 rfl h119 h163 step164
#print axioms h164
end Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
