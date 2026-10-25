/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD23Long00CompositionalNode192
import Proofs.RadenkovicGutmanD23Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e193 : NestedArithmetic.Expr 3 := .times e192 e122
noncomputable def p193 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[53,0],[0,0]],[[0,0],[0,0]],[[533,0],[0,0]],[[0,0],[0,0]],[[2800,0],[0,0]],[[0,0],[0,0]],[[8609,0],[0,0]],[[0,0],[0,0]],[[16140,2],[2,0]],[[0,0],[0,0]],[[18416,39],[39,0]],[[0,0],[0,0]],[[12156,228],[228,0]],[[0,0],[0,0]],[[3847,554],[554,0]],[[0,0],[0,0]],[[51,570],[570,0]],[[0,0],[0,0]],[[-207,207],[207,2]],[[0],[0,0]],[[0],[0,23]]]
theorem step193 : p193=NestedArithmetic.mul p192 p122 := by decide +kernel
#print axioms step193
theorem h193 : NestedArithmetic.compile e193=p193 := StagedExprCompile.compile_times e193 e192 e122 p192 p122 p193 rfl h192 h122 step193
#print axioms h193
end Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
