/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD23Long00CompositionalNode191
import Proofs.RadenkovicGutmanD23Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e192 : NestedArithmetic.Expr 3 := .times e191 e158
noncomputable def p192 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[53,0],[0,0]],[[0,0],[0,0]],[[533,0],[0,0]],[[0,0],[0,0]],[[2800,0],[0,0]],[[0,0],[0,0]],[[8609,0],[0,0]],[[0,0],[0,0]],[[16140,2],[2,0]],[[0,0],[0,0]],[[18416,39],[39,0]],[[0,0],[0,0]],[[12156,228],[228,0]],[[0,0],[0,0]],[[3847,554],[554,0]],[[0,0],[0,0]],[[51,570],[570,0]],[[0,0],[0,0]],[[-207,207],[207,2]],[[0],[0,0]],[[0],[0,23]]]
theorem step192 : p192=NestedArithmetic.mul p191 p158 := by decide +kernel
#print axioms step192
theorem h192 : NestedArithmetic.compile e192=p192 := StagedExprCompile.compile_times e192 e191 e158 p191 p158 p192 rfl h191 h158 step192
#print axioms h192
end Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
