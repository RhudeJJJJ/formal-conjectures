/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD9Long00CompositionalNode191
import Proofs.RadenkovicGutmanD9Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e192 : NestedArithmetic.Expr 3 := .times e191 e158
noncomputable def p192 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[39,0],[0,0]],[[0,0],[0,0]],[[323,0],[0,0]],[[0,0],[0,0]],[[1484,0],[0,0]],[[0,0],[0,0]],[[4143,0],[0,0]],[[0,0],[0,0]],[[7236,2],[2,0]],[[0,0],[0,0]],[[7832,25],[25,0]],[[0,0],[0,0]],[[4960,116],[116,0]],[[0,0],[0,0]],[[1509,246],[246,0]],[[0,0],[0,0]],[[9,234],[234,0]],[[0,0],[0,0]],[[-81,81],[81,2]],[[0],[0,0]],[[0],[0,9]]]
theorem step192 : p192=NestedArithmetic.mul p191 p158 := by decide +kernel
#print axioms step192
theorem h192 : NestedArithmetic.compile e192=p192 := StagedExprCompile.compile_times e192 e191 e158 p191 p158 p192 rfl h191 h158 step192
#print axioms h192
end Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
