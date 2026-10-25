/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD26Long00CompositionalNode191
import Proofs.RadenkovicGutmanD26Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e192 : NestedArithmetic.Expr 3 := .times e191 e158
noncomputable def p192 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[56,0],[0,0]],[[0,0],[0,0]],[[578,0],[0,0]],[[0,0],[0,0]],[[3082,0],[0,0]],[[0,0],[0,0]],[[9566,0],[0,0]],[[0,0],[0,0]],[[18048,2],[2,0]],[[0,0],[0,0]],[[20684,42],[42,0]],[[0,0],[0,0]],[[13698,252],[252,0]],[[0,0],[0,0]],[[4348,620],[620,0]],[[0,0],[0,0]],[[60,642],[642,0]],[[0,0],[0,0]],[[-234,234],[234,2]],[[0],[0,0]],[[0],[0,26]]]
theorem step192 : p192=NestedArithmetic.mul p191 p158 := by decide +kernel
#print axioms step192
theorem h192 : NestedArithmetic.compile e192=p192 := StagedExprCompile.compile_times e192 e191 e158 p191 p158 p192 rfl h191 h158 step192
#print axioms h192
end Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
