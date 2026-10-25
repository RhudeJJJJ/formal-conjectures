/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD6Long00CompositionalNode191
import Proofs.RadenkovicGutmanD6Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e192 : NestedArithmetic.Expr 3 := .times e191 e158
noncomputable def p192 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[36,0],[0,0]],[[0,0],[0,0]],[[278,0],[0,0]],[[0,0],[0,0]],[[1202,0],[0,0]],[[0,0],[0,0]],[[3186,0],[0,0]],[[0,0],[0,0]],[[5328,2],[2,0]],[[0,0],[0,0]],[[5564,22],[22,0]],[[0,0],[0,0]],[[3418,92],[92,0]],[[0,0],[0,0]],[[1008,180],[180,0]],[[0,0],[0,0]],[[0,162],[162,0]],[[0,0],[0,0]],[[-54,54],[54,2]],[[0],[0,0]],[[0],[0,6]]]
theorem step192 : p192=NestedArithmetic.mul p191 p158 := by decide +kernel
#print axioms step192
theorem h192 : NestedArithmetic.compile e192=p192 := StagedExprCompile.compile_times e192 e191 e158 p191 p158 p192 rfl h191 h158 step192
#print axioms h192
end Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
