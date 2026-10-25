/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD40Long00CompositionalNode191
import Proofs.RadenkovicGutmanD40Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e192 : NestedArithmetic.Expr 3 := .times e191 e158
noncomputable def p192 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[70,0],[0,0]],[[0,0],[0,0]],[[788,0],[0,0]],[[0,0],[0,0]],[[4398,0],[0,0]],[[0,0],[0,0]],[[14032,0],[0,0]],[[0,0],[0,0]],[[26952,2],[2,0]],[[0,0],[0,0]],[[31268,56],[56,0]],[[0,0],[0,0]],[[20894,364],[364,0]],[[0,0],[0,0]],[[6686,928],[928,0]],[[0,0],[0,0]],[[102,978],[978,0]],[[0,0],[0,0]],[[-360,360],[360,2]],[[0],[0,0]],[[0],[0,40]]]
theorem step192 : p192=NestedArithmetic.mul p191 p158 := by decide +kernel
#print axioms step192
theorem h192 : NestedArithmetic.compile e192=p192 := StagedExprCompile.compile_times e192 e191 e158 p191 p158 p192 rfl h191 h158 step192
#print axioms h192
end Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
