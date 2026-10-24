/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode191
import Proofs.RadenkovicGutmanD4Long00CompositionalNode194
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e195 : NestedArithmetic.Expr 3 := .plus e191 e194
noncomputable def p195 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[50,0],[0,0]],[[0,0],[0,0]],[[488,0],[0,0]],[[0,0],[0,0]],[[2518,0],[0,0]],[[0,0],[0,0]],[[7652,0],[0,0]],[[0,0],[0,0]],[[14232,2],[2,0]],[[0,0],[0,0]],[[16164,28],[28,0]],[[0,0],[0,0]],[[10742,132],[132,0]],[[0,0],[0,0]],[[3698,264],[264,0]],[[0,0],[0,0]],[[426,218],[218,0]],[[0,0],[0,0]],[[-36,60],[60,2]],[[0],[0,0]],[[0],[0,4]]]
theorem step195 : p195=NestedHorner.add p191 p194 := by decide +kernel
#print axioms step195
theorem h195 : NestedArithmetic.compile e195=p195 := StagedExprCompile.compile_plus e195 e191 e194 p191 p194 p195 rfl h191 h194 step195
#print axioms h195
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
