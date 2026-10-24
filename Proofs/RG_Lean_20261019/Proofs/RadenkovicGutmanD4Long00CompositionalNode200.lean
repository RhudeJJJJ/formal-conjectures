/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode189
import Proofs.RadenkovicGutmanD4Long00CompositionalNode175
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e200 : NestedArithmetic.Expr 3 := .times e189 e175
noncomputable def p200 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[38,0],[0,0]],[[0,0],[0,0]],[[312,0],[0,0]],[[0,0],[0,0]],[[1450,0],[0,0]],[[0,0],[0,0]],[[4196,0],[0,0]],[[0,0],[0,0]],[[7832,2],[2,0]],[[0,0],[0,0]],[[9436,20],[20,0]],[[0,0],[0,0]],[[7114,76],[76,0]],[[0,0],[0,0]],[[3106,136],[136,0]],[[0,0],[0,0]],[[654,114],[114,0]],[[0,0],[0,0]],[[36,36],[36,2]],[[0],[0,0]],[[0],[0,4]]]
theorem step200 : p200=NestedArithmetic.mul p189 p175 := by decide +kernel
#print axioms step200
theorem h200 : NestedArithmetic.compile e200=p200 := StagedExprCompile.compile_times e200 e189 e175 p189 p175 p200 rfl h189 h175 step200
#print axioms h200
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
