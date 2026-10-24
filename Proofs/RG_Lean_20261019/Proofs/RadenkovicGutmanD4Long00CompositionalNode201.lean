/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode200
import Proofs.RadenkovicGutmanD4Long00CompositionalNode121
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e201 : NestedArithmetic.Expr 3 := .times e200 e121
noncomputable def p201 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[38,0],[0,0]],[[0,0],[0,0]],[[312,0],[0,0]],[[0,0],[0,0]],[[1450,0],[0,0]],[[0,0],[0,0]],[[4196,0],[0,0]],[[0,0],[0,0]],[[7832,2],[2,0]],[[0,0],[0,0]],[[9436,20],[20,0]],[[0,0],[0,0]],[[7114,76],[76,0]],[[0,0],[0,0]],[[3106,136],[136,0]],[[0,0],[0,0]],[[654,114],[114,0]],[[0,0],[0,0]],[[36,36],[36,2]],[[0],[0,0]],[[0],[0,4]]]
theorem step201 : p201=NestedArithmetic.mul p200 p121 := by decide +kernel
#print axioms step201
theorem h201 : NestedArithmetic.compile e201=p201 := StagedExprCompile.compile_times e201 e200 e121 p200 p121 p201 rfl h200 h121 step201
#print axioms h201
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
