/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode043
import Proofs.RadenkovicGutmanD4Long00CompositionalNode051
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e061 : NestedArithmetic.Expr 3 := .times e043 e051
noncomputable def p061 : NestedHorner.Poly 3 := [[[0],[0,4]],[[0,0],[0,0]],[[36,36],[36,2]],[[0,0],[0]],[[654,114],[114]],[[0,0],[0]],[[3106,136],[136]],[[0,0],[0]],[[7114,76],[76]],[[0,0],[0]],[[9436,20],[20]],[[0,0],[0]],[[7832,2],[2]],[[0]],[[4196]],[[0]],[[1450]],[[0]],[[312]],[[0]],[[38]],[[0]],[[2]]]
theorem step061 : p061=NestedArithmetic.mul p043 p051 := by decide +kernel
#print axioms step061
theorem h061 : NestedArithmetic.compile e061=p061 := StagedExprCompile.compile_times e061 e043 e051 p043 p051 p061 rfl h043 h051 step061
#print axioms h061
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
