/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode190
import Proofs.RadenkovicGutmanD4Long00CompositionalNode121
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e191 : NestedArithmetic.Expr 3 := .times e190 e121
noncomputable def p191 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[34,0],[0,0]],[[0,0],[0,0]],[[248,0],[0,0]],[[0,0],[0,0]],[[1014,0],[0,0]],[[0,0],[0,0]],[[2548,0],[0,0]],[[0,0],[0,0]],[[4056,2],[2,0]],[[0,0],[0,0]],[[4052,20],[20,0]],[[0,0],[0,0]],[[2390,76],[76,0]],[[0,0],[0,0]],[[674,136],[136,0]],[[0,0],[0,0]],[[-6,114],[114,0]],[[0,0],[0,0]],[[-36,36],[36,2]],[[0],[0,0]],[[0],[0,4]]]
theorem step191 : p191=NestedArithmetic.mul p190 p121 := by decide +kernel
#print axioms step191
theorem h191 : NestedArithmetic.compile e191=p191 := StagedExprCompile.compile_times e191 e190 e121 p190 p121 p191 rfl h190 h121 step191
#print axioms h191
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
