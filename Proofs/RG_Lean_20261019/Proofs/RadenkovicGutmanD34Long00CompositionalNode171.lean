/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD34Long00CompositionalNode030
import Proofs.RadenkovicGutmanD34Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e171 : NestedArithmetic.Expr 3 := .times e030 e170
noncomputable def p171 : NestedHorner.Poly 3 := [[[68],[0]],[[0,0],[0]],[[1020,0],[0]],[[0,0],[0]],[[6392,0],[0]],[[0,0],[0]],[[21692,0],[0]],[[0,0],[0]],[[43248,0],[0]],[[0,0],[0]],[[51476,34],[34]],[[0,0],[0]],[[35496,238],[238]],[[0,0],[0]],[[12852,544],[544]],[[0,0],[0]],[[1836,442],[442]],[[0,0],[0]],[[0,102],[102]]]
theorem step171 : p171=NestedArithmetic.mul p030 p170 := by decide +kernel
#print axioms step171
theorem h171 : NestedArithmetic.compile e171=p171 := StagedExprCompile.compile_times e171 e030 e170 p030 p170 p171 rfl h030 h170 step171
#print axioms h171
end Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
