/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode030
import Proofs.RadenkovicGutmanD5Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e171 : NestedArithmetic.Expr 3 := .times e030 e170
noncomputable def p171 : NestedHorner.Poly 3 := [[[10],[0]],[[0,0],[0]],[[150,0],[0]],[[0,0],[0]],[[940,0],[0]],[[0,0],[0]],[[3190,0],[0]],[[0,0],[0]],[[6360,0],[0]],[[0,0],[0]],[[7570,5],[5]],[[0,0],[0]],[[5220,35],[35]],[[0,0],[0]],[[1890,80],[80]],[[0,0],[0]],[[270,65],[65]],[[0,0],[0]],[[0,15],[15]]]
theorem step171 : p171=NestedArithmetic.mul p030 p170 := by decide +kernel
#print axioms step171
theorem h171 : NestedArithmetic.compile e171=p171 := StagedExprCompile.compile_times e171 e030 e170 p030 p170 p171 rfl h030 h170 step171
#print axioms h171
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
