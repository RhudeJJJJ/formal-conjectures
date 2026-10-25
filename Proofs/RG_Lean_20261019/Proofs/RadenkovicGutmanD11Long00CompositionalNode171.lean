/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD11Long00CompositionalNode030
import Proofs.RadenkovicGutmanD11Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e171 : NestedArithmetic.Expr 3 := .times e030 e170
noncomputable def p171 : NestedHorner.Poly 3 := [[[22],[0]],[[0,0],[0]],[[330,0],[0]],[[0,0],[0]],[[2068,0],[0]],[[0,0],[0]],[[7018,0],[0]],[[0,0],[0]],[[13992,0],[0]],[[0,0],[0]],[[16654,11],[11]],[[0,0],[0]],[[11484,77],[77]],[[0,0],[0]],[[4158,176],[176]],[[0,0],[0]],[[594,143],[143]],[[0,0],[0]],[[0,33],[33]]]
theorem step171 : p171=NestedArithmetic.mul p030 p170 := by decide +kernel
#print axioms step171
theorem h171 : NestedArithmetic.compile e171=p171 := StagedExprCompile.compile_times e171 e030 e170 p030 p170 p171 rfl h030 h170 step171
#print axioms h171
end Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
