/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD39Long00CompositionalNode030
import Proofs.RadenkovicGutmanD39Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e171 : NestedArithmetic.Expr 3 := .times e030 e170
noncomputable def p171 : NestedHorner.Poly 3 := [[[78],[0]],[[0,0],[0]],[[1170,0],[0]],[[0,0],[0]],[[7332,0],[0]],[[0,0],[0]],[[24882,0],[0]],[[0,0],[0]],[[49608,0],[0]],[[0,0],[0]],[[59046,39],[39]],[[0,0],[0]],[[40716,273],[273]],[[0,0],[0]],[[14742,624],[624]],[[0,0],[0]],[[2106,507],[507]],[[0,0],[0]],[[0,117],[117]]]
theorem step171 : p171=NestedArithmetic.mul p030 p170 := by decide +kernel
#print axioms step171
theorem h171 : NestedArithmetic.compile e171=p171 := StagedExprCompile.compile_times e171 e030 e170 p030 p170 p171 rfl h030 h170 step171
#print axioms h171
end Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
