/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD13Long00CompositionalNode030
import Proofs.RadenkovicGutmanD13Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e171 : NestedArithmetic.Expr 3 := .times e030 e170
noncomputable def p171 : NestedHorner.Poly 3 := [[[26],[0]],[[0,0],[0]],[[390,0],[0]],[[0,0],[0]],[[2444,0],[0]],[[0,0],[0]],[[8294,0],[0]],[[0,0],[0]],[[16536,0],[0]],[[0,0],[0]],[[19682,13],[13]],[[0,0],[0]],[[13572,91],[91]],[[0,0],[0]],[[4914,208],[208]],[[0,0],[0]],[[702,169],[169]],[[0,0],[0]],[[0,39],[39]]]
theorem step171 : p171=NestedArithmetic.mul p030 p170 := by decide +kernel
#print axioms step171
theorem h171 : NestedArithmetic.compile e171=p171 := StagedExprCompile.compile_times e171 e030 e170 p030 p170 p171 rfl h030 h170 step171
#print axioms h171
end Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
