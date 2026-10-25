/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD13Long00CompositionalNode171
import Proofs.RadenkovicGutmanD13Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e172 : NestedArithmetic.Expr 3 := .times e171 e003
noncomputable def p172 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[26,0],[0]],[[0,0],[0]],[[390,0],[0]],[[0,0],[0]],[[2444,0],[0]],[[0,0],[0]],[[8294,0],[0]],[[0,0],[0]],[[16536,0],[0]],[[0,0],[0]],[[19682,13],[13]],[[0,0],[0]],[[13572,91],[91]],[[0,0],[0]],[[4914,208],[208]],[[0,0],[0]],[[702,169],[169]],[[0,0],[0]],[[0,39],[39]]]
theorem step172 : p172=NestedArithmetic.mul p171 p003 := by decide +kernel
#print axioms step172
theorem h172 : NestedArithmetic.compile e172=p172 := StagedExprCompile.compile_times e172 e171 e003 p171 p003 p172 rfl h171 h003 step172
#print axioms h172
end Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
