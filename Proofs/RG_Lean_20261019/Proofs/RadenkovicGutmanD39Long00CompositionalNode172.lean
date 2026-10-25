/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD39Long00CompositionalNode171
import Proofs.RadenkovicGutmanD39Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e172 : NestedArithmetic.Expr 3 := .times e171 e003
noncomputable def p172 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[78,0],[0]],[[0,0],[0]],[[1170,0],[0]],[[0,0],[0]],[[7332,0],[0]],[[0,0],[0]],[[24882,0],[0]],[[0,0],[0]],[[49608,0],[0]],[[0,0],[0]],[[59046,39],[39]],[[0,0],[0]],[[40716,273],[273]],[[0,0],[0]],[[14742,624],[624]],[[0,0],[0]],[[2106,507],[507]],[[0,0],[0]],[[0,117],[117]]]
theorem step172 : p172=NestedArithmetic.mul p171 p003 := by decide +kernel
#print axioms step172
theorem h172 : NestedArithmetic.compile e172=p172 := StagedExprCompile.compile_times e172 e171 e003 p171 p003 p172 rfl h171 h003 step172
#print axioms h172
end Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
