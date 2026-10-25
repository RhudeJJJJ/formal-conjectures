/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD11Long00CompositionalNode171
import Proofs.RadenkovicGutmanD11Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e172 : NestedArithmetic.Expr 3 := .times e171 e003
noncomputable def p172 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[22,0],[0]],[[0,0],[0]],[[330,0],[0]],[[0,0],[0]],[[2068,0],[0]],[[0,0],[0]],[[7018,0],[0]],[[0,0],[0]],[[13992,0],[0]],[[0,0],[0]],[[16654,11],[11]],[[0,0],[0]],[[11484,77],[77]],[[0,0],[0]],[[4158,176],[176]],[[0,0],[0]],[[594,143],[143]],[[0,0],[0]],[[0,33],[33]]]
theorem step172 : p172=NestedArithmetic.mul p171 p003 := by decide +kernel
#print axioms step172
theorem h172 : NestedArithmetic.compile e172=p172 := StagedExprCompile.compile_times e172 e171 e003 p171 p003 p172 rfl h171 h003 step172
#print axioms h172
end Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
