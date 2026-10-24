/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode171
import Proofs.RadenkovicGutmanD5Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e172 : NestedArithmetic.Expr 3 := .times e171 e003
noncomputable def p172 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[10,0],[0]],[[0,0],[0]],[[150,0],[0]],[[0,0],[0]],[[940,0],[0]],[[0,0],[0]],[[3190,0],[0]],[[0,0],[0]],[[6360,0],[0]],[[0,0],[0]],[[7570,5],[5]],[[0,0],[0]],[[5220,35],[35]],[[0,0],[0]],[[1890,80],[80]],[[0,0],[0]],[[270,65],[65]],[[0,0],[0]],[[0,15],[15]]]
theorem step172 : p172=NestedArithmetic.mul p171 p003 := by decide +kernel
#print axioms step172
theorem h172 : NestedArithmetic.compile e172=p172 := StagedExprCompile.compile_times e172 e171 e003 p171 p003 p172 rfl h171 h003 step172
#print axioms h172
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
