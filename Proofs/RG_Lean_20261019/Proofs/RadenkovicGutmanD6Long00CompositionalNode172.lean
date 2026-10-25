/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD6Long00CompositionalNode171
import Proofs.RadenkovicGutmanD6Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e172 : NestedArithmetic.Expr 3 := .times e171 e003
noncomputable def p172 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[12,0],[0]],[[0,0],[0]],[[180,0],[0]],[[0,0],[0]],[[1128,0],[0]],[[0,0],[0]],[[3828,0],[0]],[[0,0],[0]],[[7632,0],[0]],[[0,0],[0]],[[9084,6],[6]],[[0,0],[0]],[[6264,42],[42]],[[0,0],[0]],[[2268,96],[96]],[[0,0],[0]],[[324,78],[78]],[[0,0],[0]],[[0,18],[18]]]
theorem step172 : p172=NestedArithmetic.mul p171 p003 := by decide +kernel
#print axioms step172
theorem h172 : NestedArithmetic.compile e172=p172 := StagedExprCompile.compile_times e172 e171 e003 p171 p003 p172 rfl h171 h003 step172
#print axioms h172
end Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
