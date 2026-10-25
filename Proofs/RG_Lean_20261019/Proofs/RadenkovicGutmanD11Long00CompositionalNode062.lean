/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD11Long00CompositionalNode044
import Proofs.RadenkovicGutmanD11Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e062 : NestedArithmetic.Expr 3 := .times e044 e052
noncomputable def p062 : NestedHorner.Poly 3 := [[[0],[0,11]],[[0,0],[0,0]],[[99,99],[99,2]],[[0,0],[0]],[[1767,282],[282]],[[0,0],[0]],[[7985,290],[290]],[[0,0],[0]],[[17124,132],[132]],[[0,0],[0]],[[20944,27],[27]],[[0,0],[0]],[[15784,2],[2]],[[0]],[[7563]],[[0]],[[2304]],[[0]],[[431]],[[0]],[[45]],[[0]],[[2]]]
theorem step062 : p062=NestedArithmetic.mul p044 p052 := by decide +kernel
#print axioms step062
theorem h062 : NestedArithmetic.compile e062=p062 := StagedExprCompile.compile_times e062 e044 e052 p044 p052 p062 rfl h044 h052 step062
#print axioms h062
end Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
