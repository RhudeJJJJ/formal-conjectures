/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode035
import Proofs.RadenkovicGutmanD2Long00CompositionalNode039
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e040 : NestedArithmetic.Expr 3 := .times e035 e039
noncomputable def p040 : NestedHorner.Poly 3 := [[[],[]],[[0],[0,0]],[[0,0],[0]],[[72,0],[0]],[[0,0],[0]],[[624,0],[0]],[[0,0],[0]],[[2120,0],[0]],[[0,0],[0]],[[3664,0],[0]],[[0,0],[0]],[[3552,0],[0]],[[0]],[[2000]],[[0]],[[648]],[[0]],[[112]],[[0]],[[8]],[[0]],[[0]]]
theorem step040 : p040=NestedArithmetic.mul p035 p039 := by decide +kernel
#print axioms step040
theorem h040 : NestedArithmetic.compile e040=p040 := StagedExprCompile.compile_times e040 e035 e039 p035 p039 p040 rfl h035 h039 step040
#print axioms h040
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
