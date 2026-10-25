/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD10Long00CompositionalNode191
import Proofs.RadenkovicGutmanD10Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e202 : NestedArithmetic.Expr 3 := .times e191 e176
noncomputable def p202 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[44,0],[0,0]],[[0,0],[0,0]],[[414,0],[0,0]],[[0,0],[0,0]],[[2182,0],[0,0]],[[0,0],[0,0]],[[7082,0],[0,0]],[[0,0],[0,0]],[[14648,2],[2,0]],[[0,0],[0,0]],[[19300,26],[26,0]],[[0,0],[0,0]],[[15694,124],[124,0]],[[0,0],[0,0]],[[7288,268],[268,0]],[[0,0],[0,0]],[[1608,258],[258,0]],[[0,0],[0,0]],[[90,90],[90,2]],[[0],[0,0]],[[0],[0,10]]]
theorem step202 : p202=NestedArithmetic.mul p191 p176 := by decide +kernel
#print axioms step202
theorem h202 : NestedArithmetic.compile e202=p202 := StagedExprCompile.compile_times e202 e191 e176 p191 p176 p202 rfl h191 h176 step202
#print axioms h202
end Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
