/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD10Long00CompositionalNode202
import Proofs.RadenkovicGutmanD10Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e203 : NestedArithmetic.Expr 3 := .times e202 e122
noncomputable def p203 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[44,0],[0,0]],[[0,0],[0,0]],[[414,0],[0,0]],[[0,0],[0,0]],[[2182,0],[0,0]],[[0,0],[0,0]],[[7082,0],[0,0]],[[0,0],[0,0]],[[14648,2],[2,0]],[[0,0],[0,0]],[[19300,26],[26,0]],[[0,0],[0,0]],[[15694,124],[124,0]],[[0,0],[0,0]],[[7288,268],[268,0]],[[0,0],[0,0]],[[1608,258],[258,0]],[[0,0],[0,0]],[[90,90],[90,2]],[[0],[0,0]],[[0],[0,10]]]
theorem step203 : p203=NestedArithmetic.mul p202 p122 := by decide +kernel
#print axioms step203
theorem h203 : NestedArithmetic.compile e203=p203 := StagedExprCompile.compile_times e203 e202 e122 p202 p122 p203 rfl h202 h122 step203
#print axioms h203
end Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
