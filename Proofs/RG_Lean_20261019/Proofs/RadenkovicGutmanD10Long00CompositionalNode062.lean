/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD10Long00CompositionalNode044
import Proofs.RadenkovicGutmanD10Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e062 : NestedArithmetic.Expr 3 := .times e044 e052
noncomputable def p062 : NestedHorner.Poly 3 := [[[0],[0,10]],[[0,0],[0,0]],[[90,90],[90,2]],[[0,0],[0]],[[1608,258],[258]],[[0,0],[0]],[[7288,268],[268]],[[0,0],[0]],[[15694,124],[124]],[[0,0],[0]],[[19300,26],[26]],[[0,0],[0]],[[14648,2],[2]],[[0]],[[7082]],[[0]],[[2182]],[[0]],[[414]],[[0]],[[44]],[[0]],[[2]]]
theorem step062 : p062=NestedArithmetic.mul p044 p052 := by decide +kernel
#print axioms step062
theorem h062 : NestedArithmetic.compile e062=p062 := StagedExprCompile.compile_times e062 e044 e052 p044 p052 p062 rfl h044 h052 step062
#print axioms h062
end Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
