/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD44Long00CompositionalNode044
import Proofs.RadenkovicGutmanD44Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e062 : NestedArithmetic.Expr 3 := .times e044 e052
noncomputable def p062 : NestedHorner.Poly 3 := [[[0],[0,44]],[[0,0],[0,0]],[[396,396],[396,2]],[[0,0],[0]],[[7014,1074],[1074]],[[0,0],[0]],[[30986,1016],[1016]],[[0,0],[0]],[[64314,396],[396]],[[0,0],[0]],[[75196,60],[60]],[[0,0],[0]],[[53272,2],[2]],[[0]],[[23436]],[[0]],[[6330]],[[0]],[[992]],[[0]],[[78]],[[0]],[[2]]]
theorem step062 : p062=NestedArithmetic.mul p044 p052 := by decide +kernel
#print axioms step062
theorem h062 : NestedArithmetic.compile e062=p062 := StagedExprCompile.compile_times e062 e044 e052 p044 p052 p062 rfl h044 h052 step062
#print axioms h062
end Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
