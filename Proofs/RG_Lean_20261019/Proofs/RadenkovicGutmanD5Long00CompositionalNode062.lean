/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode044
import Proofs.RadenkovicGutmanD5Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e062 : NestedArithmetic.Expr 3 := .times e044 e052
noncomputable def p062 : NestedHorner.Poly 3 := [[[0],[0,5]],[[0,0],[0,0]],[[45,45],[45,2]],[[0,0],[0]],[[813,138],[138]],[[0,0],[0]],[[3803,158],[158]],[[0,0],[0]],[[8544,84],[84]],[[0,0],[0]],[[11080,21],[21]],[[0,0],[0]],[[8968,2],[2]],[[0]],[[4677]],[[0]],[[1572]],[[0]],[[329]],[[0]],[[39]],[[0]],[[2]]]
theorem step062 : p062=NestedArithmetic.mul p044 p052 := by decide +kernel
#print axioms step062
theorem h062 : NestedArithmetic.compile e062=p062 := StagedExprCompile.compile_times e062 e044 e052 p044 p052 p062 rfl h044 h052 step062
#print axioms h062
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
