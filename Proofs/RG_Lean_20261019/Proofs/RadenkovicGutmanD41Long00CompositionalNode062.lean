/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD41Long00CompositionalNode044
import Proofs.RadenkovicGutmanD41Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e062 : NestedArithmetic.Expr 3 := .times e044 e052
noncomputable def p062 : NestedHorner.Poly 3 := [[[0],[0,41]],[[0,0],[0,0]],[[369,369],[369,2]],[[0,0],[0]],[[6537,1002],[1002]],[[0,0],[0]],[[28895,950],[950]],[[0,0],[0]],[[60024,372],[372]],[[0,0],[0]],[[70264,57],[57]],[[0,0],[0]],[[49864,2],[2]],[[0]],[[21993]],[[0]],[[5964]],[[0]],[[941]],[[0]],[[75]],[[0]],[[2]]]
theorem step062 : p062=NestedArithmetic.mul p044 p052 := by decide +kernel
#print axioms step062
theorem h062 : NestedArithmetic.compile e062=p062 := StagedExprCompile.compile_times e062 e044 e052 p044 p052 p062 rfl h044 h052 step062
#print axioms h062
end Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
