/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD34Long00CompositionalNode044
import Proofs.RadenkovicGutmanD34Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e062 : NestedArithmetic.Expr 3 := .times e044 e052
noncomputable def p062 : NestedHorner.Poly 3 := [[[0],[0,34]],[[0,0],[0,0]],[[306,306],[306,2]],[[0,0],[0]],[[5424,834],[834]],[[0,0],[0]],[[24016,796],[796]],[[0,0],[0]],[[50014,316],[316]],[[0,0],[0]],[[58756,50],[50]],[[0,0],[0]],[[41912,2],[2]],[[0]],[[18626]],[[0]],[[5110]],[[0]],[[822]],[[0]],[[68]],[[0]],[[2]]]
theorem step062 : p062=NestedArithmetic.mul p044 p052 := by decide +kernel
#print axioms step062
theorem h062 : NestedArithmetic.compile e062=p062 := StagedExprCompile.compile_times e062 e044 e052 p044 p052 p062 rfl h044 h052 step062
#print axioms h062
end Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
