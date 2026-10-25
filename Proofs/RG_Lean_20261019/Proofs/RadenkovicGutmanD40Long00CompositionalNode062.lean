/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD40Long00CompositionalNode044
import Proofs.RadenkovicGutmanD40Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e062 : NestedArithmetic.Expr 3 := .times e044 e052
noncomputable def p062 : NestedHorner.Poly 3 := [[[0],[0,40]],[[0,0],[0,0]],[[360,360],[360,2]],[[0,0],[0]],[[6378,978],[978]],[[0,0],[0]],[[28198,928],[928]],[[0,0],[0]],[[58594,364],[364]],[[0,0],[0]],[[68620,56],[56]],[[0,0],[0]],[[48728,2],[2]],[[0]],[[21512]],[[0]],[[5842]],[[0]],[[924]],[[0]],[[74]],[[0]],[[2]]]
theorem step062 : p062=NestedArithmetic.mul p044 p052 := by decide +kernel
#print axioms step062
theorem h062 : NestedArithmetic.compile e062=p062 := StagedExprCompile.compile_times e062 e044 e052 p044 p052 p062 rfl h044 h052 step062
#print axioms h062
end Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
