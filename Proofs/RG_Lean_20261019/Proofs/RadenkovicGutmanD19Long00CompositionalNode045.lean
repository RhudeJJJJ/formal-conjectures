/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD19Long00CompositionalNode044
import Proofs.RadenkovicGutmanD19Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e045 : NestedArithmetic.Expr 3 := .times e044 e032
noncomputable def p045 : NestedHorner.Poly 3 := [[[0],[0,19]],[[0,0],[0,0]],[[-171,171],[171,2]],[[0,0],[0]],[[39,474],[474]],[[0,0],[0]],[[3179,466],[466]],[[0,0],[0]],[[10100,196],[196]],[[0,0],[0]],[[15392,35],[35]],[[0,0],[0]],[[13596,2],[2]],[[0]],[[7333]],[[0]],[[2424]],[[0]],[[473]],[[0]],[[49]],[[0]],[[2]]]
theorem step045 : p045=NestedArithmetic.mul p044 p032 := by decide +kernel
#print axioms step045
theorem h045 : NestedArithmetic.compile e045=p045 := StagedExprCompile.compile_times e045 e044 e032 p044 p032 p045 rfl h044 h032 step045
#print axioms h045
end Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
