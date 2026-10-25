/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD34Long00CompositionalNode044
import Proofs.RadenkovicGutmanD34Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e045 : NestedArithmetic.Expr 3 := .times e044 e032
noncomputable def p045 : NestedHorner.Poly 3 := [[[0],[0,34]],[[0,0],[0,0]],[[-306,306],[306,2]],[[0,0],[0]],[[84,834],[834]],[[0,0],[0]],[[5684,796],[796]],[[0,0],[0]],[[17810,316],[316]],[[0,0],[0]],[[26732,50],[50]],[[0,0],[0]],[[23136,2],[2]],[[0]],[[12118]],[[0]],[[3834]],[[0]],[[698]],[[0]],[[64]],[[0]],[[2]]]
theorem step045 : p045=NestedArithmetic.mul p044 p032 := by decide +kernel
#print axioms step045
theorem h045 : NestedArithmetic.compile e045=p045 := StagedExprCompile.compile_times e045 e044 e032 p044 p032 p045 rfl h044 h032 step045
#print axioms h045
end Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
