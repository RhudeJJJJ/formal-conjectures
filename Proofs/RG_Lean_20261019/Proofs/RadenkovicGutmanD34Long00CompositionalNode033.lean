/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD34Long00CompositionalNode030
import Proofs.RadenkovicGutmanD34Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e033 : NestedArithmetic.Expr 3 := .times e030 e032
noncomputable def p033 : NestedHorner.Poly 3 := [[[0],[0,34]],[[0,0],[0]],[[-306,306],[306]],[[0,0],[0]],[[102,816],[816]],[[0,0],[0]],[[5678,748],[748]],[[0,0],[0]],[[17476,272],[272]],[[0,0],[0]],[[25704,34],[34]],[[0]],[[21624]],[[0]],[[10846]],[[0]],[[3196]],[[0]],[[510]],[[0]],[[34]]]
theorem step033 : p033=NestedArithmetic.mul p030 p032 := by decide +kernel
#print axioms step033
theorem h033 : NestedArithmetic.compile e033=p033 := StagedExprCompile.compile_times e033 e030 e032 p030 p032 p033 rfl h030 h032 step033
#print axioms h033
end Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
