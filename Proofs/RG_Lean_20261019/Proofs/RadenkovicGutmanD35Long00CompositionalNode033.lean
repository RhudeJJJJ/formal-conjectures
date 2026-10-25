/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD35Long00CompositionalNode030
import Proofs.RadenkovicGutmanD35Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e033 : NestedArithmetic.Expr 3 := .times e030 e032
noncomputable def p033 : NestedHorner.Poly 3 := [[[0],[0,35]],[[0,0],[0]],[[-315,315],[315]],[[0,0],[0]],[[105,840],[840]],[[0,0],[0]],[[5845,770],[770]],[[0,0],[0]],[[17990,280],[280]],[[0,0],[0]],[[26460,35],[35]],[[0]],[[22260]],[[0]],[[11165]],[[0]],[[3290]],[[0]],[[525]],[[0]],[[35]]]
theorem step033 : p033=NestedArithmetic.mul p030 p032 := by decide +kernel
#print axioms step033
theorem h033 : NestedArithmetic.compile e033=p033 := StagedExprCompile.compile_times e033 e030 e032 p030 p032 p033 rfl h030 h032 step033
#print axioms h033
end Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
