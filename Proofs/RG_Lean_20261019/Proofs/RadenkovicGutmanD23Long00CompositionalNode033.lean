/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD23Long00CompositionalNode030
import Proofs.RadenkovicGutmanD23Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e033 : NestedArithmetic.Expr 3 := .times e030 e032
noncomputable def p033 : NestedHorner.Poly 3 := [[[0],[0,23]],[[0,0],[0]],[[-207,207],[207]],[[0,0],[0]],[[69,552],[552]],[[0,0],[0]],[[3841,506],[506]],[[0,0],[0]],[[11822,184],[184]],[[0,0],[0]],[[17388,23],[23]],[[0]],[[14628]],[[0]],[[7337]],[[0]],[[2162]],[[0]],[[345]],[[0]],[[23]]]
theorem step033 : p033=NestedArithmetic.mul p030 p032 := by decide +kernel
#print axioms step033
theorem h033 : NestedArithmetic.compile e033=p033 := StagedExprCompile.compile_times e033 e030 e032 p030 p032 p033 rfl h030 h032 step033
#print axioms h033
end Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
