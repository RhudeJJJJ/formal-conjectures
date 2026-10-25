/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD31Long00CompositionalNode030
import Proofs.RadenkovicGutmanD31Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e033 : NestedArithmetic.Expr 3 := .times e030 e032
noncomputable def p033 : NestedHorner.Poly 3 := [[[0],[0,31]],[[0,0],[0]],[[-279,279],[279]],[[0,0],[0]],[[93,744],[744]],[[0,0],[0]],[[5177,682],[682]],[[0,0],[0]],[[15934,248],[248]],[[0,0],[0]],[[23436,31],[31]],[[0]],[[19716]],[[0]],[[9889]],[[0]],[[2914]],[[0]],[[465]],[[0]],[[31]]]
theorem step033 : p033=NestedArithmetic.mul p030 p032 := by decide +kernel
#print axioms step033
theorem h033 : NestedArithmetic.compile e033=p033 := StagedExprCompile.compile_times e033 e030 e032 p030 p032 p033 rfl h030 h032 step033
#print axioms h033
end Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
