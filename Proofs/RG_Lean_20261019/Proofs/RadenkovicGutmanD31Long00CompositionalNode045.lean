/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD31Long00CompositionalNode044
import Proofs.RadenkovicGutmanD31Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e045 : NestedArithmetic.Expr 3 := .times e044 e032
noncomputable def p045 : NestedHorner.Poly 3 := [[[0],[0,31]],[[0,0],[0,0]],[[-279,279],[279,2]],[[0,0],[0]],[[75,762],[762]],[[0,0],[0]],[[5183,730],[730]],[[0,0],[0]],[[16268,292],[292]],[[0,0],[0]],[[24464,47],[47]],[[0,0],[0]],[[21228,2],[2]],[[0]],[[11161]],[[0]],[[3552]],[[0]],[[653]],[[0]],[[61]],[[0]],[[2]]]
theorem step045 : p045=NestedArithmetic.mul p044 p032 := by decide +kernel
#print axioms step045
theorem h045 : NestedArithmetic.compile e045=p045 := StagedExprCompile.compile_times e045 e044 e032 p044 p032 p045 rfl h044 h032 step045
#print axioms h045
end Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
