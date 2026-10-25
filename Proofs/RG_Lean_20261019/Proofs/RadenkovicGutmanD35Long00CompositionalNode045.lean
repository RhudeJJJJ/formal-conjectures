/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD35Long00CompositionalNode044
import Proofs.RadenkovicGutmanD35Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e045 : NestedArithmetic.Expr 3 := .times e044 e032
noncomputable def p045 : NestedHorner.Poly 3 := [[[0],[0,35]],[[0,0],[0,0]],[[-315,315],[315,2]],[[0,0],[0]],[[87,858],[858]],[[0,0],[0]],[[5851,818],[818]],[[0,0],[0]],[[18324,324],[324]],[[0,0],[0]],[[27488,51],[51]],[[0,0],[0]],[[23772,2],[2]],[[0]],[[12437]],[[0]],[[3928]],[[0]],[[713]],[[0]],[[65]],[[0]],[[2]]]
theorem step045 : p045=NestedArithmetic.mul p044 p032 := by decide +kernel
#print axioms step045
theorem h045 : NestedArithmetic.compile e045=p045 := StagedExprCompile.compile_times e045 e044 e032 p044 p032 p045 rfl h044 h032 step045
#print axioms h045
end Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
