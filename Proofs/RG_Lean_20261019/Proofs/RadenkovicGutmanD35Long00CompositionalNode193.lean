/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD35Long00CompositionalNode192
import Proofs.RadenkovicGutmanD35Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e193 : NestedArithmetic.Expr 3 := .times e192 e122
noncomputable def p193 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[65,0],[0,0]],[[0,0],[0,0]],[[713,0],[0,0]],[[0,0],[0,0]],[[3928,0],[0,0]],[[0,0],[0,0]],[[12437,0],[0,0]],[[0,0],[0,0]],[[23772,2],[2,0]],[[0,0],[0,0]],[[27488,51],[51,0]],[[0,0],[0,0]],[[18324,324],[324,0]],[[0,0],[0,0]],[[5851,818],[818,0]],[[0,0],[0,0]],[[87,858],[858,0]],[[0,0],[0,0]],[[-315,315],[315,2]],[[0],[0,0]],[[0],[0,35]]]
theorem step193 : p193=NestedArithmetic.mul p192 p122 := by decide +kernel
#print axioms step193
theorem h193 : NestedArithmetic.compile e193=p193 := StagedExprCompile.compile_times e193 e192 e122 p192 p122 p193 rfl h192 h122 step193
#print axioms h193
end Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
