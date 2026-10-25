/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD35Long00CompositionalNode191
import Proofs.RadenkovicGutmanD35Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e192 : NestedArithmetic.Expr 3 := .times e191 e158
noncomputable def p192 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[65,0],[0,0]],[[0,0],[0,0]],[[713,0],[0,0]],[[0,0],[0,0]],[[3928,0],[0,0]],[[0,0],[0,0]],[[12437,0],[0,0]],[[0,0],[0,0]],[[23772,2],[2,0]],[[0,0],[0,0]],[[27488,51],[51,0]],[[0,0],[0,0]],[[18324,324],[324,0]],[[0,0],[0,0]],[[5851,818],[818,0]],[[0,0],[0,0]],[[87,858],[858,0]],[[0,0],[0,0]],[[-315,315],[315,2]],[[0],[0,0]],[[0],[0,35]]]
theorem step192 : p192=NestedArithmetic.mul p191 p158 := by decide +kernel
#print axioms step192
theorem h192 : NestedArithmetic.compile e192=p192 := StagedExprCompile.compile_times e192 e191 e158 p191 p158 p192 rfl h191 h158 step192
#print axioms h192
end Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
