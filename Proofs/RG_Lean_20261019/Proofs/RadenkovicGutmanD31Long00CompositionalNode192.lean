/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD31Long00CompositionalNode191
import Proofs.RadenkovicGutmanD31Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e192 : NestedArithmetic.Expr 3 := .times e191 e158
noncomputable def p192 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[61,0],[0,0]],[[0,0],[0,0]],[[653,0],[0,0]],[[0,0],[0,0]],[[3552,0],[0,0]],[[0,0],[0,0]],[[11161,0],[0,0]],[[0,0],[0,0]],[[21228,2],[2,0]],[[0,0],[0,0]],[[24464,47],[47,0]],[[0,0],[0,0]],[[16268,292],[292,0]],[[0,0],[0,0]],[[5183,730],[730,0]],[[0,0],[0,0]],[[75,762],[762,0]],[[0,0],[0,0]],[[-279,279],[279,2]],[[0],[0,0]],[[0],[0,31]]]
theorem step192 : p192=NestedArithmetic.mul p191 p158 := by decide +kernel
#print axioms step192
theorem h192 : NestedArithmetic.compile e192=p192 := StagedExprCompile.compile_times e192 e191 e158 p191 p158 p192 rfl h191 h158 step192
#print axioms h192
end Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
