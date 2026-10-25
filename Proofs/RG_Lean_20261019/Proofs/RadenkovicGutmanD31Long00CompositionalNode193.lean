/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD31Long00CompositionalNode192
import Proofs.RadenkovicGutmanD31Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e193 : NestedArithmetic.Expr 3 := .times e192 e122
noncomputable def p193 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[61,0],[0,0]],[[0,0],[0,0]],[[653,0],[0,0]],[[0,0],[0,0]],[[3552,0],[0,0]],[[0,0],[0,0]],[[11161,0],[0,0]],[[0,0],[0,0]],[[21228,2],[2,0]],[[0,0],[0,0]],[[24464,47],[47,0]],[[0,0],[0,0]],[[16268,292],[292,0]],[[0,0],[0,0]],[[5183,730],[730,0]],[[0,0],[0,0]],[[75,762],[762,0]],[[0,0],[0,0]],[[-279,279],[279,2]],[[0],[0,0]],[[0],[0,31]]]
theorem step193 : p193=NestedArithmetic.mul p192 p122 := by decide +kernel
#print axioms step193
theorem h193 : NestedArithmetic.compile e193=p193 := StagedExprCompile.compile_times e193 e192 e122 p192 p122 p193 rfl h192 h122 step193
#print axioms h193
end Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
