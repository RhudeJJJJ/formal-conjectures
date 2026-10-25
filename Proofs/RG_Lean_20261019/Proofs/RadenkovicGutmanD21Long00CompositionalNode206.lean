/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD21Long00CompositionalNode203
import Proofs.RadenkovicGutmanD21Long00CompositionalNode205
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e206 : NestedArithmetic.Expr 3 := .plus e203 e205
noncomputable def p206 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[97,0],[0,0]],[[0,0],[0,0]],[[1273,0],[0,0]],[[0,0],[0,0]],[[8018,0],[0,0]],[[0,0],[0,0]],[[28669,0],[0,0]],[[0,0],[0,0]],[[61920,2],[2,0]],[[0,0],[0,0]],[[81736,79],[79,0]],[[0,0],[0,0]],[[64142,506],[506,0]],[[0,0],[0,0]],[[27555,1182],[1182,0]],[[0,0],[0,0]],[[5247,1068],[1068,0]],[[0,0],[0,0]],[[189,315],[315,2]],[[0],[0,0]],[[0],[0,21]]]
theorem step206 : p206=NestedHorner.add p203 p205 := by decide +kernel
#print axioms step206
theorem h206 : NestedArithmetic.compile e206=p206 := StagedExprCompile.compile_plus e206 e203 e205 p203 p205 p206 rfl h203 h205 step206
#print axioms h206
end Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
