/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD13Long00CompositionalNode203
import Proofs.RadenkovicGutmanD13Long00CompositionalNode205
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e206 : NestedArithmetic.Expr 3 := .plus e203 e205
noncomputable def p206 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[73,0],[0,0]],[[0,0],[0,0]],[[881,0],[0,0]],[[0,0],[0,0]],[[5330,0],[0,0]],[[0,0],[0,0]],[[18613,0],[0,0]],[[0,0],[0,0]],[[39584,2],[2,0]],[[0,0],[0,0]],[[51688,55],[55,0]],[[0,0],[0,0]],[[40238,330],[330,0]],[[0,0],[0,0]],[[17179,750],[750,0]],[[0,0],[0,0]],[[3255,668],[668,0]],[[0,0],[0,0]],[[117,195],[195,2]],[[0],[0,0]],[[0],[0,13]]]
theorem step206 : p206=NestedHorner.add p203 p205 := by decide +kernel
#print axioms step206
theorem h206 : NestedArithmetic.compile e206=p206 := StagedExprCompile.compile_plus e206 e203 e205 p203 p205 p206 rfl h203 h205 step206
#print axioms h206
end Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
