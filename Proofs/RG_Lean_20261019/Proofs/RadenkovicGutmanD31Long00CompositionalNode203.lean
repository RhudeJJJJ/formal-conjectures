/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD31Long00CompositionalNode202
import Proofs.RadenkovicGutmanD31Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e203 : NestedArithmetic.Expr 3 := .times e202 e122
noncomputable def p203 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[65,0],[0,0]],[[0,0],[0,0]],[[771,0],[0,0]],[[0,0],[0,0]],[[4744,0],[0,0]],[[0,0],[0,0]],[[17183,0],[0,0]],[[0,0],[0,0]],[[38504,2],[2,0]],[[0,0],[0,0]],[[53824,47],[47,0]],[[0,0],[0,0]],[[45724,292],[292,0]],[[0,0],[0,0]],[[21925,730],[730,0]],[[0,0],[0,0]],[[4947,762],[762,0]],[[0,0],[0,0]],[[279,279],[279,2]],[[0],[0,0]],[[0],[0,31]]]
theorem step203 : p203=NestedArithmetic.mul p202 p122 := by decide +kernel
#print axioms step203
theorem h203 : NestedArithmetic.compile e203=p203 := StagedExprCompile.compile_times e203 e202 e122 p202 p122 p203 rfl h202 h122 step203
#print axioms h203
end Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
