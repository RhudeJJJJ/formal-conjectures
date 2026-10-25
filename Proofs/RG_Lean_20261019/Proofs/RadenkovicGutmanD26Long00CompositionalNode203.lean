/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD26Long00CompositionalNode202
import Proofs.RadenkovicGutmanD26Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e203 : NestedArithmetic.Expr 3 := .times e202 e122
noncomputable def p203 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[60,0],[0,0]],[[0,0],[0,0]],[[686,0],[0,0]],[[0,0],[0,0]],[[4134,0],[0,0]],[[0,0],[0,0]],[[14778,0],[0,0]],[[0,0],[0,0]],[[32824,2],[2,0]],[[0,0],[0,0]],[[45604,42],[42,0]],[[0,0],[0,0]],[[38574,252],[252,0]],[[0,0],[0,0]],[[18440,620],[620,0]],[[0,0],[0,0]],[[4152,642],[642,0]],[[0,0],[0,0]],[[234,234],[234,2]],[[0],[0,0]],[[0],[0,26]]]
theorem step203 : p203=NestedArithmetic.mul p202 p122 := by decide +kernel
#print axioms step203
theorem h203 : NestedArithmetic.compile e203=p203 := StagedExprCompile.compile_times e203 e202 e122 p202 p122 p203 rfl h202 h122 step203
#print axioms h203
end Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
