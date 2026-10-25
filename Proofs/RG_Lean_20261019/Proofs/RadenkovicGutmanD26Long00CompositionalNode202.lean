/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD26Long00CompositionalNode191
import Proofs.RadenkovicGutmanD26Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e202 : NestedArithmetic.Expr 3 := .times e191 e176
noncomputable def p202 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[60,0],[0,0]],[[0,0],[0,0]],[[686,0],[0,0]],[[0,0],[0,0]],[[4134,0],[0,0]],[[0,0],[0,0]],[[14778,0],[0,0]],[[0,0],[0,0]],[[32824,2],[2,0]],[[0,0],[0,0]],[[45604,42],[42,0]],[[0,0],[0,0]],[[38574,252],[252,0]],[[0,0],[0,0]],[[18440,620],[620,0]],[[0,0],[0,0]],[[4152,642],[642,0]],[[0,0],[0,0]],[[234,234],[234,2]],[[0],[0,0]],[[0],[0,26]]]
theorem step202 : p202=NestedArithmetic.mul p191 p176 := by decide +kernel
#print axioms step202
theorem h202 : NestedArithmetic.compile e202=p202 := StagedExprCompile.compile_times e202 e191 e176 p191 p176 p202 rfl h191 h176 step202
#print axioms h202
end Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
