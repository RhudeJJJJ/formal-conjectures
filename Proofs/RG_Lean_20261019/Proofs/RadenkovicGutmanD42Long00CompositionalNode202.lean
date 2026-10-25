/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD42Long00CompositionalNode191
import Proofs.RadenkovicGutmanD42Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e202 : NestedArithmetic.Expr 3 := .times e191 e176
noncomputable def p202 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[76,0],[0,0]],[[0,0],[0,0]],[[958,0],[0,0]],[[0,0],[0,0]],[[6086,0],[0,0]],[[0,0],[0,0]],[[22474,0],[0,0]],[[0,0],[0,0]],[[51000,2],[2,0]],[[0,0],[0,0]],[[71908,58],[58,0]],[[0,0],[0,0]],[[61454,380],[380,0]],[[0,0],[0,0]],[[29592,972],[972,0]],[[0,0],[0,0]],[[6696,1026],[1026,0]],[[0,0],[0,0]],[[378,378],[378,2]],[[0],[0,0]],[[0],[0,42]]]
theorem step202 : p202=NestedArithmetic.mul p191 p176 := by decide +kernel
#print axioms step202
theorem h202 : NestedArithmetic.compile e202=p202 := StagedExprCompile.compile_times e202 e191 e176 p191 p176 p202 rfl h191 h176 step202
#print axioms h202
end Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
