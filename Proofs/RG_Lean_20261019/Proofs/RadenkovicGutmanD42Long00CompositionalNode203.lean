/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD42Long00CompositionalNode202
import Proofs.RadenkovicGutmanD42Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e203 : NestedArithmetic.Expr 3 := .times e202 e122
noncomputable def p203 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[76,0],[0,0]],[[0,0],[0,0]],[[958,0],[0,0]],[[0,0],[0,0]],[[6086,0],[0,0]],[[0,0],[0,0]],[[22474,0],[0,0]],[[0,0],[0,0]],[[51000,2],[2,0]],[[0,0],[0,0]],[[71908,58],[58,0]],[[0,0],[0,0]],[[61454,380],[380,0]],[[0,0],[0,0]],[[29592,972],[972,0]],[[0,0],[0,0]],[[6696,1026],[1026,0]],[[0,0],[0,0]],[[378,378],[378,2]],[[0],[0,0]],[[0],[0,42]]]
theorem step203 : p203=NestedArithmetic.mul p202 p122 := by decide +kernel
#print axioms step203
theorem h203 : NestedArithmetic.compile e203=p203 := StagedExprCompile.compile_times e203 e202 e122 p202 p122 p203 rfl h202 h122 step203
#print axioms h203
end Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
