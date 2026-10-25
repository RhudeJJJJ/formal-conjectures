/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD30Long00CompositionalNode195
import Proofs.RadenkovicGutmanD30Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e196 : NestedArithmetic.Expr 3 := .times e195 e003
noncomputable def p196 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[120,0],[0]],[[0,0],[0]],[[1800,0],[0]],[[0,0],[0]],[[11280,0],[0]],[[0,0],[0]],[[38280,0],[0]],[[0,0],[0]],[[76320,0],[0]],[[0,0],[0]],[[90840,60],[60]],[[0,0],[0]],[[62640,420],[420]],[[0,0],[0]],[[22680,960],[960]],[[0,0],[0]],[[3240,780],[780]],[[0,0],[0]],[[0,180],[180]]]
theorem step196 : p196=NestedArithmetic.mul p195 p003 := by decide +kernel
#print axioms step196
theorem h196 : NestedArithmetic.compile e196=p196 := StagedExprCompile.compile_times e196 e195 e003 p195 p003 p196 rfl h195 h003 step196
#print axioms h196
end Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
