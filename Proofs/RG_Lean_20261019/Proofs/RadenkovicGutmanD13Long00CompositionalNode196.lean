/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD13Long00CompositionalNode195
import Proofs.RadenkovicGutmanD13Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e196 : NestedArithmetic.Expr 3 := .times e195 e003
noncomputable def p196 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[52,0],[0]],[[0,0],[0]],[[780,0],[0]],[[0,0],[0]],[[4888,0],[0]],[[0,0],[0]],[[16588,0],[0]],[[0,0],[0]],[[33072,0],[0]],[[0,0],[0]],[[39364,26],[26]],[[0,0],[0]],[[27144,182],[182]],[[0,0],[0]],[[9828,416],[416]],[[0,0],[0]],[[1404,338],[338]],[[0,0],[0]],[[0,78],[78]]]
theorem step196 : p196=NestedArithmetic.mul p195 p003 := by decide +kernel
#print axioms step196
theorem h196 : NestedArithmetic.compile e196=p196 := StagedExprCompile.compile_times e196 e195 e003 p195 p003 p196 rfl h195 h003 step196
#print axioms h196
end Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
