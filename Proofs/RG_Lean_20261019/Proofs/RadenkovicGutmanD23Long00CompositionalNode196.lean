/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD23Long00CompositionalNode195
import Proofs.RadenkovicGutmanD23Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e196 : NestedArithmetic.Expr 3 := .times e195 e003
noncomputable def p196 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[92,0],[0]],[[0,0],[0]],[[1380,0],[0]],[[0,0],[0]],[[8648,0],[0]],[[0,0],[0]],[[29348,0],[0]],[[0,0],[0]],[[58512,0],[0]],[[0,0],[0]],[[69644,46],[46]],[[0,0],[0]],[[48024,322],[322]],[[0,0],[0]],[[17388,736],[736]],[[0,0],[0]],[[2484,598],[598]],[[0,0],[0]],[[0,138],[138]]]
theorem step196 : p196=NestedArithmetic.mul p195 p003 := by decide +kernel
#print axioms step196
theorem h196 : NestedArithmetic.compile e196=p196 := StagedExprCompile.compile_times e196 e195 e003 p195 p003 p196 rfl h195 h003 step196
#print axioms h196
end Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
