/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD36Long00CompositionalNode195
import Proofs.RadenkovicGutmanD36Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e196 : NestedArithmetic.Expr 3 := .times e195 e003
noncomputable def p196 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[144,0],[0]],[[0,0],[0]],[[2160,0],[0]],[[0,0],[0]],[[13536,0],[0]],[[0,0],[0]],[[45936,0],[0]],[[0,0],[0]],[[91584,0],[0]],[[0,0],[0]],[[109008,72],[72]],[[0,0],[0]],[[75168,504],[504]],[[0,0],[0]],[[27216,1152],[1152]],[[0,0],[0]],[[3888,936],[936]],[[0,0],[0]],[[0,216],[216]]]
theorem step196 : p196=NestedArithmetic.mul p195 p003 := by decide +kernel
#print axioms step196
theorem h196 : NestedArithmetic.compile e196=p196 := StagedExprCompile.compile_times e196 e195 e003 p195 p003 p196 rfl h195 h003 step196
#print axioms h196
end Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
