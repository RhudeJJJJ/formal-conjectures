/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD7Long00CompositionalNode195
import Proofs.RadenkovicGutmanD7Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e196 : NestedArithmetic.Expr 3 := .times e195 e003
noncomputable def p196 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[28,0],[0]],[[0,0],[0]],[[420,0],[0]],[[0,0],[0]],[[2632,0],[0]],[[0,0],[0]],[[8932,0],[0]],[[0,0],[0]],[[17808,0],[0]],[[0,0],[0]],[[21196,14],[14]],[[0,0],[0]],[[14616,98],[98]],[[0,0],[0]],[[5292,224],[224]],[[0,0],[0]],[[756,182],[182]],[[0,0],[0]],[[0,42],[42]]]
theorem step196 : p196=NestedArithmetic.mul p195 p003 := by decide +kernel
#print axioms step196
theorem h196 : NestedArithmetic.compile e196=p196 := StagedExprCompile.compile_times e196 e195 e003 p195 p003 p196 rfl h195 h003 step196
#print axioms h196
end Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
