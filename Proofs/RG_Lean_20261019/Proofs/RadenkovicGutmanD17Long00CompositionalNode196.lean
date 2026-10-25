/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD17Long00CompositionalNode195
import Proofs.RadenkovicGutmanD17Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e196 : NestedArithmetic.Expr 3 := .times e195 e003
noncomputable def p196 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[68,0],[0]],[[0,0],[0]],[[1020,0],[0]],[[0,0],[0]],[[6392,0],[0]],[[0,0],[0]],[[21692,0],[0]],[[0,0],[0]],[[43248,0],[0]],[[0,0],[0]],[[51476,34],[34]],[[0,0],[0]],[[35496,238],[238]],[[0,0],[0]],[[12852,544],[544]],[[0,0],[0]],[[1836,442],[442]],[[0,0],[0]],[[0,102],[102]]]
theorem step196 : p196=NestedArithmetic.mul p195 p003 := by decide +kernel
#print axioms step196
theorem h196 : NestedArithmetic.compile e196=p196 := StagedExprCompile.compile_times e196 e195 e003 p195 p003 p196 rfl h195 h003 step196
#print axioms h196
end Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
