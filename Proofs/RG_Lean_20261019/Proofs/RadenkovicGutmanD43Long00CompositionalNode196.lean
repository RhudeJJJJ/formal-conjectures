/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD43Long00CompositionalNode195
import Proofs.RadenkovicGutmanD43Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e196 : NestedArithmetic.Expr 3 := .times e195 e003
noncomputable def p196 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[172,0],[0]],[[0,0],[0]],[[2580,0],[0]],[[0,0],[0]],[[16168,0],[0]],[[0,0],[0]],[[54868,0],[0]],[[0,0],[0]],[[109392,0],[0]],[[0,0],[0]],[[130204,86],[86]],[[0,0],[0]],[[89784,602],[602]],[[0,0],[0]],[[32508,1376],[1376]],[[0,0],[0]],[[4644,1118],[1118]],[[0,0],[0]],[[0,258],[258]]]
theorem step196 : p196=NestedArithmetic.mul p195 p003 := by decide +kernel
#print axioms step196
theorem h196 : NestedArithmetic.compile e196=p196 := StagedExprCompile.compile_times e196 e195 e003 p195 p003 p196 rfl h195 h003 step196
#print axioms h196
end Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
