/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD29Long00CompositionalNode202
import Proofs.RadenkovicGutmanD29Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e203 : NestedArithmetic.Expr 3 := .times e202 e122
noncomputable def p203 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[63,0],[0,0]],[[0,0],[0,0]],[[737,0],[0,0]],[[0,0],[0,0]],[[4500,0],[0,0]],[[0,0],[0,0]],[[16221,0],[0,0]],[[0,0],[0,0]],[[36232,2],[2,0]],[[0,0],[0,0]],[[50536,45],[45,0]],[[0,0],[0,0]],[[42864,276],[276,0]],[[0,0],[0,0]],[[20531,686],[686,0]],[[0,0],[0,0]],[[4629,714],[714,0]],[[0,0],[0,0]],[[261,261],[261,2]],[[0],[0,0]],[[0],[0,29]]]
theorem step203 : p203=NestedArithmetic.mul p202 p122 := by decide +kernel
#print axioms step203
theorem h203 : NestedArithmetic.compile e203=p203 := StagedExprCompile.compile_times e203 e202 e122 p202 p122 p203 rfl h202 h122 step203
#print axioms h203
end Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
