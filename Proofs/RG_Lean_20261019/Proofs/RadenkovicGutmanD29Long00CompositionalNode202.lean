/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD29Long00CompositionalNode191
import Proofs.RadenkovicGutmanD29Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e202 : NestedArithmetic.Expr 3 := .times e191 e176
noncomputable def p202 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[63,0],[0,0]],[[0,0],[0,0]],[[737,0],[0,0]],[[0,0],[0,0]],[[4500,0],[0,0]],[[0,0],[0,0]],[[16221,0],[0,0]],[[0,0],[0,0]],[[36232,2],[2,0]],[[0,0],[0,0]],[[50536,45],[45,0]],[[0,0],[0,0]],[[42864,276],[276,0]],[[0,0],[0,0]],[[20531,686],[686,0]],[[0,0],[0,0]],[[4629,714],[714,0]],[[0,0],[0,0]],[[261,261],[261,2]],[[0],[0,0]],[[0],[0,29]]]
theorem step202 : p202=NestedArithmetic.mul p191 p176 := by decide +kernel
#print axioms step202
theorem h202 : NestedArithmetic.compile e202=p202 := StagedExprCompile.compile_times e202 e191 e176 p191 p176 p202 rfl h191 h176 step202
#print axioms h202
end Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
