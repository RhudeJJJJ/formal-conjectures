/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD22Long00CompositionalNode191
import Proofs.RadenkovicGutmanD22Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e202 : NestedArithmetic.Expr 3 := .times e191 e176
noncomputable def p202 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[56,0],[0,0]],[[0,0],[0,0]],[[618,0],[0,0]],[[0,0],[0,0]],[[3646,0],[0,0]],[[0,0],[0,0]],[[12854,0],[0,0]],[[0,0],[0,0]],[[28280,2],[2,0]],[[0,0],[0,0]],[[39028,38],[38,0]],[[0,0],[0,0]],[[32854,220],[220,0]],[[0,0],[0,0]],[[15652,532],[532,0]],[[0,0],[0,0]],[[3516,546],[546,0]],[[0,0],[0,0]],[[198,198],[198,2]],[[0],[0,0]],[[0],[0,22]]]
theorem step202 : p202=NestedArithmetic.mul p191 p176 := by decide +kernel
#print axioms step202
theorem h202 : NestedArithmetic.compile e202=p202 := StagedExprCompile.compile_times e202 e191 e176 p191 p176 p202 rfl h191 h176 step202
#print axioms h202
end Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
