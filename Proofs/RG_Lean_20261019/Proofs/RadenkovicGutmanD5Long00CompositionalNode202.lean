/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode191
import Proofs.RadenkovicGutmanD5Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e202 : NestedArithmetic.Expr 3 := .times e191 e176
noncomputable def p202 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[39,0],[0,0]],[[0,0],[0,0]],[[329,0],[0,0]],[[0,0],[0,0]],[[1572,0],[0,0]],[[0,0],[0,0]],[[4677,0],[0,0]],[[0,0],[0,0]],[[8968,2],[2,0]],[[0,0],[0,0]],[[11080,21],[21,0]],[[0,0],[0,0]],[[8544,84],[84,0]],[[0,0],[0,0]],[[3803,158],[158,0]],[[0,0],[0,0]],[[813,138],[138,0]],[[0,0],[0,0]],[[45,45],[45,2]],[[0],[0,0]],[[0],[0,5]]]
theorem step202 : p202=NestedArithmetic.mul p191 p176 := by decide +kernel
#print axioms step202
theorem h202 : NestedArithmetic.compile e202=p202 := StagedExprCompile.compile_times e202 e191 e176 p191 p176 p202 rfl h191 h176 step202
#print axioms h202
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
