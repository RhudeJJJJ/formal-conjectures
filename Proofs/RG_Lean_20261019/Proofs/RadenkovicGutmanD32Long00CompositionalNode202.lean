/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD32Long00CompositionalNode191
import Proofs.RadenkovicGutmanD32Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e202 : NestedArithmetic.Expr 3 := .times e191 e176
noncomputable def p202 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[66,0],[0,0]],[[0,0],[0,0]],[[788,0],[0,0]],[[0,0],[0,0]],[[4866,0],[0,0]],[[0,0],[0,0]],[[17664,0],[0,0]],[[0,0],[0,0]],[[39640,2],[2,0]],[[0,0],[0,0]],[[55468,48],[48,0]],[[0,0],[0,0]],[[47154,300],[300,0]],[[0,0],[0,0]],[[22622,752],[752,0]],[[0,0],[0,0]],[[5106,786],[786,0]],[[0,0],[0,0]],[[288,288],[288,2]],[[0],[0,0]],[[0],[0,32]]]
theorem step202 : p202=NestedArithmetic.mul p191 p176 := by decide +kernel
#print axioms step202
theorem h202 : NestedArithmetic.compile e202=p202 := StagedExprCompile.compile_times e202 e191 e176 p191 p176 p202 rfl h191 h176 step202
#print axioms h202
end Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
