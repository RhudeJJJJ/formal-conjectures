/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD32Long00CompositionalNode202
import Proofs.RadenkovicGutmanD32Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e203 : NestedArithmetic.Expr 3 := .times e202 e122
noncomputable def p203 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[66,0],[0,0]],[[0,0],[0,0]],[[788,0],[0,0]],[[0,0],[0,0]],[[4866,0],[0,0]],[[0,0],[0,0]],[[17664,0],[0,0]],[[0,0],[0,0]],[[39640,2],[2,0]],[[0,0],[0,0]],[[55468,48],[48,0]],[[0,0],[0,0]],[[47154,300],[300,0]],[[0,0],[0,0]],[[22622,752],[752,0]],[[0,0],[0,0]],[[5106,786],[786,0]],[[0,0],[0,0]],[[288,288],[288,2]],[[0],[0,0]],[[0],[0,32]]]
theorem step203 : p203=NestedArithmetic.mul p202 p122 := by decide +kernel
#print axioms step203
theorem h203 : NestedArithmetic.compile e203=p203 := StagedExprCompile.compile_times e203 e202 e122 p202 p122 p203 rfl h202 h122 step203
#print axioms h203
end Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
