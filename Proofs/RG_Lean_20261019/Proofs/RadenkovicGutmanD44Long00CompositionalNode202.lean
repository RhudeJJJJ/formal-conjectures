/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD44Long00CompositionalNode191
import Proofs.RadenkovicGutmanD44Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e202 : NestedArithmetic.Expr 3 := .times e191 e176
noncomputable def p202 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[78,0],[0,0]],[[0,0],[0,0]],[[992,0],[0,0]],[[0,0],[0,0]],[[6330,0],[0,0]],[[0,0],[0,0]],[[23436,0],[0,0]],[[0,0],[0,0]],[[53272,2],[2,0]],[[0,0],[0,0]],[[75196,60],[60,0]],[[0,0],[0,0]],[[64314,396],[396,0]],[[0,0],[0,0]],[[30986,1016],[1016,0]],[[0,0],[0,0]],[[7014,1074],[1074,0]],[[0,0],[0,0]],[[396,396],[396,2]],[[0],[0,0]],[[0],[0,44]]]
theorem step202 : p202=NestedArithmetic.mul p191 p176 := by decide +kernel
#print axioms step202
theorem h202 : NestedArithmetic.compile e202=p202 := StagedExprCompile.compile_times e202 e191 e176 p191 p176 p202 rfl h191 h176 step202
#print axioms h202
end Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
