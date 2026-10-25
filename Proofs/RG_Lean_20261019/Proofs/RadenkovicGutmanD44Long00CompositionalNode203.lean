/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD44Long00CompositionalNode202
import Proofs.RadenkovicGutmanD44Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e203 : NestedArithmetic.Expr 3 := .times e202 e122
noncomputable def p203 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[78,0],[0,0]],[[0,0],[0,0]],[[992,0],[0,0]],[[0,0],[0,0]],[[6330,0],[0,0]],[[0,0],[0,0]],[[23436,0],[0,0]],[[0,0],[0,0]],[[53272,2],[2,0]],[[0,0],[0,0]],[[75196,60],[60,0]],[[0,0],[0,0]],[[64314,396],[396,0]],[[0,0],[0,0]],[[30986,1016],[1016,0]],[[0,0],[0,0]],[[7014,1074],[1074,0]],[[0,0],[0,0]],[[396,396],[396,2]],[[0],[0,0]],[[0],[0,44]]]
theorem step203 : p203=NestedArithmetic.mul p202 p122 := by decide +kernel
#print axioms step203
theorem h203 : NestedArithmetic.compile e203=p203 := StagedExprCompile.compile_times e203 e202 e122 p202 p122 p203 rfl h202 h122 step203
#print axioms h203
end Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
