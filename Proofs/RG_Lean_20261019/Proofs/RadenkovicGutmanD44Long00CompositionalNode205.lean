/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD44Long00CompositionalNode204
import Proofs.RadenkovicGutmanD44Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e205 : NestedArithmetic.Expr 3 := .times e204 e003
noncomputable def p205 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[88,0],[0]],[[0,0],[0]],[[1408,0],[0]],[[0,0],[0]],[[9416,0],[0]],[[0,0],[0]],[[34144,0],[0]],[[0,0],[0]],[[72864,0],[0]],[[0,0],[0]],[[92928,88],[88]],[[0,0],[0]],[[68552,616],[616]],[[0,0],[0]],[[26400,1408],[1408]],[[0,0],[0]],[[3960,1144],[1144]],[[0,0],[0]],[[0,264],[264]]]
theorem step205 : p205=NestedArithmetic.mul p204 p003 := by decide +kernel
#print axioms step205
theorem h205 : NestedArithmetic.compile e205=p205 := StagedExprCompile.compile_times e205 e204 e003 p204 p003 p205 rfl h204 h003 step205
#print axioms h205
end Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
