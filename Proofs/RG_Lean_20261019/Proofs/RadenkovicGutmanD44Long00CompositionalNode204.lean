/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD44Long00CompositionalNode194
import Proofs.RadenkovicGutmanD44Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e204 : NestedArithmetic.Expr 3 := .times e194 e183
noncomputable def p204 : NestedHorner.Poly 3 := [[[88],[0]],[[0,0],[0]],[[1408,0],[0]],[[0,0],[0]],[[9416,0],[0]],[[0,0],[0]],[[34144,0],[0]],[[0,0],[0]],[[72864,0],[0]],[[0,0],[0]],[[92928,88],[88]],[[0,0],[0]],[[68552,616],[616]],[[0,0],[0]],[[26400,1408],[1408]],[[0,0],[0]],[[3960,1144],[1144]],[[0,0],[0]],[[0,264],[264]]]
theorem step204 : p204=NestedArithmetic.mul p194 p183 := by decide +kernel
#print axioms step204
theorem h204 : NestedArithmetic.compile e204=p204 := StagedExprCompile.compile_times e204 e194 e183 p194 p183 p204 rfl h194 h183 step204
#print axioms h204
end Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
