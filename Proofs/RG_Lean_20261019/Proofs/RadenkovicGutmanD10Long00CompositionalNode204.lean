/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD10Long00CompositionalNode194
import Proofs.RadenkovicGutmanD10Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e204 : NestedArithmetic.Expr 3 := .times e194 e183
noncomputable def p204 : NestedHorner.Poly 3 := [[[20],[0]],[[0,0],[0]],[[320,0],[0]],[[0,0],[0]],[[2140,0],[0]],[[0,0],[0]],[[7760,0],[0]],[[0,0],[0]],[[16560,0],[0]],[[0,0],[0]],[[21120,20],[20]],[[0,0],[0]],[[15580,140],[140]],[[0,0],[0]],[[6000,320],[320]],[[0,0],[0]],[[900,260],[260]],[[0,0],[0]],[[0,60],[60]]]
theorem step204 : p204=NestedArithmetic.mul p194 p183 := by decide +kernel
#print axioms step204
theorem h204 : NestedArithmetic.compile e204=p204 := StagedExprCompile.compile_times e204 e194 e183 p194 p183 p204 rfl h194 h183 step204
#print axioms h204
end Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
