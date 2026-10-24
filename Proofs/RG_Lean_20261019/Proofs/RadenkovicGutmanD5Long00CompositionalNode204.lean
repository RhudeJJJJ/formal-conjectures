/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode194
import Proofs.RadenkovicGutmanD5Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e204 : NestedArithmetic.Expr 3 := .times e194 e183
noncomputable def p204 : NestedHorner.Poly 3 := [[[10],[0]],[[0,0],[0]],[[160,0],[0]],[[0,0],[0]],[[1070,0],[0]],[[0,0],[0]],[[3880,0],[0]],[[0,0],[0]],[[8280,0],[0]],[[0,0],[0]],[[10560,10],[10]],[[0,0],[0]],[[7790,70],[70]],[[0,0],[0]],[[3000,160],[160]],[[0,0],[0]],[[450,130],[130]],[[0,0],[0]],[[0,30],[30]]]
theorem step204 : p204=NestedArithmetic.mul p194 p183 := by decide +kernel
#print axioms step204
theorem h204 : NestedArithmetic.compile e204=p204 := StagedExprCompile.compile_times e204 e194 e183 p194 p183 p204 rfl h194 h183 step204
#print axioms h204
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
