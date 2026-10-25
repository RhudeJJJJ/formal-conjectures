/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD17Long00CompositionalNode030
import Proofs.RadenkovicGutmanD17Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e184 : NestedArithmetic.Expr 3 := .times e030 e183
noncomputable def p184 : NestedHorner.Poly 3 := [[[17],[0]],[[0,0],[0]],[[272,0],[0]],[[0,0],[0]],[[1819,0],[0]],[[0,0],[0]],[[6596,0],[0]],[[0,0],[0]],[[14076,0],[0]],[[0,0],[0]],[[17952,17],[17]],[[0,0],[0]],[[13243,119],[119]],[[0,0],[0]],[[5100,272],[272]],[[0,0],[0]],[[765,221],[221]],[[0,0],[0]],[[0,51],[51]]]
theorem step184 : p184=NestedArithmetic.mul p030 p183 := by decide +kernel
#print axioms step184
theorem h184 : NestedArithmetic.compile e184=p184 := StagedExprCompile.compile_times e184 e030 e183 p030 p183 p184 rfl h030 h183 step184
#print axioms h184
end Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
