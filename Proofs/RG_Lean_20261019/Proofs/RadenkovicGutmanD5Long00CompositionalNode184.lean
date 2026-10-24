/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode030
import Proofs.RadenkovicGutmanD5Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e184 : NestedArithmetic.Expr 3 := .times e030 e183
noncomputable def p184 : NestedHorner.Poly 3 := [[[5],[0]],[[0,0],[0]],[[80,0],[0]],[[0,0],[0]],[[535,0],[0]],[[0,0],[0]],[[1940,0],[0]],[[0,0],[0]],[[4140,0],[0]],[[0,0],[0]],[[5280,5],[5]],[[0,0],[0]],[[3895,35],[35]],[[0,0],[0]],[[1500,80],[80]],[[0,0],[0]],[[225,65],[65]],[[0,0],[0]],[[0,15],[15]]]
theorem step184 : p184=NestedArithmetic.mul p030 p183 := by decide +kernel
#print axioms step184
theorem h184 : NestedArithmetic.compile e184=p184 := StagedExprCompile.compile_times e184 e030 e183 p030 p183 p184 rfl h030 h183 step184
#print axioms h184
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
