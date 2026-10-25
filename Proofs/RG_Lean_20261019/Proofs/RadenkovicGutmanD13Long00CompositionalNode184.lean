/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD13Long00CompositionalNode030
import Proofs.RadenkovicGutmanD13Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e184 : NestedArithmetic.Expr 3 := .times e030 e183
noncomputable def p184 : NestedHorner.Poly 3 := [[[13],[0]],[[0,0],[0]],[[208,0],[0]],[[0,0],[0]],[[1391,0],[0]],[[0,0],[0]],[[5044,0],[0]],[[0,0],[0]],[[10764,0],[0]],[[0,0],[0]],[[13728,13],[13]],[[0,0],[0]],[[10127,91],[91]],[[0,0],[0]],[[3900,208],[208]],[[0,0],[0]],[[585,169],[169]],[[0,0],[0]],[[0,39],[39]]]
theorem step184 : p184=NestedArithmetic.mul p030 p183 := by decide +kernel
#print axioms step184
theorem h184 : NestedArithmetic.compile e184=p184 := StagedExprCompile.compile_times e184 e030 e183 p030 p183 p184 rfl h030 h183 step184
#print axioms h184
end Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
