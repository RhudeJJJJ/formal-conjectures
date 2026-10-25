/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD36Long00CompositionalNode030
import Proofs.RadenkovicGutmanD36Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e184 : NestedArithmetic.Expr 3 := .times e030 e183
noncomputable def p184 : NestedHorner.Poly 3 := [[[36],[0]],[[0,0],[0]],[[576,0],[0]],[[0,0],[0]],[[3852,0],[0]],[[0,0],[0]],[[13968,0],[0]],[[0,0],[0]],[[29808,0],[0]],[[0,0],[0]],[[38016,36],[36]],[[0,0],[0]],[[28044,252],[252]],[[0,0],[0]],[[10800,576],[576]],[[0,0],[0]],[[1620,468],[468]],[[0,0],[0]],[[0,108],[108]]]
theorem step184 : p184=NestedArithmetic.mul p030 p183 := by decide +kernel
#print axioms step184
theorem h184 : NestedArithmetic.compile e184=p184 := StagedExprCompile.compile_times e184 e030 e183 p030 p183 p184 rfl h030 h183 step184
#print axioms h184
end Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
