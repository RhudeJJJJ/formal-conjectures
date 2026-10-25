/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD39Long00CompositionalNode030
import Proofs.RadenkovicGutmanD39Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e184 : NestedArithmetic.Expr 3 := .times e030 e183
noncomputable def p184 : NestedHorner.Poly 3 := [[[39],[0]],[[0,0],[0]],[[624,0],[0]],[[0,0],[0]],[[4173,0],[0]],[[0,0],[0]],[[15132,0],[0]],[[0,0],[0]],[[32292,0],[0]],[[0,0],[0]],[[41184,39],[39]],[[0,0],[0]],[[30381,273],[273]],[[0,0],[0]],[[11700,624],[624]],[[0,0],[0]],[[1755,507],[507]],[[0,0],[0]],[[0,117],[117]]]
theorem step184 : p184=NestedArithmetic.mul p030 p183 := by decide +kernel
#print axioms step184
theorem h184 : NestedArithmetic.compile e184=p184 := StagedExprCompile.compile_times e184 e030 e183 p030 p183 p184 rfl h030 h183 step184
#print axioms h184
end Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
