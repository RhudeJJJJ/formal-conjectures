/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD29Long00CompositionalNode030
import Proofs.RadenkovicGutmanD29Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e184 : NestedArithmetic.Expr 3 := .times e030 e183
noncomputable def p184 : NestedHorner.Poly 3 := [[[29],[0]],[[0,0],[0]],[[464,0],[0]],[[0,0],[0]],[[3103,0],[0]],[[0,0],[0]],[[11252,0],[0]],[[0,0],[0]],[[24012,0],[0]],[[0,0],[0]],[[30624,29],[29]],[[0,0],[0]],[[22591,203],[203]],[[0,0],[0]],[[8700,464],[464]],[[0,0],[0]],[[1305,377],[377]],[[0,0],[0]],[[0,87],[87]]]
theorem step184 : p184=NestedArithmetic.mul p030 p183 := by decide +kernel
#print axioms step184
theorem h184 : NestedArithmetic.compile e184=p184 := StagedExprCompile.compile_times e184 e030 e183 p030 p183 p184 rfl h030 h183 step184
#print axioms h184
end Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
