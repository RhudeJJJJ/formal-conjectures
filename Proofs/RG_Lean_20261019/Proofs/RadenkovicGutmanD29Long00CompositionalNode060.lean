/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD29Long00CompositionalNode030
import Proofs.RadenkovicGutmanD29Long00CompositionalNode056
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e060 : NestedArithmetic.Expr 3 := .times e030 e056
noncomputable def p060 : NestedHorner.Poly 3 := [[[0],[0]],[[0,87],[87]],[[0,0],[0]],[[1305,377],[377]],[[0,0],[0]],[[8700,464],[464]],[[0,0],[0]],[[22591,203],[203]],[[0,0],[0]],[[30624,29],[29]],[[0]],[[24012]],[[0]],[[11252]],[[0]],[[3103]],[[0]],[[464]],[[0]],[[29]]]
theorem step060 : p060=NestedArithmetic.mul p030 p056 := by decide +kernel
#print axioms step060
theorem h060 : NestedArithmetic.compile e060=p060 := StagedExprCompile.compile_times e060 e030 e056 p030 p056 p060 rfl h030 h056 step060
#print axioms h060
end Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
