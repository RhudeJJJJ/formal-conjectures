/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD8Long00CompositionalNode044
import Proofs.RadenkovicGutmanD8Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e062 : NestedArithmetic.Expr 3 := .times e044 e052
noncomputable def p062 : NestedHorner.Poly 3 := [[[0],[0,8]],[[0,0],[0,0]],[[72,72],[72,2]],[[0,0],[0]],[[1290,210],[210]],[[0,0],[0]],[[5894,224],[224]],[[0,0],[0]],[[12834,108],[108]],[[0,0],[0]],[[16012,24],[24]],[[0,0],[0]],[[12376,2],[2]],[[0]],[[6120]],[[0]],[[1938]],[[0]],[[380]],[[0]],[[42]],[[0]],[[2]]]
theorem step062 : p062=NestedArithmetic.mul p044 p052 := by decide +kernel
#print axioms step062
theorem h062 : NestedArithmetic.compile e062=p062 := StagedExprCompile.compile_times e062 e044 e052 p044 p052 p062 rfl h044 h052 step062
#print axioms h062
end Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
