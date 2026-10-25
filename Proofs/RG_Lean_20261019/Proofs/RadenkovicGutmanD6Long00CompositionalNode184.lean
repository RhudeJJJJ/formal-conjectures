/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD6Long00CompositionalNode030
import Proofs.RadenkovicGutmanD6Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e184 : NestedArithmetic.Expr 3 := .times e030 e183
noncomputable def p184 : NestedHorner.Poly 3 := [[[6],[0]],[[0,0],[0]],[[96,0],[0]],[[0,0],[0]],[[642,0],[0]],[[0,0],[0]],[[2328,0],[0]],[[0,0],[0]],[[4968,0],[0]],[[0,0],[0]],[[6336,6],[6]],[[0,0],[0]],[[4674,42],[42]],[[0,0],[0]],[[1800,96],[96]],[[0,0],[0]],[[270,78],[78]],[[0,0],[0]],[[0,18],[18]]]
theorem step184 : p184=NestedArithmetic.mul p030 p183 := by decide +kernel
#print axioms step184
theorem h184 : NestedArithmetic.compile e184=p184 := StagedExprCompile.compile_times e184 e030 e183 p030 p183 p184 rfl h030 h183 step184
#print axioms h184
end Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
