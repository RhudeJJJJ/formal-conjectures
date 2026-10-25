/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD44Long00CompositionalNode030
import Proofs.RadenkovicGutmanD44Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e053 : NestedArithmetic.Expr 3 := .times e030 e052
noncomputable def p053 : NestedHorner.Poly 3 := [[[0],[0,44]],[[0,0],[0]],[[396,396],[396]],[[0,0],[0]],[[6996,1056],[1056]],[[0,0],[0]],[[30668,968],[968]],[[0,0],[0]],[[62920,352],[352]],[[0,0],[0]],[[72336,44],[44]],[[0]],[[49984]],[[0]],[[21164]],[[0]],[[5368]],[[0]],[[748]],[[0]],[[44]]]
theorem step053 : p053=NestedArithmetic.mul p030 p052 := by decide +kernel
#print axioms step053
theorem h053 : NestedArithmetic.compile e053=p053 := StagedExprCompile.compile_times e053 e030 e052 p030 p052 p053 rfl h030 h052 step053
#print axioms h053
end Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
