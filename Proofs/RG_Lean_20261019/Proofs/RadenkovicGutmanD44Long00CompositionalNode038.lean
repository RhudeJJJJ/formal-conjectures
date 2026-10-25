/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD44Long00CompositionalNode037
import Proofs.RadenkovicGutmanD44Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e038 : NestedArithmetic.Expr 3 := .times e037 e032
noncomputable def p038 : NestedHorner.Poly 3 := [[[0],[0,-42]],[[0,0],[0]],[[378,-378],[-378]],[[0,0],[0]],[[-126,-1008],[-1008]],[[0,0],[0]],[[-7014,-924],[-924]],[[0,0],[0]],[[-21588,-336],[-336]],[[0,0],[0]],[[-31752,-42],[-42]],[[0]],[[-26712]],[[0]],[[-13398]],[[0]],[[-3948]],[[0]],[[-630]],[[0]],[[-42]]]
theorem step038 : p038=NestedArithmetic.mul p037 p032 := by decide +kernel
#print axioms step038
theorem h038 : NestedArithmetic.compile e038=p038 := StagedExprCompile.compile_times e038 e037 e032 p037 p032 p038 rfl h037 h032 step038
#print axioms h038
end Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
