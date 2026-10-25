/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD45Long00CompositionalNode037
import Proofs.RadenkovicGutmanD45Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e038 : NestedArithmetic.Expr 3 := .times e037 e032
noncomputable def p038 : NestedHorner.Poly 3 := [[[0],[0,-43]],[[0,0],[0]],[[387,-387],[-387]],[[0,0],[0]],[[-129,-1032],[-1032]],[[0,0],[0]],[[-7181,-946],[-946]],[[0,0],[0]],[[-22102,-344],[-344]],[[0,0],[0]],[[-32508,-43],[-43]],[[0]],[[-27348]],[[0]],[[-13717]],[[0]],[[-4042]],[[0]],[[-645]],[[0]],[[-43]]]
theorem step038 : p038=NestedArithmetic.mul p037 p032 := by decide +kernel
#print axioms step038
theorem h038 : NestedArithmetic.compile e038=p038 := StagedExprCompile.compile_times e038 e037 e032 p037 p032 p038 rfl h037 h032 step038
#print axioms h038
end Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
