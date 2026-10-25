/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD26Long00CompositionalNode037
import Proofs.RadenkovicGutmanD26Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e038 : NestedArithmetic.Expr 3 := .times e037 e032
noncomputable def p038 : NestedHorner.Poly 3 := [[[0],[0,-24]],[[0,0],[0]],[[216,-216],[-216]],[[0,0],[0]],[[-72,-576],[-576]],[[0,0],[0]],[[-4008,-528],[-528]],[[0,0],[0]],[[-12336,-192],[-192]],[[0,0],[0]],[[-18144,-24],[-24]],[[0]],[[-15264]],[[0]],[[-7656]],[[0]],[[-2256]],[[0]],[[-360]],[[0]],[[-24]]]
theorem step038 : p038=NestedArithmetic.mul p037 p032 := by decide +kernel
#print axioms step038
theorem h038 : NestedArithmetic.compile e038=p038 := StagedExprCompile.compile_times e038 e037 e032 p037 p032 p038 rfl h037 h032 step038
#print axioms h038
end Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
