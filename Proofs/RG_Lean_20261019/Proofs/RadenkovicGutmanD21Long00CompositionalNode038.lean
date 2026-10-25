/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD21Long00CompositionalNode037
import Proofs.RadenkovicGutmanD21Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e038 : NestedArithmetic.Expr 3 := .times e037 e032
noncomputable def p038 : NestedHorner.Poly 3 := [[[0],[0,-19]],[[0,0],[0]],[[171,-171],[-171]],[[0,0],[0]],[[-57,-456],[-456]],[[0,0],[0]],[[-3173,-418],[-418]],[[0,0],[0]],[[-9766,-152],[-152]],[[0,0],[0]],[[-14364,-19],[-19]],[[0]],[[-12084]],[[0]],[[-6061]],[[0]],[[-1786]],[[0]],[[-285]],[[0]],[[-19]]]
theorem step038 : p038=NestedArithmetic.mul p037 p032 := by decide +kernel
#print axioms step038
theorem h038 : NestedArithmetic.compile e038=p038 := StagedExprCompile.compile_times e038 e037 e032 p037 p032 p038 rfl h037 h032 step038
#print axioms h038
end Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
