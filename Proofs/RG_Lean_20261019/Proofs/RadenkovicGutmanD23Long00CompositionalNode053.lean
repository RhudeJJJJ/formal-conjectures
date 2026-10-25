/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD23Long00CompositionalNode030
import Proofs.RadenkovicGutmanD23Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e053 : NestedArithmetic.Expr 3 := .times e030 e052
noncomputable def p053 : NestedHorner.Poly 3 := [[[0],[0,23]],[[0,0],[0]],[[207,207],[207]],[[0,0],[0]],[[3657,552],[552]],[[0,0],[0]],[[16031,506],[506]],[[0,0],[0]],[[32890,184],[184]],[[0,0],[0]],[[37812,23],[23]],[[0]],[[26128]],[[0]],[[11063]],[[0]],[[2806]],[[0]],[[391]],[[0]],[[23]]]
theorem step053 : p053=NestedArithmetic.mul p030 p052 := by decide +kernel
#print axioms step053
theorem h053 : NestedArithmetic.compile e053=p053 := StagedExprCompile.compile_times e053 e030 e052 p030 p052 p053 rfl h030 h052 step053
#print axioms h053
end Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
