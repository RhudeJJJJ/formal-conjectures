/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD33Long00CompositionalNode037
import Proofs.RadenkovicGutmanD33Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e038 : NestedArithmetic.Expr 3 := .times e037 e032
noncomputable def p038 : NestedHorner.Poly 3 := [[[0],[0,-31]],[[0,0],[0]],[[279,-279],[-279]],[[0,0],[0]],[[-93,-744],[-744]],[[0,0],[0]],[[-5177,-682],[-682]],[[0,0],[0]],[[-15934,-248],[-248]],[[0,0],[0]],[[-23436,-31],[-31]],[[0]],[[-19716]],[[0]],[[-9889]],[[0]],[[-2914]],[[0]],[[-465]],[[0]],[[-31]]]
theorem step038 : p038=NestedArithmetic.mul p037 p032 := by decide +kernel
#print axioms step038
theorem h038 : NestedArithmetic.compile e038=p038 := StagedExprCompile.compile_times e038 e037 e032 p037 p032 p038 rfl h037 h032 step038
#print axioms h038
end Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
