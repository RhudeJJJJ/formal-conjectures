/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD13Long00CompositionalNode037
import Proofs.RadenkovicGutmanD13Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e038 : NestedArithmetic.Expr 3 := .times e037 e032
noncomputable def p038 : NestedHorner.Poly 3 := [[[0],[0,-11]],[[0,0],[0]],[[99,-99],[-99]],[[0,0],[0]],[[-33,-264],[-264]],[[0,0],[0]],[[-1837,-242],[-242]],[[0,0],[0]],[[-5654,-88],[-88]],[[0,0],[0]],[[-8316,-11],[-11]],[[0]],[[-6996]],[[0]],[[-3509]],[[0]],[[-1034]],[[0]],[[-165]],[[0]],[[-11]]]
theorem step038 : p038=NestedArithmetic.mul p037 p032 := by decide +kernel
#print axioms step038
theorem h038 : NestedArithmetic.compile e038=p038 := StagedExprCompile.compile_times e038 e037 e032 p037 p032 p038 rfl h037 h032 step038
#print axioms h038
end Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
