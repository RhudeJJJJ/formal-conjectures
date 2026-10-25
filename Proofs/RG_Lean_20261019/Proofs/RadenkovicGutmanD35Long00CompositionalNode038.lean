/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD35Long00CompositionalNode037
import Proofs.RadenkovicGutmanD35Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e038 : NestedArithmetic.Expr 3 := .times e037 e032
noncomputable def p038 : NestedHorner.Poly 3 := [[[0],[0,-33]],[[0,0],[0]],[[297,-297],[-297]],[[0,0],[0]],[[-99,-792],[-792]],[[0,0],[0]],[[-5511,-726],[-726]],[[0,0],[0]],[[-16962,-264],[-264]],[[0,0],[0]],[[-24948,-33],[-33]],[[0]],[[-20988]],[[0]],[[-10527]],[[0]],[[-3102]],[[0]],[[-495]],[[0]],[[-33]]]
theorem step038 : p038=NestedArithmetic.mul p037 p032 := by decide +kernel
#print axioms step038
theorem h038 : NestedArithmetic.compile e038=p038 := StagedExprCompile.compile_times e038 e037 e032 p037 p032 p038 rfl h037 h032 step038
#print axioms h038
end Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
