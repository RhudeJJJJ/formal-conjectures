/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD12Long00CompositionalNode037
import Proofs.RadenkovicGutmanD12Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e038 : NestedArithmetic.Expr 3 := .times e037 e032
noncomputable def p038 : NestedHorner.Poly 3 := [[[0],[0,-10]],[[0,0],[0]],[[90,-90],[-90]],[[0,0],[0]],[[-30,-240],[-240]],[[0,0],[0]],[[-1670,-220],[-220]],[[0,0],[0]],[[-5140,-80],[-80]],[[0,0],[0]],[[-7560,-10],[-10]],[[0]],[[-6360]],[[0]],[[-3190]],[[0]],[[-940]],[[0]],[[-150]],[[0]],[[-10]]]
theorem step038 : p038=NestedArithmetic.mul p037 p032 := by decide +kernel
#print axioms step038
theorem h038 : NestedArithmetic.compile e038=p038 := StagedExprCompile.compile_times e038 e037 e032 p037 p032 p038 rfl h037 h032 step038
#print axioms h038
end Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
