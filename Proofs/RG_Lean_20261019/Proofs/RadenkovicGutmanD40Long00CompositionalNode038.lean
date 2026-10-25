/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD40Long00CompositionalNode037
import Proofs.RadenkovicGutmanD40Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e038 : NestedArithmetic.Expr 3 := .times e037 e032
noncomputable def p038 : NestedHorner.Poly 3 := [[[0],[0,-38]],[[0,0],[0]],[[342,-342],[-342]],[[0,0],[0]],[[-114,-912],[-912]],[[0,0],[0]],[[-6346,-836],[-836]],[[0,0],[0]],[[-19532,-304],[-304]],[[0,0],[0]],[[-28728,-38],[-38]],[[0]],[[-24168]],[[0]],[[-12122]],[[0]],[[-3572]],[[0]],[[-570]],[[0]],[[-38]]]
theorem step038 : p038=NestedArithmetic.mul p037 p032 := by decide +kernel
#print axioms step038
theorem h038 : NestedArithmetic.compile e038=p038 := StagedExprCompile.compile_times e038 e037 e032 p037 p032 p038 rfl h037 h032 step038
#print axioms h038
end Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
