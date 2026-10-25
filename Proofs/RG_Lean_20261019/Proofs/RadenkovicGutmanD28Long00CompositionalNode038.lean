/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD28Long00CompositionalNode037
import Proofs.RadenkovicGutmanD28Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e038 : NestedArithmetic.Expr 3 := .times e037 e032
noncomputable def p038 : NestedHorner.Poly 3 := [[[0],[0,-26]],[[0,0],[0]],[[234,-234],[-234]],[[0,0],[0]],[[-78,-624],[-624]],[[0,0],[0]],[[-4342,-572],[-572]],[[0,0],[0]],[[-13364,-208],[-208]],[[0,0],[0]],[[-19656,-26],[-26]],[[0]],[[-16536]],[[0]],[[-8294]],[[0]],[[-2444]],[[0]],[[-390]],[[0]],[[-26]]]
theorem step038 : p038=NestedArithmetic.mul p037 p032 := by decide +kernel
#print axioms step038
theorem h038 : NestedArithmetic.compile e038=p038 := StagedExprCompile.compile_times e038 e037 e032 p037 p032 p038 rfl h037 h032 step038
#print axioms h038
end Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
