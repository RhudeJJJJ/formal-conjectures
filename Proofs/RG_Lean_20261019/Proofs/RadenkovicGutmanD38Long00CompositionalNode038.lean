/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD38Long00CompositionalNode037
import Proofs.RadenkovicGutmanD38Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e038 : NestedArithmetic.Expr 3 := .times e037 e032
noncomputable def p038 : NestedHorner.Poly 3 := [[[0],[0,-36]],[[0,0],[0]],[[324,-324],[-324]],[[0,0],[0]],[[-108,-864],[-864]],[[0,0],[0]],[[-6012,-792],[-792]],[[0,0],[0]],[[-18504,-288],[-288]],[[0,0],[0]],[[-27216,-36],[-36]],[[0]],[[-22896]],[[0]],[[-11484]],[[0]],[[-3384]],[[0]],[[-540]],[[0]],[[-36]]]
theorem step038 : p038=NestedArithmetic.mul p037 p032 := by decide +kernel
#print axioms step038
theorem h038 : NestedArithmetic.compile e038=p038 := StagedExprCompile.compile_times e038 e037 e032 p037 p032 p038 rfl h037 h032 step038
#print axioms h038
end Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
