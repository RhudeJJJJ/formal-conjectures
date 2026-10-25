/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD38Long00CompositionalNode058
import Proofs.RadenkovicGutmanD38Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e059 : NestedArithmetic.Expr 3 := .times e058 e052
noncomputable def p059 : NestedHorner.Poly 3 := [[[],[]],[[0],[0,-72]],[[0,0],[0]],[[-648,-648],[-648]],[[0,0],[0]],[[-11448,-1728],[-1728]],[[0,0],[0]],[[-50184,-1584],[-1584]],[[0,0],[0]],[[-102960,-576],[-576]],[[0,0],[0]],[[-118368,-72],[-72]],[[0]],[[-81792]],[[0]],[[-34632]],[[0]],[[-8784]],[[0]],[[-1224]],[[0]],[[-72]]]
theorem step059 : p059=NestedArithmetic.mul p058 p052 := by decide +kernel
#print axioms step059
theorem h059 : NestedArithmetic.compile e059=p059 := StagedExprCompile.compile_times e059 e058 e052 p058 p052 p059 rfl h058 h052 step059
#print axioms h059
end Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
