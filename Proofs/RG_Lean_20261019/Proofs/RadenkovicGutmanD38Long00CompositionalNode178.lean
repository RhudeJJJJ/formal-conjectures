/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD38Long00CompositionalNode177
import Proofs.RadenkovicGutmanD38Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e178 : NestedArithmetic.Expr 3 := .times e177 e122
noncomputable def p178 : NestedHorner.Poly 3 := [[[-72],[0]],[[0,0],[0]],[[-1224,0],[0,0]],[[0,0],[0,0]],[[-8784,0],[0,0]],[[0,0],[0,0]],[[-34632,0],[0,0]],[[0,0],[0,0]],[[-81792,0],[0,0]],[[0,0],[0,0]],[[-118368,-72],[-72,0]],[[0,0],[0,0]],[[-102960,-576],[-576,0]],[[0,0],[0,0]],[[-50184,-1584],[-1584,0]],[[0,0],[0,0]],[[-11448,-1728],[-1728,0]],[[0,0],[0,0]],[[-648,-648],[-648,0]],[[0],[0,0]],[[0],[0,-72]]]
theorem step178 : p178=NestedArithmetic.mul p177 p122 := by decide +kernel
#print axioms step178
theorem h178 : NestedArithmetic.compile e178=p178 := StagedExprCompile.compile_times e178 e177 e122 p177 p122 p178 rfl h177 h122 step178
#print axioms h178
end Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
