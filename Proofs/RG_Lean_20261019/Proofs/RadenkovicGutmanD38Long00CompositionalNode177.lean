/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD38Long00CompositionalNode174
import Proofs.RadenkovicGutmanD38Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e177 : NestedArithmetic.Expr 3 := .times e174 e176
noncomputable def p177 : NestedHorner.Poly 3 := [[[-72],[0]],[[0,0],[0]],[[-1224,0],[0,0]],[[0,0],[0,0]],[[-8784,0],[0,0]],[[0,0],[0,0]],[[-34632,0],[0,0]],[[0,0],[0,0]],[[-81792,0],[0,0]],[[0,0],[0,0]],[[-118368,-72],[-72,0]],[[0,0],[0,0]],[[-102960,-576],[-576,0]],[[0,0],[0,0]],[[-50184,-1584],[-1584,0]],[[0,0],[0,0]],[[-11448,-1728],[-1728,0]],[[0,0],[0,0]],[[-648,-648],[-648,0]],[[0],[0,0]],[[0],[0,-72]]]
theorem step177 : p177=NestedArithmetic.mul p174 p176 := by decide +kernel
#print axioms step177
theorem h177 : NestedArithmetic.compile e177=p177 := StagedExprCompile.compile_times e177 e174 e176 p174 p176 p177 rfl h174 h176 step177
#print axioms h177
end Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
