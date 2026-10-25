/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD35Long00CompositionalNode174
import Proofs.RadenkovicGutmanD35Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e177 : NestedArithmetic.Expr 3 := .times e174 e176
noncomputable def p177 : NestedHorner.Poly 3 := [[[-66],[0]],[[0,0],[0]],[[-1122,0],[0,0]],[[0,0],[0,0]],[[-8052,0],[0,0]],[[0,0],[0,0]],[[-31746,0],[0,0]],[[0,0],[0,0]],[[-74976,0],[0,0]],[[0,0],[0,0]],[[-108504,-66],[-66,0]],[[0,0],[0,0]],[[-94380,-528],[-528,0]],[[0,0],[0,0]],[[-46002,-1452],[-1452,0]],[[0,0],[0,0]],[[-10494,-1584],[-1584,0]],[[0,0],[0,0]],[[-594,-594],[-594,0]],[[0],[0,0]],[[0],[0,-66]]]
theorem step177 : p177=NestedArithmetic.mul p174 p176 := by decide +kernel
#print axioms step177
theorem h177 : NestedArithmetic.compile e177=p177 := StagedExprCompile.compile_times e177 e174 e176 p174 p176 p177 rfl h174 h176 step177
#print axioms h177
end Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
