/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD35Long00CompositionalNode177
import Proofs.RadenkovicGutmanD35Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e178 : NestedArithmetic.Expr 3 := .times e177 e122
noncomputable def p178 : NestedHorner.Poly 3 := [[[-66],[0]],[[0,0],[0]],[[-1122,0],[0,0]],[[0,0],[0,0]],[[-8052,0],[0,0]],[[0,0],[0,0]],[[-31746,0],[0,0]],[[0,0],[0,0]],[[-74976,0],[0,0]],[[0,0],[0,0]],[[-108504,-66],[-66,0]],[[0,0],[0,0]],[[-94380,-528],[-528,0]],[[0,0],[0,0]],[[-46002,-1452],[-1452,0]],[[0,0],[0,0]],[[-10494,-1584],[-1584,0]],[[0,0],[0,0]],[[-594,-594],[-594,0]],[[0],[0,0]],[[0],[0,-66]]]
theorem step178 : p178=NestedArithmetic.mul p177 p122 := by decide +kernel
#print axioms step178
theorem h178 : NestedArithmetic.compile e178=p178 := StagedExprCompile.compile_times e178 e177 e122 p177 p122 p178 rfl h177 h122 step178
#print axioms h178
end Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
