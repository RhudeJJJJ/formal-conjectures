/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD36Long00CompositionalNode034
import Proofs.RadenkovicGutmanD36Long00CompositionalNode028
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e035 : NestedArithmetic.Expr 3 := .times e034 e028
noncomputable def p035 : NestedHorner.Poly 3 := [[[0],[0]],[[0,-108],[-108]],[[0,0],[0]],[[-1944,-468],[-468]],[[0,0],[0]],[[-13608,-576],[-576]],[[0,0],[0]],[[-37584,-252],[-252]],[[0,0],[0]],[[-54504,-36],[-36]],[[0]],[[-45792]],[[0]],[[-22968]],[[0]],[[-6768]],[[0]],[[-1080]],[[0]],[[-72]]]
theorem step035 : p035=NestedArithmetic.mul p034 p028 := by decide +kernel
#print axioms step035
theorem h035 : NestedArithmetic.compile e035=p035 := StagedExprCompile.compile_times e035 e034 e028 p034 p028 p035 rfl h034 h028 step035
#print axioms h035
end Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
