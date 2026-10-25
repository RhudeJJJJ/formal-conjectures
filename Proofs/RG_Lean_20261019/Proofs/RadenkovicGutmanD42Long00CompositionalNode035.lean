/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD42Long00CompositionalNode034
import Proofs.RadenkovicGutmanD42Long00CompositionalNode028
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e035 : NestedArithmetic.Expr 3 := .times e034 e028
noncomputable def p035 : NestedHorner.Poly 3 := [[[0],[0]],[[0,-126],[-126]],[[0,0],[0]],[[-2268,-546],[-546]],[[0,0],[0]],[[-15876,-672],[-672]],[[0,0],[0]],[[-43848,-294],[-294]],[[0,0],[0]],[[-63588,-42],[-42]],[[0]],[[-53424]],[[0]],[[-26796]],[[0]],[[-7896]],[[0]],[[-1260]],[[0]],[[-84]]]
theorem step035 : p035=NestedArithmetic.mul p034 p028 := by decide +kernel
#print axioms step035
theorem h035 : NestedArithmetic.compile e035=p035 := StagedExprCompile.compile_times e035 e034 e028 p034 p028 p035 rfl h034 h028 step035
#print axioms h035
end Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
