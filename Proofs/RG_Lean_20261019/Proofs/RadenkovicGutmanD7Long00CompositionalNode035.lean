/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD7Long00CompositionalNode034
import Proofs.RadenkovicGutmanD7Long00CompositionalNode028
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e035 : NestedArithmetic.Expr 3 := .times e034 e028
noncomputable def p035 : NestedHorner.Poly 3 := [[[0],[0]],[[0,-21],[-21]],[[0,0],[0]],[[-378,-91],[-91]],[[0,0],[0]],[[-2646,-112],[-112]],[[0,0],[0]],[[-7308,-49],[-49]],[[0,0],[0]],[[-10598,-7],[-7]],[[0]],[[-8904]],[[0]],[[-4466]],[[0]],[[-1316]],[[0]],[[-210]],[[0]],[[-14]]]
theorem step035 : p035=NestedArithmetic.mul p034 p028 := by decide +kernel
#print axioms step035
theorem h035 : NestedArithmetic.compile e035=p035 := StagedExprCompile.compile_times e035 e034 e028 p034 p028 p035 rfl h034 h028 step035
#print axioms h035
end Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
