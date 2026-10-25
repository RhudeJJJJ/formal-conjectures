/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD6Long00CompositionalNode034
import Proofs.RadenkovicGutmanD6Long00CompositionalNode028
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e035 : NestedArithmetic.Expr 3 := .times e034 e028
noncomputable def p035 : NestedHorner.Poly 3 := [[[0],[0]],[[0,-18],[-18]],[[0,0],[0]],[[-324,-78],[-78]],[[0,0],[0]],[[-2268,-96],[-96]],[[0,0],[0]],[[-6264,-42],[-42]],[[0,0],[0]],[[-9084,-6],[-6]],[[0]],[[-7632]],[[0]],[[-3828]],[[0]],[[-1128]],[[0]],[[-180]],[[0]],[[-12]]]
theorem step035 : p035=NestedArithmetic.mul p034 p028 := by decide +kernel
#print axioms step035
theorem h035 : NestedArithmetic.compile e035=p035 := StagedExprCompile.compile_times e035 e034 e028 p034 p028 p035 rfl h034 h028 step035
#print axioms h035
end Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
