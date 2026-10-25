/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD8Long00CompositionalNode034
import Proofs.RadenkovicGutmanD8Long00CompositionalNode028
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e035 : NestedArithmetic.Expr 3 := .times e034 e028
noncomputable def p035 : NestedHorner.Poly 3 := [[[0],[0]],[[0,-24],[-24]],[[0,0],[0]],[[-432,-104],[-104]],[[0,0],[0]],[[-3024,-128],[-128]],[[0,0],[0]],[[-8352,-56],[-56]],[[0,0],[0]],[[-12112,-8],[-8]],[[0]],[[-10176]],[[0]],[[-5104]],[[0]],[[-1504]],[[0]],[[-240]],[[0]],[[-16]]]
theorem step035 : p035=NestedArithmetic.mul p034 p028 := by decide +kernel
#print axioms step035
theorem h035 : NestedArithmetic.compile e035=p035 := StagedExprCompile.compile_times e035 e034 e028 p034 p028 p035 rfl h034 h028 step035
#print axioms h035
end Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
