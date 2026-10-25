/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD40Long00CompositionalNode036
import Proofs.RadenkovicGutmanD40Long00CompositionalNode040
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e041 : NestedArithmetic.Expr 3 := .times e036 e040
noncomputable def p041 : NestedHorner.Poly 3 := [[[],[]],[[0],[0,-76]],[[0,0],[0]],[[756,-684],[-684]],[[0,0],[0]],[[396,-1824],[-1824]],[[0,0],[0]],[[-10572,-1672],[-1672]],[[0,0],[0]],[[-35400,-608],[-608]],[[0,0],[0]],[[-53904,-76],[-76]],[[0]],[[-46336]],[[0]],[[-23596]],[[0]],[[-7032]],[[0]],[[-1132]],[[0]],[[-76]]]
theorem step041 : p041=NestedArithmetic.mul p036 p040 := by decide +kernel
#print axioms step041
theorem h041 : NestedArithmetic.compile e041=p041 := StagedExprCompile.compile_times e041 e036 e040 p036 p040 p041 rfl h036 h040 step041
#print axioms h041
end Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
