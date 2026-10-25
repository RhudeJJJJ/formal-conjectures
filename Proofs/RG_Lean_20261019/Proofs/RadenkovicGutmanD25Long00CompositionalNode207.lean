/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD25Long00CompositionalNode065
import Proofs.RadenkovicGutmanD25Long00CompositionalNode206
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e207 : NestedArithmetic.Expr 3 := .times e065 e206
noncomputable def p207 : NestedHorner.Poly 3 := [[[-2],[0]],[[0,0],[0]],[[-109,0],[0,0]],[[0,0],[0,0]],[[-1469,0],[0,0]],[[0,0],[0,0]],[[-9362,0],[0,0]],[[0,0],[0,0]],[[-33697,0],[0,0]],[[0,0],[0,0]],[[-73088,-2],[-2,0]],[[0,0],[0,0]],[[-96760,-91],[-91,0]],[[0,0],[0,0]],[[-76094,-594],[-594,0]],[[0,0],[0,0]],[[-32743,-1398],[-1398,0]],[[0,0],[0,0]],[[-6243,-1268],[-1268,0]],[[0,0],[0,0]],[[-225,-375],[-375,-2]],[[0],[0,0]],[[0],[0,-25]]]
theorem step207 : p207=NestedArithmetic.mul p065 p206 := by decide +kernel
#print axioms step207
theorem h207 : NestedArithmetic.compile e207=p207 := StagedExprCompile.compile_times e207 e065 e206 p065 p206 p207 rfl h065 h206 step207
#print axioms h207
end Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
