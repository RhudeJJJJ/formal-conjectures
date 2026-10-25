/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD25Long00CompositionalNode065
import Proofs.RadenkovicGutmanD25Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e066 : NestedArithmetic.Expr 3 := .times e065 e064
noncomputable def p066 : NestedHorner.Poly 3 := [[[0],[0,-25]],[[0,0],[0,0]],[[-225,-375],[-375,-2]],[[0,0],[0]],[[-6243,-1268],[-1268]],[[0,0],[0]],[[-32743,-1398],[-1398]],[[0,0],[0]],[[-76094,-594],[-594]],[[0,0],[0]],[[-96760,-91],[-91]],[[0,0],[0]],[[-73088,-2],[-2]],[[0]],[[-33697]],[[0]],[[-9362]],[[0]],[[-1469]],[[0]],[[-109]],[[0]],[[-2]]]
theorem step066 : p066=NestedArithmetic.mul p065 p064 := by decide +kernel
#print axioms step066
theorem h066 : NestedArithmetic.compile e066=p066 := StagedExprCompile.compile_times e066 e065 e064 p065 p064 p066 rfl h065 h064 step066
#print axioms h066
end Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
