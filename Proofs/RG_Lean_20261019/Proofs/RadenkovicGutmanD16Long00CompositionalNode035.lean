/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD16Long00CompositionalNode034
import Proofs.RadenkovicGutmanD16Long00CompositionalNode028
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e035 : NestedArithmetic.Expr 3 := .times e034 e028
noncomputable def p035 : NestedHorner.Poly 3 := [[[0],[0]],[[0,-48],[-48]],[[0,0],[0]],[[-864,-208],[-208]],[[0,0],[0]],[[-6048,-256],[-256]],[[0,0],[0]],[[-16704,-112],[-112]],[[0,0],[0]],[[-24224,-16],[-16]],[[0]],[[-20352]],[[0]],[[-10208]],[[0]],[[-3008]],[[0]],[[-480]],[[0]],[[-32]]]
theorem step035 : p035=NestedArithmetic.mul p034 p028 := by decide +kernel
#print axioms step035
theorem h035 : NestedArithmetic.compile e035=p035 := StagedExprCompile.compile_times e035 e034 e028 p034 p028 p035 rfl h034 h028 step035
#print axioms h035
end Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
