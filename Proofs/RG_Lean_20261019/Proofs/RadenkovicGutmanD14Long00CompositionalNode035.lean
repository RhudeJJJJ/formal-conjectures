/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD14Long00CompositionalNode034
import Proofs.RadenkovicGutmanD14Long00CompositionalNode028
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e035 : NestedArithmetic.Expr 3 := .times e034 e028
noncomputable def p035 : NestedHorner.Poly 3 := [[[0],[0]],[[0,-42],[-42]],[[0,0],[0]],[[-756,-182],[-182]],[[0,0],[0]],[[-5292,-224],[-224]],[[0,0],[0]],[[-14616,-98],[-98]],[[0,0],[0]],[[-21196,-14],[-14]],[[0]],[[-17808]],[[0]],[[-8932]],[[0]],[[-2632]],[[0]],[[-420]],[[0]],[[-28]]]
theorem step035 : p035=NestedArithmetic.mul p034 p028 := by decide +kernel
#print axioms step035
theorem h035 : NestedArithmetic.compile e035=p035 := StagedExprCompile.compile_times e035 e034 e028 p034 p028 p035 rfl h034 h028 step035
#print axioms h035
end Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
