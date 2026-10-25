/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD21Long00CompositionalNode034
import Proofs.RadenkovicGutmanD21Long00CompositionalNode028
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e035 : NestedArithmetic.Expr 3 := .times e034 e028
noncomputable def p035 : NestedHorner.Poly 3 := [[[0],[0]],[[0,-63],[-63]],[[0,0],[0]],[[-1134,-273],[-273]],[[0,0],[0]],[[-7938,-336],[-336]],[[0,0],[0]],[[-21924,-147],[-147]],[[0,0],[0]],[[-31794,-21],[-21]],[[0]],[[-26712]],[[0]],[[-13398]],[[0]],[[-3948]],[[0]],[[-630]],[[0]],[[-42]]]
theorem step035 : p035=NestedArithmetic.mul p034 p028 := by decide +kernel
#print axioms step035
theorem h035 : NestedArithmetic.compile e035=p035 := StagedExprCompile.compile_times e035 e034 e028 p034 p028 p035 rfl h034 h028 step035
#print axioms h035
end Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
