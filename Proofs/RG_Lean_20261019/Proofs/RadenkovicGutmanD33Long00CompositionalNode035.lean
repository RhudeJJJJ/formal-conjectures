/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD33Long00CompositionalNode034
import Proofs.RadenkovicGutmanD33Long00CompositionalNode028
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e035 : NestedArithmetic.Expr 3 := .times e034 e028
noncomputable def p035 : NestedHorner.Poly 3 := [[[0],[0]],[[0,-99],[-99]],[[0,0],[0]],[[-1782,-429],[-429]],[[0,0],[0]],[[-12474,-528],[-528]],[[0,0],[0]],[[-34452,-231],[-231]],[[0,0],[0]],[[-49962,-33],[-33]],[[0]],[[-41976]],[[0]],[[-21054]],[[0]],[[-6204]],[[0]],[[-990]],[[0]],[[-66]]]
theorem step035 : p035=NestedArithmetic.mul p034 p028 := by decide +kernel
#print axioms step035
theorem h035 : NestedArithmetic.compile e035=p035 := StagedExprCompile.compile_times e035 e034 e028 p034 p028 p035 rfl h034 h028 step035
#print axioms h035
end Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
