/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD39Long00CompositionalNode034
import Proofs.RadenkovicGutmanD39Long00CompositionalNode028
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e035 : NestedArithmetic.Expr 3 := .times e034 e028
noncomputable def p035 : NestedHorner.Poly 3 := [[[0],[0]],[[0,-117],[-117]],[[0,0],[0]],[[-2106,-507],[-507]],[[0,0],[0]],[[-14742,-624],[-624]],[[0,0],[0]],[[-40716,-273],[-273]],[[0,0],[0]],[[-59046,-39],[-39]],[[0]],[[-49608]],[[0]],[[-24882]],[[0]],[[-7332]],[[0]],[[-1170]],[[0]],[[-78]]]
theorem step035 : p035=NestedArithmetic.mul p034 p028 := by decide +kernel
#print axioms step035
theorem h035 : NestedArithmetic.compile e035=p035 := StagedExprCompile.compile_times e035 e034 e028 p034 p028 p035 rfl h034 h028 step035
#print axioms h035
end Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
