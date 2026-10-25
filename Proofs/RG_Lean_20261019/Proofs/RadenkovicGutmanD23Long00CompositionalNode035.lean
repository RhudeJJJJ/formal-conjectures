/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD23Long00CompositionalNode034
import Proofs.RadenkovicGutmanD23Long00CompositionalNode028
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e035 : NestedArithmetic.Expr 3 := .times e034 e028
noncomputable def p035 : NestedHorner.Poly 3 := [[[0],[0]],[[0,-69],[-69]],[[0,0],[0]],[[-1242,-299],[-299]],[[0,0],[0]],[[-8694,-368],[-368]],[[0,0],[0]],[[-24012,-161],[-161]],[[0,0],[0]],[[-34822,-23],[-23]],[[0]],[[-29256]],[[0]],[[-14674]],[[0]],[[-4324]],[[0]],[[-690]],[[0]],[[-46]]]
theorem step035 : p035=NestedArithmetic.mul p034 p028 := by decide +kernel
#print axioms step035
theorem h035 : NestedArithmetic.compile e035=p035 := StagedExprCompile.compile_times e035 e034 e028 p034 p028 p035 rfl h034 h028 step035
#print axioms h035
end Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
