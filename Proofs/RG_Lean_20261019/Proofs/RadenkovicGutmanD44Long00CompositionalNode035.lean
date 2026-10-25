/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD44Long00CompositionalNode034
import Proofs.RadenkovicGutmanD44Long00CompositionalNode028
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e035 : NestedArithmetic.Expr 3 := .times e034 e028
noncomputable def p035 : NestedHorner.Poly 3 := [[[0],[0]],[[0,-132],[-132]],[[0,0],[0]],[[-2376,-572],[-572]],[[0,0],[0]],[[-16632,-704],[-704]],[[0,0],[0]],[[-45936,-308],[-308]],[[0,0],[0]],[[-66616,-44],[-44]],[[0]],[[-55968]],[[0]],[[-28072]],[[0]],[[-8272]],[[0]],[[-1320]],[[0]],[[-88]]]
theorem step035 : p035=NestedArithmetic.mul p034 p028 := by decide +kernel
#print axioms step035
theorem h035 : NestedArithmetic.compile e035=p035 := StagedExprCompile.compile_times e035 e034 e028 p034 p028 p035 rfl h034 h028 step035
#print axioms h035
end Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
