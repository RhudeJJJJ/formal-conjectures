/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD20Long00CompositionalNode034
import Proofs.RadenkovicGutmanD20Long00CompositionalNode028
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e035 : NestedArithmetic.Expr 3 := .times e034 e028
noncomputable def p035 : NestedHorner.Poly 3 := [[[0],[0]],[[0,-60],[-60]],[[0,0],[0]],[[-1080,-260],[-260]],[[0,0],[0]],[[-7560,-320],[-320]],[[0,0],[0]],[[-20880,-140],[-140]],[[0,0],[0]],[[-30280,-20],[-20]],[[0]],[[-25440]],[[0]],[[-12760]],[[0]],[[-3760]],[[0]],[[-600]],[[0]],[[-40]]]
theorem step035 : p035=NestedArithmetic.mul p034 p028 := by decide +kernel
#print axioms step035
theorem h035 : NestedArithmetic.compile e035=p035 := StagedExprCompile.compile_times e035 e034 e028 p034 p028 p035 rfl h034 h028 step035
#print axioms h035
end Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
