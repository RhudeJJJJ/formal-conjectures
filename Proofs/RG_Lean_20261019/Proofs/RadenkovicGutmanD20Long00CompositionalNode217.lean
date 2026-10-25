/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD20Long00CompositionalNode034
import Proofs.RadenkovicGutmanD20Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e217 : NestedArithmetic.Expr 3 := .times e034 e170
noncomputable def p217 : NestedHorner.Poly 3 := [[[-40],[0]],[[0,0],[0]],[[-600,0],[0]],[[0,0],[0]],[[-3760,0],[0]],[[0,0],[0]],[[-12760,0],[0]],[[0,0],[0]],[[-25440,0],[0]],[[0,0],[0]],[[-30280,-20],[-20]],[[0,0],[0]],[[-20880,-140],[-140]],[[0,0],[0]],[[-7560,-320],[-320]],[[0,0],[0]],[[-1080,-260],[-260]],[[0,0],[0]],[[0,-60],[-60]]]
theorem step217 : p217=NestedArithmetic.mul p034 p170 := by decide +kernel
#print axioms step217
theorem h217 : NestedArithmetic.compile e217=p217 := StagedExprCompile.compile_times e217 e034 e170 p034 p170 p217 rfl h034 h170 step217
#print axioms h217
end Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
