/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD32Long00CompositionalNode034
import Proofs.RadenkovicGutmanD32Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e217 : NestedArithmetic.Expr 3 := .times e034 e170
noncomputable def p217 : NestedHorner.Poly 3 := [[[-64],[0]],[[0,0],[0]],[[-960,0],[0]],[[0,0],[0]],[[-6016,0],[0]],[[0,0],[0]],[[-20416,0],[0]],[[0,0],[0]],[[-40704,0],[0]],[[0,0],[0]],[[-48448,-32],[-32]],[[0,0],[0]],[[-33408,-224],[-224]],[[0,0],[0]],[[-12096,-512],[-512]],[[0,0],[0]],[[-1728,-416],[-416]],[[0,0],[0]],[[0,-96],[-96]]]
theorem step217 : p217=NestedArithmetic.mul p034 p170 := by decide +kernel
#print axioms step217
theorem h217 : NestedArithmetic.compile e217=p217 := StagedExprCompile.compile_times e217 e034 e170 p034 p170 p217 rfl h034 h170 step217
#print axioms h217
end Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
