/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD35Long00CompositionalNode034
import Proofs.RadenkovicGutmanD35Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e217 : NestedArithmetic.Expr 3 := .times e034 e170
noncomputable def p217 : NestedHorner.Poly 3 := [[[-70],[0]],[[0,0],[0]],[[-1050,0],[0]],[[0,0],[0]],[[-6580,0],[0]],[[0,0],[0]],[[-22330,0],[0]],[[0,0],[0]],[[-44520,0],[0]],[[0,0],[0]],[[-52990,-35],[-35]],[[0,0],[0]],[[-36540,-245],[-245]],[[0,0],[0]],[[-13230,-560],[-560]],[[0,0],[0]],[[-1890,-455],[-455]],[[0,0],[0]],[[0,-105],[-105]]]
theorem step217 : p217=NestedArithmetic.mul p034 p170 := by decide +kernel
#print axioms step217
theorem h217 : NestedArithmetic.compile e217=p217 := StagedExprCompile.compile_times e217 e034 e170 p034 p170 p217 rfl h034 h170 step217
#print axioms h217
end Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
