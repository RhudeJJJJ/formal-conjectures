/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD37Long00CompositionalNode164
import Proofs.RadenkovicGutmanD37Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e165 : NestedArithmetic.Expr 3 := .times e164 e122
noncomputable def p165 : NestedHorner.Poly 3 := [[[-70],[0]],[[0,0],[0]],[[-1042,0],[0,0]],[[0,0],[0,0]],[[-6468,0],[0,0]],[[0,0],[0,0]],[[-21682,0],[0,0]],[[0,0],[0,0]],[[-42520,0],[0,0]],[[0,0],[0,0]],[[-49368,-70],[-70,0]],[[0,0],[0,0]],[[-32316,-560],[-560,0]],[[0,0],[0,0]],[[-9570,-1540],[-1540,0]],[[0,0],[0,0]],[[414,-1680],[-1680,0]],[[0,0],[0,0]],[[702,-630],[-630,0]],[[0],[0,0]],[[0],[0,-70]]]
theorem step165 : p165=NestedArithmetic.mul p164 p122 := by decide +kernel
#print axioms step165
theorem h165 : NestedArithmetic.compile e165=p165 := StagedExprCompile.compile_times e165 e164 e122 p164 p122 p165 rfl h164 h122 step165
#print axioms h165
end Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
