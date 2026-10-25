/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD37Long00CompositionalNode119
import Proofs.RadenkovicGutmanD37Long00CompositionalNode163
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e164 : NestedArithmetic.Expr 3 := .times e119 e163
noncomputable def p164 : NestedHorner.Poly 3 := [[[-70],[0]],[[0,0],[0]],[[-1042,0],[0,0]],[[0,0],[0,0]],[[-6468,0],[0,0]],[[0,0],[0,0]],[[-21682,0],[0,0]],[[0,0],[0,0]],[[-42520,0],[0,0]],[[0,0],[0,0]],[[-49368,-70],[-70,0]],[[0,0],[0,0]],[[-32316,-560],[-560,0]],[[0,0],[0,0]],[[-9570,-1540],[-1540,0]],[[0,0],[0,0]],[[414,-1680],[-1680,0]],[[0,0],[0,0]],[[702,-630],[-630,0]],[[0],[0,0]],[[0],[0,-70]]]
theorem step164 : p164=NestedArithmetic.mul p119 p163 := by decide +kernel
#print axioms step164
theorem h164 : NestedArithmetic.compile e164=p164 := StagedExprCompile.compile_times e164 e119 e163 p119 p163 p164 rfl h119 h163 step164
#print axioms h164
end Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
