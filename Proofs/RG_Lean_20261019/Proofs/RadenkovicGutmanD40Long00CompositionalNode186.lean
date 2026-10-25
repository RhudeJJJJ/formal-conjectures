/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD40Long00CompositionalNode178
import Proofs.RadenkovicGutmanD40Long00CompositionalNode185
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e186 : NestedArithmetic.Expr 3 := .plus e178 e185
noncomputable def p186 : NestedHorner.Poly 3 := [[[-76],[0]],[[0,0],[0]],[[-1252,0],[0,0]],[[0,0],[0,0]],[[-8632,0],[0,0]],[[0,0],[0,0]],[[-32276,0],[0,0]],[[0,0],[0,0]],[[-70816,0],[0,0]],[[0,0],[0,0]],[[-91824,-76],[-76,0]],[[0,0],[0,0]],[[-66440,-568],[-568,0]],[[0,0],[0,0]],[[-21812,-1392],[-1392,0]],[[0,0],[0,0]],[[-84,-1184],[-1184,0]],[[0,0],[0,0]],[[1116,-164],[-164,0]],[[0,0],[0,0]],[[0,120],[120,-76]]]
theorem step186 : p186=NestedHorner.add p178 p185 := by decide +kernel
#print axioms step186
theorem h186 : NestedArithmetic.compile e186=p186 := StagedExprCompile.compile_plus e186 e178 e185 p178 p185 p186 rfl h178 h185 step186
#print axioms h186
end Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
