/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD40Long00CompositionalNode165
import Proofs.RadenkovicGutmanD40Long00CompositionalNode172
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e173 : NestedArithmetic.Expr 3 := .plus e165 e172
noncomputable def p173 : NestedHorner.Poly 3 := [[[-76],[0]],[[0,0],[0]],[[-1052,0],[0,0]],[[0,0],[0,0]],[[-5832,0],[0,0]],[[0,0],[0,0]],[[-16076,0],[0,0]],[[0,0],[0,0]],[[-20816,0],[0,0]],[[0,0],[0,0]],[[-3024,-76],[-76,0]],[[0,0],[0,0]],[[25160,-568],[-568,0]],[[0,0],[0,0]],[[31188,-1392],[-1392,0]],[[0,0],[0,0]],[[15516,-1184],[-1184,0]],[[0,0],[0,0]],[[2916,-164],[-164,0]],[[0,0],[0,0]],[[0,120],[120,-76]]]
theorem step173 : p173=NestedHorner.add p165 p172 := by decide +kernel
#print axioms step173
theorem h173 : NestedArithmetic.compile e173=p173 := StagedExprCompile.compile_plus e173 e165 e172 p165 p172 p173 rfl h165 h172 step173
#print axioms h173
end Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
